import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# ZIP-203: transaction expiry semantics

ZIP-203 defines transaction expiry: each Overwinter+ transaction carries an
`nExpiryHeight` field. The spec says

> No limit: To set no limit on transactions (so that they do not expire),
> nExpiryHeight should be set to 0.

and the Overwinter-onward consensus rule

> If a transaction is not a coinbase transaction and its nExpiryHeight
> field is nonzero, then it MUST NOT be mined at a block height greater
> than its nExpiryHeight.

Zebra encodes this in several places:

* `Transaction::expiry_height` in `zebra-chain/src/transaction.rs:492-513`
  returns `None` for V1/V2 (which lack the field entirely) and for V3+ with
  `Height(0)` (the explicit "no expiry" sentinel), and `Some(h)` otherwise.
* `validate_expiry_height_mined` in
  `zebra-consensus/src/transaction/check.rs:474-490` enforces the
  Overwinter-onward rule: if `expiry_height` is `Some(h)` and
  `block_height > h`, the transaction is rejected with `ExpiredTransaction`.
* `non_coinbase_expiry_height` in
  `zebra-consensus/src/transaction/check.rs:414-442` short-circuits to `Ok`
  for non-Overwintered (V1/V2) transactions.
* `coinbase_expiry_height` in
  `zebra-consensus/src/transaction/check.rs:373-407` enforces the stricter
  NU5-onward coinbase rule: `expiry_height = Some(block_height)` exactly.

The cap `MAX_EXPIRY_HEIGHT = 499_999_999` from
`zebra-chain/src/block/height.rs:78` bounds the field for all
pre-NU5 transactions and for all non-coinbase transactions from NU5 onward;
it is enforced by `validate_expiry_height_max` in
`zebra-consensus/src/transaction/check.rs:450-468`.

We model:

* the *field provenance* (V1/V2 lacks the field; V3+ has it with `0` as
  sentinel), reproducing the Rust `Option<Height>` accessor exactly,
* the non-coinbase `expired` predicate as the conjunction `field is some
  ∧ h > field`,
* the NU5-onward coinbase "equality" predicate,
* monotonicity in block height, decidability, boundary sharpness, and the
  `MAX_EXPIRY_HEIGHT` cap,
* the equivalence between `mineable` and `¬ expired` (matching the two
  sides of the Rust check).

Source: <https://zips.z.cash/zip-0203#specification>
Source: `zebra-chain/src/transaction.rs:492` (`expiry_height`)
Source: `zebra-chain/src/transaction.rs:377` (`is_overwintered`)
Source: `zebra-chain/src/block/height.rs:78` (`MAX_EXPIRY_HEIGHT`)
Source: `zebra-consensus/src/transaction/check.rs:373`
(`coinbase_expiry_height`)
Source: `zebra-consensus/src/transaction/check.rs:414`
(`non_coinbase_expiry_height`)
Source: `zebra-consensus/src/transaction/check.rs:450`
(`validate_expiry_height_max`)
Source: `zebra-consensus/src/transaction/check.rs:474`
(`validate_expiry_height_mined`).
-/

namespace Zebra.Zip203Expiry

/-! ## Constants -/

/-- `Height::MAX_EXPIRY_HEIGHT = 499_999_999`. Source:
`zebra-chain/src/block/height.rs:78`. Pre-NU5 transactions and NU5+
non-coinbase transactions must have `expiry_height ≤ MAX_EXPIRY_HEIGHT`. -/
def MAX_EXPIRY_HEIGHT : Nat := 499_999_999

/-- `Height::MAX = u32::MAX / 2 = 2^31 - 1`. Source:
`zebra-chain/src/block/height.rs:67`. -/
def HEIGHT_MAX : Nat := 2_147_483_647

/-! ## Model

A transaction's *raw* expiry field, when present, is a `u32` (modelled as
`Nat`) with `0` reserved as the "no expiry" sentinel. But V1 and V2
transactions don't have the field at all: they predate Overwinter, where
`fOverwintered = 0` and `expiry_height` is absent from the serialised
form. To stay faithful to Rust, we distinguish *absence* from *sentinel*.
-/

/-- Transaction version classes, distinguishing pre-Overwinter (V1/V2) from
post-Overwinter (V3, V4, V5, …). Source:
`zebra-chain/src/transaction.rs:377` (`Transaction::is_overwintered`).

We collapse all post-Overwinter versions into one constructor because the
expiry-field semantics are identical across V3..V6. The boolean argument
to `overwintered` is the raw `nExpiryHeight` field value. -/
inductive TxVersion : Type
  /-- V1 or V2: pre-Overwinter, no `nExpiryHeight` field present. -/
  | preOverwinter : TxVersion
  /-- V3+: Overwintered, with a `u32` `nExpiryHeight` field. `0` is the
  "no expiry" sentinel; non-zero is a real expiry height. -/
  | overwintered (field : Nat) : TxVersion
  deriving DecidableEq

/-- The `is_overwintered` accessor. Source:
`zebra-chain/src/transaction.rs:377`. -/
def TxVersion.isOverwintered : TxVersion → Bool
  | .preOverwinter   => false
  | .overwintered _  => true

/-- The `expiry_height()` accessor, returning `Option<Height>`. Source:
`zebra-chain/src/transaction.rs:492-513`:

* V1/V2 ⇒ `None` (the field is absent from the wire);
* V3+ with `Height(0)` ⇒ `None` (the "no expiry" sentinel);
* V3+ with `Height(n)`, `n ≠ 0` ⇒ `Some n`.

Both `None`-producing cases collapse into the same `Option` value, but
they have different *provenance* — Rust's `Option::None` is the join of
"no field" and "sentinel". -/
def TxVersion.expiryHeight : TxVersion → Option Nat
  | .preOverwinter      => none
  | .overwintered 0     => none
  | .overwintered (n+1) => some (n+1)

/-! ## Field provenance (V1/V2 ≠ field=0) -/

/-- **T1 (provenance: V1/V2 has no expiry).** Pre-Overwinter transactions
return `None` because the `nExpiryHeight` field is absent from their
serialised form, not because of any sentinel. Source:
`zebra-chain/src/transaction.rs:494`
(`Transaction::V1 { .. } | Transaction::V2 { .. } => None`). -/
theorem preOverwinter_expiryHeight :
    TxVersion.preOverwinter.expiryHeight = none := rfl

/-- **T2 (provenance: V3+ sentinel).** An Overwintered transaction with
the explicit sentinel field=0 returns `None`. This is the ZIP-203 "no
limit" clause. Source: `zebra-chain/src/transaction.rs:501`
(`block::Height(0) => None`). -/
theorem overwintered_zero_expiryHeight :
    (TxVersion.overwintered 0).expiryHeight = none := rfl

/-- **T3 (provenance: V3+ non-sentinel).** An Overwintered transaction with
non-zero field returns `Some` of that field. Source:
`zebra-chain/src/transaction.rs:502`
(`block::Height(expiry_height) => Some(block::Height(*expiry_height))`). -/
theorem overwintered_nonzero_expiryHeight (n : Nat) (hne : n ≠ 0) :
    (TxVersion.overwintered n).expiryHeight = some n := by
  cases n with
  | zero      => exact (hne rfl).elim
  | succ n'   => rfl

/-- **T4 (None is a join of two distinct causes).** Even though
`expiryHeight = none` for both V1/V2 and the field=0 sentinel, the
provenance is not the same: `is_overwintered` distinguishes them. This
is the structural reason `non_coinbase_expiry_height` in Rust short-
circuits on `!is_overwintered()` rather than on `expiry_height().is_none()`.
Source: `zebra-consensus/src/transaction/check.rs:418`. -/
theorem expiryHeight_none_split (tx : TxVersion) (hnone : tx.expiryHeight = none) :
    tx = TxVersion.preOverwinter ∨ tx = TxVersion.overwintered 0 := by
  cases tx with
  | preOverwinter        => exact Or.inl rfl
  | overwintered field   =>
      cases field with
      | zero    => exact Or.inr rfl
      | succ n  =>
          -- expiryHeight (overwintered (n+1)) = some (n+1), contradicting hnone
          exact nomatch hnone

/-! ## The `expired` predicate

The non-coinbase Overwinter-onward consensus rule. We define it on the
post-`expiry_height()` `Option<Height>` view, matching the body of
`validate_expiry_height_mined`. -/

/-- **The** ZIP-203 expiry predicate: a transaction is expired at block
height `h` iff its `expiry_height()` accessor returns `some he` *and*
`h > he`. This is the consensus rule body in
`zebra-consensus/src/transaction/check.rs:479-486`:

```rust
if let Some(expiry_height) = expiry_height {
    if *block_height > expiry_height {
        Err(TransactionError::ExpiredTransaction { ... })?
    }
}
```

`expiry_height = None` (whether from V1/V2 absence or the field=0
sentinel) makes the predicate vacuously false: V1/V2 don't expire, and
field=0 means "no limit". -/
def expired (tx : TxVersion) (h : Nat) : Prop :=
  ∃ he, tx.expiryHeight = some he ∧ h > he

/-! ## Core theorems -/

/-- **T5 (Rust-shape unfolding).** Direct statement of the predicate. -/
theorem expired_iff_option (tx : TxVersion) (h : Nat) :
    expired tx h ↔ ∃ he, tx.expiryHeight = some he ∧ h > he := Iff.rfl

/-- **T6 (V1/V2 never expires).** Pre-Overwinter transactions don't carry
the expiry field, so they're never subject to expiry. This is why
`non_coinbase_expiry_height` short-circuits on `!is_overwintered()`. -/
theorem not_expired_preOverwinter (h : Nat) :
    ¬ expired TxVersion.preOverwinter h := by
  rintro ⟨_, hsome, _⟩
  exact nomatch hsome

/-- **T7 (field=0 sentinel never expires).** An Overwintered transaction
with `nExpiryHeight = 0` can never expire, at any height. ZIP-203
"no limit" clause. -/
theorem not_expired_sentinel (h : Nat) :
    ¬ expired (TxVersion.overwintered 0) h := by
  rintro ⟨_, hsome, _⟩
  exact nomatch hsome

/-- **T8 (non-sentinel expired iff `h > field`).** For a V3+ transaction
with non-zero field `n`, expiry is exactly `h > n`. -/
theorem expired_overwintered_succ_iff (n h : Nat) :
    expired (TxVersion.overwintered (n+1)) h ↔ h > n+1 := by
  unfold expired
  constructor
  · rintro ⟨he, hsome, hgt⟩
    have heq : n + 1 = he := by
      simpa [TxVersion.expiryHeight] using hsome
    exact heq.symm ▸ hgt
  · intro hgt
    exact ⟨n+1, rfl, hgt⟩

/-- **T9 (monotone in `h`).** Once a transaction has expired at some
height `h₁`, it is still expired at any later height `h₂ ≥ h₁`. Matches
the consensus intuition: blocks only get later, so a once-expired
transaction stays rejected forever. -/
theorem expired_mono (tx : TxVersion) {h₁ h₂ : Nat}
    (hle : h₁ ≤ h₂) (he : expired tx h₁) :
    expired tx h₂ := by
  obtain ⟨ex, hsome, hgt⟩ := he
  exact ⟨ex, hsome, lt_of_lt_of_le hgt hle⟩

/-- **T10 (contrapositive: not-expired is downward-closed).** Convenient
for mempool-eviction reasoning: if a transaction wasn't expired later,
it wasn't expired earlier. -/
theorem not_expired_of_le (tx : TxVersion) {h₁ h₂ : Nat}
    (hle : h₁ ≤ h₂) (hne : ¬ expired tx h₂) :
    ¬ expired tx h₁ := fun he => hne (expired_mono tx hle he)

/-! ## Boundary and sharpness lemmas -/

/-- **T11 (sharpness at `h = expiry_height`).** Right at the expiry
height, the transaction is *not yet* expired — Rust uses strict `>`.
For a non-zero field `n+1`, `expired` at height `n+1` is false. -/
theorem not_expired_at_boundary (n : Nat) :
    ¬ expired (TxVersion.overwintered (n+1)) (n+1) := by
  rw [expired_overwintered_succ_iff]
  exact Nat.lt_irrefl _

/-- **T12 (just-past-boundary expires).** The minimal expiring height for
a non-zero field `n+1` is `n+2`. -/
theorem expired_at_succ (n : Nat) :
    expired (TxVersion.overwintered (n+1)) (n+2) := by
  rw [expired_overwintered_succ_iff]
  exact Nat.lt_succ_self _

/-- **T13 (small heights never expire).** For a non-zero field `n+1` and
height `h ≤ n+1`, the transaction is not expired. -/
theorem not_expired_below (n : Nat) {h : Nat} (hle : h ≤ n + 1) :
    ¬ expired (TxVersion.overwintered (n + 1)) h := by
  rw [expired_overwintered_succ_iff]
  intro hgt
  exact (Nat.lt_irrefl _) (lt_of_lt_of_le hgt hle)

/-! ## Interaction with `MAX_EXPIRY_HEIGHT` -/

/-- **T14 (cap respects sentinel).** `0` (the "no expiry" sentinel) is
trivially `≤ MAX_EXPIRY_HEIGHT`, so the consensus cap never rejects the
sentinel. -/
theorem zero_le_max_expiry : (0 : Nat) ≤ MAX_EXPIRY_HEIGHT := by
  unfold MAX_EXPIRY_HEIGHT; omega

/-- **T15 (cap is strictly below Height::MAX).** The expiry cap is
considerably smaller than the maximum representable block height, so a
field at the cap can still be exceeded — expiry *can* fire even at the
cap. -/
theorem max_expiry_lt_height_max : MAX_EXPIRY_HEIGHT < HEIGHT_MAX := by
  unfold MAX_EXPIRY_HEIGHT HEIGHT_MAX; omega

/-- **T16 (capped field can expire).** A non-zero, capped field is
expired at height `MAX_EXPIRY_HEIGHT + 1` — well within the
representable range. -/
theorem expired_at_capped_succ :
    expired (TxVersion.overwintered MAX_EXPIRY_HEIGHT) (MAX_EXPIRY_HEIGHT + 1) := by
  -- MAX_EXPIRY_HEIGHT = 499_999_999 ≠ 0, so use the existence witness directly
  refine ⟨MAX_EXPIRY_HEIGHT, ?_, Nat.lt_succ_self _⟩
  unfold MAX_EXPIRY_HEIGHT TxVersion.expiryHeight
  rfl

/-- The admissibility cap: a field with `field ≤ MAX_EXPIRY_HEIGHT`
satisfies `validate_expiry_height_max`. Source:
`zebra-consensus/src/transaction/check.rs:450-468`. -/
def AdmissibleCap (field : Nat) : Prop := field ≤ MAX_EXPIRY_HEIGHT

/-- **T17.** The "no expiry" sentinel is admissible under the cap. -/
theorem admissibleCap_zero : AdmissibleCap 0 := by
  unfold AdmissibleCap; exact zero_le_max_expiry

/-- **T18.** The cap itself is admissible (the rule is `≤`, not `<`). -/
theorem admissibleCap_at_max : AdmissibleCap MAX_EXPIRY_HEIGHT := by
  unfold AdmissibleCap; exact Nat.le_refl _

/-- **T19.** Just-above the cap is *not* admissible. -/
theorem not_admissibleCap_succ_max : ¬ AdmissibleCap (MAX_EXPIRY_HEIGHT + 1) := by
  unfold AdmissibleCap MAX_EXPIRY_HEIGHT
  decide

/-- **T20 (V1/V2 cap is vacuous).** Pre-Overwinter transactions have no
field, so `validate_expiry_height_max` is vacuous on them (the body
`if let Some(expiry_height) = expiry_height` skips). Captures the
short-circuit behaviour of `non_coinbase_expiry_height`. -/
theorem preOverwinter_cap_vacuous (tx : TxVersion)
    (hpre : tx = TxVersion.preOverwinter) :
    ∀ {ex}, tx.expiryHeight = some ex → ex ≤ MAX_EXPIRY_HEIGHT := by
  subst hpre
  intro ex hsome
  exact nomatch hsome

/-! ## NU5-onward coinbase rule

`coinbase_expiry_height` in
`zebra-consensus/src/transaction/check.rs:373-407` enforces a strictly
stronger rule for NU5-onward coinbase transactions: the expiry height
*must equal* the block height (not just ≤ MAX). Pre-NU5 coinbase is
governed only by the cap.
-/

/-- The NU5-onward coinbase rule: `expiry_height = Some(block_height)`
*exactly*. Source: `zebra-consensus/src/transaction/check.rs:388`. -/
def CoinbaseNu5Valid (tx : TxVersion) (blockHeight : Nat) : Prop :=
  tx.expiryHeight = some blockHeight

/-- **T21 (NU5 coinbase rejects V1/V2).** A V1/V2 coinbase cannot satisfy
the NU5-onward rule because its `expiry_height()` is always `None`,
never `Some(block_height)`. (V1/V2 coinbase can't appear at NU5 anyway,
but the Rust check is stated as `expiry_height != Some(*block_height)`
and would reject.) -/
theorem coinbase_nu5_rejects_preOverwinter (blockHeight : Nat) :
    ¬ CoinbaseNu5Valid TxVersion.preOverwinter blockHeight := by
  intro h
  exact nomatch h

/-- **T22 (NU5 coinbase rejects field=0).** The sentinel `field = 0` does
not satisfy the NU5 coinbase rule because `expiry_height()` returns
`None`. So a NU5 coinbase cannot use the "no expiry" sentinel. -/
theorem coinbase_nu5_rejects_sentinel (blockHeight : Nat) :
    ¬ CoinbaseNu5Valid (TxVersion.overwintered 0) blockHeight := by
  intro h
  exact nomatch h

/-- **T23 (NU5 coinbase accepts exact match).** A NU5 coinbase with
`nExpiryHeight = block_height` (and block_height > 0) is accepted. -/
theorem coinbase_nu5_accepts_match (n : Nat) :
    CoinbaseNu5Valid (TxVersion.overwintered (n+1)) (n+1) := rfl

/-- **T24 (NU5 coinbase rejects off-by-one).** A NU5 coinbase with
`nExpiryHeight` one below the block height is rejected. -/
theorem coinbase_nu5_rejects_off_by_one (n : Nat) :
    ¬ CoinbaseNu5Valid (TxVersion.overwintered (n+1)) (n+2) := by
  unfold CoinbaseNu5Valid TxVersion.expiryHeight
  intro h
  exact Nat.succ_ne_self _ (Option.some.inj h).symm

/-- **T25 (NU5 coinbase admissibility implies cap admissibility).** Any
NU5 coinbase satisfying the equality rule with `block_height ≤
MAX_EXPIRY_HEIGHT` also satisfies the cap. (Trivial corollary, but
documents that the NU5 rule is the *stronger* of the two.) -/
theorem coinbase_nu5_implies_cap (tx : TxVersion) (blockHeight : Nat)
    (hvalid : CoinbaseNu5Valid tx blockHeight)
    (hcap : blockHeight ≤ MAX_EXPIRY_HEIGHT) :
    ∃ ex, tx.expiryHeight = some ex ∧ AdmissibleCap ex := by
  refine ⟨blockHeight, hvalid, ?_⟩
  unfold AdmissibleCap
  exact hcap

/-! ## Decidability and Rust-style helpers -/

/-- **T26 (decidability).** `expired tx h` is decidable: it reduces to a
decidable case-split on `tx.expiryHeight`. The Rust check is itself a
decidable computation; this matches it. -/
instance instDecidableExpired (tx : TxVersion) (h : Nat) :
    Decidable (expired tx h) :=
  match hview : tx.expiryHeight with
  | none =>
      isFalse (by
        rintro ⟨_, hsome, _⟩
        rw [hview] at hsome
        exact nomatch hsome)
  | some he =>
      if hgt : h > he then
        isTrue ⟨he, hview, hgt⟩
      else
        isFalse (by
          rintro ⟨he', hsome', hgt'⟩
          rw [hview] at hsome'
          have : he' = he := (Option.some.inj hsome').symm
          exact hgt (this ▸ hgt'))

/-- **T27 (decidability of admissibility cap).** -/
instance instDecidableAdmissibleCap (field : Nat) :
    Decidable (AdmissibleCap field) := by
  unfold AdmissibleCap
  infer_instance

/-- **T28 (decidability of NU5 coinbase rule).** -/
instance instDecidableCoinbaseNu5Valid (tx : TxVersion) (blockHeight : Nat) :
    Decidable (CoinbaseNu5Valid tx blockHeight) := by
  unfold CoinbaseNu5Valid
  infer_instance

/-! ## Concrete examples -/

/-- **T29 (concrete expiry case).** A V3+ transaction with `nExpiryHeight =
1000` is expired at block height `1001` but not at `1000`. -/
theorem example_expired_concrete :
    expired (TxVersion.overwintered 1000) 1001 ∧
    ¬ expired (TxVersion.overwintered 1000) 1000 := by
  refine ⟨⟨1000, rfl, by decide⟩, ?_⟩
  rw [show (1000 : Nat) = 999 + 1 from rfl, expired_overwintered_succ_iff]
  omega

/-- **T30 (concrete no-expiry sentinel case).** A V3+ transaction with the
sentinel `nExpiryHeight = 0` is never expired, however far in the future
the block height gets. -/
theorem example_no_expiry_far_future :
    ¬ expired (TxVersion.overwintered 0) 1_000_000_000 :=
  not_expired_sentinel _

/-- **T31 (concrete V1/V2 case).** A V1 transaction is never expired, no
matter the height. -/
theorem example_preOverwinter_far_future :
    ¬ expired TxVersion.preOverwinter 1_000_000_000 :=
  not_expired_preOverwinter _

/-- **T32 (concrete NU5 coinbase match).** A NU5 coinbase at block height
2_000_000 with `nExpiryHeight = 2_000_000` is accepted. -/
theorem example_coinbase_nu5_match :
    CoinbaseNu5Valid (TxVersion.overwintered 2_000_000) 2_000_000 := rfl

/-! ## Connection to mining rule

The mining-side check in `validate_expiry_height_mined`
(`zebra-consensus/src/transaction/check.rs:474-490`) is equivalent to
`¬ expired`. We bundle the two directions of that equivalence here so
that downstream proofs can switch between "Zebra accepted at this
height" and "not expired" freely.
-/

/-- A transaction is *mineable* at height `h` iff the Overwinter rule
does not reject it: either its `expiry_height()` is `None`, or
`h ≤ expiry_height`. Matches the body of `validate_expiry_height_mined`. -/
def mineable (tx : TxVersion) (h : Nat) : Prop :=
  tx.expiryHeight = none ∨ ∃ he, tx.expiryHeight = some he ∧ h ≤ he

/-- **T33 (`mineable` ↔ not `expired`).** The mining-side check accepts
exactly when the expiry-side predicate rejects. This is the precise
statement of the equivalence between the two sides of ZIP-203 in
Zebra's codebase. -/
theorem mineable_iff_not_expired (tx : TxVersion) (h : Nat) :
    mineable tx h ↔ ¬ expired tx h := by
  unfold mineable expired
  constructor
  · rintro (hnone | ⟨he, hsome, hle⟩)
    · rintro ⟨_, hsome', _⟩
      rw [hnone] at hsome'
      exact nomatch hsome'
    · rintro ⟨he', hsome', hgt⟩
      have : he' = he := by
        rw [hsome] at hsome'
        exact (Option.some.inj hsome').symm
      rw [this] at hgt
      exact absurd hgt (Nat.not_lt_of_le hle)
  · intro hne
    -- Case-split on the underlying TxVersion to get the option to reduce
    cases tx with
    | preOverwinter => exact Or.inl rfl
    | overwintered field =>
        cases field with
        | zero        => exact Or.inl rfl
        | succ n      =>
            right
            refine ⟨n + 1, rfl, ?_⟩
            by_contra hgt
            exact hne ⟨n + 1, rfl, Nat.lt_of_not_le hgt⟩

/-- **T34 (mineable for preOverwinter at every height).** V1/V2 are
mineable at every height — the rule doesn't apply to them. -/
theorem mineable_preOverwinter (h : Nat) :
    mineable TxVersion.preOverwinter h := Or.inl rfl

/-- **T35 (mineable for sentinel at every height).** The "no expiry"
sentinel is mineable at every height. -/
theorem mineable_sentinel (h : Nat) :
    mineable (TxVersion.overwintered 0) h := Or.inl rfl

end Zebra.Zip203Expiry
