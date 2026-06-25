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

Zebra encodes this in two places:

* `Transaction::expiry_height` in `zebra-chain/src/transaction.rs:492-513`
  returns `None` for `Height(0)` and `Some(h)` otherwise — collapsing the
  raw `u32` field into an `Option<Height>` that already carries the "no
  expiry" sentinel.
* `validate_expiry_height_mined` in
  `zebra-consensus/src/transaction/check.rs:474-490` enforces the
  Overwinter rule: if `expiry_height` is `Some(h)` and `block_height > h`,
  the transaction is rejected with `ExpiredTransaction`.

The cap `MAX_EXPIRY_HEIGHT = 499_999_999` from
`zebra-chain/src/block/height.rs:78` bounds the field for all
pre-NU5 transactions and for all non-coinbase transactions; it is enforced
by `validate_expiry_height_max` in
`zebra-consensus/src/transaction/check.rs:450-468`.

We model the expiry field as a `Nat` and prove:

* the `expired` predicate is equivalent to the conjunction `field ≠ 0 ∧
  h > field` (T1),
* `field = 0` makes `expired` vacuous at every height (T2),
* `expired` is monotone in `h`: once expired, always expired (T3),
* the Overwinter cap interacts cleanly with the predicate (T4..),
* `expired` is decidable, matches the Rust `Option::map` view (T7), and
  is sharp at the boundary `h = expiry_height` (T8).

Source: <https://zips.z.cash/zip-0203#specification>
Source: `zebra-chain/src/transaction.rs:492` (`expiry_height`)
Source: `zebra-chain/src/block/height.rs:78` (`MAX_EXPIRY_HEIGHT`)
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

A transaction's expiry field is a single `u32` (modelled as `Nat`).
`0` is the sentinel for "no expiry"; any non-zero value is the actual
expiry height.
-/

/-- The raw `nExpiryHeight` field as it sits on the wire. `0` means "no
expiry". Source: `zebra-chain/src/transaction.rs:498-502` (the
`match expiry_height` arms in `Transaction::expiry_height`).

We use `abbrev` (not `def`) so that arithmetic, ordering, and `0`-literal
instances flow through transparently — the Rust field is just a `u32`. -/
abbrev ExpiryField : Type := Nat

/-- The view as `Option Nat` that matches the Rust `expiry_height()`
return type: `0 ↦ none`, `n ↦ some n`. Source:
`zebra-chain/src/transaction.rs:497-503`. -/
def expiryHeight (field : ExpiryField) : Option Nat :=
  if field = 0 then none else some field

/-- **The** ZIP-203 expiry predicate: a transaction with field `field`
is expired at block height `h` iff `field ≠ 0` *and* `h > field`.

This is the consensus rule from
`zebra-consensus/src/transaction/check.rs:479-486`:

```rust
if let Some(expiry_height) = expiry_height {
    if *block_height > expiry_height {
        Err(TransactionError::ExpiredTransaction { ... })?
    }
}
```

The outer `Some` guard is exactly `field ≠ 0` (per the `expiry_height()`
view), and the inner check is `block_height > expiry_height`. -/
def expired (field : ExpiryField) (h : Nat) : Prop :=
  field ≠ 0 ∧ h > field

/-! ## Core theorems -/

/-- **T1 (the spec iff).** Unfolds the definition: a transaction is
expired at `h` iff its expiry field is non-zero and `h` strictly exceeds
it. This is the theorem the consensus check is implementing. -/
theorem expired_iff (field : ExpiryField) (h : Nat) :
    expired field h ↔ (field ≠ 0 ∧ h > field) := Iff.rfl

/-- **T2 (vacuous at expiry_height = 0).** A transaction with the "no
expiry" sentinel can *never* expire, at any height. This is the ZIP-203
"no limit" clause: `nExpiryHeight = 0 ⇒ no expiry`. -/
theorem not_expired_of_field_zero (h : Nat) :
    ¬ expired 0 h := by
  unfold expired
  intro ⟨hne, _⟩
  exact hne rfl

/-- **T2b (vacuous at expiry_height = 0, all h).** The same fact stated as
a universal: with `field = 0` the predicate is identically false. -/
theorem expired_zero_false (h : Nat) : expired 0 h ↔ False := by
  unfold expired
  constructor
  · intro ⟨hne, _⟩; exact hne rfl
  · intro h; exact h.elim

/-- **T3 (monotone in `h`).** Once a transaction has expired at some
height `h₁`, it is still expired at any later height `h₂ ≥ h₁`. This
matches the consensus intuition: blocks only get later, so a
once-expired transaction stays rejected forever.

Note this is monotonicity in the block height, with `field` fixed. -/
theorem expired_mono (field : ExpiryField) {h₁ h₂ : Nat}
    (hle : h₁ ≤ h₂) (he : expired field h₁) :
    expired field h₂ := by
  unfold expired at he ⊢
  obtain ⟨hne, hgt⟩ := he
  exact ⟨hne, lt_of_lt_of_le hgt hle⟩

/-- **T3b (contrapositive: not-expired is downward-closed).** If a
transaction is not expired at `h₂` and `h₁ ≤ h₂`, it was not expired at
`h₁` either. Convenient for mempool eviction reasoning. -/
theorem not_expired_of_le (field : ExpiryField) {h₁ h₂ : Nat}
    (hle : h₁ ≤ h₂) (hne : ¬ expired field h₂) :
    ¬ expired field h₁ := fun he => hne (expired_mono field hle he)

/-! ## Field/option interplay (matches the Rust `Option<Height>` view) -/

/-- **T4 (`expiryHeight` is `some` iff field is non-zero).** Mirrors the
Rust `expiry_height()` accessor: it returns `Some` precisely on the
non-sentinel branch. -/
theorem expiryHeight_isSome_iff (field : ExpiryField) :
    (expiryHeight field).isSome ↔ field ≠ 0 := by
  unfold expiryHeight
  by_cases hf : field = 0
  · simp [hf]
  · simp [hf]

/-- **T5 (`expiryHeight = none` iff field is zero).** The complementary
direction. -/
theorem expiryHeight_eq_none_iff (field : ExpiryField) :
    expiryHeight field = none ↔ field = 0 := by
  unfold expiryHeight
  by_cases hf : field = 0
  · simp [hf]
  · simp [hf]

set_option linter.flexible false in
/-- **T6 (`expiryHeight = some n` recovers the field).** Reading off the
underlying height when the option says `some`. -/
theorem expiryHeight_eq_some_iff (field : ExpiryField) (n : Nat) :
    expiryHeight field = some n ↔ (field ≠ 0 ∧ field = n) := by
  unfold expiryHeight
  by_cases hf : field = 0
  · simp [hf]
  · constructor
    · intro h
      simp [hf] at h
      exact ⟨hf, h⟩
    · rintro ⟨_, heq⟩
      have hn : n ≠ 0 := heq ▸ hf
      simp [hn, heq]

/-- **T7 (Rust-style reformulation).** `expired` corresponds to
"`expiryHeight` is `some h_e` and `block_height > h_e`": this is the
exact `if let Some(...)` pattern in the Rust check. -/
theorem expired_iff_option (field : ExpiryField) (h : Nat) :
    expired field h ↔
      ∃ he, expiryHeight field = some he ∧ h > he := by
  constructor
  · intro ⟨hne, hgt⟩
    refine ⟨field, ?_, hgt⟩
    rw [expiryHeight_eq_some_iff]; exact ⟨hne, rfl⟩
  · rintro ⟨he, hsome, hgt⟩
    rw [expiryHeight_eq_some_iff] at hsome
    obtain ⟨hne, heq⟩ := hsome
    exact ⟨hne, heq ▸ hgt⟩

/-! ## Boundary and sharpness lemmas -/

/-- **T8 (sharpness at `h = field`).** Right at the expiry height, the
transaction is *not yet* expired — it's only expired at heights
*strictly greater* than `field`. This matches the Rust check:
`block_height > expiry_height` (strict). The `field ≠ 0` hypothesis is
unused here (the boundary fact holds even at the sentinel because `0 > 0`
is false), but it documents the intended call site: non-sentinel
transactions at their own expiry height. -/
theorem not_expired_at_boundary (field : ExpiryField) (_hne : field ≠ 0) :
    ¬ expired field field := by
  unfold expired
  rintro ⟨_, hgt⟩
  exact (Nat.lt_irrefl _) hgt

/-- **T9 (just-past-boundary).** A non-zero `field`, at height `field + 1`,
is expired. The minimal expiring height. -/
theorem expired_at_succ (field : ExpiryField) (hne : field ≠ 0) :
    expired field (field + 1) := ⟨hne, Nat.lt_succ_self _⟩

/-- **T10 (small heights never expire).** For any height `h ≤ field`,
the transaction is not expired. The "valid window" extends through the
expiry height inclusive. -/
theorem not_expired_below (field : ExpiryField) {h : Nat}
    (hle : h ≤ field) : ¬ expired field h := by
  unfold expired
  rintro ⟨_, hgt⟩
  exact (Nat.lt_irrefl _) (lt_of_lt_of_le hgt hle)

/-! ## Interaction with `MAX_EXPIRY_HEIGHT` -/

/-- **T11 (cap respects sentinel).** `0` (the "no expiry" sentinel) is
trivially `≤ MAX_EXPIRY_HEIGHT`, so the consensus cap never rejects the
sentinel. -/
theorem zero_le_max_expiry : (0 : Nat) ≤ MAX_EXPIRY_HEIGHT := by
  unfold MAX_EXPIRY_HEIGHT; omega

/-- **T12 (cap is strictly below Height::MAX).** The expiry cap is
considerably smaller than the maximum representable block height, so a
field at the cap can still be exceeded by a block height — i.e. expiry
*can* fire even at the cap. -/
theorem max_expiry_lt_height_max : MAX_EXPIRY_HEIGHT < HEIGHT_MAX := by
  unfold MAX_EXPIRY_HEIGHT HEIGHT_MAX; omega

/-- **T13 (capped field can expire).** A non-zero, capped field is
expired at height `MAX_EXPIRY_HEIGHT + 1` (well within the representable
range — see T12). Confirms that the cap doesn't make `expired` vacuous. -/
theorem expired_at_capped_succ :
    expired MAX_EXPIRY_HEIGHT (MAX_EXPIRY_HEIGHT + 1) := by
  refine ⟨?_, Nat.lt_succ_self _⟩
  unfold MAX_EXPIRY_HEIGHT
  decide

/-- **T14 (admissibility cap).** A field with `field ≤ MAX_EXPIRY_HEIGHT`
satisfies the Overwinter→Canopy / non-coinbase consensus rule
"`nExpiryHeight ≤ 499_999_999`" (`validate_expiry_height_max` in
`zebra-consensus/src/transaction/check.rs:450-468`). -/
def AdmissibleCap (field : ExpiryField) : Prop := field ≤ MAX_EXPIRY_HEIGHT

/-- **T14a.** The "no expiry" sentinel is admissible under the cap. -/
theorem admissibleCap_zero : AdmissibleCap 0 := by
  unfold AdmissibleCap; exact zero_le_max_expiry

/-- **T14b.** The cap itself is admissible (the rule is `≤`, not `<`). -/
theorem admissibleCap_at_max : AdmissibleCap MAX_EXPIRY_HEIGHT := by
  unfold AdmissibleCap; exact Nat.le_refl _

/-- **T14c.** Just-above the cap is *not* admissible. -/
theorem not_admissibleCap_succ_max : ¬ AdmissibleCap (MAX_EXPIRY_HEIGHT + 1) := by
  unfold AdmissibleCap MAX_EXPIRY_HEIGHT
  decide

/-! ## Decidability and Rust-style helpers -/

/-- **T15 (decidability).** `expired field h` is decidable: it's a
conjunction of decidable Nat predicates. The Rust check is itself a
decidable computation; this matches it. -/
instance instDecidableExpired (field : ExpiryField) (h : Nat) :
    Decidable (expired field h) := by
  unfold expired
  infer_instance

/-- **T16 (decidability of admissibility cap).** -/
instance instDecidableAdmissibleCap (field : ExpiryField) :
    Decidable (AdmissibleCap field) := by
  unfold AdmissibleCap
  infer_instance

/-! ## Concrete example -/

/-- **T17 (concrete expiry case).** A transaction with `expiry_height =
1000` is expired at block height `1001` but not at `1000`. -/
theorem example_expired_concrete :
    expired 1000 1001 ∧ ¬ expired 1000 1000 := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩ <;> decide
  · intro ⟨_, hgt⟩
    exact (Nat.lt_irrefl _) hgt

/-- **T18 (concrete no-expiry case).** A transaction with the sentinel
`expiry_height = 0` is never expired, however far in the future the
block height gets. -/
theorem example_no_expiry_far_future :
    ¬ expired 0 1_000_000_000 :=
  not_expired_of_field_zero _

/-! ## Connection to mining rule

The mining-side check in `validate_expiry_height_mined`
(`zebra-consensus/src/transaction/check.rs:474-490`) is equivalent to
`¬ expired`. We bundle the two directions of that equivalence here so
that downstream proofs can switch between "Zebra accepted at this
height" and "not expired" freely.
-/

/-- A transaction is *mineable* at height `h` iff the Overwinter rule
does not reject it: either it has no expiry, or the block height is
within the expiry. Matches the body of `validate_expiry_height_mined`. -/
def mineable (field : ExpiryField) (h : Nat) : Prop :=
  field = 0 ∨ h ≤ field

/-- **T19 (`mineable` ↔ not `expired`).** The mining-side check accepts
exactly when the expiry-side predicate rejects. This is the precise
statement of the equivalence between the two sides of ZIP-203 in
Zebra's codebase. -/
theorem mineable_iff_not_expired (field : ExpiryField) (h : Nat) :
    mineable field h ↔ ¬ expired field h := by
  unfold mineable expired
  constructor
  · rintro (heq | hle)
    · intro ⟨hne, _⟩; exact hne heq
    · intro ⟨_, hgt⟩; exact (Nat.lt_irrefl _) (lt_of_lt_of_le hgt hle)
  · intro hne
    by_cases hf : field = 0
    · exact Or.inl hf
    · right
      by_contra hgt
      exact hne ⟨hf, Nat.lt_of_not_le hgt⟩

end Zebra.Zip203Expiry
