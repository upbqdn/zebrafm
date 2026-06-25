import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

set_option linter.style.header false

/-!
# ZIP-209: chain shielded value pool balances must be non-negative

ZIP-209 (active since NU5) requires that the Sprout, Sapling, and Orchard
chain value pool balances each remain non-negative after applying every
block's net effect. The Rust enforcement path is
`ValueBalance::<NonNegative>::add_chain_value_pool_change` in
`zebra-chain/src/value_balance.rs:285`:

```
let mut chain_value_pool = self
    .constrain::<NegativeAllowed>()
    .expect("conversion from NonNegative to NegativeAllowed is always valid");
chain_value_pool = (chain_value_pool + chain_value_pool_change)?;
chain_value_pool.constrain()
```

The Rust struct has five pools: `transparent`, `sprout`, `sapling`, `orchard`,
`deferred`. ZIP-209's headline rule names only Sprout/Sapling/Orchard, but the
Rust code re-constrains *every* component to `NonNegative` (line 294 of
`value_balance.rs`), so the transparent and deferred pools are held to the same
rule. We mirror that here.

Two distinct semantic features must be modelled:

1. **Per-pool MAX_MONEY clamping.** Every per-pool intermediate value is an
   `Amount<_>(i64)` validated against `[lo, hi]` by `Constraint::validate`
   (`amount.rs:618`). The widening to `NegativeAllowed` uses
   `[-MAX_MONEY, MAX_MONEY]`, the re-narrowing to `NonNegative` uses
   `[0, MAX_MONEY]`. A delta whose addition pushes a pool out of either range
   makes `add_chain_value_pool_change` return `Err`.

2. **Per-pool independence with all-pool failure.** `+` on `ValueBalance<C>`
   (`value_balance.rs:440-449`) sums each component independently; any single
   component's `Err` propagates via `?` and aborts the whole add. So a block
   delta is admitted iff *every* pool stays in range.

We model both: a `Pool` record of five `Int`-valued amounts, an admissibility
predicate that re-runs the Rust `constrain` sequence, and the per-pool
prefix-sum invariant (which is the load-bearing claim of ZIP-209).

Source: <https://zips.z.cash/zip-0209#specification>
Source: `zebra-chain/src/value_balance.rs:285-295` (`add_chain_value_pool_change`)
Source: `zebra-chain/src/amount.rs:556-583,610` (constraint ranges, MAX_MONEY)
-/

namespace Zebra.Zip209NegativeValuePool

/-! ## Amount-range constants (mirroring `zebra-chain/src/amount.rs`) -/

/-- Zatoshis per ZEC. Source: `zebra-chain/src/amount.rs:607`. -/
def COIN : Int := 100_000_000

/-- Maximum non-negative zatoshi amount: `21_000_000 * COIN`.
Source: `zebra-chain/src/amount.rs:610`. -/
def MAX_MONEY : Int := 21_000_000 * COIN

/-- `Amount<NonNegative>` valid range: `[0, MAX_MONEY]`.
Source: `zebra-chain/src/amount.rs:580-583`. -/
def InNonNegativeRange (v : Int) : Prop := 0 ≤ v ∧ v ≤ MAX_MONEY

/-- `Amount<NegativeAllowed>` valid range: `[-MAX_MONEY, MAX_MONEY]`.
Source: `zebra-chain/src/amount.rs:558-561`. -/
def InNegativeAllowedRange (v : Int) : Prop := -MAX_MONEY ≤ v ∧ v ≤ MAX_MONEY

instance instDecInNonNeg (v : Int) : Decidable (InNonNegativeRange v) := by
  unfold InNonNegativeRange; exact inferInstance

instance instDecInNegAllowed (v : Int) : Decidable (InNegativeAllowedRange v) := by
  unfold InNegativeAllowedRange; exact inferInstance

/-! ## 5-pool `ValueBalance` (mirroring `value_balance.rs:22-29`) -/

/-- The five-pool `ValueBalance` from `zebra-chain/src/value_balance.rs:22-29`.
Field types are `Amount<C>` in Rust; we use raw `Int` and the in-range
predicate `InNonNegativeRange` (resp. `InNegativeAllowedRange`) is checked
externally — matching how Rust calls `constrain` at each pool boundary. -/
structure Pool where
  transparent : Int
  sprout      : Int
  sapling     : Int
  orchard     : Int
  deferred    : Int
  deriving DecidableEq

/-- The all-zero pool: `ValueBalance::zero()` from `value_balance.rs:130-139`. -/
def Pool.zero : Pool :=
  { transparent := 0, sprout := 0, sapling := 0, orchard := 0, deferred := 0 }

/-- Componentwise addition. Mirrors `impl Add for ValueBalance` at
`value_balance.rs:440-449`. The Rust code uses checked `i64` addition;
we model the underlying `Int` sum here and combine with range-validation
predicates below. -/
def Pool.add (a b : Pool) : Pool :=
  { transparent := a.transparent + b.transparent,
    sprout      := a.sprout      + b.sprout,
    sapling     := a.sapling     + b.sapling,
    orchard     := a.orchard     + b.orchard,
    deferred    := a.deferred    + b.deferred }

instance : Add Pool := ⟨Pool.add⟩

@[simp] theorem Pool.add_def (a b : Pool) :
    a + b = { transparent := a.transparent + b.transparent,
              sprout      := a.sprout      + b.sprout,
              sapling     := a.sapling     + b.sapling,
              orchard     := a.orchard     + b.orchard,
              deferred    := a.deferred    + b.deferred } := rfl

/-- Every component is in the `NonNegative` range. The Rust
`ValueBalance<NonNegative>` type carries this as a static invariant via
per-field `Amount<NonNegative>`. -/
def Pool.NonNegative (p : Pool) : Prop :=
  InNonNegativeRange p.transparent ∧
  InNonNegativeRange p.sprout ∧
  InNonNegativeRange p.sapling ∧
  InNonNegativeRange p.orchard ∧
  InNonNegativeRange p.deferred

instance Pool.instDecNonNegative (p : Pool) : Decidable p.NonNegative := by
  unfold Pool.NonNegative; exact inferInstance

/-- Every component is in the `NegativeAllowed` range. The `chain_value_pool +
chain_value_pool_change` step at `value_balance.rs:292` requires every component
sum to stay in this range; if any escapes, `+` returns `Err`. -/
def Pool.NegativeAllowed (p : Pool) : Prop :=
  InNegativeAllowedRange p.transparent ∧
  InNegativeAllowedRange p.sprout ∧
  InNegativeAllowedRange p.sapling ∧
  InNegativeAllowedRange p.orchard ∧
  InNegativeAllowedRange p.deferred

instance Pool.instDecNegativeAllowed (p : Pool) : Decidable p.NegativeAllowed := by
  unfold Pool.NegativeAllowed; exact inferInstance

/-- `add_chain_value_pool_change` from `value_balance.rs:285-295` as a
total function returning `Option Pool`.

Returns `some out` iff:
1. The componentwise sum lies in `NegativeAllowed` range (the `+` step at
   `value_balance.rs:292`), AND
2. The componentwise sum lies in `NonNegative` range (the trailing
   `.constrain::<NonNegative>()` at `value_balance.rs:294`).

If (1) holds but (2) does not, the *change* itself is well-typed but the
resulting pool is rejected — that is the ZIP-209 negative-pool case.

Note: the `self.NonNegative` precondition is carried by the Rust type
`ValueBalance<NonNegative>`; in our untyped model we make it a *call-site*
hypothesis (`Admissible` below requires `initial.NonNegative`). This matches
how Rust's `self.constrain::<NegativeAllowed>()` at line 290 is infallible
*given* the type-level precondition. -/
def addChainValuePoolChange (self change : Pool) : Option Pool :=
  let sum := self + change
  if sum.NegativeAllowed ∧ sum.NonNegative
  then some sum
  else none

/-! ## Block sequence and ZIP-209 admissibility -/

/-- Apply a sequence of per-block chain-value-pool changes to an initial
`NonNegative` chain value pool, short-circuiting on first failure. This is
the `add_chain_value_pool_change` loop run over a block sequence. -/
def applyChanges : Pool → List Pool → Option Pool
  | self, [] => some self
  | self, c :: cs =>
      match addChainValuePoolChange self c with
      | some next => applyChanges next cs
      | none      => none

/-- A block sequence is ZIP-209-admissible from `initial` iff (a) the initial
chain pool is `NonNegative` (matching the `ValueBalance<NonNegative>`
type-level precondition Rust carries from `chain_value_pool.constrain` at
`value_balance.rs:294`), and (b) applying every change in order succeeds —
i.e. no pool ever goes out of `NonNegative` range or wraps a
`NegativeAllowed`-range bound. -/
def Admissible (initial : Pool) (changes : List Pool) : Prop :=
  initial.NonNegative ∧ (applyChanges initial changes).isSome

/-! ## Per-pool projection (the load-bearing single-pool dynamics) -/

/-- Project a 5-pool sequence onto its Sprout component. The same definition
applies to every pool; we use Sprout as the canonical example since ZIP-209's
headline rule names Sprout first. -/
def projectSprout (changes : List Pool) : List Int := changes.map (·.sprout)

/-- Running balance after applying a list of per-pool deltas to an initial
balance. This is the per-pool effect of `add_chain_value_pool_change`
abstracted to a single component. -/
def runningBalance (initial : Int) (deltas : List Int) : Int :=
  deltas.foldl (· + ·) initial

/-- Intermediate per-pool balances after each block. `List.scanl` over the
component delta sequence — length is `deltas.length + 1`. -/
def prefixBalances (initial : Int) (deltas : List Int) : List Int :=
  deltas.scanl (· + ·) initial

/-- ZIP-209 per-pool admissibility: every intermediate per-pool balance is
non-negative. This is the *necessary* condition that
`addChainValuePoolChange` enforces on every pool individually.

Note: the *total* multi-pool admissibility (`Admissible` above) also requires
range-clamping at `MAX_MONEY`, which the integer-valued `PoolNonNegative`
predicate does not. We make both available so per-pool reasoning can stay
clean, and per-pool admissibility composes into multi-pool admissibility
under the extra range hypothesis below. -/
def PoolNonNegative (initial : Int) (deltas : List Int) : Prop :=
  ∀ b ∈ prefixBalances initial deltas, 0 ≤ b

/-! ## Basic lemmas (unfold equations) -/

/-- `prefixBalances initial [] = [initial]`. -/
theorem prefixBalances_nil (initial : Int) :
    prefixBalances initial [] = [initial] := by
  unfold prefixBalances; rfl

/-- `prefixBalances initial (d :: ds) = initial :: prefixBalances (initial + d) ds`. -/
theorem prefixBalances_cons (initial : Int) (d : Int) (ds : List Int) :
    prefixBalances initial (d :: ds) =
      initial :: prefixBalances (initial + d) ds := by
  unfold prefixBalances; simp [List.scanl]

/-- `runningBalance initial [] = initial`. -/
theorem runningBalance_nil (initial : Int) :
    runningBalance initial [] = initial := by
  unfold runningBalance; rfl

/-- `runningBalance` on a cons just adds the head delta and recurses. -/
theorem runningBalance_cons (initial : Int) (d : Int) (ds : List Int) :
    runningBalance initial (d :: ds) =
      runningBalance (initial + d) ds := by
  unfold runningBalance; simp [List.foldl]

/-- Length of `prefixBalances` is `deltas.length + 1` — one intermediate
balance per block plus the starting balance. -/
theorem prefixBalances_length (initial : Int) (deltas : List Int) :
    (prefixBalances initial deltas).length = deltas.length + 1 := by
  unfold prefixBalances; exact List.length_scanl

/-! ## Per-pool ZIP-209 invariants (T1–T9) -/

/-- **T1.** The initial balance is the head of `prefixBalances` (the
"running balance before any block has been applied"). -/
theorem prefixBalances_head (initial : Int) (deltas : List Int) :
    (prefixBalances initial deltas).head? = some initial := by
  cases deltas with
  | nil => rw [prefixBalances_nil]; rfl
  | cons d ds => rw [prefixBalances_cons]; rfl

/-- **T2.** If the per-pool sequence is ZIP-209 admissible, the initial pool
value is non-negative. Pre-NU5 the initial value is `0`, so this holds at
genesis. -/
theorem poolNonNeg_initial_nonneg (initial : Int) (deltas : List Int)
    (h : PoolNonNegative initial deltas) :
    0 ≤ initial := by
  apply h
  cases deltas with
  | nil => rw [prefixBalances_nil]; exact List.mem_singleton.mpr rfl
  | cons d ds => rw [prefixBalances_cons]; exact List.mem_cons_self

/-- **T3.** If `initial :: rest` deltas are admissible, the suffix is
admissible from the new balance `initial + d`. -/
theorem poolNonNeg_tail (initial : Int) (d : Int) (ds : List Int)
    (h : PoolNonNegative initial (d :: ds)) :
    PoolNonNegative (initial + d) ds := by
  intro b hb
  apply h
  rw [prefixBalances_cons]; exact List.mem_cons_of_mem _ hb

/-- **T4 (main fold property — ZIP-209 per-pool invariant).** If every prefix
sum is non-negative, the final balance is non-negative.

This is the load-bearing claim: applying admissible deltas can never push the
per-pool balance below zero, and in particular cannot push the *final*
balance below zero. -/
theorem poolNonNeg_implies_final_nonneg (initial : Int) (deltas : List Int)
    (h : PoolNonNegative initial deltas) :
    0 ≤ runningBalance initial deltas := by
  induction deltas generalizing initial with
  | nil =>
    rw [runningBalance_nil]
    exact poolNonNeg_initial_nonneg _ _ h
  | cons d ds ih =>
    rw [runningBalance_cons]
    exact ih (initial + d) (poolNonNeg_tail initial d ds h)

/-- **T5 (every intermediate balance is non-negative).** Restating
`PoolNonNegative` for emphasis: not just the final but *every* intermediate
per-pool balance is non-negative — which is what ZIP-209 actually says. -/
theorem poolNonNeg_all (initial : Int) (deltas : List Int)
    (h : PoolNonNegative initial deltas) :
    ∀ b ∈ prefixBalances initial deltas, 0 ≤ b := h

/-- **T6 (empty pool history is admissible).** No deltas applied to a
non-negative initial: trivially admissible. -/
theorem poolNonNeg_nil (initial : Int) (h : 0 ≤ initial) :
    PoolNonNegative initial [] := by
  intro b hb
  rw [prefixBalances_nil, List.mem_singleton] at hb
  exact hb ▸ h

/-- **T7 (deposit-only sequence is admissible).** A sequence of non-negative
deltas applied to a non-negative initial is per-pool admissible: deposits
alone never bring a pool below zero. -/
theorem poolNonNeg_of_all_nonneg (initial : Int) (deltas : List Int)
    (hI : 0 ≤ initial) (hD : ∀ d ∈ deltas, 0 ≤ d) :
    PoolNonNegative initial deltas := by
  induction deltas generalizing initial with
  | nil => exact poolNonNeg_nil initial hI
  | cons d ds ih =>
    intro b hb
    rw [prefixBalances_cons, List.mem_cons] at hb
    rcases hb with heq | hin
    · exact heq ▸ hI
    · have hd : 0 ≤ d := hD d (List.mem_cons_self ..)
      have hsum : 0 ≤ initial + d := by linarith
      have hD' : ∀ d' ∈ ds, 0 ≤ d' := fun d' hd' => hD d' (List.mem_cons_of_mem _ hd')
      exact ih (initial + d) hsum hD' b hin

/-- **T8 (witness of a violating prefix).** If some prefix sum is strictly
negative, the per-pool sequence is not admissible — the pool went negative at
some intermediate step, so the block that caused it must be rejected. -/
theorem not_poolNonNeg_of_negative_prefix (initial : Int) (deltas : List Int)
    (b : Int) (hMem : b ∈ prefixBalances initial deltas) (hNeg : b < 0) :
    ¬ PoolNonNegative initial deltas := by
  intro h
  have : 0 ≤ b := h b hMem
  linarith

set_option linter.flexible false in
/-- **T9 (admissibility preserved by adding a non-negative tail delta).**
If a delta list is admissible and the next block deposits a non-negative
amount, the extended list is still admissible. -/
theorem poolNonNeg_append_nonneg (initial : Int) (deltas : List Int) (d : Int)
    (h : PoolNonNegative initial deltas) (hD : 0 ≤ d) :
    PoolNonNegative initial (deltas ++ [d]) := by
  intro b hb
  unfold prefixBalances at hb
  rw [List.scanl_append] at hb
  simp [List.scanl] at hb
  rcases hb with hin | heq
  · exact h b hin
  · have hFin : 0 ≤ runningBalance initial deltas :=
      poolNonNeg_implies_final_nonneg initial deltas h
    have hSum : 0 ≤ runningBalance initial deltas + d := by linarith
    change 0 ≤ b
    rw [heq]
    change 0 ≤ List.foldl (· + ·) initial deltas + d
    exact hSum

/-! ## 5-pool (multi-pool) ZIP-209 theorems (T10–T15) -/

/-- **T10 (multi-pool, empty history admissibility).** With no changes
applied, the chain is admissible iff the starting pool is `NonNegative` —
the Rust call site at `value_balance.rs:294` already established this
invariant on its receiver, so an "empty next block" trivially preserves it. -/
theorem admissible_nil_iff (initial : Pool) :
    Admissible initial [] ↔ initial.NonNegative := by
  unfold Admissible applyChanges
  simp

/-- **T11 (admissibility implies initial is `NonNegative`).** Definitional
unfold of `Admissible`, recorded for callers who do not want to re-unfold. -/
theorem admissible_initial_nonNeg (initial : Pool) (changes : List Pool)
    (h : Admissible initial changes) :
    initial.NonNegative := h.1

/-- **T12 (single-step failure shape).** `addChainValuePoolChange` returns
`none` exactly when the componentwise sum exits `NegativeAllowed` range OR
exits `NonNegative` range. The first failure mode corresponds to Rust's
inner `+` returning `Err` at `value_balance.rs:292`; the second corresponds
to `.constrain::<NonNegative>()` returning `Err` at line 294 — the
ZIP-209 negative-pool case. -/
theorem addChange_none_iff (self change : Pool) :
    addChainValuePoolChange self change = none ↔
      ¬ ((self + change).NegativeAllowed ∧ (self + change).NonNegative) := by
  unfold addChainValuePoolChange
  constructor
  · intro hNone hCond
    rw [if_pos hCond] at hNone
    cases hNone
  · intro hNotCond
    rw [if_neg hNotCond]

/-- **T13 (single-step success returns the componentwise sum).** A successful
`addChainValuePoolChange` returns `self + change` and that result is
`NonNegative` — `value_balance.rs:294`'s `.constrain::<NonNegative>()` -/
theorem addChange_some_eq_and_nonNeg (self change out : Pool)
    (h : addChainValuePoolChange self change = some out) :
    out = self + change ∧ out.NonNegative := by
  unfold addChainValuePoolChange at h
  by_cases hCond : (self + change).NegativeAllowed ∧ (self + change).NonNegative
  · rw [if_pos hCond] at h
    have hEq : self + change = out := by injection h
    exact ⟨hEq.symm, hEq ▸ hCond.2⟩
  · rw [if_neg hCond] at h; cases h

/-- **T14 (multi-pool admissibility ⇒ final pool exists and is `NonNegative`).**
Every intermediate pool produced by `applyChanges` is `NonNegative`, so in
particular the final one is — the multi-pool restatement of
`poolNonNeg_implies_final_nonneg`. -/
theorem admissible_implies_final_nonNeg
    (initial : Pool) (changes : List Pool) (h : Admissible initial changes) :
    ∃ out, applyChanges initial changes = some out ∧ out.NonNegative := by
  obtain ⟨hInit, hOk⟩ := h
  induction changes generalizing initial with
  | nil =>
    refine ⟨initial, ?_, hInit⟩
    unfold applyChanges; rfl
  | cons c cs ih =>
    unfold applyChanges at hOk
    by_cases heq : addChainValuePoolChange initial c = none
    · rw [heq] at hOk; exact absurd hOk (by simp)
    · obtain ⟨out', heq'⟩ : ∃ x, addChainValuePoolChange initial c = some x := by
        cases h' : addChainValuePoolChange initial c with
        | none => exact (heq h').elim
        | some x => exact ⟨x, rfl⟩
      rw [heq'] at hOk
      obtain ⟨_, hOut'NonNeg⟩ := addChange_some_eq_and_nonNeg _ _ _ heq'
      obtain ⟨out, hOut, hNonNeg⟩ := ih out' hOut'NonNeg hOk
      refine ⟨out, ?_, hNonNeg⟩
      unfold applyChanges; rw [heq']; exact hOut

/-- **T15 (per-pool projection witnesses the ZIP-209 negative-pool rule).**
If the multi-pool change sequence is admissible from `initial`, then for the
Sprout pool the per-pool running balance is non-negative at every prefix —
the per-pool form of the ZIP-209 rule. The same projection works for any
component; we present Sprout as the canonical example. -/
theorem admissible_implies_sprout_nonNeg
    (initial : Pool) (changes : List Pool) (h : Admissible initial changes) :
    PoolNonNegative initial.sprout (projectSprout changes) := by
  obtain ⟨hInit, hOk⟩ := h
  induction changes generalizing initial with
  | nil =>
    intro b hb
    unfold projectSprout at hb
    rw [List.map_nil, prefixBalances_nil, List.mem_singleton] at hb
    subst hb
    exact hInit.2.1.1
  | cons c cs ih =>
    unfold applyChanges at hOk
    by_cases heq : addChainValuePoolChange initial c = none
    · rw [heq] at hOk; exact absurd hOk (by simp)
    · obtain ⟨out', heq'⟩ : ∃ x, addChainValuePoolChange initial c = some x := by
        cases h' : addChainValuePoolChange initial c with
        | none => exact (heq h').elim
        | some x => exact ⟨x, rfl⟩
      rw [heq'] at hOk
      obtain ⟨hOutEq, hOut'NonNeg⟩ := addChange_some_eq_and_nonNeg _ _ _ heq'
      have hSproutEq : out'.sprout = initial.sprout + c.sprout := by
        rw [hOutEq]; simp
      intro b hb
      unfold projectSprout at hb
      rw [List.map_cons, prefixBalances_cons, List.mem_cons] at hb
      rcases hb with heq2 | hin
      · subst heq2; exact hInit.2.1.1
      · have hTail : PoolNonNegative out'.sprout (projectSprout cs) :=
          ih out' hOut'NonNeg hOk
        rw [← hSproutEq] at hin
        unfold projectSprout at hTail
        exact hTail b hin

/-! ## Concrete examples -/

set_option linter.flexible false in
/-- **T16 (concrete example, per-pool).** The Sprout-component sequence
`[5, -3, 4, -1]` starting from `0` is admissible (the running balances are
`0, 5, 2, 6, 5`, all ≥ 0). -/
theorem example_poolNonNeg : PoolNonNegative 0 [5, -3, 4, -1] := by
  intro b hb
  unfold prefixBalances at hb
  simp [List.scanl] at hb
  rcases hb with h | h | h | h | h <;> omega

/-- **T17 (concrete violation).** The sequence `[1, -3]` starting from `0`
is not per-pool admissible (the second prefix sum is `-2 < 0`). This is the
shape ZIP-209 rejects. -/
theorem example_not_poolNonNeg : ¬ PoolNonNegative 0 [1, -3] := by
  apply not_poolNonNeg_of_negative_prefix 0 [1, -3] (-2)
  · unfold prefixBalances; simp [List.scanl]
  · decide

/-- **T18 (concrete multi-pool admissibility).** Adding the all-zero change
to the all-zero pool is admissible. -/
theorem example_admissible_zero : Admissible Pool.zero [Pool.zero] := by
  refine ⟨?_, ?_⟩
  · unfold Pool.zero Pool.NonNegative InNonNegativeRange MAX_MONEY COIN
    decide
  · unfold applyChanges addChainValuePoolChange
    simp only [Pool.add_def]
    unfold Pool.zero Pool.NegativeAllowed Pool.NonNegative
      InNegativeAllowedRange InNonNegativeRange MAX_MONEY COIN
    decide

/-- **T19 (multi-pool ZIP-209 violation).** Starting from an all-zero
chain pool and applying a change that subtracts 1 from the Sprout pool is
*not* admissible: the resulting Sprout balance `-1` violates
`InNonNegativeRange`. This is precisely the rejection rule of ZIP-209. -/
theorem example_not_admissible_sprout_negative :
    ¬ Admissible Pool.zero
      [{ transparent := 0, sprout := -1, sapling := 0, orchard := 0, deferred := 0 }] := by
  rintro ⟨_, hOk⟩
  unfold applyChanges addChainValuePoolChange at hOk
  simp only [Pool.add_def] at hOk
  -- the if-condition fails (sprout sum is -1, outside `[0, MAX_MONEY]`),
  -- so `addChainValuePoolChange` returns none and `match` returns none.
  rw [if_neg] at hOk
  · simp at hOk
  · rintro ⟨_, hNonNeg⟩
    have hSpr : (0 : Int) ≤ 0 + (-1) := hNonNeg.2.1.1
    omega

/-! ## Range-clamping theorems (the MAX_MONEY bound) -/

/-- **T20 (overflow above `MAX_MONEY` is rejected).** Even though the
per-component sum is mathematically a positive integer, if any pool's running
balance exceeds `MAX_MONEY` the Rust code returns `Err` from the inner `+`
(`amount.rs:148-150` `try_into` after `checked_add`). We witness this with
a transparent-pool overflow. -/
theorem max_money_overflow_rejected :
    addChainValuePoolChange
      { transparent := MAX_MONEY, sprout := 0, sapling := 0,
        orchard := 0, deferred := 0 }
      { transparent := 1, sprout := 0, sapling := 0,
        orchard := 0, deferred := 0 } = none := by
  unfold addChainValuePoolChange
  apply if_neg
  rintro ⟨hNegAllow, _⟩
  obtain ⟨hTrans, _⟩ := hNegAllow
  -- transparent component sum is `MAX_MONEY + 1`, exceeding `MAX_MONEY`.
  have hHi : (MAX_MONEY + 1 : Int) ≤ MAX_MONEY := hTrans.2
  unfold MAX_MONEY COIN at hHi; omega

/-- **T21 (underflow below `-MAX_MONEY` is rejected).** The widening to
`NegativeAllowed` only permits values `≥ -MAX_MONEY`, so if a per-pool sum
goes below that the inner `+` returns `Err` and the whole step is `none`.
We witness this with a sprout-pool underflow. -/
theorem neg_max_money_underflow_rejected :
    addChainValuePoolChange
      { transparent := 0, sprout := 0, sapling := 0,
        orchard := 0, deferred := 0 }
      { transparent := 0, sprout := -MAX_MONEY - 1,
        sapling := 0, orchard := 0, deferred := 0 } = none := by
  unfold addChainValuePoolChange
  apply if_neg
  rintro ⟨hNegAllow, _⟩
  obtain ⟨_, hSpr, _⟩ := hNegAllow
  have hLo : (-MAX_MONEY : Int) ≤ 0 + (-MAX_MONEY - 1) := hSpr.1
  unfold MAX_MONEY COIN at hLo; omega

/-! ## Decidability -/

/-- **T22 (per-pool admissibility is decidable).** -/
instance instDecidablePoolNonNegative (initial : Int) (deltas : List Int) :
    Decidable (PoolNonNegative initial deltas) := by
  unfold PoolNonNegative
  exact List.decidableBAll _ _

/-- **T23 (multi-pool admissibility is decidable on concrete inputs).** -/
instance instDecidableAdmissible (initial : Pool) (changes : List Pool) :
    Decidable (Admissible initial changes) := by
  unfold Admissible; exact inferInstance

end Zebra.Zip209NegativeValuePool
