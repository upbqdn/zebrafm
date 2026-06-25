import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# ZIP-209: chain shielded value pool balances must be non-negative

ZIP-209 (active since NU5) requires that the Sprout, Sapling, and Orchard
chain value pool balances each remain non-negative after applying every
block's net effect. The Rust enforcement path is
`ValueBalance::<NonNegative>::add_chain_value_pool_change` in
`zebra-chain/src/value_balance.rs:285`: each per-pool balance is first
widened to `NegativeAllowed`, the per-block delta is added, and the result
is `constrain::<NonNegative>()`-ed — which fails if any pool went negative.

For verification purposes the per-pool dynamics are identical (each pool is
a running `i64`-typed sum with the constraint that every intermediate value
is `≥ 0`), so we model a single pool: a sequence of per-block deltas as
`List Int`, with the per-pool running balance as a left-fold over `(· + ·)`
and the ZIP-209 admissibility predicate as "every prefix sum is `≥ 0`".

The load-bearing claim of this module is the fold-level invariant:

> If every prefix sum of a delta list is `≥ 0`, then the final balance is
> `≥ 0`.

This is exactly the per-pool consensus rule of ZIP-209, expressed at the
abstraction level Zebra enforces it on.

Source: <https://zips.z.cash/zip-0209#specification>
Source: `zebra-chain/src/value_balance.rs:265-295`
(`add_chain_value_pool_change`).
-/

namespace Zebra.Zip209NegativeValuePool

/-! ## Model -/

/-- Running balance after applying a list of deltas to an initial balance.
This is `add_chain_value_pool_change` iterated over a block sequence: the
per-pool balance evolves as `balance := balance + delta` for each block.

Source: `zebra-chain/src/value_balance.rs:285` — the per-pool effect of
`add_chain_value_pool_change` is integer addition; we model that addition
directly with `Int`.
-/
def runningBalance (initial : Int) (deltas : List Int) : Int :=
  deltas.foldl (· + ·) initial

/-- The list of intermediate balances *after each block*: `init`, `init +
d₀`, `init + d₀ + d₁`, …. This is `List.scanl (· + ·) init deltas` and has
length `deltas.length + 1`. -/
def prefixBalances (initial : Int) (deltas : List Int) : List Int :=
  deltas.scanl (· + ·) initial

/-- ZIP-209 admissibility: every intermediate per-pool balance must be
non-negative.

Source: <https://zips.z.cash/zip-0209#specification>
("…would become negative in the block chain created as a result of accepting
a block, then all nodes MUST reject the block as invalid"). -/
def Admissible (initial : Int) (deltas : List Int) : Prop :=
  ∀ b ∈ prefixBalances initial deltas, 0 ≤ b

/-- The final per-pool balance after applying every block's delta.
Equivalent to `runningBalance`, but stated by indexing into
`prefixBalances`. -/
def finalBalance (initial : Int) (deltas : List Int) : Int :=
  runningBalance initial deltas

/-! ## Lemmas about `prefixBalances` and `runningBalance` -/

/-- `prefixBalances` on the empty delta list is `[initial]`. -/
theorem prefixBalances_nil (initial : Int) :
    prefixBalances initial [] = [initial] := by
  unfold prefixBalances; rfl

/-- `prefixBalances initial (d :: ds)` is `initial` followed by the prefix
balances starting from `initial + d`. -/
theorem prefixBalances_cons (initial : Int) (d : Int) (ds : List Int) :
    prefixBalances initial (d :: ds) =
      initial :: prefixBalances (initial + d) ds := by
  unfold prefixBalances
  simp [List.scanl]

/-- `runningBalance` is the recurrence `init + sum(deltas)` written
explicitly: empty deltas yield `initial`. -/
theorem runningBalance_nil (initial : Int) :
    runningBalance initial [] = initial := by
  unfold runningBalance; rfl

/-- `runningBalance` on a cons just adds the head delta and recurses. -/
theorem runningBalance_cons (initial : Int) (d : Int) (ds : List Int) :
    runningBalance initial (d :: ds) =
      runningBalance (initial + d) ds := by
  unfold runningBalance
  simp [List.foldl]

/-- The length of `prefixBalances` is `deltas.length + 1`: there's one
intermediate balance per block, plus the starting balance. -/
theorem prefixBalances_length (initial : Int) (deltas : List Int) :
    (prefixBalances initial deltas).length = deltas.length + 1 := by
  unfold prefixBalances
  exact List.length_scanl

/-! ## ZIP-209 invariant theorems -/

/-- **T1.** The initial balance is always the first element of
`prefixBalances` (it is the running balance "before any block has been
applied"). -/
theorem prefixBalances_head (initial : Int) (deltas : List Int) :
    (prefixBalances initial deltas).head? = some initial := by
  cases deltas with
  | nil => rw [prefixBalances_nil]; rfl
  | cons d ds => rw [prefixBalances_cons]; rfl

/-- **T2 (admissibility ⇒ initial ≥ 0).** If the delta sequence is
ZIP-209-admissible from `initial`, the initial balance itself must be
non-negative. The pre-NU5 initial balance is `0`, so this is automatically
satisfied for the chain start. -/
theorem admissible_initial_nonneg (initial : Int) (deltas : List Int)
    (h : Admissible initial deltas) :
    0 ≤ initial := by
  apply h
  cases deltas with
  | nil => rw [prefixBalances_nil]; exact List.mem_singleton.mpr rfl
  | cons d ds =>
    rw [prefixBalances_cons]
    exact List.mem_cons_self

/-- **T3 (admissibility tail).** If `initial :: rest` deltas are
admissible, the suffix is admissible from the new balance `initial + d`. -/
theorem admissible_tail (initial : Int) (d : Int) (ds : List Int)
    (h : Admissible initial (d :: ds)) :
    Admissible (initial + d) ds := by
  intro b hb
  apply h
  rw [prefixBalances_cons]
  exact List.mem_cons_of_mem _ hb

/-- **T4 (main fold property — the ZIP-209 invariant).** If every prefix
sum is non-negative, then the final balance is non-negative.

This is exactly the load-bearing claim: applying admissible deltas can
never push the per-pool balance below zero, and in particular cannot push
the *final* balance below zero. -/
theorem admissible_implies_final_nonneg (initial : Int) (deltas : List Int)
    (h : Admissible initial deltas) :
    0 ≤ finalBalance initial deltas := by
  induction deltas generalizing initial with
  | nil =>
    -- final balance is `initial`; the singleton prefix list `[initial]` is
    -- in the admissibility hypothesis.
    unfold finalBalance
    rw [runningBalance_nil]
    exact admissible_initial_nonneg _ _ h
  | cons d ds ih =>
    -- step: peel off `d`, apply IH to the updated balance.
    unfold finalBalance at *
    rw [runningBalance_cons]
    exact ih (initial + d) (admissible_tail initial d ds h)

/-- **T5 (every intermediate balance is non-negative).** Strengthening of
T4: not just the final but *every* intermediate per-pool balance is
non-negative, which is what ZIP-209 actually says.

This follows directly from `Admissible`'s definition; we restate it so the
theorem name records that we've proved the full ZIP-209 invariant, not just
its final-balance consequence. -/
theorem admissible_implies_all_nonneg (initial : Int) (deltas : List Int)
    (h : Admissible initial deltas) :
    ∀ b ∈ prefixBalances initial deltas, 0 ≤ b := h

/-! ## Examples and constructive facts -/

/-- **T6 (empty pool history is admissible).** No deltas applied to a
non-negative initial balance: trivially admissible. -/
theorem admissible_nil (initial : Int) (h : 0 ≤ initial) :
    Admissible initial [] := by
  intro b hb
  rw [prefixBalances_nil] at hb
  rw [List.mem_singleton] at hb
  exact hb ▸ h

/-- **T7 (deposit-only sequence is admissible).** A sequence of strictly
non-negative deltas applied to a non-negative initial balance is
ZIP-209-admissible: deposits can never bring the pool below zero.

This is the canonical "transparent-to-shielded only" scenario for the
Sapling/Orchard pools in early NU5. -/
theorem admissible_of_all_nonneg (initial : Int) (deltas : List Int)
    (hI : 0 ≤ initial) (hD : ∀ d ∈ deltas, 0 ≤ d) :
    Admissible initial deltas := by
  induction deltas generalizing initial with
  | nil => exact admissible_nil initial hI
  | cons d ds ih =>
    intro b hb
    rw [prefixBalances_cons] at hb
    rw [List.mem_cons] at hb
    rcases hb with heq | hin
    · exact heq ▸ hI
    · have hd : 0 ≤ d := hD d (List.mem_cons_self ..)
      have hsum : 0 ≤ initial + d := by linarith
      have hD' : ∀ d' ∈ ds, 0 ≤ d' := fun d' hd' => hD d' (List.mem_cons_of_mem _ hd')
      exact ih (initial + d) hsum hD' b hin

/-- **T8 (witness of a violating prefix).** If some prefix sum is *strictly*
negative, the delta list is *not* admissible — the pool went negative at
some intermediate step, so the block that caused it must be rejected. -/
theorem not_admissible_of_negative_prefix (initial : Int) (deltas : List Int)
    (b : Int) (hMem : b ∈ prefixBalances initial deltas)
    (hNeg : b < 0) :
    ¬ Admissible initial deltas := by
  intro h
  have hPos : 0 ≤ b := h b hMem
  linarith

set_option linter.flexible false in
/-- **T9 (admissibility is preserved by adding a non-negative tail
delta).** If a delta list is admissible and the next block deposits a
non-negative amount, the extended list is still admissible.

This corresponds to "appending a coinbase-only block can never push the
shielded pools negative". -/
theorem admissible_append_nonneg (initial : Int) (deltas : List Int) (d : Int)
    (h : Admissible initial deltas) (hD : 0 ≤ d) :
    Admissible initial (deltas ++ [d]) := by
  intro b hb
  -- `prefixBalances initial (deltas ++ [d])` is `prefixBalances initial deltas`
  -- followed by one extra entry, namely `final balance + d`.
  unfold prefixBalances at hb
  rw [List.scanl_append] at hb
  simp [List.scanl] at hb
  rcases hb with hin | heq
  · -- `b ∈ prefixBalances initial deltas`
    exact h b hin
  · -- `b = (running balance after deltas) + d`
    have hFin : 0 ≤ runningBalance initial deltas :=
      admissible_implies_final_nonneg initial deltas h
    have hSum : 0 ≤ runningBalance initial deltas + d := by linarith
    -- `heq : b = ...`
    change 0 ≤ b
    rw [heq]
    -- `List.foldl (· + ·) initial deltas` equals `runningBalance initial deltas`
    change 0 ≤ List.foldl (· + ·) initial deltas + d
    exact hSum

set_option linter.flexible false in
/-- **T10 (concrete example).** The sequence `[5, -3, 4, -1]` starting from
`0` is admissible (the running balances are `0, 5, 2, 6, 5`, all ≥ 0). -/
theorem example_admissible : Admissible 0 [5, -3, 4, -1] := by
  intro b hb
  unfold prefixBalances at hb
  simp [List.scanl] at hb
  rcases hb with h | h | h | h | h <;> omega

/-- **T11 (concrete violation).** The sequence `[1, -3]` starting from `0`
is *not* admissible (the second prefix sum is `-2 < 0`). This is the
shape that ZIP-209 rejects. -/
theorem example_not_admissible : ¬ Admissible 0 [1, -3] := by
  apply not_admissible_of_negative_prefix 0 [1, -3] (-2)
  · unfold prefixBalances
    simp [List.scanl]
  · decide

/-! ## Decidability and finite-data consequences -/

/-- **T12 (admissibility is decidable on concrete delta lists).**
The predicate `Admissible` reduces to a finite conjunction of
`0 ≤ b` over a fixed list, so it is decidable. -/
instance instDecidableAdmissible (initial : Int) (deltas : List Int) :
    Decidable (Admissible initial deltas) := by
  unfold Admissible
  exact List.decidableBAll _ _

/-- **T13 (final balance equals fold).** Restates the connection between
`finalBalance` and `runningBalance` directly, so callers can switch
representations freely. -/
theorem finalBalance_eq_runningBalance (initial : Int) (deltas : List Int) :
    finalBalance initial deltas = runningBalance initial deltas := rfl

/-- **T14 (monotonicity in the deposit case).** Adding a non-negative
delta `d` to the *end* of a delta sequence (e.g. coinbase-only block)
cannot decrease the final balance.

This is a one-line consequence of `runningBalance` definition, but it
captures the consensus intuition that pure deposits never reduce the
shielded pool. -/
theorem finalBalance_append_nonneg_ge (initial : Int) (deltas : List Int)
    (d : Int) (hD : 0 ≤ d) :
    finalBalance initial deltas ≤ finalBalance initial (deltas ++ [d]) := by
  unfold finalBalance runningBalance
  rw [List.foldl_append]
  simp [List.foldl]
  linarith

end Zebra.Zip209NegativeValuePool
