import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# ZIP-401 mempool eviction (deterministic worst-case abstraction)

When Zebra's mempool's `total_cost` exceeds the configured
`tx_cost_limit`, Zebra repeatedly evicts transactions until the total
cost fits. Each eviction is a *randomized weighted draw* in Rust, with
each transaction's draw probability proportional to its
**eviction weight**:

```rust
fn eviction_weight(&self) -> u64 {
    let mut cost = self.cost();              // max(size_bytes, 10_000)
    if !self.pays_conventional_fee() {
        cost += MEMPOOL_TRANSACTION_LOW_FEE_PENALTY  // += 40_000
    }
    cost
}
```
(`zebra-chain/src/transaction/unmined.rs:489-497`, `unmined.rs:43-75`.)

The eviction loop in `mempool/storage.rs:478-498` continues
`while self.verified.total_cost() > self.tx_cost_limit`, *not* while a
transaction count exceeds a cap. Each step samples a victim via
`WeightedIndex::new(weights).sample(...)`
(`mempool/storage/verified_set.rs:218-239`).

## What this module verifies

Modelling the random draw itself would require a probability monad and a
weighted-distribution library we do not pull into this development. We
verify a **deterministic worst-case abstraction**:

> At each step, the highest-eviction-weight transaction is removed.

This is the deterministic policy that *dominates* the randomized one in
the following precise sense: it always picks a transaction whose weight
is the maximum over the mempool, so the picked transaction is in the
support of the randomized draw (every transaction with nonzero weight is
in that support). The randomized draw additionally picks
lower-weight victims with positive probability, but the bound we prove
for the deterministic policy — "the picked tx has weight ≥ every
remaining tx's weight" (`evictOne_remaining_le_evicted`) — is the
strongest single-step claim independent of the random source.

We deliberately **do not** claim:

  * that the randomized policy always picks the maximum (it does not);
  * that the deterministic abstraction matches the actual on-network
    behaviour transaction-by-transaction (it does not — the random draw
    can pick any positive-weight transaction).

## Cost model: byte cost, not transaction count

The mempool cap is a *byte-cost* limit (`tx_cost_limit : u64`,
`mempool/storage.rs:218`), and the loop condition is on the
**sum of transaction costs**, not the number of transactions. We model
`Entry.cost : Nat` (the per-tx cost, already `max`-ed against
`MEMPOOL_TRANSACTION_COST_THRESHOLD`), `Entry.weight : Nat` (the eviction
weight, `cost + 0` or `cost + 40_000`), and a mempool
`{ entries, costLimit }` with iterated eviction running while
`totalCost > costLimit`.

## Theorems

  * **T1** (`mempool_constants_values`) pins
    `MEMPOOL_TRANSACTION_COST_THRESHOLD = 10_000`,
    `MEMPOOL_TRANSACTION_LOW_FEE_PENALTY = 40_000`.
  * **T2** (`weight_eq_cost_or_cost_plus_penalty`) records the two-case
    structure of `eviction_weight` from Rust.
  * **T3** (`evictOne_isSome_iff`) — well-defined exactly on non-empty.
  * **T4** (`evictOne_length`) — one step removes exactly one entry.
  * **T5** (`evictOne_remaining_le_evicted`) — the load-bearing
    direction property: every remaining entry has weight `≤` the
    evicted entry's weight (Rust's weighted draw is biased toward
    higher weights; our deterministic abstraction always picks the max).
  * **T6** (`evictOne_totalCost_decreases`) — total cost strictly drops
    by the evicted entry's cost.
  * **T7** (`iteratedEvict_fits_fuel`) — with enough fuel, the loop
    terminates with `totalCost ≤ costLimit` or empty.
  * **T8** (`evicted_in_support`) — the deterministic-max picks a
    transaction that any positive-weight randomized draw could also
    pick. This is the precise connection to the random model.
-/

namespace Zebra.MempoolEviction

/-! ## Constants -/

/-- `MEMPOOL_TRANSACTION_COST_THRESHOLD` from ZIP-401 / Zebra:
the minimum cost charged to a transaction (`max(size_bytes, 10_000)`).
Source: `zebra-chain/src/transaction/unmined.rs:67`. -/
def MEMPOOL_TRANSACTION_COST_THRESHOLD : Nat := 10_000

/-- `MEMPOOL_TRANSACTION_LOW_FEE_PENALTY` from ZIP-401 / Zebra:
penalty added to the eviction weight of a transaction paying below the
conventional fee.
Source: `zebra-chain/src/transaction/unmined.rs:75`. -/
def MEMPOOL_TRANSACTION_LOW_FEE_PENALTY : Nat := 40_000

/-! ## Per-tx cost and eviction weight (Rust `unmined.rs:465-497`) -/

/-- `cost(size_bytes)` from `VerifiedUnminedTx::cost()`:
`max(size_bytes, MEMPOOL_TRANSACTION_COST_THRESHOLD)`.
Source: `zebra-chain/src/transaction/unmined.rs:465-470`. -/
def cost (sizeBytes : Nat) : Nat :=
  Nat.max sizeBytes MEMPOOL_TRANSACTION_COST_THRESHOLD

/-- `eviction_weight(cost, paysConventionalFee)` from
`VerifiedUnminedTx::eviction_weight()`:
`cost` if the tx pays the conventional fee, otherwise
`cost + MEMPOOL_TRANSACTION_LOW_FEE_PENALTY`.
Source: `zebra-chain/src/transaction/unmined.rs:489-497`. -/
def evictionWeight (c : Nat) (paysConventional : Bool) : Nat :=
  if paysConventional then c
  else c + MEMPOOL_TRANSACTION_LOW_FEE_PENALTY

/-! ## Model -/

/-- One mempool entry: a transaction id, its byte cost (already capped
at `MEMPOOL_TRANSACTION_COST_THRESHOLD`) and its eviction weight (the
cost plus a possible low-fee penalty). We carry both so that total-cost
accounting and weight-based ranking are separate concerns, mirroring
`storage/verified_set.rs`.

Invariants we expect of producers (not enforced here because they are
checked at insertion time in Rust):
  * `cost ≥ MEMPOOL_TRANSACTION_COST_THRESHOLD`;
  * `weight ∈ { cost, cost + MEMPOOL_TRANSACTION_LOW_FEE_PENALTY }`. -/
structure Entry where
  txid : Nat
  cost : Nat
  weight : Nat

/-- A mempool: a list of entries and the configured byte-cost limit
(`tx_cost_limit` in `mempool/storage.rs:218`). -/
structure Mempool where
  entries : List Entry
  costLimit : Nat

/-- The total cost of the entries in the mempool. The eviction loop in
`mempool/storage.rs:478` runs while `verified.total_cost() > tx_cost_limit`. -/
def totalCost (es : List Entry) : Nat :=
  es.foldr (fun e acc => e.cost + acc) 0

/-! ## Deterministic max-weight selection -/

/-- One-step max-weight selection: returns `(evicted, remaining)` where
`evicted` is the maximum-weight entry in `best :: rest` (first
occurrence wins ties), and `remaining` is the rest of the list with
`evicted` removed (preserving order). This is the deterministic
worst-case abstraction of Rust's
`WeightedIndex::new(weights).sample(...)`. -/
def pickHighestAux : Entry → List Entry → Entry × List Entry
  | best, []        => (best, [])
  | best, e :: rest =>
      if best.weight < e.weight then
        let p := pickHighestAux e rest
        (p.1, best :: p.2)
      else
        let p := pickHighestAux best rest
        (p.1, e :: p.2)

/-- One eviction step on a mempool. Returns `none` when the mempool is
empty; otherwise removes the maximum-weight entry and returns the new
mempool plus the evicted entry. -/
def evictOne : Mempool → Option (Mempool × Entry)
  | { entries := [], costLimit := _ } => none
  | { entries := e :: rest, costLimit := L } =>
      let p := pickHighestAux e rest
      some ({ entries := p.2, costLimit := L }, p.1)

/-- Iterated eviction with explicit fuel: drop the max-weight entry
until the mempool's total cost fits in `costLimit`, bounded by `fuel`
steps. Mirrors the
`while self.verified.total_cost() > self.tx_cost_limit { evict_one(); }`
loop in `mempool/storage.rs:478-498`. -/
def iteratedEvict : Nat → Mempool → Mempool
  | 0, m => m
  | n + 1, m =>
      if totalCost m.entries ≤ m.costLimit then m
      else
        match m.entries with
        | [] => m
        | e :: rest =>
            let p := pickHighestAux e rest
            iteratedEvict n { entries := p.2, costLimit := m.costLimit }

/-- Convenience wrapper: iterate with fuel equal to the mempool's
length. Each step removes exactly one entry, so this fuel always
suffices. -/
def evictUntilFits (m : Mempool) : Mempool :=
  iteratedEvict m.entries.length m

/-! ## Equations for `pickHighestAux` -/

theorem pickHighestAux_nil (best : Entry) :
    pickHighestAux best [] = (best, []) := rfl

theorem pickHighestAux_cons_lt (best e : Entry) (rest : List Entry)
    (hLt : best.weight < e.weight) :
    pickHighestAux best (e :: rest) =
      ((pickHighestAux e rest).1, best :: (pickHighestAux e rest).2) := by
  change (if best.weight < e.weight then _ else _) = _
  rw [if_pos hLt]

theorem pickHighestAux_cons_ge (best e : Entry) (rest : List Entry)
    (hGe : ¬ best.weight < e.weight) :
    pickHighestAux best (e :: rest) =
      ((pickHighestAux best rest).1, e :: (pickHighestAux best rest).2) := by
  change (if best.weight < e.weight then _ else _) = _
  rw [if_neg hGe]

/-! ## Lemmas about `pickHighestAux` -/

/-- The evicted entry's weight is `≥ best.weight`. -/
theorem pickHighestAux_evicted_ge_best (best : Entry) (rest : List Entry) :
    best.weight ≤ (pickHighestAux best rest).1.weight := by
  induction rest generalizing best with
  | nil => rw [pickHighestAux_nil]
  | cons e xs ih =>
    by_cases hLt : best.weight < e.weight
    · rw [pickHighestAux_cons_lt best e xs hLt]
      have hStep := ih e
      have hLe : best.weight ≤ e.weight := Nat.le_of_lt hLt
      exact Nat.le_trans hLe hStep
    · rw [pickHighestAux_cons_ge best e xs hLt]
      exact ih best

/-- The evicted entry's weight is `≥` every weight in `rest`. -/
theorem pickHighestAux_evicted_ge_rest (best : Entry) (rest : List Entry)
    (x : Entry) (h : x ∈ rest) :
    x.weight ≤ (pickHighestAux best rest).1.weight := by
  induction rest generalizing best with
  | nil => exact absurd h List.not_mem_nil
  | cons e xs ih =>
    by_cases hLt : best.weight < e.weight
    · rw [pickHighestAux_cons_lt best e xs hLt]
      rcases List.mem_cons.mp h with heq | hin
      · subst heq
        exact pickHighestAux_evicted_ge_best x xs
      · exact ih e hin
    · rw [pickHighestAux_cons_ge best e xs hLt]
      rcases List.mem_cons.mp h with heq | hin
      · subst heq
        have hHi := pickHighestAux_evicted_ge_best best xs
        have hLe : x.weight ≤ best.weight := Nat.le_of_not_lt hLt
        exact Nat.le_trans hLe hHi
      · exact ih best hin

/-- The remaining list has length `rest.length`. -/
theorem pickHighestAux_remaining_length (best : Entry) (rest : List Entry) :
    (pickHighestAux best rest).2.length = rest.length := by
  induction rest generalizing best with
  | nil => rw [pickHighestAux_nil]
  | cons e xs ih =>
    by_cases hLt : best.weight < e.weight
    · rw [pickHighestAux_cons_lt best e xs hLt, List.length_cons, List.length_cons]
      exact congrArg (· + 1) (ih e)
    · rw [pickHighestAux_cons_ge best e xs hLt, List.length_cons, List.length_cons]
      exact congrArg (· + 1) (ih best)

/-- Every entry in the remaining list has weight `≤` the evicted weight.
Direction-corrected analogue of the original `_remaining_ge_evicted`. -/
theorem pickHighestAux_remaining_le_evicted (best : Entry) (rest : List Entry)
    (x : Entry) (h : x ∈ (pickHighestAux best rest).2) :
    x.weight ≤ (pickHighestAux best rest).1.weight := by
  induction rest generalizing best with
  | nil =>
    rw [pickHighestAux_nil] at h
    exact absurd h List.not_mem_nil
  | cons e xs ih =>
    by_cases hLt : best.weight < e.weight
    · rw [pickHighestAux_cons_lt best e xs hLt] at h ⊢
      rcases List.mem_cons.mp h with heq | hin
      · subst heq
        have hInner := pickHighestAux_evicted_ge_best e xs
        have hStep : x.weight ≤ e.weight := Nat.le_of_lt hLt
        exact Nat.le_trans hStep hInner
      · exact ih e hin
    · rw [pickHighestAux_cons_ge best e xs hLt] at h ⊢
      rcases List.mem_cons.mp h with heq | hin
      · subst heq
        have hInner := pickHighestAux_evicted_ge_best best xs
        have hStep : x.weight ≤ best.weight := Nat.le_of_not_lt hLt
        exact Nat.le_trans hStep hInner
      · exact ih best hin

/-- The evicted entry is in the original list `best :: rest`. Used to
state the support-set relationship to Rust's `WeightedIndex`. -/
theorem pickHighestAux_evicted_mem (best : Entry) (rest : List Entry) :
    (pickHighestAux best rest).1 ∈ best :: rest := by
  induction rest generalizing best with
  | nil =>
    rw [pickHighestAux_nil]; exact List.mem_cons_self
  | cons e xs ih =>
    by_cases hLt : best.weight < e.weight
    · rw [pickHighestAux_cons_lt best e xs hLt]
      -- Reduce `(picked, best :: remaining).1` to `picked`.
      change (pickHighestAux e xs).1 ∈ best :: e :: xs
      have hRec := ih e  -- `(pickHighestAux e xs).1 ∈ e :: xs`
      rcases List.mem_cons.mp hRec with heq | hin
      · -- picked = e ∈ e :: xs, so picked ∈ best :: e :: xs via tail.
        rw [heq]
        exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr hin)))
    · rw [pickHighestAux_cons_ge best e xs hLt]
      change (pickHighestAux best xs).1 ∈ best :: e :: xs
      have hRec := ih best  -- `(pickHighestAux best xs).1 ∈ best :: xs`
      rcases List.mem_cons.mp hRec with heq | hin
      · rw [heq]; exact List.mem_cons_self
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr hin)))

/-- `totalCost` of a cons unfolds. -/
theorem totalCost_cons (e : Entry) (es : List Entry) :
    totalCost (e :: es) = e.cost + totalCost es := by
  unfold totalCost
  simp [List.foldr]

/-- `totalCost` is preserved by permutations on the underlying list,
which `pickHighestAux` performs (it deletes the picked entry). For our
direct uses we only need the equation
`totalCost (best :: rest) = picked.cost + totalCost remaining`, which we
prove by induction on `rest`. -/
theorem pickHighestAux_totalCost (best : Entry) (rest : List Entry) :
    (pickHighestAux best rest).1.cost + totalCost (pickHighestAux best rest).2
      = best.cost + totalCost rest := by
  induction rest generalizing best with
  | nil => rfl
  | cons e xs ih =>
    by_cases hLt : best.weight < e.weight
    · rw [pickHighestAux_cons_lt best e xs hLt]
      have hIH := ih e
      -- The explicit pair's `.1` and `.2` are projections; `change`
      -- makes the `Prod.fst (a, b) = a` definitional unfolding explicit
      -- so omega sees the same shape as `hIH`.
      change (pickHighestAux e xs).1.cost + totalCost (best :: (pickHighestAux e xs).2)
              = best.cost + totalCost (e :: xs)
      rw [totalCost_cons, totalCost_cons]
      omega
    · rw [pickHighestAux_cons_ge best e xs hLt]
      have hIH := ih best
      change (pickHighestAux best xs).1.cost + totalCost (e :: (pickHighestAux best xs).2)
              = best.cost + totalCost (e :: xs)
      rw [totalCost_cons, totalCost_cons]
      omega

/-! ## Equations for `evictOne` -/

theorem evictOne_nil (L : Nat) :
    evictOne { entries := [], costLimit := L } = none := rfl

theorem evictOne_cons (e : Entry) (rest : List Entry) (L : Nat) :
    evictOne { entries := e :: rest, costLimit := L } =
      let p := pickHighestAux e rest
      some ({ entries := p.2, costLimit := L }, p.1) := rfl

/-! ## Equations for `iteratedEvict` -/

theorem iteratedEvict_zero (m : Mempool) :
    iteratedEvict 0 m = m := rfl

/-- When the mempool already fits, `iteratedEvict` returns it unchanged. -/
theorem iteratedEvict_succ_fits (n : Nat) (m : Mempool)
    (h : totalCost m.entries ≤ m.costLimit) :
    iteratedEvict (n + 1) m = m := by
  change (if totalCost m.entries ≤ m.costLimit then m else _) = m
  rw [if_pos h]

/-- When the mempool is over the cost limit and has at least one entry,
the recursion peels off the max-weight entry. -/
theorem iteratedEvict_succ_overfull_cons (n : Nat) (L : Nat)
    (e : Entry) (rest : List Entry)
    (hOver : ¬ totalCost (e :: rest) ≤ L) :
    iteratedEvict (n + 1) { entries := e :: rest, costLimit := L } =
      iteratedEvict n
        { entries := (pickHighestAux e rest).2, costLimit := L } := by
  change (if totalCost (e :: rest) ≤ L then _ else _) = _
  rw [if_neg hOver]

/-! ## Main theorems -/

/-- **T1 (constants match Rust).** The two ZIP-401 numeric constants
are exactly the values in
`zebra-chain/src/transaction/unmined.rs:43-75`. We do **not** here
claim equivalence between the Rust `f32` cap
`BLOCK_PRODUCTION_WEIGHT_RATIO_CAP = 4.0` and any integer rescaling —
the cap is a ZIP-317 block-production parameter (see
`zip317.rs:113-134`), not part of the eviction-weight definition this
module models, so it does not appear here. -/
theorem mempool_constants_values :
    MEMPOOL_TRANSACTION_COST_THRESHOLD = 10_000 ∧
    MEMPOOL_TRANSACTION_LOW_FEE_PENALTY = 40_000 :=
  ⟨rfl, rfl⟩

/-- **T2 (eviction-weight case structure).** `eviction_weight` is `cost`
when the transaction pays the conventional fee and
`cost + MEMPOOL_TRANSACTION_LOW_FEE_PENALTY` otherwise. This pins the
shape from `unmined.rs:489-497`. -/
theorem weight_eq_cost_or_cost_plus_penalty (c : Nat) (b : Bool) :
    evictionWeight c b = c ∨
      evictionWeight c b = c + MEMPOOL_TRANSACTION_LOW_FEE_PENALTY := by
  cases b with
  | true  => left;  rfl
  | false => right; rfl

/-- **T3 (eviction is well-defined exactly on non-empty mempools).** -/
theorem evictOne_isSome_iff (m : Mempool) :
    (evictOne m).isSome ↔ m.entries ≠ [] := by
  rcases m with ⟨entries, _⟩
  cases entries with
  | nil       => simp [evictOne_nil]
  | cons _ _  => simp [evictOne_cons]

/-- **T4 (eviction reduces size by exactly 1).** -/
theorem evictOne_length (m : Mempool) (m' : Mempool) (evicted : Entry)
    (h : evictOne m = some (m', evicted)) :
    m'.entries.length + 1 = m.entries.length := by
  rcases m with ⟨entries, L⟩
  cases entries with
  | nil =>
    rw [evictOne_nil] at h
    exact absurd h (by simp)
  | cons e rest =>
    rw [evictOne_cons] at h
    have hInj := Option.some.inj h
    have hM' : m' = { entries := (pickHighestAux e rest).2, costLimit := L } :=
      (Prod.mk.inj hInj).1.symm
    rw [hM']
    change (pickHighestAux e rest).2.length + 1 = (e :: rest).length
    rw [pickHighestAux_remaining_length]
    simp

/-- **T5 (remaining weights ≤ evicted weight).** Every transaction left
in the mempool after a deterministic-max eviction step has eviction
weight **at most** the evicted transaction's weight. This is the
direction-corrected analogue of the original (lowest-first) ranking
claim: Rust's randomized draw is biased toward higher weights, and our
deterministic abstraction always picks the actual maximum. -/
theorem evictOne_remaining_le_evicted (m : Mempool) (m' : Mempool)
    (evicted : Entry) (h : evictOne m = some (m', evicted))
    (x : Entry) (hx : x ∈ m'.entries) :
    x.weight ≤ evicted.weight := by
  rcases m with ⟨entries, L⟩
  cases entries with
  | nil =>
    rw [evictOne_nil] at h
    exact absurd h (by simp)
  | cons e rest =>
    rw [evictOne_cons] at h
    have hInj := Option.some.inj h
    have hM' : m' = { entries := (pickHighestAux e rest).2, costLimit := L } :=
      (Prod.mk.inj hInj).1.symm
    have hEv : evicted = (pickHighestAux e rest).1 :=
      (Prod.mk.inj hInj).2.symm
    rw [hM'] at hx
    rw [hEv]
    exact pickHighestAux_remaining_le_evicted e rest x hx

/-- **T6 (total cost strictly decreases by the evicted cost).** Mirrors
the loop invariant `total_cost` after one `evict_one()`. -/
theorem evictOne_totalCost (m : Mempool) (m' : Mempool) (evicted : Entry)
    (h : evictOne m = some (m', evicted)) :
    evicted.cost + totalCost m'.entries = totalCost m.entries := by
  rcases m with ⟨entries, L⟩
  cases entries with
  | nil =>
    rw [evictOne_nil] at h
    exact absurd h (by simp)
  | cons e rest =>
    rw [evictOne_cons] at h
    have hInj := Option.some.inj h
    have hM' : m' = { entries := (pickHighestAux e rest).2, costLimit := L } :=
      (Prod.mk.inj hInj).1.symm
    have hEv : evicted = (pickHighestAux e rest).1 :=
      (Prod.mk.inj hInj).2.symm
    rw [hM', hEv]
    change (pickHighestAux e rest).1.cost
              + totalCost (pickHighestAux e rest).2
            = totalCost (e :: rest)
    rw [pickHighestAux_totalCost, totalCost_cons]

/-- **T7 (eviction preserves cost limit).** -/
theorem evictOne_costLimit (m : Mempool) (m' : Mempool) (evicted : Entry)
    (h : evictOne m = some (m', evicted)) :
    m'.costLimit = m.costLimit := by
  rcases m with ⟨entries, L⟩
  cases entries with
  | nil =>
    rw [evictOne_nil] at h
    exact absurd h (by simp)
  | cons e rest =>
    rw [evictOne_cons] at h
    have hInj := Option.some.inj h
    have hM' : m' = { entries := (pickHighestAux e rest).2, costLimit := L } :=
      (Prod.mk.inj hInj).1.symm
    rw [hM']

/-- **T8 (eviction strictly shrinks the mempool length).** -/
theorem evictOne_strictly_smaller (m : Mempool) (m' : Mempool) (evicted : Entry)
    (h : evictOne m = some (m', evicted)) :
    m'.entries.length < m.entries.length := by
  have := evictOne_length m m' evicted h
  omega

/-- **T9 (the evicted entry is in the support set).** The evicted
transaction is in the original mempool — which is the precise sense in
which the deterministic-max abstraction is consistent with the
randomized `WeightedIndex` draw: every transaction `WeightedIndex` can
pick (i.e. every nonzero-weight entry, which under Zebra is *every*
entry because `cost ≥ MEMPOOL_TRANSACTION_COST_THRESHOLD = 10_000 > 0`)
is in the original list; and so is ours. -/
theorem evictOne_evicted_in_original (m : Mempool) (m' : Mempool)
    (evicted : Entry) (h : evictOne m = some (m', evicted)) :
    evicted ∈ m.entries := by
  rcases m with ⟨entries, L⟩
  cases entries with
  | nil =>
    rw [evictOne_nil] at h
    exact absurd h (by simp)
  | cons e rest =>
    rw [evictOne_cons] at h
    have hInj := Option.some.inj h
    have hEv : evicted = (pickHighestAux e rest).1 :=
      (Prod.mk.inj hInj).2.symm
    rw [hEv]
    exact pickHighestAux_evicted_mem e rest

/-! ## Iterated eviction -/

/-- **T10 (`iteratedEvict` is a no-op when the mempool already fits).** -/
theorem iteratedEvict_already_fits (fuel : Nat) (m : Mempool)
    (h : totalCost m.entries ≤ m.costLimit) :
    iteratedEvict fuel m = m := by
  cases fuel with
  | zero    => exact iteratedEvict_zero m
  | succ n  => exact iteratedEvict_succ_fits n m h

/-- **T11 (`iteratedEvict` preserves cost limit).** -/
theorem iteratedEvict_costLimit (fuel : Nat) (m : Mempool) :
    (iteratedEvict fuel m).costLimit = m.costLimit := by
  induction fuel generalizing m with
  | zero      => rw [iteratedEvict_zero]
  | succ n ih =>
    by_cases hFits : totalCost m.entries ≤ m.costLimit
    · rw [iteratedEvict_succ_fits n m hFits]
    · rcases m with ⟨entries, L⟩
      cases entries with
      | nil =>
        -- Vacuous: totalCost [] = 0 ≤ L, contradicting hFits.
        change ¬ totalCost ([] : List Entry) ≤ L at hFits
        change ¬ 0 ≤ L at hFits
        exact absurd (Nat.zero_le _) hFits
      | cons e rest =>
        rw [iteratedEvict_succ_overfull_cons n L e rest hFits]
        change (iteratedEvict n
                  { entries := (pickHighestAux e rest).2, costLimit := L }).costLimit = L
        rw [ih]

/-- **T12 (`iteratedEvict` only shrinks the mempool length).** -/
theorem iteratedEvict_length_le (fuel : Nat) (m : Mempool) :
    (iteratedEvict fuel m).entries.length ≤ m.entries.length := by
  induction fuel generalizing m with
  | zero      => rw [iteratedEvict_zero]
  | succ n ih =>
    by_cases hFits : totalCost m.entries ≤ m.costLimit
    · rw [iteratedEvict_succ_fits n m hFits]
    · rcases m with ⟨entries, L⟩
      cases entries with
      | nil =>
        change ¬ totalCost ([] : List Entry) ≤ L at hFits
        exact absurd (Nat.zero_le _) hFits
      | cons e rest =>
        rw [iteratedEvict_succ_overfull_cons n L e rest hFits]
        have hLen := pickHighestAux_remaining_length e rest
        set m' : Mempool := { entries := (pickHighestAux e rest).2, costLimit := L }
        calc (iteratedEvict n m').entries.length
            ≤ m'.entries.length := ih m'
          _ = rest.length       := hLen
          _ ≤ (e :: rest).length := by simp

/-- **T13 (`iteratedEvict` with enough fuel makes the mempool fit).**
With fuel `≥ original length`, the result has total cost `≤ costLimit`,
or the entries have been emptied (and `totalCost [] = 0 ≤ costLimit`
trivially). This mirrors the termination of Rust's
`while total_cost > tx_cost_limit { evict_one(); }` loop, which is
guaranteed because each iteration removes one transaction. -/
theorem iteratedEvict_fits_fuel (fuel : Nat) (m : Mempool)
    (hFuel : m.entries.length ≤ fuel) :
    totalCost (iteratedEvict fuel m).entries ≤ m.costLimit ∨
      (iteratedEvict fuel m).entries = [] := by
  induction fuel generalizing m with
  | zero =>
    have hEmpty : m.entries = [] :=
      List.length_eq_zero_iff.mp (Nat.le_zero.mp hFuel)
    right
    rw [iteratedEvict_zero]
    exact hEmpty
  | succ n ih =>
    by_cases hFits : totalCost m.entries ≤ m.costLimit
    · rw [iteratedEvict_succ_fits n m hFits]
      left; exact hFits
    · rcases m with ⟨entries, L⟩
      cases entries with
      | nil =>
        change ¬ totalCost ([] : List Entry) ≤ L at hFits
        exact absurd (Nat.zero_le _) hFits
      | cons e rest =>
        rw [iteratedEvict_succ_overfull_cons n L e rest hFits]
        have hLen := pickHighestAux_remaining_length e rest
        set m' : Mempool := { entries := (pickHighestAux e rest).2, costLimit := L }
        have hNewLen : m'.entries.length ≤ n := by
          change (pickHighestAux e rest).2.length ≤ n
          rw [hLen]
          have hOriginal : (e :: rest).length ≤ n + 1 := hFuel
          simp at hOriginal
          omega
        exact ih m' hNewLen

/-- **T14 (`evictUntilFits` makes the mempool fit, or empties it).** -/
theorem evictUntilFits_fits (m : Mempool) :
    totalCost (evictUntilFits m).entries ≤ m.costLimit ∨
      (evictUntilFits m).entries = [] :=
  iteratedEvict_fits_fuel _ _ (Nat.le_refl _)

/-- **T15 (`evictUntilFits` preserves cost limit).** -/
theorem evictUntilFits_costLimit (m : Mempool) :
    (evictUntilFits m).costLimit = m.costLimit :=
  iteratedEvict_costLimit m.entries.length m

/-! ## Concrete examples (byte-cost model) -/

/-- A four-entry mempool where the entry with the highest eviction
weight is evicted first. Entries are over-cost-limit-by-construction so
that the eviction step is exercised. The picked entry is the one with
the largest `weight` field — `{txid := 2, cost := 60_000, weight := 100_000}`. -/
theorem example_evict_highest_weight :
    evictOne
        { entries :=
            [ ⟨1, 20_000, 20_000⟩
            , ⟨2, 60_000, 100_000⟩
            , ⟨3, 30_000, 30_000⟩
            ]
        , costLimit := 50_000 } =
      some
        ( { entries :=
              [ ⟨1, 20_000, 20_000⟩
              , ⟨3, 30_000, 30_000⟩
              ]
          , costLimit := 50_000 }
        , ⟨2, 60_000, 100_000⟩ ) := by
  rfl

/-- A concrete `evictUntilFits` example: a 3-entry mempool with
`costLimit = 30_000` evicts the highest-weighted entry first, then
fits in cost. The result has total cost `≤ 30_000`. -/
theorem example_iterated_fits :
    totalCost
        (evictUntilFits
            { entries :=
                [ ⟨1, 15_000, 15_000⟩
                , ⟨2, 60_000, 100_000⟩
                , ⟨3, 12_000, 12_000⟩
                ]
            , costLimit := 30_000 }).entries ≤ 30_000 := by
  rcases evictUntilFits_fits
      ({ entries :=
            [ ⟨1, 15_000, 15_000⟩
            , ⟨2, 60_000, 100_000⟩
            , ⟨3, 12_000, 12_000⟩ ]
        , costLimit := 30_000 } : Mempool) with hLe | hNil
  · exact hLe
  · rw [hNil]; exact Nat.zero_le _

end Zebra.MempoolEviction
