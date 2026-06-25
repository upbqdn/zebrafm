import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# ZIP-317 mempool eviction (abstract weight-ratio policy)

When Zebra's mempool reaches its configured maximum size, transactions must
be evicted to make room. The economic intent of ZIP-317's mempool/block
production rules is captured by a transaction's *fee weight ratio* — the
quantity `miner_fee / conventional_fee`, clamped at
`BLOCK_PRODUCTION_WEIGHT_RATIO_CAP`
(`zebra-chain/src/transaction/unmined/zip317.rs:113`,
`conventional_fee_weight_ratio`). Transactions with the lowest weight ratios
contribute the least block-production value per byte of cost; the abstract
eviction policy this module models is:

> When the mempool is full, evict the transaction with the lowest fee weight
> ratio first.

This is the *deterministic-lowest-first* abstraction of the full ZIP-401
randomised weighted eviction (which adds the
`MEMPOOL_TRANSACTION_LOW_FEE_PENALTY = 40_000` low-fee penalty before drawing,
`zebra-chain/src/transaction/unmined.rs:75`). The two policies agree on the
load-bearing economic property: cheaper transactions are evicted in
preference to more expensive ones. We do not model randomisation here;
the deterministic version is what the consensus-adjacent reasoning relies on.

We model the mempool abstractly:

  * a transaction is an `Entry` with a `txid` and a `ratio` (the scaled
    weight ratio; the actual Rust type is `f32` — we use `Nat` to avoid a
    floating-point model, which would change *only* the numeric type, not
    the eviction semantics);
  * a mempool is a `List Entry` together with a capacity `cap : Nat`;
  * one eviction step recursively walks the list, threading the smallest
    `best` seen so far and removing it from the result. This makes the
    selection-and-removal compositional and the per-step properties
    (length reduction; remaining ratios are `≥` evicted ratio) follow by
    a single induction on the list, with one `by_cases` on whether the
    next entry's ratio strictly improves on `best`.

The three load-bearing theorems requested by the task are:

  * **size reduction** (T3): an eviction step reduces the mempool length by
    exactly `1`;
  * **remaining ratios ≥ evicted ratio** (T4): every entry left in the
    mempool after eviction has weight ratio at least as large as the
    evicted transaction's weight ratio;
  * **eventually fits** (T9 — `iteratedEvict_fits`): iterating eviction
    until size ≤ cap terminates and the final mempool fits in the cap.

Sources cited:
  * `MEMPOOL_TRANSACTION_COST_THRESHOLD`, `MEMPOOL_TRANSACTION_LOW_FEE_PENALTY`,
    `eviction_weight()` —
    `zebra-chain/src/transaction/unmined.rs:43-75, 472-497`.
  * `conventional_fee_weight_ratio` —
    `zebra-chain/src/transaction/unmined/zip317.rs:113-134`.
  * `BLOCK_PRODUCTION_WEIGHT_RATIO_CAP = 4.0` —
    `zebra-chain/src/transaction/unmined/zip317.rs:36`.
-/

namespace Zebra.MempoolEviction

/-! ## Constants and model -/

/-- The `MEMPOOL_TRANSACTION_COST_THRESHOLD` from ZIP-401: a transaction's
cost is `max(size_bytes, 10_000)`.
Source: `zebra-chain/src/transaction/unmined.rs:67`. -/
def MEMPOOL_TRANSACTION_COST_THRESHOLD : Nat := 10_000

/-- The `MEMPOOL_TRANSACTION_LOW_FEE_PENALTY` from ZIP-401: penalty added to
the eviction weight of a transaction paying below the conventional fee.
Source: `zebra-chain/src/transaction/unmined.rs:75`. -/
def MEMPOOL_TRANSACTION_LOW_FEE_PENALTY : Nat := 40_000

/-- The `BLOCK_PRODUCTION_WEIGHT_RATIO_CAP` from ZIP-317, scaled by `1_000` so
that the `f32`-valued `4.0` cap is representable as a `Nat`.
Source: `zebra-chain/src/transaction/unmined/zip317.rs:36`. -/
def BLOCK_PRODUCTION_WEIGHT_RATIO_CAP_SCALED : Nat := 4_000

/-- One mempool entry: a transaction id together with its scaled weight
ratio. -/
structure Entry where
  txid : Nat
  ratio : Nat

/-- A mempool: a list of entries and a configured capacity in number of
transactions. -/
structure Mempool where
  entries : List Entry
  cap : Nat

/-! ## Eviction step — recursive selection-and-removal -/

/-- One-step eviction with a running "best so far". Returns
`(evicted, remaining)` where `evicted` is the minimum-ratio entry in
`best :: rest` (first occurrence wins ties), and `remaining` is the rest
of the list with `evicted` removed (preserving order). -/
def pickLowestAux : Entry → List Entry → Entry × List Entry
  | best, []        => (best, [])
  | best, e :: rest =>
      if e.ratio < best.ratio then
        let p := pickLowestAux e rest
        (p.1, best :: p.2)
      else
        let p := pickLowestAux best rest
        (p.1, e :: p.2)

/-- One eviction step on a mempool. Returns `none` when the mempool is
empty; otherwise removes the minimum-ratio entry and returns the new
mempool plus the evicted entry. -/
def evictOne : Mempool → Option (Mempool × Entry)
  | { entries := [], cap := _ } => none
  | { entries := e :: rest, cap := c } =>
      let p := pickLowestAux e rest
      some ({ entries := p.2, cap := c }, p.1)

/-- Iterated eviction with explicit fuel: drop the minimum-ratio entry
until the mempool fits in its capacity, bounded by `fuel` steps. -/
def iteratedEvict : Nat → Mempool → Mempool
  | 0, m => m
  | n + 1, m =>
      if m.entries.length ≤ m.cap then m
      else
        match m.entries with
        | [] => m
        | e :: rest =>
            let p := pickLowestAux e rest
            iteratedEvict n { entries := p.2, cap := m.cap }

/-- Convenience wrapper: iterate with fuel equal to initial size. -/
def evictUntilFits (m : Mempool) : Mempool :=
  iteratedEvict m.entries.length m

/-! ## Equations for `pickLowestAux` -/

theorem pickLowestAux_nil (best : Entry) :
    pickLowestAux best [] = (best, []) := rfl

theorem pickLowestAux_cons_lt (best e : Entry) (rest : List Entry)
    (hLt : e.ratio < best.ratio) :
    pickLowestAux best (e :: rest) =
      ((pickLowestAux e rest).1, best :: (pickLowestAux e rest).2) := by
  change (if e.ratio < best.ratio then _ else _) = _
  rw [if_pos hLt]

theorem pickLowestAux_cons_ge (best e : Entry) (rest : List Entry)
    (hGe : ¬ e.ratio < best.ratio) :
    pickLowestAux best (e :: rest) =
      ((pickLowestAux best rest).1, e :: (pickLowestAux best rest).2) := by
  change (if e.ratio < best.ratio then _ else _) = _
  rw [if_neg hGe]

/-! ## Lemmas about `pickLowestAux` -/

/-- The evicted entry's ratio is `≤ best.ratio`. -/
theorem pickLowestAux_evicted_le_best (best : Entry) (rest : List Entry) :
    (pickLowestAux best rest).1.ratio ≤ best.ratio := by
  induction rest generalizing best with
  | nil => rw [pickLowestAux_nil]
  | cons e xs ih =>
    by_cases hLt : e.ratio < best.ratio
    · rw [pickLowestAux_cons_lt best e xs hLt]
      have hStep := ih e
      have hLe : e.ratio ≤ best.ratio := Nat.le_of_lt hLt
      exact Nat.le_trans hStep hLe
    · rw [pickLowestAux_cons_ge best e xs hLt]
      exact ih best

/-- The evicted entry's ratio is `≤` every ratio in `rest`. -/
theorem pickLowestAux_evicted_le_rest (best : Entry) (rest : List Entry)
    (x : Entry) (h : x ∈ rest) :
    (pickLowestAux best rest).1.ratio ≤ x.ratio := by
  induction rest generalizing best with
  | nil => exact absurd h List.not_mem_nil
  | cons e xs ih =>
    by_cases hLt : e.ratio < best.ratio
    · rw [pickLowestAux_cons_lt best e xs hLt]
      rcases List.mem_cons.mp h with heq | hin
      · subst heq
        exact pickLowestAux_evicted_le_best x xs
      · exact ih e hin
    · rw [pickLowestAux_cons_ge best e xs hLt]
      rcases List.mem_cons.mp h with heq | hin
      · subst heq
        have hBest := pickLowestAux_evicted_le_best best xs
        have hGe : best.ratio ≤ x.ratio := Nat.le_of_not_lt hLt
        exact Nat.le_trans hBest hGe
      · exact ih best hin

/-- The remaining list has length `rest.length`. -/
theorem pickLowestAux_remaining_length (best : Entry) (rest : List Entry) :
    (pickLowestAux best rest).2.length = rest.length := by
  induction rest generalizing best with
  | nil => rw [pickLowestAux_nil]
  | cons e xs ih =>
    by_cases hLt : e.ratio < best.ratio
    · rw [pickLowestAux_cons_lt best e xs hLt, List.length_cons, List.length_cons]
      exact congrArg (· + 1) (ih e)
    · rw [pickLowestAux_cons_ge best e xs hLt, List.length_cons, List.length_cons]
      exact congrArg (· + 1) (ih best)

/-- Every entry in the remaining list has ratio `≥` the evicted ratio. -/
theorem pickLowestAux_remaining_ge_evicted (best : Entry) (rest : List Entry)
    (x : Entry) (h : x ∈ (pickLowestAux best rest).2) :
    (pickLowestAux best rest).1.ratio ≤ x.ratio := by
  induction rest generalizing best with
  | nil =>
    rw [pickLowestAux_nil] at h
    exact absurd h List.not_mem_nil
  | cons e xs ih =>
    by_cases hLt : e.ratio < best.ratio
    · rw [pickLowestAux_cons_lt best e xs hLt] at h ⊢
      rcases List.mem_cons.mp h with heq | hin
      · subst heq
        have hInner := pickLowestAux_evicted_le_best e xs
        have hStep : e.ratio ≤ x.ratio := Nat.le_of_lt hLt
        exact Nat.le_trans hInner hStep
      · exact ih e hin
    · rw [pickLowestAux_cons_ge best e xs hLt] at h ⊢
      rcases List.mem_cons.mp h with heq | hin
      · subst heq
        have hInner := pickLowestAux_evicted_le_best best xs
        have hStep : best.ratio ≤ x.ratio := Nat.le_of_not_lt hLt
        exact Nat.le_trans hInner hStep
      · exact ih best hin

/-! ## Equations for `evictOne` -/

theorem evictOne_nil (c : Nat) :
    evictOne { entries := [], cap := c } = none := rfl

theorem evictOne_cons (e : Entry) (rest : List Entry) (c : Nat) :
    evictOne { entries := e :: rest, cap := c } =
      let p := pickLowestAux e rest
      some ({ entries := p.2, cap := c }, p.1) := rfl

/-! ## Equations for `iteratedEvict` -/

theorem iteratedEvict_zero (m : Mempool) :
    iteratedEvict 0 m = m := rfl

/-- When the mempool already fits, `iteratedEvict` returns it unchanged. -/
theorem iteratedEvict_succ_fits (n : Nat) (m : Mempool)
    (h : m.entries.length ≤ m.cap) :
    iteratedEvict (n + 1) m = m := by
  change (if m.entries.length ≤ m.cap then m else _) = m
  rw [if_pos h]

/-- When the mempool is overfull and has at least one entry, the recursion
peels off the minimum-ratio entry. -/
theorem iteratedEvict_succ_overfull_cons (n : Nat) (c : Nat)
    (e : Entry) (rest : List Entry)
    (hOver : ¬ (e :: rest).length ≤ c) :
    iteratedEvict (n + 1) { entries := e :: rest, cap := c } =
      iteratedEvict n
        { entries := (pickLowestAux e rest).2, cap := c } := by
  change (if (e :: rest).length ≤ c then _ else _) = _
  rw [if_neg hOver]

/-- When the mempool is overfull and empty (impossible in practice), the
recursion returns it unchanged. (The "empty" branch is dead code because
`[].length = 0 ≤ c`, but the definition handles it.) -/
theorem iteratedEvict_succ_overfull_nil (n : Nat) (c : Nat)
    (hOver : ¬ ([] : List Entry).length ≤ c) :
    iteratedEvict (n + 1) { entries := [], cap := c } =
      ({ entries := [], cap := c } : Mempool) := by
  change (if _ ≤ c then _ else _) = _
  rw [if_neg hOver]

/-! ## Main theorems -/

/-- **T1 (constants match Rust).** Spot-check that the ZIP-401 constants
match the values in `zebra-chain/src/transaction/unmined.rs`. -/
theorem mempool_constants_values :
    MEMPOOL_TRANSACTION_COST_THRESHOLD = 10_000 ∧
    MEMPOOL_TRANSACTION_LOW_FEE_PENALTY = 40_000 ∧
    BLOCK_PRODUCTION_WEIGHT_RATIO_CAP_SCALED = 4_000 :=
  ⟨rfl, rfl, rfl⟩

/-- **T2 (eviction is well-defined exactly on non-empty mempools).** -/
theorem evictOne_isSome_iff (m : Mempool) :
    (evictOne m).isSome ↔ m.entries ≠ [] := by
  rcases m with ⟨entries, cap⟩
  cases entries with
  | nil => simp [evictOne_nil]
  | cons e rest => simp [evictOne_cons]

/-- **T3 (eviction reduces size by exactly 1).** One step of eviction
reduces the mempool length by exactly one. This is the load-bearing
"size reduction" property. -/
theorem evictOne_length (m : Mempool) (m' : Mempool) (evicted : Entry)
    (h : evictOne m = some (m', evicted)) :
    m'.entries.length + 1 = m.entries.length := by
  rcases m with ⟨entries, cap⟩
  cases entries with
  | nil =>
    rw [evictOne_nil] at h
    exact absurd h (by simp)
  | cons e rest =>
    rw [evictOne_cons] at h
    -- `h` peels to `m' = { entries := (pickLowestAux e rest).2, cap := cap }`.
    have hInj := Option.some.inj h
    have hM' : m' = { entries := (pickLowestAux e rest).2, cap := cap } :=
      (Prod.mk.inj hInj).1.symm
    rw [hM']
    change (pickLowestAux e rest).2.length + 1 = (e :: rest).length
    have hLen := pickLowestAux_remaining_length e rest
    rw [hLen]
    simp

/-- **T4 (remaining ratios ≥ evicted ratio).** Every transaction left in
the mempool after eviction has weight ratio at least as large as the
evicted transaction's weight ratio. This is the load-bearing "lowest
weight-ratio first" property: no remaining transaction is worse than the
one we evicted. -/
theorem evictOne_remaining_ge_evicted (m : Mempool) (m' : Mempool)
    (evicted : Entry) (h : evictOne m = some (m', evicted))
    (x : Entry) (hx : x ∈ m'.entries) :
    evicted.ratio ≤ x.ratio := by
  rcases m with ⟨entries, cap⟩
  cases entries with
  | nil =>
    rw [evictOne_nil] at h
    exact absurd h (by simp)
  | cons e rest =>
    rw [evictOne_cons] at h
    have hInj := Option.some.inj h
    have hM' : m' = { entries := (pickLowestAux e rest).2, cap := cap } :=
      (Prod.mk.inj hInj).1.symm
    have hEv : evicted = (pickLowestAux e rest).1 :=
      (Prod.mk.inj hInj).2.symm
    rw [hM'] at hx
    rw [hEv]
    exact pickLowestAux_remaining_ge_evicted e rest x hx

/-- **T5 (eviction preserves capacity).** -/
theorem evictOne_cap (m : Mempool) (m' : Mempool) (evicted : Entry)
    (h : evictOne m = some (m', evicted)) :
    m'.cap = m.cap := by
  rcases m with ⟨entries, cap⟩
  cases entries with
  | nil =>
    rw [evictOne_nil] at h
    exact absurd h (by simp)
  | cons e rest =>
    rw [evictOne_cons] at h
    have hInj := Option.some.inj h
    have hM' : m' = { entries := (pickLowestAux e rest).2, cap := cap } :=
      (Prod.mk.inj hInj).1.symm
    rw [hM']

/-- **T6 (eviction strictly decreases the mempool length).** -/
theorem evictOne_strictly_smaller (m : Mempool) (m' : Mempool) (evicted : Entry)
    (h : evictOne m = some (m', evicted)) :
    m'.entries.length < m.entries.length := by
  have := evictOne_length m m' evicted h
  omega

/-- **T7 (`iteratedEvict` is a no-op when the mempool already fits).** -/
theorem iteratedEvict_already_fits (fuel : Nat) (m : Mempool)
    (h : m.entries.length ≤ m.cap) :
    iteratedEvict fuel m = m := by
  cases fuel with
  | zero => exact iteratedEvict_zero m
  | succ n => exact iteratedEvict_succ_fits n m h

/-- **T8 (`iteratedEvict` only shrinks the mempool).** -/
theorem iteratedEvict_length_le (fuel : Nat) (m : Mempool) :
    (iteratedEvict fuel m).entries.length ≤ m.entries.length := by
  induction fuel generalizing m with
  | zero =>
    rw [iteratedEvict_zero]
  | succ n ih =>
    by_cases hFits : m.entries.length ≤ m.cap
    · rw [iteratedEvict_succ_fits n m hFits]
    · rcases m with ⟨entries, cap⟩
      cases entries with
      | nil =>
        -- Vacuous: 0 ≤ cap is true, contradicting hFits.
        simp at hFits
      | cons e rest =>
        rw [iteratedEvict_succ_overfull_cons n cap e rest hFits]
        have hLen := pickLowestAux_remaining_length e rest
        set m' : Mempool := { entries := (pickLowestAux e rest).2, cap := cap }
        have hIH := ih m'
        have hRem : m'.entries.length = rest.length := hLen
        have hRestLe : rest.length ≤ (e :: rest).length := by simp
        calc (iteratedEvict n m').entries.length
            ≤ m'.entries.length := hIH
          _ = rest.length := hRem
          _ ≤ (e :: rest).length := hRestLe

/-- **T9 (`iteratedEvict` preserves capacity).** -/
theorem iteratedEvict_cap (fuel : Nat) (m : Mempool) :
    (iteratedEvict fuel m).cap = m.cap := by
  induction fuel generalizing m with
  | zero => rw [iteratedEvict_zero]
  | succ n ih =>
    by_cases hFits : m.entries.length ≤ m.cap
    · rw [iteratedEvict_succ_fits n m hFits]
    · rcases m with ⟨entries, cap⟩
      cases entries with
      | nil =>
        simp at hFits
      | cons e rest =>
        rw [iteratedEvict_succ_overfull_cons n cap e rest hFits]
        change (iteratedEvict n { entries := (pickLowestAux e rest).2, cap := cap }).cap = cap
        rw [ih]

/-- **T10 (`iteratedEvict` with enough fuel makes the mempool fit).** This
is the load-bearing "eventually fits" property. With fuel `≥ original
length`, the result has length `≤ cap` (or is empty, which trivially fits
even when `cap = 0`). -/
theorem iteratedEvict_fits_fuel (fuel : Nat) (m : Mempool)
    (hFuel : m.entries.length ≤ fuel) :
    (iteratedEvict fuel m).entries.length ≤ m.cap ∨
      (iteratedEvict fuel m).entries = [] := by
  induction fuel generalizing m with
  | zero =>
    have hEmpty : m.entries = [] :=
      List.length_eq_zero_iff.mp (Nat.le_zero.mp hFuel)
    right
    rw [iteratedEvict_zero]
    exact hEmpty
  | succ n ih =>
    by_cases hFits : m.entries.length ≤ m.cap
    · rw [iteratedEvict_succ_fits n m hFits]; left; exact hFits
    · rcases m with ⟨entries, cap⟩
      cases entries with
      | nil =>
        simp at hFits
      | cons e rest =>
        rw [iteratedEvict_succ_overfull_cons n cap e rest hFits]
        have hLen := pickLowestAux_remaining_length e rest
        set m' : Mempool := { entries := (pickLowestAux e rest).2, cap := cap }
        have hNewLen : m'.entries.length ≤ n := by
          change (pickLowestAux e rest).2.length ≤ n
          rw [hLen]
          have hOriginal : (e :: rest).length ≤ n + 1 := hFuel
          simp at hOriginal
          omega
        exact ih m' hNewLen

/-- **T11 (the load-bearing "eventually fits" wrapper).** Iterating
eviction with fuel = initial size yields a mempool that fits in its cap
(or has been emptied). -/
theorem iteratedEvict_fits (m : Mempool) :
    (iteratedEvict m.entries.length m).entries.length ≤ m.cap ∨
      (iteratedEvict m.entries.length m).entries = [] :=
  iteratedEvict_fits_fuel _ _ (Nat.le_refl _)

/-- **T12 (`evictUntilFits` makes the mempool fit, or empties it).** -/
theorem evictUntilFits_fits (m : Mempool) :
    (evictUntilFits m).entries.length ≤ m.cap ∨
      (evictUntilFits m).entries = [] :=
  iteratedEvict_fits m

/-- **T13 (`evictUntilFits` preserves capacity).** -/
theorem evictUntilFits_cap (m : Mempool) :
    (evictUntilFits m).cap = m.cap :=
  iteratedEvict_cap m.entries.length m

/-- **T14 (concrete example: lowest-ratio entry is evicted).** A mempool
with entries `[{txid:=1, ratio:=50}, {txid:=2, ratio:=10}, {txid:=3, ratio:=30}]`
evicts entry `2` (ratio `10`) first. -/
theorem example_evict_lowest :
    evictOne { entries := [⟨1, 50⟩, ⟨2, 10⟩, ⟨3, 30⟩], cap := 2 } =
      some ({ entries := [⟨1, 50⟩, ⟨3, 30⟩], cap := 2 }, ⟨2, 10⟩) := by
  rfl

/-- **T15 (concrete `evictUntilFits` example).** A 3-entry mempool with
cap 2 fits after iterated eviction. -/
theorem example_iterated_fits :
    (evictUntilFits { entries := [⟨1, 50⟩, ⟨2, 10⟩, ⟨3, 30⟩], cap := 2 }).entries.length ≤ 2 := by
  rcases evictUntilFits_fits
      ({ entries := [⟨1, 50⟩, ⟨2, 10⟩, ⟨3, 30⟩], cap := 2 } : Mempool) with hLe | hNil
  · exact hLe
  · rw [hNil]; exact Nat.zero_le _

end Zebra.MempoolEviction
