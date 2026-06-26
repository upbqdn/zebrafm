import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Non-finalized chain-state queue (zebra-state)

Zebra's `NonFinalizedState` keeps a `BTreeSet<Arc<Chain>>` ordered by
proof-of-work, plus a tail-loop that drains the best chain down to the
reorg window after every successful block commit. This module models the
three *queue* properties Zebra maintains:

* **Forks cap** — `chain_set.len() ≤ MAX_NON_FINALIZED_CHAIN_FORKS = 10`.
  The cap is enforced by the inner loop in `NonFinalizedState::insert_with`
  (`zebra-state/src/service/non_finalized_state.rs:271-274`), which
  repeatedly pops the **lowest-work** chain via `BTreeSet::pop_first`
  until the set fits.

* **Best-chain length cap** — `best_chain_len() ≤ MAX_BLOCK_REORG_HEIGHT
  = 1000`. After `validate_and_commit_non_finalized` succeeds, the write
  task drains the best chain via the
  `while non_finalized_state.best_chain_len() > MAX_BLOCK_REORG_HEIGHT`
  loop in `zebra-state/src/service/write.rs:451-463`, each iteration
  popping the **root** block to the finalized state via
  `NonFinalizedState::finalize` (`non_finalized_state.rs:286-343`).

* **Invalidated-block queue cap** — `invalidated_blocks.len() ≤
  MAX_INVALIDATED_BLOCKS = 100`. Enforced by the loop at
  `non_finalized_state.rs:411-413`, which drops the oldest entry via
  `shift_remove_index(0)`.

Once `finalize` pops a block from the front of the best chain, it is
moved to the finalized state and the non-finalized side cannot bring it
back: this is the state-machine-level statement of "no reorg past the
finalized tip".

Source map for the constants used here:

* `MAX_NON_FINALIZED_CHAIN_FORKS = 10` —
   `zebra-state/src/constants.rs:92`.
* `MAX_BLOCK_REORG_HEIGHT = 1000` —
   `zebra-chain/src/parameters/constants.rs:30`, re-exported via
   `zebra-state/src/constants.rs:19`.
* `MAX_INVALIDATED_BLOCKS = 100` —
   `zebra-state/src/constants.rs:106`.

## Model

We avoid bringing in a real `BTreeSet`; instead, the chain set is modelled
as a `List Nat` of cumulative-work values, kept *sorted in non-decreasing
order* (so the head is the lowest-work chain and the last element is the
best). This matches `BTreeSet<Arc<Chain>>` because `Chain::cmp` is
exactly by cumulative work (`Chain::Ord` impl in `non_finalized_state/
chain.rs`). The two operations we mirror:

* `popLowestStep` / `popLowestUntilCap` — repeated `BTreeSet::pop_first`,
  draining the front until the set fits below the forks cap. This is
  the `while self.chain_set.len() > MAX_NON_FINALIZED_CHAIN_FORKS {
  pop_first() }` loop in `non_finalized_state.rs:271-274`.

* `popRootStep` / `popRootUntilWindow` — repeated `Chain::pop_root`,
  draining the front of the best chain until it fits inside the reorg
  window. This is the `write.rs:451-463` loop.

Both are length-only abstractions: we track the chain count and the best
chain's block count as `Nat`s and prove the loops terminate at the
correct caps. The shape mirrors `Zebra.MempoolEviction.iteratedEvict`.
-/

namespace Zebra.StateNonFinalized

/-! ## Constants -/

/-- `MAX_NON_FINALIZED_CHAIN_FORKS = 10`: the upper bound on the number of
non-finalized chain forks Zebra tracks before evicting the lowest-work
fork. Source: `zebra-state/src/constants.rs:92`. -/
def MAX_NON_FINALIZED_CHAIN_FORKS : Nat := 10

/-- `MAX_BLOCK_REORG_HEIGHT = 1000`: the upper bound on the best chain's
non-finalized portion. Source: `zebra-chain/src/parameters/constants.rs:30`,
re-exported via `zebra-state/src/constants.rs:19`. -/
def MAX_BLOCK_REORG_HEIGHT : Nat := 1000

/-- `MAX_INVALIDATED_BLOCKS = 100`: the upper bound on the invalidated-block
record queue. Source: `zebra-state/src/constants.rs:106`. -/
def MAX_INVALIDATED_BLOCKS : Nat := 100

/-! ## Chain set: sorted work list -/

/-- The non-finalized chain set is modelled as a `List Nat` of
cumulative-work values, kept sorted in non-decreasing order (matching
`BTreeSet<Arc<Chain>>` under `Chain::Ord`). The head is the lowest-work
chain (the `BTreeSet::pop_first` target); the last element is the best
chain. -/
abbrev ChainSet := List Nat

/-- Forks-cap predicate: `chain_set.len() > MAX_NON_FINALIZED_CHAIN_FORKS`
fires the eviction loop in `non_finalized_state.rs:271`. -/
def forksCapExceeded (cs : ChainSet) : Bool :=
  decide (cs.length > MAX_NON_FINALIZED_CHAIN_FORKS)

/-- One step of the forks-cap drain: pop the **lowest-work** chain via
`BTreeSet::pop_first`. Modelled as `List.tail`. When the list is empty,
`List.tail` returns `[]`; the guard prevents this branch from firing on
an empty list (an empty list cannot have length > 10). -/
def popLowestStep (cs : ChainSet) : ChainSet :=
  if forksCapExceeded cs then cs.tail else cs

/-- Iterated forks-cap drain with explicit fuel. The Rust loop pops one
chain per iteration; with fuel equal to the input length, termination is
guaranteed. -/
def popLowestUntilCap : Nat → ChainSet → ChainSet
  | 0, cs => cs
  | n + 1, cs =>
      if forksCapExceeded cs then
        popLowestUntilCap n cs.tail
      else
        cs

/-! ## Best chain length: reorg-window drain -/

/-- The best chain is modelled by its block count. The reorg-window
drain in `write.rs:451-463` is a `while best_chain_len() >
MAX_BLOCK_REORG_HEIGHT { finalize() }` loop; each iteration decreases
the best-chain length by one (the root block becomes finalized). -/
abbrev BestChainLen := Nat

/-- Reorg-window predicate: `best_chain_len() > MAX_BLOCK_REORG_HEIGHT`
fires the finalization loop. -/
def reorgWindowExceeded (len : BestChainLen) : Bool :=
  decide (len > MAX_BLOCK_REORG_HEIGHT)

/-- One step of the reorg-window drain: shrink the best chain by one
(the root is moved to the finalized state). When the guard does not
fire, the step is the identity. -/
def popRootStep (len : BestChainLen) : BestChainLen :=
  if reorgWindowExceeded len then len - 1 else len

/-- Iterated reorg-window drain with explicit fuel. -/
def popRootUntilWindow : Nat → BestChainLen → BestChainLen
  | 0, len => len
  | n + 1, len =>
      if reorgWindowExceeded len then
        popRootUntilWindow n (len - 1)
      else
        len

/-! ## Invalidated-block queue -/

/-- `MAX_INVALIDATED_BLOCKS` drain guard: fires when the invalidated
queue exceeds 100. -/
def invalidatedCapExceeded (n : Nat) : Bool :=
  decide (n > MAX_INVALIDATED_BLOCKS)

/-- One step of the invalidated-block drain, modelled on Rust's
`shift_remove_index(0)` from `non_finalized_state.rs:412`. -/
def shiftRemoveOldestStep (n : Nat) : Nat :=
  if invalidatedCapExceeded n then n - 1 else n

/-- Iterated invalidated-block drain with explicit fuel. -/
def trimInvalidated : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n =>
      if invalidatedCapExceeded n then
        trimInvalidated k (n - 1)
      else
        n

/-! ## Finalisation: state-machine model

To talk about "once finalized, never reorged", we model finalisation as
moving the front of the non-finalized chain into a finalized counter.
The combined invariant: the sum of finalized-count and best-chain length
equals the original total, so no finalisation step can ever bring a
block back into the non-finalized side. -/

/-- A snapshot of the chain-tip state machine: a count of finalised
blocks and the length of the non-finalized best chain. -/
structure ChainState where
  finalized : Nat
  bestLen : Nat
  deriving Repr

/-- One finalisation step on the state machine: when the reorg-window
guard fires, move one block from the non-finalized chain into the
finalized count. -/
def finalizeStep (s : ChainState) : ChainState :=
  if reorgWindowExceeded s.bestLen then
    { finalized := s.finalized + 1, bestLen := s.bestLen - 1 }
  else s

/-- Iterated finalisation with explicit fuel. -/
def finalizeUntilWindow : Nat → ChainState → ChainState
  | 0, s => s
  | n + 1, s =>
      if reorgWindowExceeded s.bestLen then
        finalizeUntilWindow n
          { finalized := s.finalized + 1, bestLen := s.bestLen - 1 }
      else s

/-! ## Theorems

We prove the four claims requested in the task brief:
  * forks cap: `chain_set.len() ≤ MAX_NON_FINALIZED_CHAIN_FORKS`
    (T3, T4, T5, T6);
  * reorg-window cap: `best_chain_len() ≤ MAX_BLOCK_REORG_HEIGHT`
    (T7, T8, T9, T10);
  * eviction order at the forks cap: it is the **lowest-work** chain
    that goes first (T11 — modelled by `List.tail` removing the head of
    a non-decreasing list);
  * finalisation invariant: once finalized, never reorged (T12, T13). -/

/-- **T1 (constants match Rust).** The three eviction constants modelled
here pin their upstream values exactly. -/
theorem constants_values :
    MAX_NON_FINALIZED_CHAIN_FORKS = 10 ∧
    MAX_BLOCK_REORG_HEIGHT = 1000 ∧
    MAX_INVALIDATED_BLOCKS = 100 :=
  ⟨rfl, rfl, rfl⟩

/-- **T2 (forks-cap unfolds).** Defining iff for the forks-cap guard. -/
theorem forksCapExceeded_iff (cs : ChainSet) :
    forksCapExceeded cs = true ↔ cs.length > MAX_NON_FINALIZED_CHAIN_FORKS := by
  unfold forksCapExceeded
  simp

/-! ### Forks-cap layer -/

/-- **T3 (forks-cap step strictly decreases length).** When the forks
cap is exceeded, `popLowestStep` strictly decreases the chain count.
This is the termination measure for the Rust `while` loop. -/
theorem popLowestStep_strict_decrease (cs : ChainSet)
    (hFire : forksCapExceeded cs = true) :
    (popLowestStep cs).length < cs.length := by
  unfold popLowestStep
  rw [if_pos hFire]
  have hLen : cs.length > MAX_NON_FINALIZED_CHAIN_FORKS :=
    (forksCapExceeded_iff cs).mp hFire
  -- cs.length > 10 ≥ 1, so cs is non-empty.
  cases cs with
  | nil =>
    simp [List.length_nil, MAX_NON_FINALIZED_CHAIN_FORKS] at hLen
  | cons x xs =>
    simp [List.tail_cons, List.length_cons]

/-- **T4 (forks-cap step no-op).** When the forks cap is not exceeded,
the step leaves the chain set unchanged. -/
theorem popLowestStep_noop (cs : ChainSet)
    (hNoFire : forksCapExceeded cs = false) :
    popLowestStep cs = cs := by
  unfold popLowestStep
  rw [if_neg]
  simp [hNoFire]

/-- Helper: fuel-stable drain. Once the guard no longer fires, extra fuel
has no effect. -/
theorem popLowestUntilCap_fuel_stable (n : Nat) (cs : ChainSet)
    (hStable : forksCapExceeded cs = false) :
    popLowestUntilCap n cs = cs := by
  cases n with
  | zero => rfl
  | succ k =>
    unfold popLowestUntilCap
    simp [hStable]

/-- Helper: each iteration with the guard firing pops one element. The
length goes down by 1, so iterating with fuel ≥ `cs.length - cap` ends
with the guard not firing. -/
theorem popLowestUntilCap_postcondition_aux (n : Nat) (cs : ChainSet)
    (hFuel : n ≥ cs.length) :
    forksCapExceeded (popLowestUntilCap n cs) = false := by
  induction n generalizing cs with
  | zero =>
    -- `cs.length ≤ 0` forces `cs = []`.
    have : cs.length = 0 := Nat.le_zero.mp hFuel
    have hNil : cs = [] := List.length_eq_zero_iff.mp this
    subst hNil
    decide
  | succ k ih =>
    unfold popLowestUntilCap
    by_cases hFire : forksCapExceeded cs = true
    · -- Guard fires: chain non-empty (since cap > 0), recurse on tail.
      rw [if_pos hFire]
      have hLen : cs.length > MAX_NON_FINALIZED_CHAIN_FORKS :=
        (forksCapExceeded_iff cs).mp hFire
      cases cs with
      | nil =>
        simp only [List.length_nil] at hLen
        unfold MAX_NON_FINALIZED_CHAIN_FORKS at hLen
        exact absurd hLen (by decide)
      | cons x xs =>
        simp only [List.tail_cons]
        apply ih
        simp only [List.length_cons] at hFuel
        omega
    · -- Guard does not fire: the step is the identity.
      have hF : forksCapExceeded cs = false := by
        cases hbit : forksCapExceeded cs with
        | false => rfl
        | true => exact absurd hbit hFire
      rw [if_neg hFire]
      exact hF

/-- **T5 (forks-cap post-condition).** With fuel equal to the chain
set's length, `popLowestUntilCap` returns a chain set whose guard does
not fire — i.e. the count is at most the cap. -/
theorem popLowestUntilCap_postcondition (cs : ChainSet) :
    forksCapExceeded (popLowestUntilCap cs.length cs) = false :=
  popLowestUntilCap_postcondition_aux cs.length cs (Nat.le_refl _)

/-- **T6 (forks-cap bound).** After draining, the chain set's length is
at most `MAX_NON_FINALIZED_CHAIN_FORKS`. This is the bound the
non-finalized state advertises. -/
theorem popLowestUntilCap_length_le_cap (cs : ChainSet) :
    (popLowestUntilCap cs.length cs).length ≤ MAX_NON_FINALIZED_CHAIN_FORKS := by
  have h := popLowestUntilCap_postcondition cs
  unfold forksCapExceeded at h
  simp only [decide_eq_false_iff_not, not_lt] at h
  exact h

/-! ### Reorg-window layer -/

/-- **T7 (reorg-window unfolds).** Defining iff for the reorg-window
guard. -/
theorem reorgWindowExceeded_iff (len : BestChainLen) :
    reorgWindowExceeded len = true ↔ len > MAX_BLOCK_REORG_HEIGHT := by
  unfold reorgWindowExceeded
  simp

/-- **T8 (reorg-window step strictly decreases).** When the guard fires,
`popRootStep` strictly decreases the best-chain length. -/
theorem popRootStep_strict_decrease (len : BestChainLen)
    (hFire : reorgWindowExceeded len = true) :
    popRootStep len < len := by
  have hLen : len > MAX_BLOCK_REORG_HEIGHT :=
    (reorgWindowExceeded_iff len).mp hFire
  have hPos : 0 < len := by
    have h1 : 1000 < len := hLen
    exact Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 1000) (Nat.le_of_lt h1)
  unfold popRootStep
  rw [if_pos hFire]
  exact Nat.sub_lt hPos Nat.one_pos

/-- Helper: fuel-stable for the reorg-window drain. -/
theorem popRootUntilWindow_fuel_stable (n : Nat) (len : BestChainLen)
    (hStable : reorgWindowExceeded len = false) :
    popRootUntilWindow n len = len := by
  cases n with
  | zero => rfl
  | succ k =>
    unfold popRootUntilWindow
    simp [hStable]

/-- **T9 (reorg-window post-condition).** With enough fuel,
`popRootUntilWindow` terminates with the guard not firing. -/
theorem popRootUntilWindow_postcondition (len : BestChainLen) :
    reorgWindowExceeded (popRootUntilWindow len len) = false := by
  induction len with
  | zero => decide
  | succ k ih =>
    unfold popRootUntilWindow
    by_cases hFire : reorgWindowExceeded (k + 1) = true
    · -- Guard fires: drop to k, recurse with fuel k.
      rw [if_pos hFire]
      exact ih
    · -- Guard does not fire.
      have hF : reorgWindowExceeded (k + 1) = false := by
        cases hbit : reorgWindowExceeded (k + 1) with
        | false => rfl
        | true => exact absurd hbit hFire
      rw [if_neg hFire]
      exact hF

/-- **T10 (reorg-window bound).** After the drain, the best chain is at
most `MAX_BLOCK_REORG_HEIGHT` blocks long. This is the headline bound
on the non-finalized chain queue. -/
theorem popRootUntilWindow_le_max (len : BestChainLen) :
    popRootUntilWindow len len ≤ MAX_BLOCK_REORG_HEIGHT := by
  have h := popRootUntilWindow_postcondition len
  unfold reorgWindowExceeded at h
  simp only [decide_eq_false_iff_not, not_lt] at h
  exact h

/-! ### Eviction order: lowest-work first -/

/-- **T11 (eviction order at the forks cap).** When the chain set is
sorted in non-decreasing order of cumulative work (`Chain::Ord`),
`popLowestStep` removes a chain whose work is `≤` every remaining
chain's work. This witnesses Rust's `BTreeSet::pop_first` policy:
the lowest-work chain is evicted, not an arbitrary fork.

We state this in the form that does not need the full `Sorted`
predicate: under the sorted assumption, every element of the resulting
list (i.e. the tail) has work `≥` the head's work, by definition of
`Sorted (· ≤ ·)`. -/
theorem popLowestStep_evicts_lowest_work
    (head : Nat) (rest : ChainSet)
    (hSorted : ∀ x ∈ rest, head ≤ x)
    (hFire : forksCapExceeded (head :: rest) = true) :
    ∀ y ∈ popLowestStep (head :: rest), head ≤ y := by
  intro y hy
  unfold popLowestStep at hy
  rw [if_pos hFire] at hy
  simp only [List.tail_cons] at hy
  exact hSorted y hy

/-! ### Finalisation invariant: once finalized, never reorged -/

/-- **T12 (finalisation conservation).** A single finalisation step
preserves the total `finalized + bestLen`. Combined with `bestLen ≥ 0`,
this says no step can ever **decrease** the finalized count: blocks
move one-way from the non-finalized side to the finalized side. -/
theorem finalizeStep_conserves (s : ChainState) :
    (finalizeStep s).finalized + (finalizeStep s).bestLen
      = s.finalized + s.bestLen := by
  unfold finalizeStep
  by_cases hFire : reorgWindowExceeded s.bestLen = true
  · rw [if_pos hFire]
    -- bestLen > 1000, so bestLen ≥ 1; the Nat subtraction `bestLen - 1`
    -- behaves arithmetically.
    have hLen : s.bestLen > MAX_BLOCK_REORG_HEIGHT :=
      (reorgWindowExceeded_iff s.bestLen).mp hFire
    have hPos : s.bestLen ≥ 1 := by
      unfold MAX_BLOCK_REORG_HEIGHT at hLen
      omega
    change (s.finalized + 1) + (s.bestLen - 1) = s.finalized + s.bestLen
    omega
  · rw [if_neg hFire]

/-- **T13 (finalisation is monotone — once finalized, never reorged).**
A single finalisation step never decreases the `finalized` counter.
Combined with T12, this is the state-machine-level "no reorg past the
finalized tip" property: blocks cross the finalisation boundary in one
direction only. -/
theorem finalizeStep_monotone (s : ChainState) :
    s.finalized ≤ (finalizeStep s).finalized := by
  unfold finalizeStep
  by_cases hFire : reorgWindowExceeded s.bestLen = true
  · rw [if_pos hFire]
    exact Nat.le_succ _
  · have hF : reorgWindowExceeded s.bestLen = false := by
      cases hbit : reorgWindowExceeded s.bestLen with
      | false => rfl
      | true => exact absurd hbit hFire
    rw [if_neg hFire]

/-- **T14 (iterated finalisation conserves total).** Generalises T12 to
the full drain loop in `write.rs:451-463`. -/
theorem finalizeUntilWindow_conserves (n : Nat) (s : ChainState) :
    (finalizeUntilWindow n s).finalized + (finalizeUntilWindow n s).bestLen
      = s.finalized + s.bestLen := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
    unfold finalizeUntilWindow
    by_cases hFire : reorgWindowExceeded s.bestLen = true
    · rw [if_pos hFire]
      have hLen : s.bestLen > MAX_BLOCK_REORG_HEIGHT :=
        (reorgWindowExceeded_iff s.bestLen).mp hFire
      have hPos : s.bestLen ≥ 1 := by
        unfold MAX_BLOCK_REORG_HEIGHT at hLen
        omega
      have hStep := ih { finalized := s.finalized + 1, bestLen := s.bestLen - 1 }
      simp at hStep
      omega
    · have hF : reorgWindowExceeded s.bestLen = false := by
        cases hbit : reorgWindowExceeded s.bestLen with
        | false => rfl
        | true => exact absurd hbit hFire
      rw [if_neg hFire]

/-- **T15 (iterated finalisation is monotone in `finalized`).** The
`finalized` counter only grows under the drain loop, never shrinks. -/
theorem finalizeUntilWindow_monotone (n : Nat) (s : ChainState) :
    s.finalized ≤ (finalizeUntilWindow n s).finalized := by
  induction n generalizing s with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    unfold finalizeUntilWindow
    by_cases hFire : reorgWindowExceeded s.bestLen = true
    · rw [if_pos hFire]
      have hStep := ih { finalized := s.finalized + 1, bestLen := s.bestLen - 1 }
      -- `hStep` knows `s.finalized + 1 ≤ (drained).finalized`; transitive
      -- chain `s.finalized ≤ s.finalized + 1 ≤ (drained).finalized`.
      exact Nat.le_trans (Nat.le_succ _) hStep
    · rw [if_neg hFire]

/-- **T16 (best-chain length after drain is ≤ window).** With fuel
equal to `bestLen`, the finalisation drain leaves the non-finalized
best chain at most `MAX_BLOCK_REORG_HEIGHT` blocks long. This combines
T10 with the state-machine model. -/
theorem finalizeUntilWindow_bestLen_le_max (s : ChainState) :
    (finalizeUntilWindow s.bestLen s).bestLen ≤ MAX_BLOCK_REORG_HEIGHT := by
  -- The `finalizeUntilWindow` drain on `s.bestLen` proceeds identically
  -- to `popRootUntilWindow` on `s.bestLen` (the only thing the drain
  -- modifies on the bestLen-axis is `bestLen`); a direct induction
  -- gives the bound.
  suffices h : ∀ (n : Nat) (s : ChainState), n ≥ s.bestLen →
      (finalizeUntilWindow n s).bestLen ≤ MAX_BLOCK_REORG_HEIGHT by
    exact h s.bestLen s (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro s hFuel
    have : s.bestLen = 0 := Nat.le_zero.mp hFuel
    unfold finalizeUntilWindow
    rw [this]
    decide
  | succ k ih =>
    intro s hFuel
    unfold finalizeUntilWindow
    by_cases hFire : reorgWindowExceeded s.bestLen = true
    · rw [if_pos hFire]
      have hLen : s.bestLen > MAX_BLOCK_REORG_HEIGHT :=
        (reorgWindowExceeded_iff s.bestLen).mp hFire
      have hPos : s.bestLen ≥ 1 := by
        unfold MAX_BLOCK_REORG_HEIGHT at hLen
        omega
      apply ih
      simp
      omega
    · have hF : reorgWindowExceeded s.bestLen = false := by
        cases hbit : reorgWindowExceeded s.bestLen with
        | false => rfl
        | true => exact absurd hbit hFire
      rw [if_neg hFire]
      have hLen : ¬ s.bestLen > MAX_BLOCK_REORG_HEIGHT := by
        unfold reorgWindowExceeded at hF
        simp only [decide_eq_false_iff_not] at hF
        exact hF
      omega

/-! ### Invalidated-block queue bound -/

/-- **T17 (invalidated-block guard unfolds).** Defining iff for
`invalidatedCapExceeded`. -/
theorem invalidatedCapExceeded_iff (n : Nat) :
    invalidatedCapExceeded n = true ↔ n > MAX_INVALIDATED_BLOCKS := by
  unfold invalidatedCapExceeded
  simp

/-- **T18 (invalidated-queue post-condition).** With enough fuel, the
invalidated-block drain ends with the guard not firing. -/
theorem trimInvalidated_postcondition (n : Nat) :
    invalidatedCapExceeded (trimInvalidated n n) = false := by
  induction n with
  | zero => decide
  | succ k ih =>
    unfold trimInvalidated
    by_cases hFire : invalidatedCapExceeded (k + 1) = true
    · rw [if_pos hFire]
      exact ih
    · have hF : invalidatedCapExceeded (k + 1) = false := by
        cases hbit : invalidatedCapExceeded (k + 1) with
        | false => rfl
        | true => exact absurd hbit hFire
      rw [if_neg hFire]
      exact hF

/-- **T19 (invalidated-queue bound).** After the drain, the invalidated
record queue is at most `MAX_INVALIDATED_BLOCKS = 100`. -/
theorem trimInvalidated_le_max (n : Nat) :
    trimInvalidated n n ≤ MAX_INVALIDATED_BLOCKS := by
  have h := trimInvalidated_postcondition n
  unfold invalidatedCapExceeded at h
  simp only [decide_eq_false_iff_not, not_lt] at h
  exact h

end Zebra.StateNonFinalized
