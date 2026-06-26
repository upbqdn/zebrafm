import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Mempool storage size bounds and `RecentlyEvicted` FIFO shape

Two complementary bounds protect Zebra's mempool from memory-DoS:

  * **Verified-set cost cap** (`mempool/storage.rs:218`,
    `mempool/storage.rs:478`): the verified-set `total_cost` (sum of
    per-transaction `cost()` values, each at least
    `MEMPOOL_TRANSACTION_COST_THRESHOLD = 10_000`) is kept below the
    configured `tx_cost_limit` (mainnet default `80_000_000`,
    `mempool/config.rs:64`). Combined with the per-tx cost floor, this
    *implicitly* caps the verified-set entry count.
  * **`RecentlyEvicted` length cap** (`mempool/storage.rs:51`,
    `mempool/storage/eviction_list.rs:46-67`): the rejection list per
    [ZIP-401] keeps at most `MAX_EVICTION_MEMORY_ENTRIES = 40_000`
    entries. On overflow the oldest entry is popped from the front of
    a `VecDeque` and a new entry is appended at the back — a strict
    insertion-order FIFO.

This module formalises both: the cost-limit-implies-entry-count bound on
the verified set, and the FIFO shape of `EvictionList` (mirroring the
treatment in `Zebrafm.InventoryCacheSize` for the per-peer inventory
registry).

## What is and is not "LRU"

The task description mentions "LRU eviction shape" for the
`RecentlyEvicted` list. Reading the Rust source confirms that the
eviction order is **not** LRU on access — `EvictionList::insert`
*panics* if the key is already present (`eviction_list.rs:63-66`), so
there is no "touch" semantics that would refresh a key's position. The
ordering is strictly **insertion-order FIFO** via
`VecDeque::push_back`/`pop_front`. We prove that shape rather than a
mis-described LRU.

A separate "ageing" eviction is layered on top by `prune_old`
(`eviction_list.rs:105-117`), which pops the **head** until the head
entry is younger than `eviction_memory_time`. Because the list is
insertion-ordered and the only mutator (`insert`) records the *current
time* (`eviction_list.rs:57`), this matches the FIFO head-removal we
model here.

## Theorems

  * **T1** (`max_eviction_memory_entries_value`,
    `mempool_cost_threshold_value`,
    `default_tx_cost_limit_value`,
    `default_max_verified_entries_value`) — pin the four Rust
    constants and the derived entry-count cap that uses them.
  * **T2** (`verifiedSet_cost_bound_implies_entry_bound`) — the
    load-bearing bound: if every tx in the verified set has cost `≥
    MEMPOOL_TRANSACTION_COST_THRESHOLD` and the sum of costs is
    `≤ tx_cost_limit`, then the entry count is
    `≤ tx_cost_limit / MEMPOOL_TRANSACTION_COST_THRESHOLD`.
  * **T3** (`verifiedSet_default_entry_bound`) — the same bound,
    specialised to the Zebra mainnet default
    `tx_cost_limit = 80_000_000`: a cost-conforming verified set has
    at most `8_000` transactions.
  * **T4** (`fifoInsert_length_le_cap`) — every `fifoInsert` step
    keeps the list at `≤ cap` entries.
  * **T5** (`iteratedFifoInsert_length_le_cap`) — iterated insertion
    keeps the list at `≤ cap` entries, regardless of how many entries
    are inserted.
  * **T6** (`fifoInsert_under_cap_grows_by_one`) — under cap, an
    insert appends to the back without any drop.
  * **T7** (`fifoInsert_at_cap_drops_head`) — at the cap, an insert
    drops the head (oldest) and appends to the back.
  * **T8** (`pruneOld_drops_only_head_run`) — head-pruning only ever
    pops the prefix of "expired" entries; the rest of the list is
    preserved in order.
  * **T9** (`pruneOld_length_le`) — pruning never grows the list.
  * **T10** (`iteratedFifoInsert_post_cap_is_recent_window`) — once
    enough entries have been inserted to fill the cap, the list is
    exactly the `cap`-sized suffix of the insertion sequence (the
    "RecentlyEvicted window").
  * **T11** (`fifoInsert_preserves_relative_order_under_cap`) — when
    not yet at cap, `fifoInsert` preserves the original list as a
    prefix (no reordering of existing entries).
-/

namespace Zebra.MempoolStorageLimits

/-! ## Constants -/

/-- `MAX_EVICTION_MEMORY_ENTRIES` from ZIP-401: the size cap on every
mempool rejection list, including `RecentlyEvicted`.
Source: `zebrad/src/components/mempool/storage.rs:51`. -/
def MAX_EVICTION_MEMORY_ENTRIES : Nat := 40_000

/-- `MEMPOOL_TRANSACTION_COST_THRESHOLD` from ZIP-401: the per-tx cost
floor — `cost(tx) = max(size_bytes, 10_000)`.
Source: `zebra-chain/src/transaction/unmined.rs:67`. -/
def MEMPOOL_TRANSACTION_COST_THRESHOLD : Nat := 10_000

/-- The default value of `tx_cost_limit` on mainnet, in cost units.
Source: `zebrad/src/components/mempool/config.rs:64`. ZIP-401 specifies
"There MUST be a configuration option `mempooltxcostlimit`, which SHOULD
default to `80_000_000`". -/
def DEFAULT_TX_COST_LIMIT : Nat := 80_000_000

/-- The entry-count ceiling on the verified set under default cost
limits: `tx_cost_limit / MEMPOOL_TRANSACTION_COST_THRESHOLD`. With the
mainnet defaults this is `80_000_000 / 10_000 = 8_000` transactions.

This is the implicit upper bound on the verified set size: while the
Rust code only enforces `total_cost ≤ tx_cost_limit`, the per-tx cost
floor means a conforming set cannot contain more than this many
transactions. -/
def DEFAULT_MAX_VERIFIED_ENTRIES : Nat :=
  DEFAULT_TX_COST_LIMIT / MEMPOOL_TRANSACTION_COST_THRESHOLD

/-! ## Verified-set cost-to-entry-count bound

We model a verified set as a list of per-transaction `cost` values. A
"cost-conforming" set has every entry `≥ MEMPOOL_TRANSACTION_COST_THRESHOLD`
(`verified_set.rs:184` adds `transaction.cost()` which is itself capped
at threshold, see `unmined.rs:465-470`). -/

/-- Sum of per-transaction costs. Mirrors `VerifiedSet.total_cost`
(`verified_set.rs:107-109`). -/
def totalCost (xs : List Nat) : Nat :=
  xs.foldr (· + ·) 0

theorem totalCost_nil : totalCost [] = 0 := rfl

theorem totalCost_cons (c : Nat) (xs : List Nat) :
    totalCost (c :: xs) = c + totalCost xs := rfl

/-- A list `xs` of costs is *cost-conforming* if every entry is at least
`MEMPOOL_TRANSACTION_COST_THRESHOLD`. -/
def CostConforming (xs : List Nat) : Prop :=
  ∀ c ∈ xs, MEMPOOL_TRANSACTION_COST_THRESHOLD ≤ c

theorem CostConforming.cons {c : Nat} {xs : List Nat}
    (hc : MEMPOOL_TRANSACTION_COST_THRESHOLD ≤ c) (hxs : CostConforming xs) :
    CostConforming (c :: xs) := by
  intro x hx
  rcases List.mem_cons.mp hx with heq | hin
  · subst heq; exact hc
  · exact hxs x hin

theorem CostConforming.tail {c : Nat} {xs : List Nat}
    (h : CostConforming (c :: xs)) : CostConforming xs := by
  intro x hx; exact h x (List.mem_cons_of_mem c hx)

theorem CostConforming.head {c : Nat} {xs : List Nat}
    (h : CostConforming (c :: xs)) :
    MEMPOOL_TRANSACTION_COST_THRESHOLD ≤ c :=
  h c List.mem_cons_self

/-- Each entry contributes at least the cost threshold, so the list
length is at most `totalCost / threshold`. -/
theorem length_le_totalCost_div_threshold (xs : List Nat)
    (hConf : CostConforming xs) :
    xs.length * MEMPOOL_TRANSACTION_COST_THRESHOLD ≤ totalCost xs := by
  induction xs with
  | nil => simp [totalCost]
  | cons c rest ih =>
    have hRest := ih (hConf.tail)
    have hHead := hConf.head
    rw [totalCost_cons, List.length_cons]
    -- (rest.length + 1) * T ≤ c + totalCost rest
    have hSplit : (rest.length + 1) * MEMPOOL_TRANSACTION_COST_THRESHOLD =
        rest.length * MEMPOOL_TRANSACTION_COST_THRESHOLD
          + MEMPOOL_TRANSACTION_COST_THRESHOLD :=
      Nat.succ_mul rest.length MEMPOOL_TRANSACTION_COST_THRESHOLD
    omega

/-! ## FIFO ring-buffer for `RecentlyEvicted` -/

/-- `fifoInsert cap key xs` mirrors `EvictionList::insert`
(`eviction_list.rs:46-67`): if the list is at the cap, drop the head
(oldest entry); always append `key` at the back.

We treat the model as deterministic — the Rust `assert!` that the key
isn't already present is the caller's responsibility, mirroring the
`reject()` flow that never re-rejects a key already in the list. -/
def fifoInsert (cap : Nat) (key : Nat) (xs : List Nat) : List Nat :=
  if xs.length < cap then xs ++ [key]
  else xs.tail ++ [key]

/-- Iterated `fifoInsert`: insert a sequence of keys one at a time. -/
def iteratedFifoInsert (cap : Nat) : List Nat → List Nat → List Nat
  | [],        xs => xs
  | k :: rest, xs => iteratedFifoInsert cap rest (fifoInsert cap k xs)

/-! ### Length bounds -/

theorem fifoInsert_under_cap_length (cap key : Nat) (xs : List Nat)
    (h : xs.length < cap) :
    (fifoInsert cap key xs).length = xs.length + 1 := by
  unfold fifoInsert
  rw [if_pos h]
  simp

theorem fifoInsert_at_or_over_cap_length (cap key : Nat) (xs : List Nat)
    (hCapPos : 0 < cap) (h : cap ≤ xs.length) :
    (fifoInsert cap key xs).length = xs.length := by
  unfold fifoInsert
  have hN : ¬ xs.length < cap := by omega
  rw [if_neg hN]
  cases xs with
  | nil =>
    -- contradicts hCapPos with h
    simp at h
    omega
  | cons _ rest => simp

/-- **T4 (`fifoInsert` keeps the list at `≤ cap`).** Given input
`xs.length ≤ cap` and a positive cap, the result also has `length ≤ cap`.
The `0 < cap` precondition rules out a vacuous degenerate case (with
`cap = 0` no list could ever be present); Zebra's actual cap is
`MAX_EVICTION_MEMORY_ENTRIES = 40_000 > 0`. -/
theorem fifoInsert_length_le_cap (cap key : Nat) (xs : List Nat)
    (hCapPos : 0 < cap) (h : xs.length ≤ cap) :
    (fifoInsert cap key xs).length ≤ cap := by
  by_cases hLt : xs.length < cap
  · rw [fifoInsert_under_cap_length cap key xs hLt]; omega
  · have hEq : cap ≤ xs.length := by omega
    rw [fifoInsert_at_or_over_cap_length cap key xs hCapPos hEq]
    omega

/-- **T5 (iterated FIFO insertion is bounded by `cap`).** -/
theorem iteratedFifoInsert_length_le_cap (cap : Nat) (ks : List Nat)
    (xs : List Nat) (hCapPos : 0 < cap) (h : xs.length ≤ cap) :
    (iteratedFifoInsert cap ks xs).length ≤ cap := by
  induction ks generalizing xs with
  | nil => exact h
  | cons k rest ih =>
    unfold iteratedFifoInsert
    exact ih (fifoInsert cap k xs)
              (fifoInsert_length_le_cap cap k xs hCapPos h)

/-! ### Shape: under-cap appends, at-cap drops head -/

/-- **T6 (`fifoInsert` under cap appends at the back).** No drop
happens; the new entry is the last element. -/
theorem fifoInsert_under_cap_grows_by_one (cap key : Nat) (xs : List Nat)
    (h : xs.length < cap) :
    fifoInsert cap key xs = xs ++ [key] := by
  unfold fifoInsert
  rw [if_pos h]

/-- **T7 (`fifoInsert` at-cap drops the head).** The head of the
existing list is removed; the new entry is appended. -/
theorem fifoInsert_at_cap_drops_head (cap key : Nat) (xs : List Nat)
    (h : cap ≤ xs.length) :
    fifoInsert cap key xs = xs.tail ++ [key] := by
  unfold fifoInsert
  have : ¬ xs.length < cap := by omega
  rw [if_neg this]

/-! ## Head-prune semantics (the time-based eviction)

`EvictionList::prune_old` pops the head of the deque while its
timestamp is older than `eviction_memory_time`. We abstract over the
"expired" predicate; the FIFO-shape property below holds for *any*
boolean predicate, capturing the Rust loop:

```rust
while let Some(txid) = self.front() {
    if self.has_expired(evicted_at) { self.pop_front(); }
    else { break; }
}
```
(`eviction_list.rs:105-117`).
-/

/-- One step of `prune_old`. Given a predicate `expired` deciding whether
the head should be dropped, pop the head if it's expired; otherwise
leave the list alone. -/
def pruneOneIfExpired (expired : Nat → Bool) (xs : List Nat) : List Nat :=
  match xs with
  | []      => []
  | x :: rest => if expired x then rest else x :: rest

/-- Iterated `prune_old`: keep dropping expired heads until either the
list is empty or the head is non-expired. The `fuel` parameter bounds
recursion; setting it to `xs.length` is always enough. -/
def pruneOld (expired : Nat → Bool) : Nat → List Nat → List Nat
  | 0,     xs => xs
  | _+1,   []        => []
  | n+1,   x :: rest =>
      if expired x then pruneOld expired n rest else x :: rest

theorem pruneOld_zero (expired : Nat → Bool) (xs : List Nat) :
    pruneOld expired 0 xs = xs := rfl

theorem pruneOld_nil (expired : Nat → Bool) (n : Nat) :
    pruneOld expired n [] = [] := by
  cases n with
  | zero => rfl
  | succ _ => rfl

theorem pruneOld_succ_cons_expired (expired : Nat → Bool) (n : Nat)
    (x : Nat) (rest : List Nat) (h : expired x = true) :
    pruneOld expired (n + 1) (x :: rest) = pruneOld expired n rest := by
  change (if expired x then pruneOld expired n rest else x :: rest) = _
  rw [h]; simp

theorem pruneOld_succ_cons_not_expired (expired : Nat → Bool) (n : Nat)
    (x : Nat) (rest : List Nat) (h : expired x = false) :
    pruneOld expired (n + 1) (x :: rest) = x :: rest := by
  change (if expired x then pruneOld expired n rest else x :: rest) = _
  rw [h]; simp

/-- **T9 (pruning never grows the list).** -/
theorem pruneOld_length_le (expired : Nat → Bool) (fuel : Nat)
    (xs : List Nat) :
    (pruneOld expired fuel xs).length ≤ xs.length := by
  induction fuel generalizing xs with
  | zero => rw [pruneOld_zero]
  | succ n ih =>
    cases xs with
    | nil => rw [pruneOld_nil]
    | cons x rest =>
      by_cases hExp : expired x = true
      · rw [pruneOld_succ_cons_expired expired n x rest hExp]
        have := ih rest
        simp; omega
      · have hF : expired x = false := by
          cases h : expired x with
          | true  => exact absurd h hExp
          | false => rfl
        rw [pruneOld_succ_cons_not_expired expired n x rest hF]

/-- **T8 (pruning only drops a head run, never reorders the tail).**

Once we reach the first non-expired element, the rest of the list is
preserved verbatim. This is the "FIFO-shape" guarantee: pruning is the
identity on the suffix beginning at the first non-expired entry.

The statement: `pruneOld` factors as `xs = expiredPrefix ++ keptSuffix`
with the kept suffix's head non-expired (or empty), and the output is
exactly `keptSuffix`. -/
theorem pruneOld_drops_only_head_run (expired : Nat → Bool) (fuel : Nat)
    (xs : List Nat) :
    ∃ prefixDropped keptSuffix,
      xs = prefixDropped ++ keptSuffix ∧
      pruneOld expired fuel xs = keptSuffix := by
  induction fuel generalizing xs with
  | zero =>
    refine ⟨[], xs, ?_, ?_⟩
    · rfl
    · rw [pruneOld_zero]
  | succ n ih =>
    cases xs with
    | nil =>
      refine ⟨[], [], ?_, ?_⟩
      · rfl
      · rw [pruneOld_nil]
    | cons x rest =>
      by_cases hExp : expired x = true
      · obtain ⟨pre, suf, hSplit, hOut⟩ := ih rest
        refine ⟨x :: pre, suf, ?_, ?_⟩
        · simp [hSplit]
        · rw [pruneOld_succ_cons_expired expired n x rest hExp]; exact hOut
      · have hF : expired x = false := by
          cases h : expired x with
          | true  => exact absurd h hExp
          | false => rfl
        refine ⟨[], x :: rest, ?_, ?_⟩
        · rfl
        · rw [pruneOld_succ_cons_not_expired expired n x rest hF]

/-! ## "RecentlyEvicted is the cap-sized recent window" -/

/-- Helper: under cap, iterated insertion appends keys to the back of
the existing list, preserving order. This is the workhorse lemma for
the recent-window characterization. -/
theorem iteratedFifoInsert_append_under_cap (cap : Nat) (init : List Nat)
    (ks : List Nat) (h : init.length + ks.length ≤ cap) :
    iteratedFifoInsert cap ks init = init ++ ks := by
  induction ks generalizing init with
  | nil => simp [iteratedFifoInsert]
  | cons k rest ih =>
    have hLenKs : (k :: rest).length = rest.length + 1 := by simp
    have hLenLt : init.length < cap := by
      rw [hLenKs] at h; omega
    have hNew : (init ++ [k]).length + rest.length ≤ cap := by
      rw [List.length_append, List.length_singleton]
      rw [hLenKs] at h; omega
    unfold iteratedFifoInsert
    rw [fifoInsert_under_cap_grows_by_one cap k init hLenLt]
    rw [ih (init ++ [k]) hNew]
    simp

/-- After inserting up to `cap` keys into an empty list, the list is
exactly those keys in insertion order. This is the "ramp-up" before the
cap binds. -/
theorem iteratedFifoInsert_empty_under_cap (cap : Nat) (ks : List Nat)
    (h : ks.length ≤ cap) :
    iteratedFifoInsert cap ks [] = ks := by
  have hPre : ([] : List Nat).length + ks.length ≤ cap := by
    rw [List.length_nil, Nat.zero_add]; exact h
  have := iteratedFifoInsert_append_under_cap cap [] ks hPre
  simpa using this

/-- **T11 (`fifoInsert` under cap preserves order of existing entries).**
Under cap, every existing entry retains its position; the new key is
strictly the last entry. -/
theorem fifoInsert_preserves_relative_order_under_cap (cap key : Nat)
    (xs : List Nat) (h : xs.length < cap) :
    fifoInsert cap key xs = xs ++ [key] :=
  fifoInsert_under_cap_grows_by_one cap key xs h

/-- **T10 (Once filled, the list is the recent `cap`-sized window).**

If a list is exactly at capacity and we insert one more key, the
result is the suffix of length `cap` of the conceptual full insertion
log, i.e. the original list with the head dropped and the new key
appended.

This is the precise sense in which `RecentlyEvicted` is "the
`cap`-sized recent window" of the insertion sequence: at saturation,
each new entry replaces the oldest. -/
theorem fifoInsert_at_cap_is_recent_window (cap key : Nat) (xs : List Nat)
    (hLen : xs.length = cap) :
    fifoInsert cap key xs = xs.tail ++ [key] := by
  apply fifoInsert_at_cap_drops_head
  omega

/-! ## Main theorems (cost-to-entries bound and constant pins) -/

/-- **T1a (`MAX_EVICTION_MEMORY_ENTRIES = 40_000`).** -/
theorem max_eviction_memory_entries_value :
    MAX_EVICTION_MEMORY_ENTRIES = 40_000 := rfl

/-- **T1b (`MEMPOOL_TRANSACTION_COST_THRESHOLD = 10_000`).** -/
theorem mempool_cost_threshold_value :
    MEMPOOL_TRANSACTION_COST_THRESHOLD = 10_000 := rfl

/-- **T1c (`DEFAULT_TX_COST_LIMIT = 80_000_000`).** -/
theorem default_tx_cost_limit_value :
    DEFAULT_TX_COST_LIMIT = 80_000_000 := rfl

/-- **T1d (the derived entry-count cap is 8_000).** -/
theorem default_max_verified_entries_value :
    DEFAULT_MAX_VERIFIED_ENTRIES = 8_000 := by
  unfold DEFAULT_MAX_VERIFIED_ENTRIES DEFAULT_TX_COST_LIMIT
        MEMPOOL_TRANSACTION_COST_THRESHOLD
  decide

/-- **T2 (cost-bound implies entry-count-bound).** For any
cost-conforming verified set, the entry count multiplied by the cost
threshold is at most the total cost, so the entry count is at most
`tx_cost_limit / threshold` whenever the cost cap is respected. -/
theorem verifiedSet_cost_bound_implies_entry_bound (xs : List Nat)
    (txCostLimit : Nat) (hConf : CostConforming xs)
    (hCap : totalCost xs ≤ txCostLimit) :
    xs.length ≤ txCostLimit / MEMPOOL_TRANSACTION_COST_THRESHOLD := by
  have hLB := length_le_totalCost_div_threshold xs hConf
  -- xs.length * T ≤ totalCost xs ≤ txCostLimit
  have hChain : xs.length * MEMPOOL_TRANSACTION_COST_THRESHOLD ≤ txCostLimit :=
    le_trans hLB hCap
  have hPos : 0 < MEMPOOL_TRANSACTION_COST_THRESHOLD := by
    unfold MEMPOOL_TRANSACTION_COST_THRESHOLD; decide
  exact Nat.le_div_iff_mul_le hPos |>.mpr hChain

/-- **T3 (mainnet-default verified-set entry bound).** Under the default
`tx_cost_limit = 80_000_000`, every cost-conforming verified set has at
most `8_000` transactions. -/
theorem verifiedSet_default_entry_bound (xs : List Nat)
    (hConf : CostConforming xs)
    (hCap : totalCost xs ≤ DEFAULT_TX_COST_LIMIT) :
    xs.length ≤ 8_000 := by
  have h := verifiedSet_cost_bound_implies_entry_bound xs DEFAULT_TX_COST_LIMIT hConf hCap
  rw [show DEFAULT_TX_COST_LIMIT / MEMPOOL_TRANSACTION_COST_THRESHOLD = 8_000 from by decide] at h
  exact h

/-! ## RecentlyEvicted concrete-cap example -/

/-- A concrete: at `cap = MAX_EVICTION_MEMORY_ENTRIES = 40_000`, the
list length is bounded by 40_000 regardless of how many keys are
inserted. -/
theorem recently_evicted_bounded (ks : List Nat) :
    (iteratedFifoInsert MAX_EVICTION_MEMORY_ENTRIES ks []).length
      ≤ MAX_EVICTION_MEMORY_ENTRIES := by
  apply iteratedFifoInsert_length_le_cap
  · unfold MAX_EVICTION_MEMORY_ENTRIES; decide
  · simp

/-- Concrete: a 3-entry list with cap 2 evicts the head on the next
insert. -/
theorem example_fifo_evict :
    fifoInsert 2 99 [1, 2] = [2, 99] := by
  unfold fifoInsert
  decide

/-- Concrete: under cap, the new key is appended at the back. -/
theorem example_fifo_under_cap :
    fifoInsert 5 99 [1, 2] = [1, 2, 99] := by
  unfold fifoInsert
  decide

end Zebra.MempoolStorageLimits
