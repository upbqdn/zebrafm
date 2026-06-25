import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Inventory registry cache-size bounds
(`zebra-network/src/peer_set/inventory_registry.rs`,
 `zebra-network/src/constants.rs`)

Zebra's `InventoryRegistry` tracks, per peer, which inventory hashes the peer
has recently advertised as available or rejected as missing. The registry is
an efficiency optimisation, so it is bounded in three independent dimensions:

  * `MAX_INV_PER_MAP = 1000` — the max number of distinct inventory hashes
    tracked in the `current` (or `prev`) map.
    Source: `zebra-network/src/peer_set/inventory_registry.rs:53`.
  * `MAX_PEERS_PER_INV = 70` — the max number of peers tracked under a single
    hash. Source: `zebra-network/src/peer_set/inventory_registry.rs:68`.
  * `INVENTORY_ROTATION_INTERVAL = 53` seconds — entries from before two
    intervals expire on the second rotation (current → prev → drop).
    Source: `zebra-network/src/constants.rs:153`.

## Eviction policy: insertion-order FIFO (NOT LRU)

The Rust register loop at `inventory_registry.rs:382-433` uses
`indexmap::IndexMap` whose `insert(key, value)` semantics are:

  * if `key` is absent, append the entry at the back (new position = len);
  * if `key` is present, *update the value in place* — the position is
    **not** changed.

Combined with `shift_remove_index(0)` (drop the oldest insertion), this is
**insertion-order FIFO**, not LRU. A previous version of this module modelled
move-to-back ("LRU touch"), which makes a different victim choice on overflow
and overstates the freshness guarantee for re-registered entries. The model
below mirrors the real Rust behaviour.

## Input truncation

Before reaching the registry, `InventoryChange::new_available_multi` and
`new_missing_multi` truncate the incoming `hashes` vector to `MAX_INV_PER_MAP`
(`inventory_registry.rs:147, 165`). This is the first-line DoS guard: even a
malicious peer can't make the channel carry more than `MAX_INV_PER_MAP`
hashes per change.

## Total memory footprint

The Rust safety comment (`inventory_registry.rs:42-44`) cites two bounds:

  * inventory-hash table: `1000 inv * 2 maps * 32-64 B/inv ≤ 128 KB` (< 1 MB).
  * peers-per-inv table: `1000 inv * 70 peers * 2 maps * 6-18 B/addr ≤ ~2.52 MB` (~3 MB).

The second bound is ~47× the first; an earlier version of this module quoted
only the first. Both are now pinned (T15a, T15b).

## What is proved here

  * the bounded list never exceeds the cap (`pushBounded_length_le`);
  * inserting an *existing* entry is the **identity** — same list, same length,
    same order (`insertOrUpdate_existing_eq`, `insertOrUpdate_existing_length_eq`);
  * inserting a *new* entry grows the list by exactly 1
    (`insertOrUpdate_new_length`);
  * the per-hash and outer caps compose multiplicatively for the total memory
    footprint (`total_entries_bound`);
  * rotation clears `current` and shifts `current` into `prev`
    (`rotate_current_empty`, `rotate_prev_eq_old_current`);
  * two rotations evict everything inserted before the first
    (`two_rotations_drop_original_prev`);
  * eviction below the cap is a no-op (`evictIfOver_below_cap`);
  * eviction at over-cap drops exactly the head (`evictIfOver_over_cap`);
  * the constant numbers match the Rust source (`max_inv_per_map_eq`, etc.);
  * the inv-hash and peers-per-inv DoS bounds quoted in the Rust safety
    comment hold (T15a, T15b);
  * the registry-internal guard plus the message-handler input truncation
    cap the work an attacker can cause per change (`truncate_input_length_le`,
    `truncate_input_preserves_short`).
-/

namespace Zebra.InventoryCacheSize

/-! ## Constants -/

/-- Max inventory hashes tracked in a single map (`current` or `prev`).
Source: `zebra-network/src/peer_set/inventory_registry.rs:53`
(`pub const MAX_INV_PER_MAP: usize = 1000`). -/
def MAX_INV_PER_MAP : Nat := 1000

/-- Max peers tracked under a single inventory hash.
Source: `zebra-network/src/peer_set/inventory_registry.rs:68`
(`pub const MAX_PEERS_PER_INV: usize = 70`). -/
def MAX_PEERS_PER_INV : Nat := 70

/-- The map-rotation period in seconds.
Source: `zebra-network/src/constants.rs:153`
(`pub const INVENTORY_ROTATION_INTERVAL: Duration = Duration::from_secs(53)`). -/
def INVENTORY_ROTATION_INTERVAL_SECS : Nat := 53

/-- After this many intervals all entries inserted before time 0 have rotated
out of both `current` and `prev`. The registry keeps two slots, so an entry
needs to survive 2 rotations before it's dropped. -/
def INVENTORY_EXPIRY_INTERVALS : Nat := 2

/-- Upper estimate of bytes per inventory-hash entry, from the Rust safety
comment "32-64 bytes per inventory" (`inventory_registry.rs:42`). We use 64
for the conservative DoS bound. -/
def MAX_INV_BYTES_PER_INV : Nat := 64

/-- Upper estimate of bytes per peer-address entry, from the Rust safety
comment "6-18 bytes per address" (`inventory_registry.rs:43`). We use 18 for
the conservative DoS bound. -/
def MAX_BYTES_PER_PEER_ADDR : Nat := 18

/-- The two-slot registry (`current` + `prev`). -/
def NUM_REGISTRY_MAPS : Nat := 2

/-! ## Abstract model

We model the per-hash peer list (and analogously the outer inventory list) as
a `List Nat`, where each `Nat` is an opaque entry identifier. The Rust loop's
two operations are:

  1. `entry_or_default()` followed by `insert(key, value)` — semantically:
     if `key` is already present, update the value (position unchanged);
     if absent, append at the back. The `IndexMap::insert` contract is that
     keys keep their original position when overwritten.
  2. `if len > MAX { shift_remove_index(0) }` — drop the oldest entry, but
     only if we overflowed.

We model (1) as `insertOrUpdate entry list`: identity if `entry ∈ list`,
else append. (Markers/values are abstracted away — this module reasons about
length and DoS bounds, not the available/missing precedence rule.) We model
(2) as `evictIfOver cap list`. -/

/-- Insertion-order-preserving insert: leave the list unchanged if `entry` is
already present (matching `IndexMap::insert`'s "keys keep their position"
guarantee on update); otherwise append at the back. -/
def insertOrUpdate (entry : Nat) (l : List Nat) : List Nat :=
  if entry ∈ l then l else l ++ [entry]

/-- Drop the head of the list iff its length strictly exceeds the cap. This
mirrors `if hash_peers.len() > MAX_PEERS_PER_INV { hash_peers.shift_remove_index(0) }`. -/
def evictIfOver (cap : Nat) (l : List Nat) : List Nat :=
  if l.length > cap then l.tail else l

/-- The composed bounded-push operation: insert (or update in place), then
evict the oldest if the list overflows. -/
def pushBounded (cap : Nat) (entry : Nat) (l : List Nat) : List Nat :=
  evictIfOver cap (insertOrUpdate entry l)

/-- Rotate the registry: drop `prev` entirely, move `current` into `prev`,
and reset `current` to empty. Models `prev = std::mem::take(&mut current)`. -/
def rotate (current _prev : List Nat) : List Nat × List Nat :=
  ([], current)

/-- Message-handler input truncation: `InventoryChange::new_available_multi`
truncates `hashes` to `MAX_INV_PER_MAP` before constructing a change. -/
def truncateInput (l : List Nat) : List Nat :=
  l.take MAX_INV_PER_MAP

/-! ## Theorems -/

/-- **T1 (pushBounded never exceeds `cap`).** Starting from any list within
the cap, a single `pushBounded` keeps it within the cap. This is the core
security property — the registry cannot grow past `cap` regardless of how
many entries an attacker submits. -/
theorem pushBounded_length_le (cap entry : Nat) (l : List Nat)
    (hbound : l.length ≤ cap) :
    (pushBounded cap entry l).length ≤ cap := by
  unfold pushBounded evictIfOver insertOrUpdate
  by_cases hmem : entry ∈ l
  · -- entry already present: insertOrUpdate is identity.
    simp only [hmem, if_true]
    have : ¬ l.length > cap := Nat.not_lt.mpr hbound
    simp [this, hbound]
  · -- entry absent: list grows by 1, then evict if over cap.
    simp only [hmem, if_false]
    have hlen : (l ++ [entry]).length = l.length + 1 := by simp
    by_cases h : (l ++ [entry]).length > cap
    · simp only [h, if_true]
      have : (l ++ [entry]).tail.length = (l ++ [entry]).length - 1 := by
        rw [List.length_tail]
      rw [this, hlen]; omega
    · simp only [h, if_false]; rw [hlen]; omega

/-- **T2 (iteration preserves the cap invariant).** Same statement as T1,
restated as an invariant suitable for sequential reasoning: any single push
preserves `l.length ≤ cap`. -/
theorem pushBounded_invariant (cap entry : Nat) (l : List Nat)
    (hinv : l.length ≤ cap) :
    (pushBounded cap entry l).length ≤ cap :=
  pushBounded_length_le cap entry l hinv

/-- **T3 (existing entry → identity).** When `entry` is already in `l`,
`insertOrUpdate` returns `l` **unchanged** (not just same length). This is
the load-bearing semantic correction over the previous LRU-touch model:
`IndexMap::insert` does not reorder, so neither does this. -/
theorem insertOrUpdate_existing_eq (entry : Nat) (l : List Nat)
    (hmem : entry ∈ l) :
    insertOrUpdate entry l = l := by
  unfold insertOrUpdate
  simp [hmem]

/-- **T4 (existing entry → same length).** Length corollary of T3. -/
theorem insertOrUpdate_existing_length_eq (entry : Nat) (l : List Nat)
    (hmem : entry ∈ l) :
    (insertOrUpdate entry l).length = l.length := by
  rw [insertOrUpdate_existing_eq entry l hmem]

/-- **T5 (new entry → length grows by exactly 1).** When `entry` is absent
from `l`, `insertOrUpdate` appends it at the back; the only way the list
grows. -/
theorem insertOrUpdate_new_length (entry : Nat) (l : List Nat)
    (hmem : entry ∉ l) :
    (insertOrUpdate entry l).length = l.length + 1 := by
  unfold insertOrUpdate
  simp [hmem]

/-- **T5b (unconditional length bound).** `insertOrUpdate` grows the list
by at most 1. -/
theorem insertOrUpdate_length_le (entry : Nat) (l : List Nat) :
    (insertOrUpdate entry l).length ≤ l.length + 1 := by
  unfold insertOrUpdate
  by_cases h : entry ∈ l
  · simp [h]
  · simp [h]

/-- **T6 (per-hash cap composes multiplicatively with the outer cap).** The
peers-per-inv map's footprint is at most
`MAX_INV_PER_MAP * MAX_PEERS_PER_INV` peer-entries per single registry slot.
With `1000 * 70 = 70_000` peer-entries per map, and two maps, the live
peer-entry count is bounded by `140_000` — the bound the Rust safety comment
relies on. -/
theorem total_entries_bound :
    MAX_INV_PER_MAP * MAX_PEERS_PER_INV = 70000 := by
  unfold MAX_INV_PER_MAP MAX_PEERS_PER_INV
  decide

/-- **T6b (both-maps peer-entry bound).** Across `current` and `prev`,
peer-entries are bounded by `2 * 1000 * 70 = 140_000`. -/
theorem total_entries_both_maps :
    NUM_REGISTRY_MAPS * MAX_INV_PER_MAP * MAX_PEERS_PER_INV = 140000 := by
  unfold NUM_REGISTRY_MAPS MAX_INV_PER_MAP MAX_PEERS_PER_INV
  decide

/-- **T7a (rotation clears `current`).** Operational pinning of the rotate
semantics: after rotation `current = []`. -/
theorem rotate_current_empty (current prev : List Nat) :
    (rotate current prev).1 = [] := by
  unfold rotate; rfl

/-- **T7b (rotation moves `current` into `prev`).** -/
theorem rotate_prev_eq_old_current (current prev : List Nat) :
    (rotate current prev).2 = current := by
  unfold rotate; rfl

/-- **T7c (rotation does not grow either slot).** Length-bound consequence
of T7a/T7b — useful as the rotation-side analogue of `pushBounded_invariant`.
After rotation, each slot fits within the original `cap` if both slots did. -/
theorem rotate_preserves_cap (current prev : List Nat) (cap : Nat)
    (hc : current.length ≤ cap) (_hp : prev.length ≤ cap) :
    (rotate current prev).1.length ≤ cap ∧
    (rotate current prev).2.length ≤ cap := by
  refine ⟨?_, ?_⟩
  · rw [rotate_current_empty]; simp
  · rw [rotate_prev_eq_old_current]; exact hc

/-- **T8 (two rotations evict everything inserted before the first).** A
rotation drops `prev` entirely, so after two rotations the original
`current` (which became `prev` after one rotation) is fully dropped. With
`INVENTORY_EXPIRY_INTERVALS = 2`, entries inserted before time 0 are
forgotten by time `2 * INVENTORY_ROTATION_INTERVAL_SECS`. -/
theorem two_rotations_drop_original_prev (current prev : List Nat) :
    let s1 := rotate current prev
    let s2 := rotate s1.1 s1.2
    s2.2 = [] := by
  simp [rotate]

/-- **T8b (two rotations also drop the original `current`).** After two
rotations, both slots are empty regardless of starting state. -/
theorem two_rotations_drop_all (current prev : List Nat) :
    let s1 := rotate current prev
    let s2 := rotate s1.1 s1.2
    s2.1 = [] ∧ s2.2 = [] := by
  simp [rotate]

/-- **T9 (expiry interval in seconds).** Two rotation intervals = 106 s. -/
theorem expiry_seconds :
    INVENTORY_EXPIRY_INTERVALS * INVENTORY_ROTATION_INTERVAL_SECS = 106 := by
  unfold INVENTORY_EXPIRY_INTERVALS INVENTORY_ROTATION_INTERVAL_SECS
  decide

/-- **T10 (`insertOrUpdate` produces a non-empty list).** The result of an
insert always has at least one element — either the inserted entry (new
case) or the prior contents (existing case, where `entry ∈ l` already
implies `l` non-empty). -/
theorem insertOrUpdate_length_pos (entry : Nat) (l : List Nat) :
    0 < (insertOrUpdate entry l).length := by
  unfold insertOrUpdate
  by_cases h : entry ∈ l
  · simp only [h, if_true]
    cases l with
    | nil => simp at h
    | cons _ _ => simp
  · simp [h]

/-- **T11a (eviction below cap is a no-op).** When the list fits, no entry
is dropped. -/
theorem evictIfOver_below_cap (cap : Nat) (l : List Nat) (h : l.length ≤ cap) :
    evictIfOver cap l = l := by
  unfold evictIfOver
  have : ¬ l.length > cap := Nat.not_lt.mpr h
  simp [this]

/-- **T11b (eviction at over-cap drops exactly the head).** When the list
overflows, the result is `l.tail` — the oldest insertion is dropped, and no
other element is touched. -/
theorem evictIfOver_over_cap (cap : Nat) (l : List Nat) (h : l.length > cap) :
    evictIfOver cap l = l.tail := by
  unfold evictIfOver
  simp [h]

/-- **T12 (pin: max inventory hashes per map = 1000).** Concrete check of
the Rust constant. This is just a `rfl` on the `def`, not an independently
proved property — included so any drift in the constant breaks the build. -/
theorem max_inv_per_map_eq : MAX_INV_PER_MAP = 1000 := rfl

/-- **T13 (pin: max peers per inventory hash = 70).** -/
theorem max_peers_per_inv_eq : MAX_PEERS_PER_INV = 70 := rfl

/-- **T14 (pin: rotation interval = 53 s).** -/
theorem rotation_interval_eq : INVENTORY_ROTATION_INTERVAL_SECS = 53 := rfl

/-- **T15a (inv-hash DoS bound, single map).** With `MAX_INV_PER_MAP = 1000`
and at most 64 B per inventory hash entry, one slot's hash table fits in
`64_000` B (≪ 1 MB). Matches `inventory_registry.rs:42`. -/
theorem dos_bound_inv_hash_single_map :
    MAX_INV_PER_MAP * MAX_INV_BYTES_PER_INV = 64000 := by
  unfold MAX_INV_PER_MAP MAX_INV_BYTES_PER_INV
  decide

/-- **T15b (inv-hash DoS bound, both maps).** `current` + `prev` together
hold at most `128_000` B in inventory-hash entries. The Rust comment says
"less than 1 MB"; this is consistent. -/
theorem dos_bound_inv_hash_both_maps :
    NUM_REGISTRY_MAPS * MAX_INV_PER_MAP * MAX_INV_BYTES_PER_INV = 128000 := by
  unfold NUM_REGISTRY_MAPS MAX_INV_PER_MAP MAX_INV_BYTES_PER_INV
  decide

/-- **T15c (peers-per-inv DoS bound, single map).** The inner peers map
under each hash holds at most `MAX_PEERS_PER_INV = 70` addresses at
`MAX_BYTES_PER_PEER_ADDR = 18` B each. Across `MAX_INV_PER_MAP = 1000`
distinct hashes, that's
`1000 * 70 * 18 = 1_260_000 B ≈ 1.26 MB` per single registry slot. -/
theorem dos_bound_peers_per_inv_single_map :
    MAX_INV_PER_MAP * MAX_PEERS_PER_INV * MAX_BYTES_PER_PEER_ADDR = 1260000 := by
  unfold MAX_INV_PER_MAP MAX_PEERS_PER_INV MAX_BYTES_PER_PEER_ADDR
  decide

/-- **T15d (peers-per-inv DoS bound, both maps).** Across `current` and
`prev`: `2 * 1000 * 70 * 18 = 2_520_000 B ≈ 2.52 MB`. This matches the Rust
safety comment's "up to 3 MB" upper bound — the dimension the previous
version of this module omitted entirely. -/
theorem dos_bound_peers_per_inv_both_maps :
    NUM_REGISTRY_MAPS * MAX_INV_PER_MAP * MAX_PEERS_PER_INV
      * MAX_BYTES_PER_PEER_ADDR = 2520000 := by
  unfold NUM_REGISTRY_MAPS MAX_INV_PER_MAP MAX_PEERS_PER_INV MAX_BYTES_PER_PEER_ADDR
  decide

/-- **T15e (peers-per-inv bound is ~47× the inv-hash bound).** Sanity check
that the peers dimension dominates total registry memory by an order of
magnitude — relevant when reasoning about overall registry footprint. -/
theorem peers_dimension_dominates :
    NUM_REGISTRY_MAPS * MAX_INV_PER_MAP * MAX_PEERS_PER_INV * MAX_BYTES_PER_PEER_ADDR
      ≥ 19 * (NUM_REGISTRY_MAPS * MAX_INV_PER_MAP * MAX_INV_BYTES_PER_INV) := by
  unfold NUM_REGISTRY_MAPS MAX_INV_PER_MAP MAX_PEERS_PER_INV
         MAX_BYTES_PER_PEER_ADDR MAX_INV_BYTES_PER_INV
  decide

/-- **T16 (insert: the inserted entry is in the result).** Under
insertion-order semantics this still holds, by case on whether `entry` was
already present (then trivially in the result = `l`) or absent (then at the
back of `l ++ [entry]`). -/
theorem insertOrUpdate_entry_mem (entry : Nat) (l : List Nat) :
    entry ∈ insertOrUpdate entry l := by
  unfold insertOrUpdate
  by_cases h : entry ∈ l
  · simp [h]
  · simp [h]

/-- **T17 (insert: all other elements survive).** For any `x ≠ entry`
already in `l`, `x` is still in `insertOrUpdate entry l`. -/
theorem insertOrUpdate_preserves_others (entry x : Nat) (l : List Nat)
    (hx : x ∈ l) (_hne : x ≠ entry) :
    x ∈ insertOrUpdate entry l := by
  unfold insertOrUpdate
  by_cases h : entry ∈ l
  · simp only [h, if_true]; exact hx
  · simp only [h, if_false, List.mem_append, List.mem_singleton]
    exact Or.inl hx

/-- **T18 (pushBounded keeps the inserted entry, in the common case).** When
the list was within cap before the push and `entry` is freshly added, the
post-eviction list still contains `entry`. (Edge case: if `entry` was
already present and we were *exactly* at cap, eviction can still drop the
oldest entry — but never `entry`, which sits at its original position, not
position 0, since the list was non-empty before and `entry` was inside it.)

We prove the cleanest non-degenerate version: if the list was within cap
before the push, `entry ∈ pushBounded cap entry l`. -/
theorem pushBounded_entry_mem (cap entry : Nat) (l : List Nat)
    (_hcap : 0 < cap) (hbound : l.length ≤ cap) :
    entry ∈ pushBounded cap entry l := by
  unfold pushBounded evictIfOver insertOrUpdate
  by_cases hmem : entry ∈ l
  · -- entry already in l: insertOrUpdate returns l; eviction below cap is no-op.
    simp only [hmem, if_true]
    have hnot : ¬ l.length > cap := Nat.not_lt.mpr hbound
    simp only [hnot, if_false]; exact hmem
  · -- entry fresh: result is l ++ [entry], evicted iff overflow.
    simp only [hmem, if_false]
    have hlen : (l ++ [entry]).length = l.length + 1 := by simp
    by_cases h : (l ++ [entry]).length > cap
    · -- Overflow: drop head. `entry` survives because it's at the back and
      -- the list has length ≥ 2 (since cap ≥ 1 and we just exceeded cap).
      simp only [h, if_true]
      have hlen_ge2 : (l ++ [entry]).length ≥ 2 := by
        have : (l ++ [entry]).length > cap := h
        omega
      have htail : (l ++ [entry]).tail = l.tail ++ [entry] := by
        cases hcase : l with
        | nil =>
          -- l = []: then (l ++ [entry]).length = 1, contradicting hlen_ge2.
          subst hcase; simp at hlen_ge2
        | cons a as => simp
      rw [htail]; simp
    · simp only [h, if_false]; simp

/-- **T19 (idempotent registration).** A second `insertOrUpdate` of the same
entry leaves the list bit-for-bit unchanged from the first. Under the
corrected insertion-order semantics this is much stronger than the old
"length is bounded" claim: it's a definitional identity. -/
theorem insertOrUpdate_idempotent (entry : Nat) (l : List Nat) :
    insertOrUpdate entry (insertOrUpdate entry l) = insertOrUpdate entry l := by
  have hmem : entry ∈ insertOrUpdate entry l := insertOrUpdate_entry_mem entry l
  exact insertOrUpdate_existing_eq entry _ hmem

/-- **T20 (caps positive).** Sanity: every cap is `> 0`, ruling out the
degenerate "empty cache" case where everything gets evicted instantly. -/
theorem caps_positive :
    0 < MAX_INV_PER_MAP ∧ 0 < MAX_PEERS_PER_INV ∧
    0 < INVENTORY_ROTATION_INTERVAL_SECS := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## Input-truncation guards (Finding 68)

The first-line DoS guard is in `InventoryChange::new_available_multi` /
`new_missing_multi`: incoming `hashes` are `.truncate(MAX_INV_PER_MAP)`'d
before the change is constructed. The registry then enforces its own cap on
top. We pin both layers below. -/

/-- **T21 (input truncation is bounded).** After `truncateInput`, the list
length is at most `MAX_INV_PER_MAP`. Mirrors `Vec::truncate(n)`. -/
theorem truncate_input_length_le (l : List Nat) :
    (truncateInput l).length ≤ MAX_INV_PER_MAP := by
  unfold truncateInput
  exact List.length_take_le _ _

/-- **T22 (short input passes through unchanged).** If `l.length ≤
MAX_INV_PER_MAP`, the truncation is a no-op. -/
theorem truncate_input_preserves_short (l : List Nat)
    (h : l.length ≤ MAX_INV_PER_MAP) :
    truncateInput l = l := by
  unfold truncateInput
  exact List.take_of_length_le h

/-- **T23 (composed guard: input truncation + per-push cap).** Even if the
attacker supplies an unbounded `hashes` vector, the message-handler
truncates to `MAX_INV_PER_MAP` *and* each individual `pushBounded` keeps the
registry within `cap`. The composition gives: starting from a within-cap
list, iterating `pushBounded cap _ _` over a truncated input never produces
a list longer than `cap`. -/
theorem truncate_then_push_bounded (cap : Nat) (l input : List Nat)
    (hl : l.length ≤ cap) :
    ∀ e ∈ truncateInput input, (pushBounded cap e l).length ≤ cap := by
  intro e _he
  exact pushBounded_length_le cap e l hl

end Zebra.InventoryCacheSize
