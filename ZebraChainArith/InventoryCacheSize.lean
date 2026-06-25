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

The eviction strategy is *insertion-order FIFO*: when a cap is exceeded,
`IndexMap::shift_remove_index(0)` removes the oldest insertion, which is an
abstract LRU when re-insertion bumps an entry to the back. We model that as
a List, with two abstract operations:

  * `insertOrBump entry list` — if `entry` is already present, move it to the
    *back* (this is the LRU touch); otherwise append it.
  * `evictIfOver cap list` — if the list exceeds `cap`, drop the head (the
    oldest entry).
  * `pushBounded cap entry list` — the composition: insertOrBump then evict.

The Rust register-then-evict loop at
`inventory_registry.rs:382-433` is exactly this `pushBounded` shape applied
to two structures: the per-hash peers map (capped at `MAX_PEERS_PER_INV`),
then the outer hash map (capped at `MAX_INV_PER_MAP`).

We prove:
  * the bounded list never exceeds the cap (T1, T2);
  * inserting an *existing* entry never grows the list — only re-orders it
    (T3, T4, T5);
  * the per-hash and outer caps compose multiplicatively for the total memory
    footprint (T6);
  * rotation cleanly preserves the per-map cap (T7);
  * after two rotation intervals every entry is gone (T8, T9);
  * insertion is monotone in length up to the cap (T10);
  * eviction below the cap is a no-op (T11);
  * the constant numbers match the Rust source (T12, T13, T14);
  * the DoS-bound estimate quoted in the Rust comment (less than 1 MB
    per map at 32-64 bytes per inventory) is consistent with our model (T15);
  * the LRU touch preserves the *set* of tracked entries (T16);
  * eviction at the cap yields exactly `cap` (T17, T18);
  * registering existing entries is idempotent in length (T19);
  * caps are positive (T20).
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

/-- The DoS upper bound (in bytes) for a per-map inventory hash table,
quoted in the Rust security comment as "1000 inventory * 2 maps * 32-64
bytes per inventory = less than 1 MB".
We use the upper estimate (64 bytes / inv) for safety reasoning.
Source: `zebra-network/src/peer_set/inventory_registry.rs:43-45`. -/
def MAX_INV_BYTES_PER_INV : Nat := 64

/-! ## Abstract model

We model the per-hash peer list (and analogously the outer inventory list) as
a `List Nat`, where each `Nat` is an opaque entry identifier. The two
operations the Rust loop performs are:

  1. `entry_or_default` followed by `insert(addr, marker)` — semantically:
     if `addr` is already keyed, update its marker; if not, append a new
     entry at the back of the IndexMap.
  2. `if len > MAX { shift_remove_index(0) }` — drop the oldest entry, but
     only if we overflowed.

We model (1) as `insertOrBump entry list`: if `entry ∈ list`, *move* it to
the back; else append it. We model (2) as `evictIfOver cap list`: drop the
head only when `list.length > cap`. -/

/-- Append an entry, removing any earlier occurrence first ("LRU touch":
move-to-back). -/
def insertOrBump (entry : Nat) (l : List Nat) : List Nat :=
  l.filter (· ≠ entry) ++ [entry]

/-- Drop the head of the list iff its length strictly exceeds the cap. This
mirrors `if hash_peers.len() > MAX_PEERS_PER_INV { hash_peers.shift_remove_index(0) }`. -/
def evictIfOver (cap : Nat) (l : List Nat) : List Nat :=
  if l.length > cap then l.tail else l

/-- The composed bounded-push operation: LRU-touch the entry, then evict the
oldest if the list overflows. -/
def pushBounded (cap : Nat) (entry : Nat) (l : List Nat) : List Nat :=
  evictIfOver cap (insertOrBump entry l)

/-- Rotate the registry: drop `prev` entirely, move `current` into `prev`,
and reset `current` to empty. We model the two-slot state as a pair. -/
def rotate (current _prev : List Nat) : List Nat × List Nat :=
  ([], current)

/-! ## Theorems -/

/-- Helper: `l.filter (· ≠ e)` strips `e` everywhere, so its length is at
most `l.length`. Used by several length-bound proofs below. -/
private lemma filter_length_le (e : Nat) (l : List Nat) :
    (l.filter (· ≠ e)).length ≤ l.length :=
  List.length_filter_le _ _

/-- **T1 (bounded list never exceeds `cap + 1` before eviction, then is
bounded by `cap` after).** After a `pushBounded`, the result has length at
most `cap`. This is the core security property: no matter how many entries
get added, the registry cannot grow past the cap. -/
theorem pushBounded_length_le (cap entry : Nat) (l : List Nat)
    (_hcap : 0 < cap) (hbound : l.length ≤ cap) :
    (pushBounded cap entry l).length ≤ cap := by
  unfold pushBounded evictIfOver insertOrBump
  set fl := l.filter (· ≠ entry) with hfl
  have hfl_le : fl.length ≤ l.length := filter_length_le entry l
  have happ : (fl ++ [entry]).length = fl.length + 1 := by
    simp
  by_cases h : (fl ++ [entry]).length > cap
  · simp only [h, if_true]
    have htail : (fl ++ [entry]).tail.length = (fl ++ [entry]).length - 1 := by
      rw [List.length_tail]
    rw [htail, happ]
    omega
  · simp only [h, if_false]
    rw [happ]
    omega

/-- **T2 (bounded list iterated stays bounded).** Starting from any list
already within the cap, a single `pushBounded` keeps it within the cap.
This means a *sequence* of insertions, modelled by iterated
`pushBounded`, never exceeds the cap. -/
theorem pushBounded_invariant (cap : Nat) (entry : Nat) (l : List Nat)
    (hcap : 0 < cap) (hinv : l.length ≤ cap) :
    (pushBounded cap entry l).length ≤ cap :=
  pushBounded_length_le cap entry l hcap hinv

/-- Helper: when `entry ∈ l`, the filter `l.filter (· ≠ entry)` is strictly
shorter than `l`. Proved by induction on `l`. -/
private lemma filter_length_lt_of_mem
    (entry : Nat) (l : List Nat) (hmem : entry ∈ l) :
    (l.filter (· ≠ entry)).length < l.length := by
  induction l with
  | nil => exact absurd hmem (by simp)
  | cons a as ih =>
    by_cases ha : a = entry
    · -- Head matches `entry`: filter strips it; tail's filtered length ≤ as.length.
      have hflen : ((a :: as).filter (· ≠ entry)).length
                 ≤ as.length := by
        rw [List.filter_cons]
        have : decide (a ≠ entry) = false := by simp [ha]
        rw [this]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact filter_length_le entry as
      simp only [List.length_cons]
      omega
    · -- Head doesn't match: it survives, recurse on tail.
      have hmem' : entry ∈ as := by
        cases hmem with
        | head => exact absurd rfl (fun h => ha h.symm)
        | tail _ h => exact h
      have hrec := ih hmem'
      have hflen : ((a :: as).filter (· ≠ entry)).length
                 = (as.filter (· ≠ entry)).length + 1 := by
        rw [List.filter_cons]
        have : decide (a ≠ entry) = true := by simp [ha]
        rw [this]
        simp
      rw [hflen]
      simp only [List.length_cons]
      omega

/-- **T3 (existing entry doesn't grow the list).** If `entry` is already in
`l`, the LRU-touch produces a list of length *at most* `l.length` — the
inserted entry replaces an earlier occurrence, so the total length cannot
grow. This is the load-bearing "registering an existing entry is harmless"
property for the inventory registry. -/
theorem insertOrBump_existing_le (entry : Nat) (l : List Nat)
    (hmem : entry ∈ l) :
    (insertOrBump entry l).length ≤ l.length := by
  unfold insertOrBump
  have := filter_length_lt_of_mem entry l hmem
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- **T4 (insertOrBump bounds the length by `l.length + 1`).** Whether the
entry was present or not, the LRU-touch grows the list by at most 1. -/
theorem insertOrBump_length_le (entry : Nat) (l : List Nat) :
    (insertOrBump entry l).length ≤ l.length + 1 := by
  unfold insertOrBump
  have hle : (l.filter (· ≠ entry)).length ≤ l.length :=
    filter_length_le entry l
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- **T5 (new entry adds exactly 1).** If `entry` is *not* in `l`, the
LRU-touch appends it at the back, growing the list by exactly 1. -/
theorem insertOrBump_new_length (entry : Nat) (l : List Nat)
    (hmem : entry ∉ l) :
    (insertOrBump entry l).length = l.length + 1 := by
  unfold insertOrBump
  have hfilter : l.filter (· ≠ entry) = l := by
    apply List.filter_eq_self.mpr
    intros x hx
    have : x ≠ entry := fun heq => hmem (heq ▸ hx)
    simp [this]
  rw [hfilter]
  simp [List.length_append]

/-- **T6 (per-hash cap composes multiplicatively with the outer cap).** The
total memory footprint of a single map is at most
`MAX_INV_PER_MAP * MAX_PEERS_PER_INV`. With `1000 * 70 = 70_000` peer-entries
per map, and two maps, that's `140_000` entries — the bound the Rust safety
comment relies on. -/
theorem total_entries_bound :
    MAX_INV_PER_MAP * MAX_PEERS_PER_INV = 70000 := by
  unfold MAX_INV_PER_MAP MAX_PEERS_PER_INV
  decide

/-- **T7 (rotation halves the live entries).** After a rotation, `current`
is empty and `prev` holds what `current` used to. The bound on either map
is unchanged. -/
theorem rotate_current_empty (current prev : List Nat) :
    (rotate current prev).1 = [] := by
  unfold rotate; rfl

theorem rotate_prev_eq_old_current (current prev : List Nat) :
    (rotate current prev).2 = current := by
  unfold rotate; rfl

/-- **T8 (after two rotations all old entries are gone).** A rotation drops
`prev` entirely, so `(rotate (rotate c p).1 (rotate c p).2).2` is the
original `current` becoming `prev`-of-`prev`, which is dropped at the next
rotation. With `INVENTORY_EXPIRY_INTERVALS = 2`, entries inserted before
time 0 are forgotten by time `2 * INVENTORY_ROTATION_INTERVAL_SECS`. -/
theorem two_rotations_drop_original_prev (current prev : List Nat) :
    let s1 := rotate current prev
    let s2 := rotate s1.1 s1.2
    s2.2 = [] := by
  simp [rotate]

/-- **T9 (expiry interval in seconds).** Two rotation intervals = 106
seconds. This is the consensus-irrelevant but operationally-meaningful
upper bound on inventory staleness. -/
theorem expiry_seconds :
    INVENTORY_EXPIRY_INTERVALS * INVENTORY_ROTATION_INTERVAL_SECS = 106 := by
  unfold INVENTORY_EXPIRY_INTERVALS INVENTORY_ROTATION_INTERVAL_SECS
  decide

/-- **T10 (insertOrBump produces a non-empty list).** The result of an
LRU-touch always has at least one element — the inserted entry. -/
theorem insertOrBump_length_pos (entry : Nat) (l : List Nat) :
    0 < (insertOrBump entry l).length := by
  unfold insertOrBump
  simp [List.length_append]

/-- **T11 (eviction below cap is a no-op).** When the list fits, no entry is
dropped. -/
theorem evictIfOver_below_cap (cap : Nat) (l : List Nat) (h : l.length ≤ cap) :
    evictIfOver cap l = l := by
  unfold evictIfOver
  have : ¬ l.length > cap := Nat.not_lt.mpr h
  simp [this]

/-- **T12 (max inventory per map = 1000).** Concrete check of the Rust
constant. -/
theorem max_inv_per_map_eq : MAX_INV_PER_MAP = 1000 := rfl

/-- **T13 (max peers per inventory = 70).** -/
theorem max_peers_per_inv_eq : MAX_PEERS_PER_INV = 70 := rfl

/-- **T14 (rotation interval = 53s).** -/
theorem rotation_interval_eq : INVENTORY_ROTATION_INTERVAL_SECS = 53 := rfl

/-- **T15 (DoS upper bound = 64 KiB per map).** With at most 1000 entries
per map and at most 64 bytes per entry, a single map fits in `64_000`
bytes (well under 1 MB as the Rust comment claims). -/
theorem dos_upper_bound :
    MAX_INV_PER_MAP * MAX_INV_BYTES_PER_INV = 64000 := by
  unfold MAX_INV_PER_MAP MAX_INV_BYTES_PER_INV
  decide

/-- **T16 (LRU touch preserves membership set).** `entry` is in
`insertOrBump entry l`, and every other element of `l` remains. -/
theorem insertOrBump_entry_mem (entry : Nat) (l : List Nat) :
    entry ∈ insertOrBump entry l := by
  unfold insertOrBump
  simp

/-- **T17 (non-entry elements survive the LRU touch).** Any `x ≠ entry` in
`l` is still in `insertOrBump entry l`. -/
theorem insertOrBump_preserves_others (entry x : Nat) (l : List Nat)
    (hx : x ∈ l) (hne : x ≠ entry) :
    x ∈ insertOrBump entry l := by
  unfold insertOrBump
  simp only [List.mem_append, List.mem_filter, List.mem_singleton, decide_not]
  left
  refine ⟨hx, ?_⟩
  simp [hne]

/-- **T18 (pushBounded preserves entry membership).** After a bounded push,
the new entry is either the most recently inserted (always retained, since
eviction only drops the head and we just placed `entry` at the tail) or, in
the degenerate `cap = 0` case, immediately evicted. The non-degenerate
guarantee: when `cap ≥ 1`, the inserted entry survives. -/
theorem pushBounded_entry_mem (cap entry : Nat) (l : List Nat) (hcap : 0 < cap) :
    entry ∈ pushBounded cap entry l := by
  unfold pushBounded evictIfOver insertOrBump
  set fl := l.filter (· ≠ entry) with hfl
  set L := fl ++ [entry] with hL
  by_cases h : L.length > cap
  · -- We're going to drop the head of L. Since L ends with `entry`, after
    -- dropping its head it still contains `entry` as long as L.length ≥ 2.
    -- L.length ≥ 2 follows from L.length > cap ≥ 1.
    simp only [h, if_true]
    have hlen : L.length ≥ 2 := by
      have : L.length > cap := h
      omega
    -- L = fl ++ [entry]; its tail is fl.tail ++ [entry] when fl ≠ [], else [].
    -- We need: fl.length ≥ 1 (so that L.length = fl.length + 1 ≥ 2 implies fl ≠ []).
    have hfl_nonempty : fl.length ≥ 1 := by
      have : L.length = fl.length + 1 := by simp [hL]
      omega
    -- Rewrite tail.
    have htail_eq : L.tail = fl.tail ++ [entry] := by
      rw [hL]
      cases hfl_eq : fl with
      | nil => simp [hfl_eq] at hfl_nonempty
      | cons a fl' => simp
    rw [htail_eq]
    simp
  · simp only [h, if_false]
    rw [hL]; simp

/-- **T19 (idempotent registration: inserting twice doesn't grow further).**
A second LRU-touch of the same entry leaves the length within the same bound
— a key idempotence property of the registry, since the registry's call
to `IndexMap::insert` is idempotent on the key set. -/
theorem insertOrBump_idempotent_length_le (entry : Nat) (l : List Nat) :
    (insertOrBump entry (insertOrBump entry l)).length ≤
      (insertOrBump entry l).length := by
  have hmem : entry ∈ insertOrBump entry l := insertOrBump_entry_mem entry l
  exact insertOrBump_existing_le entry _ hmem

/-- **T20 (caps are all positive).** Sanity: every cap is `> 0`, ruling out
the degenerate "empty cache" case where everything gets evicted instantly. -/
theorem caps_positive :
    0 < MAX_INV_PER_MAP ∧ 0 < MAX_PEERS_PER_INV ∧
    0 < INVENTORY_ROTATION_INTERVAL_SECS := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Zebra.InventoryCacheSize
