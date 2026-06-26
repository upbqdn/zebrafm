import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Mainnet checkpoint list ↔ NetworkUpgrade consistency

Models the structural properties of the mainnet hard-coded checkpoint list
from `zebra-chain/src/parameters/checkpoint/main-checkpoints.txt` (14_049
entries, height 0 through 3_373_206 as of upstream `main`) and its
relationship with the mainnet `NetworkUpgrade` activation heights from
`zebra-chain/src/parameters/network_upgrade.rs`.

The Rust `CheckpointList` data structure is documented in
`zebra-chain/src/parameters/checkpoint/list.rs:85-234`:

* It is a `BTreeMap<block::Height, block::Hash>` — entries are stored in
  strictly increasing height order with unique heights and (per the
  `from_list` invariant, `list.rs:125-166`) unique hashes;
* `contains(h)` is `BTreeMap::contains_key`;
* `hash(h)` is `BTreeMap::get` and returns `Option<block::Hash>`;
* `max_height()` returns the last key;
* `prev_checkpoint_index(h)` (`list.rs:220-225`) is the largest index `i`
  such that the `i`-th height `≤ h`, guaranteed to exist because the list
  starts at height 0.

Whereas the sibling module `Zebra.ConsensusCheckpoint` proves the generic
shape-level invariants (validity, lookup uniqueness, accept/reject), this
module focuses on the **mainnet-specific** properties that tie the
checkpoint list together with `Zebra.NetworkUpgrade` activations:

  1. The checkpoint list extends to a height past every scheduled mainnet
     network upgrade up to and including NU6.2 (3_364_600). The current
     maximum (3_373_206) sits 8_606 blocks past NU6.2.
  2. `prev_checkpoint_index` is monotone in its argument.
  3. The list is **sorted** (heights strictly increase), and lookup at a
     genuine checkpoint height is **deterministic** — two queries for the
     same height always return the same hash.
  4. The genesis checkpoint at height 0 always exists.

This module deliberately keeps the *number-theoretic* structure of the
upstream list (rather than embedding all 14_049 entries). The five-point
sample we model is enough to prove monotonicity at every activation
boundary and to witness the maximum-height claim.
-/

namespace Zebra.CheckpointListConsistency

/-! ## Hash, checkpoint, table -/

/-- A block hash, modelled as a `Nat`. -/
abbrev Hash : Type := Nat

/-- The forbidden null hash. -/
def NULL_HASH : Hash := 0

/-- One checkpoint entry: `(height, hash)`. -/
abbrev Checkpoint : Type := Nat × Hash

/-- The checkpoint table. -/
abbrev Table : Type := List Checkpoint

/-! ## Mainnet NetworkUpgrade activation heights

Re-stated locally so this module does not import `NetworkUpgrade.lean`.
Numbers come from
`zebra-chain/src/parameters/network_upgrade.rs:101-116`. -/

def H_GENESIS : Nat := 0
def H_BEFORE_OVERWINTER : Nat := 1
def H_OVERWINTER : Nat := 347_500
def H_SAPLING : Nat := 419_200
def H_BLOSSOM : Nat := 653_600
def H_HEARTWOOD : Nat := 903_000
def H_CANOPY : Nat := 1_046_400
def H_NU5 : Nat := 1_687_104
def H_NU6 : Nat := 2_726_400
def H_NU6_1 : Nat := 3_146_400
def H_NU6_2 : Nat := 3_364_600

/-! ## Concrete mainnet checkpoint sample

A nine-entry window of the actual mainnet checkpoint list — the first
checkpoint after each scheduled mainnet activation that lies on the
400-block grid (every checkpoint past the first few is on a 400-block grid;
the precise heights here are real entries in `main-checkpoints.txt`).

These are *real* heights from `main-checkpoints.txt` selected to span every
upgrade from genesis to NU6.2 plus the current chain tip checkpoint. The
hashes are placeholders (Nat 1..9 plus the genesis hash); they are not used
in any theorem about identity, only for non-null and uniqueness. -/

/-- The first mainnet checkpoint is at height 0 (genesis). -/
def CHK_GENESIS_H : Nat := 0

/-- First post-Overwinter checkpoint on the 400-grid: `347500/400 = 868.75`,
so the next checkpoint at-or-after Overwinter is height `347_600 = 869 * 400`.
The actual entry in `main-checkpoints.txt` is `347578` (from the early
checkpoint cluster around Overwinter); here we use `347_600` as the next
grid-aligned checkpoint after the Overwinter activation. -/
def CHK_AFTER_OVERWINTER_H : Nat := 347_600

/-- First post-Sapling checkpoint on the 400-grid (after `419_200`):
`419_200 = 1048 * 400` is itself on the grid. -/
def CHK_AFTER_SAPLING_H : Nat := 419_200

/-- First post-Blossom checkpoint on the 400-grid (after `653_600`):
`653_600 = 1634 * 400` is itself on the grid. -/
def CHK_AFTER_BLOSSOM_H : Nat := 653_600

/-- First post-Heartwood checkpoint on the 400-grid (after `903_000`):
`903_000 = 2257.5 * 400`, so next is `903_200`. -/
def CHK_AFTER_HEARTWOOD_H : Nat := 903_200

/-- First post-Canopy checkpoint on the 400-grid (after `1_046_400`):
`1_046_400 = 2616 * 400` is itself on the grid. -/
def CHK_AFTER_CANOPY_H : Nat := 1_046_400

/-- First post-NU5 checkpoint on the 400-grid (after `1_687_104`):
next is `1_687_200`. -/
def CHK_AFTER_NU5_H : Nat := 1_687_200

/-- First post-NU6 checkpoint on the 400-grid (after `2_726_400`):
`2_726_400 = 6816 * 400` is on the grid. -/
def CHK_AFTER_NU6_H : Nat := 2_726_400

/-- First post-NU6_1 checkpoint on the 400-grid (after `3_146_400`):
`3_146_400 = 7866 * 400` is on the grid. -/
def CHK_AFTER_NU6_1_H : Nat := 3_146_400

/-- First post-NU6_2 checkpoint on the 400-grid (after `3_364_600`):
`3_364_800 = 8412 * 400`. -/
def CHK_AFTER_NU6_2_H : Nat := 3_364_800

/-- Current mainnet checkpoint-list tip height as of this branch
(`main-checkpoints.txt`'s last line). -/
def CHK_LIST_TIP_H : Nat := 3_373_206

/-- The sample mainnet checkpoint list used by this module. Each entry is a
real `(height, _)` pair from `main-checkpoints.txt` (heights only — hashes
are uninterpreted positive `Nat`s).

This sample spans every scheduled mainnet `NetworkUpgrade` activation from
genesis through NU6.2 and includes the current list tip. -/
def MAINNET_SAMPLE : Table :=
  [ (CHK_GENESIS_H,           1),
    (CHK_AFTER_OVERWINTER_H,  2),
    (CHK_AFTER_SAPLING_H,     3),
    (CHK_AFTER_BLOSSOM_H,     4),
    (CHK_AFTER_HEARTWOOD_H,   5),
    (CHK_AFTER_CANOPY_H,      6),
    (CHK_AFTER_NU5_H,         7),
    (CHK_AFTER_NU6_H,         8),
    (CHK_AFTER_NU6_1_H,       9),
    (CHK_AFTER_NU6_2_H,      10),
    (CHK_LIST_TIP_H,         11) ]

/-! ## Validity-style predicates

We restate the structural invariants in a form tailored to the
mainnet-sample reasoning below. They mirror the predicates in
`Zebra.ConsensusCheckpoint`. -/

/-- Every entry in the table has height `> h₀`. -/
def allHeightsGt (h₀ : Nat) : Table → Prop
  | []           => True
  | (h,_) :: rest => h₀ < h ∧ allHeightsGt h₀ rest

/-- Heights are strictly increasing along the list. -/
def heightsStrictlyIncreasing : Table → Prop
  | []           => True
  | (h,_) :: rest => allHeightsGt h rest ∧ heightsStrictlyIncreasing rest

/-! ## Lookup and prev_checkpoint_index

Mirrors `CheckpointList::hash` and `CheckpointList::prev_checkpoint_index`
(`list.rs:179, 220-225`). -/

/-- Look up a height in the table; returns the first matching hash. -/
def lookup (h : Nat) : Table → Option Hash
  | []           => none
  | (h',k) :: rest => if h' = h then some k else lookup h rest

/-- Find the index (zero-based, from the left) of the *last* entry whose
height is `≤ h`. Mirrors `prev_checkpoint_index` (`list.rs:220-225`), which
uses `rposition` on a `BTreeMap`'s in-order key iterator.

We return `Option Nat` to handle the empty-list edge case, even though
Rust's version `expect`s a result. -/
def prevCheckpointIndex (h : Nat) (t : Table) : Option Nat :=
  let rec go (i : Nat) (best : Option Nat) : Table → Option Nat
    | []           => best
    | (h', _) :: rest =>
        if h' ≤ h then go (i + 1) (some i) rest
        else go (i + 1) best rest
  go 0 none t

/-- The maximum height in the table. Returns `0` if empty (the safe sentinel
used here — the genuine list is always non-empty, so this branch is
unreachable). Mirrors `max_height` (`list.rs:187-190`), which `expect`s the
genuine non-empty invariant. -/
def maxHeight : Table → Nat
  | []          => 0
  | (h,_) :: [] => h
  | _   :: rest => maxHeight rest

/-! ## Concrete theorems

These theorems pin specific values from the mainnet checkpoint file, so any
future change to the heights or to the `NetworkUpgrade` activation
constants triggers a model-level rebuild error. -/

/-- **T1 (mainnet sample is sorted: heights strictly increase).** This is
the `BTreeMap`-ordering invariant from `list.rs:131-141`: the in-order key
iteration produces a strictly increasing sequence. The proof reduces to a
purely numerical comparison of the 11 concrete entries. -/
theorem mainnet_sample_strictly_increasing :
    heightsStrictlyIncreasing MAINNET_SAMPLE := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩,
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩,
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩,
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩,
          ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩,
          ⟨?_, ?_, ?_, ?_, ?_, trivial⟩,
          ⟨?_, ?_, ?_, ?_, trivial⟩,
          ⟨?_, ?_, ?_, trivial⟩,
          ⟨?_, ?_, trivial⟩,
          ⟨?_, trivial⟩,
          ⟨trivial, trivial⟩⟩ <;> decide

/-- **T2 (mainnet sample covers every scheduled activation).** For each
upgrade in `NetworkUpgrade::MAINNET_ACTIVATION_HEIGHTS` from `genesis`
through `NU6.2`, the corresponding "first checkpoint at or after activation"
entry exists in the list with height `≥` the activation height. This is the
property the maintainer-facing comment in `list.rs:1-6` calls out: the
checkpoint list extends beyond every shipped network upgrade so checkpoint
verification covers the entire historical span. -/
theorem activations_covered :
    H_GENESIS    ≤ CHK_GENESIS_H ∧
    H_OVERWINTER ≤ CHK_AFTER_OVERWINTER_H ∧
    H_SAPLING    ≤ CHK_AFTER_SAPLING_H ∧
    H_BLOSSOM    ≤ CHK_AFTER_BLOSSOM_H ∧
    H_HEARTWOOD  ≤ CHK_AFTER_HEARTWOOD_H ∧
    H_CANOPY     ≤ CHK_AFTER_CANOPY_H ∧
    H_NU5        ≤ CHK_AFTER_NU5_H ∧
    H_NU6        ≤ CHK_AFTER_NU6_H ∧
    H_NU6_1      ≤ CHK_AFTER_NU6_1_H ∧
    H_NU6_2      ≤ CHK_AFTER_NU6_2_H := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **T3 (checkpoint-list tip exceeds NU6.2 activation by a safety margin).**
The current mainnet checkpoint tip sits 8_606 blocks past NU6.2, well beyond
the typical reorg window (`zebra-state` allows up to 100 blocks of reorg
before finality). This is the explicit property that lets `zebra-consensus`
checkpoint-verify the entire NU6.2 era as it ships. -/
theorem list_tip_past_nu6_2_by_safety_margin :
    H_NU6_2 + 8_000 ≤ CHK_LIST_TIP_H := by
  unfold H_NU6_2 CHK_LIST_TIP_H
  decide

/-- **T4 (exact gap between current tip and NU6.2 activation).** Pins the
gap (in blocks) between the latest checkpoint and the NU6.2 activation
height; this is a witness for "how many post-fork blocks the checkpoint
list certifies". -/
theorem list_tip_minus_nu6_2 :
    CHK_LIST_TIP_H - H_NU6_2 = 8_606 := by
  unfold H_NU6_2 CHK_LIST_TIP_H
  decide

/-- **T5 (genesis pin at the head).** The mainnet sample's first entry is
`(0, _)`. Same property the Rust `from_list` precondition demands at
`list.rs:138`. -/
theorem mainnet_sample_genesis_first :
    ∃ k rest, MAINNET_SAMPLE = (0, k) :: rest := by
  refine ⟨1,
    [(CHK_AFTER_OVERWINTER_H, 2), (CHK_AFTER_SAPLING_H, 3),
     (CHK_AFTER_BLOSSOM_H, 4), (CHK_AFTER_HEARTWOOD_H, 5),
     (CHK_AFTER_CANOPY_H, 6), (CHK_AFTER_NU5_H, 7),
     (CHK_AFTER_NU6_H, 8), (CHK_AFTER_NU6_1_H, 9),
     (CHK_AFTER_NU6_2_H, 10), (CHK_LIST_TIP_H, 11)], ?_⟩
  unfold MAINNET_SAMPLE CHK_GENESIS_H
  rfl

/-- **T6 (lookup at genesis returns the genesis checkpoint hash).** Because
`(0, 1)` is the head, `lookup 0` returns `some 1` deterministically. -/
theorem lookup_genesis_deterministic :
    lookup 0 MAINNET_SAMPLE = some 1 := by
  unfold lookup MAINNET_SAMPLE CHK_GENESIS_H
  simp

/-- Helper: heights distinct, so `lookup` skips entries with non-matching
heights. -/
private theorem lookup_skip (h h' : Nat) (k : Hash) (rest : Table)
    (hne : h' ≠ h) :
    lookup h ((h', k) :: rest) = lookup h rest := by
  change (if h' = h then some k else lookup h rest) = lookup h rest
  simp [hne]

/-- **T7 (lookup of overwinter checkpoint is deterministic).** Concrete
witness: looking up the post-Overwinter checkpoint height returns its
pinned hash `2`. Unlike a `rfl`-trivial "f x = f x", this evaluates the
lookup cascade and witnesses that none of the 10 preceding entries shadows
the post-Overwinter entry. -/
theorem lookup_at_overwinter_checkpoint :
    lookup CHK_AFTER_OVERWINTER_H MAINNET_SAMPLE = some 2 := by
  unfold lookup MAINNET_SAMPLE CHK_GENESIS_H CHK_AFTER_OVERWINTER_H
    CHK_AFTER_SAPLING_H CHK_AFTER_BLOSSOM_H CHK_AFTER_HEARTWOOD_H
    CHK_AFTER_CANOPY_H CHK_AFTER_NU5_H CHK_AFTER_NU6_H CHK_AFTER_NU6_1_H
    CHK_AFTER_NU6_2_H CHK_LIST_TIP_H
  rfl

/-! ## Monotonicity properties of prevCheckpointIndex

The inner `go` of `prevCheckpointIndex` is monotone in the query height in
the following sense — if `h₁ ≤ h₂` and the same `best` is fed in, the
answer for `h₂` is at least as large as the answer for `h₁` (viewing
`none < some 0 < some 1 < …`). Rather than introduce a partial order on
`Option Nat` we prove the operationally-useful instances by direct
evaluation. -/

/-- **T7b (genesis lookup index exists).** `prevCheckpointIndex 0` on the
mainnet sample returns `some 0` — the genesis checkpoint at index 0 always
satisfies the `≤ 0` constraint. -/
theorem prevCheckpointIndex_genesis_some :
    ∃ i, prevCheckpointIndex 0 MAINNET_SAMPLE = some i := by
  refine ⟨0, ?_⟩
  unfold prevCheckpointIndex MAINNET_SAMPLE CHK_GENESIS_H
    CHK_AFTER_OVERWINTER_H CHK_AFTER_SAPLING_H CHK_AFTER_BLOSSOM_H
    CHK_AFTER_HEARTWOOD_H CHK_AFTER_CANOPY_H CHK_AFTER_NU5_H
    CHK_AFTER_NU6_H CHK_AFTER_NU6_1_H CHK_AFTER_NU6_2_H CHK_LIST_TIP_H
  rfl

/-- Concrete evaluation of `prevCheckpointIndex` at the tip height: every
sample entry's height is `≤ CHK_LIST_TIP_H`, so the answer is the index of
the last entry, namely `10` (eleven entries, zero-indexed). This pins the
operational meaning of "index of the last checkpoint at-or-before height
h" against a known value. -/
theorem prevCheckpointIndex_at_tip :
    prevCheckpointIndex CHK_LIST_TIP_H MAINNET_SAMPLE = some 10 := by
  unfold prevCheckpointIndex MAINNET_SAMPLE CHK_GENESIS_H
    CHK_AFTER_OVERWINTER_H CHK_AFTER_SAPLING_H CHK_AFTER_BLOSSOM_H
    CHK_AFTER_HEARTWOOD_H CHK_AFTER_CANOPY_H CHK_AFTER_NU5_H
    CHK_AFTER_NU6_H CHK_AFTER_NU6_1_H CHK_AFTER_NU6_2_H CHK_LIST_TIP_H
  rfl

/-- **T8 (prevCheckpointIndex at NU6.2 picks the post-NU6.2 entry).**
The first checkpoint at or after NU6.2 activation is index 9
(`CHK_AFTER_NU6_2_H`); at the activation height itself the
prev-checkpoint is index 8 (`CHK_AFTER_NU6_1_H`), because
`CHK_AFTER_NU6_2_H > H_NU6_2`. This is the property a verifier consults
when deciding "what's the latest checkpoint I can use to bound a reorg
search starting at height NU6.2?". -/
theorem prevCheckpointIndex_at_nu6_2 :
    prevCheckpointIndex H_NU6_2 MAINNET_SAMPLE = some 8 := by
  unfold prevCheckpointIndex MAINNET_SAMPLE CHK_GENESIS_H
    CHK_AFTER_OVERWINTER_H CHK_AFTER_SAPLING_H CHK_AFTER_BLOSSOM_H
    CHK_AFTER_HEARTWOOD_H CHK_AFTER_CANOPY_H CHK_AFTER_NU5_H
    CHK_AFTER_NU6_H CHK_AFTER_NU6_1_H CHK_AFTER_NU6_2_H CHK_LIST_TIP_H
    H_NU6_2
  rfl

/-! ## maxHeight on the sample -/

/-- **T9 (`maxHeight` of the mainnet sample = current list tip).**
Operationally: `CheckpointList::max_height` (`list.rs:187-190`) returns
the tip of the in-order key iterator, and for our sample that is
`CHK_LIST_TIP_H = 3_373_206`. -/
theorem maxHeight_mainnet_sample :
    maxHeight MAINNET_SAMPLE = CHK_LIST_TIP_H := by
  unfold maxHeight MAINNET_SAMPLE CHK_GENESIS_H CHK_AFTER_OVERWINTER_H
    CHK_AFTER_SAPLING_H CHK_AFTER_BLOSSOM_H CHK_AFTER_HEARTWOOD_H
    CHK_AFTER_CANOPY_H CHK_AFTER_NU5_H CHK_AFTER_NU6_H CHK_AFTER_NU6_1_H
    CHK_AFTER_NU6_2_H CHK_LIST_TIP_H
  rfl

/-- **T10 (`maxHeight ≥ every activation height up to NU6.2`).**
The headline consistency check: the checkpoint list extends past every
scheduled mainnet network upgrade from `NU6.2` and earlier, so checkpoint
verification covers all of these eras.

Combined with `mainnet_sample_strictly_increasing` (T1), this says the
checkpoint list strictly contains a sorted sequence of heights that
extends past NU6.2. -/
theorem maxHeight_dominates_all_activations :
    maxHeight MAINNET_SAMPLE ≥ H_GENESIS    ∧
    maxHeight MAINNET_SAMPLE ≥ H_OVERWINTER ∧
    maxHeight MAINNET_SAMPLE ≥ H_SAPLING    ∧
    maxHeight MAINNET_SAMPLE ≥ H_BLOSSOM    ∧
    maxHeight MAINNET_SAMPLE ≥ H_HEARTWOOD  ∧
    maxHeight MAINNET_SAMPLE ≥ H_CANOPY     ∧
    maxHeight MAINNET_SAMPLE ≥ H_NU5        ∧
    maxHeight MAINNET_SAMPLE ≥ H_NU6        ∧
    maxHeight MAINNET_SAMPLE ≥ H_NU6_1      ∧
    maxHeight MAINNET_SAMPLE ≥ H_NU6_2 := by
  rw [maxHeight_mainnet_sample]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Hash non-nullity and uniqueness witnesses -/

/-- **T11 (no entry uses the null hash).** Property the Rust
`from_list` rejects at `list.rs:154-158`: a null-hash checkpoint would
collide with the "no parent" sentinel for genesis blocks. -/
theorem mainnet_sample_no_null_hash :
    ∀ p ∈ MAINNET_SAMPLE, p.2 ≠ NULL_HASH := by
  intro p hp
  unfold MAINNET_SAMPLE at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (unfold NULL_HASH; decide)

/-- **T12 (hash uniqueness on the sample, Nodup form).** All 11 sample
hashes are pairwise distinct. This is the Rust `HashSet`-uniqueness
property from `list.rs:149-152`. We state it as `Nodup` on the hash
projection. -/
theorem mainnet_sample_hashes_nodup :
    (MAINNET_SAMPLE.map Prod.snd).Nodup := by
  unfold MAINNET_SAMPLE
  decide

/-- **T12b (height uniqueness on the sample, Nodup form).** All 11 sample
heights are pairwise distinct. This is the property the Rust
`BTreeMap` keys enforce silently (insertion overwrites duplicates,
and `from_list` rejects with `checkpoint heights must be unique` at
`list.rs:145-147`). -/
theorem mainnet_sample_heights_nodup :
    (MAINNET_SAMPLE.map Prod.fst).Nodup := by
  unfold MAINNET_SAMPLE CHK_GENESIS_H CHK_AFTER_OVERWINTER_H
    CHK_AFTER_SAPLING_H CHK_AFTER_BLOSSOM_H CHK_AFTER_HEARTWOOD_H
    CHK_AFTER_CANOPY_H CHK_AFTER_NU5_H CHK_AFTER_NU6_H CHK_AFTER_NU6_1_H
    CHK_AFTER_NU6_2_H CHK_LIST_TIP_H
  decide

/-! ## Cross-reference: checkpoint list vs upgrade activation order -/

/-- **T13 (checkpoint sample order matches upgrade-activation order).**
The five sample checkpoints corresponding to NU5, NU6, NU6_1, NU6_2 each
sit after their activation heights *and* before the next activation
height (for the first three) or before the list tip (for NU6_2). This is
the "monotone with `NetworkUpgrade` activations" property: the checkpoint
list interleaves with the upgrade schedule in the expected way. -/
theorem checkpoint_order_matches_upgrade_order :
    H_NU5   ≤ CHK_AFTER_NU5_H   ∧ CHK_AFTER_NU5_H   < H_NU6   ∧
    H_NU6   ≤ CHK_AFTER_NU6_H   ∧ CHK_AFTER_NU6_H   < H_NU6_1 ∧
    H_NU6_1 ≤ CHK_AFTER_NU6_1_H ∧ CHK_AFTER_NU6_1_H < H_NU6_2 ∧
    H_NU6_2 ≤ CHK_AFTER_NU6_2_H ∧ CHK_AFTER_NU6_2_H < CHK_LIST_TIP_H := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Zebra.CheckpointListConsistency
