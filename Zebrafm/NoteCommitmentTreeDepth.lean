import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sapling and Orchard note-commitment tree depths

The Sapling and Orchard note-commitment trees are *incremental Merkle trees of
fixed depth 32*. The depth pins:

  * the maximum number of leaves at `2^32`,
  * the consensus rule that no block may exceed this capacity (the
    `FullTree` error returned by `append` when full),
  * the fact that Sapling and Orchard have *identical* tree depth.

Source constants:

```rust
// zebra-chain/src/sapling/tree.rs:40
pub(super) const MERKLE_DEPTH: u8 = 32;

// zebra-chain/src/orchard/tree.rs:45
pub(super) const MERKLE_DEPTH: u8 = 32;
```

Source consensus rule (Sapling):

> [Sapling onward] A block MUST NOT add Sapling note commitments that would
> result in the Sapling note commitment tree exceeding its capacity of
> `2^(MerkleDepth^Sapling)` leaf nodes.
>
> [zebra-chain/src/sapling/tree.rs:168-172]

Source append failure mode:

```rust
// zebra-chain/src/sapling/tree.rs:204-218
pub fn append(&mut self, cm_u: NoteCommitmentUpdate) -> Result<(), NoteCommitmentTreeError> {
    if self.inner.append(sapling_crypto::Node::from_cmu(&cm_u)) {
        ...
        Ok(())
    } else {
        Err(NoteCommitmentTreeError::FullTree)
    }
}
```

We model:
  * the depth as `Nat`,
  * the tree as a `Nat` count of leaves so far,
  * `maxCapacity = 2^depth`,
  * `isFull` as `count = maxCapacity`,
  * `append` as the count-incrementing partial function that returns `None`
    when the tree is full (this corresponds to `Err(FullTree)`).
-/

namespace Zebra.NoteCommitmentTreeDepth

/-- Sapling note commitment tree depth.
Source: `zebra-chain/src/sapling/tree.rs:40` -/
def SAPLING_NOTE_COMMITMENT_TREE_DEPTH : Nat := 32

/-- Orchard note commitment tree depth.
Source: `zebra-chain/src/orchard/tree.rs:45` -/
def ORCHARD_NOTE_COMMITMENT_TREE_DEPTH : Nat := 32

/-- Maximum capacity of a Merkle tree of the given depth: `2^depth` leaves.
Source: `zebra-chain/src/sapling/tree.rs:168-172` (consensus rule on tree
capacity); same wording applies to Orchard via `MerkleDepth^Orchard`. -/
def maxCapacity (depth : Nat) : Nat := 2 ^ depth

/-- A tree of given depth is *full* when its leaf count equals `maxCapacity`.
This matches the underlying frontier's append-returns-false condition that
maps to `Err(FullTree)` at `zebra-chain/src/sapling/tree.rs:216`. -/
def isFull (depth count : Nat) : Prop := count = maxCapacity depth

/-- `append` models `NoteCommitmentTree::append`: returns `Some (count + 1)`
when there is room, or `None` (i.e. `Err(FullTree)`) when the tree is full.
Source: `zebra-chain/src/sapling/tree.rs:204-218` (`pub fn append`). -/
def append (depth count : Nat) : Option Nat :=
  if count < maxCapacity depth then some (count + 1) else none

/-- `count` after a sequence of `n` successful appends to an initially empty
tree. Models the post-fact `count()` accessor at
`zebra-chain/src/sapling/tree.rs:437-441` (`u64::from(x.position()) + 1`). -/
def countAfter (n : Nat) : Nat := n

/-! ## Theorems -/

/-- **T1 (Sapling depth = Orchard depth = 32).** Both trees are pinned at the
same depth. -/
theorem sapling_depth_eq_orchard_depth :
    SAPLING_NOTE_COMMITMENT_TREE_DEPTH = ORCHARD_NOTE_COMMITMENT_TREE_DEPTH := rfl

/-- **T2 (concrete maximum capacity).** A tree of depth 32 can hold exactly
`2^32 = 4_294_967_296` leaves. -/
theorem sapling_max_capacity :
    maxCapacity SAPLING_NOTE_COMMITMENT_TREE_DEPTH = 4_294_967_296 := by
  unfold maxCapacity SAPLING_NOTE_COMMITMENT_TREE_DEPTH
  decide

/-- **T3 (Orchard max capacity coincides).** -/
theorem orchard_max_capacity :
    maxCapacity ORCHARD_NOTE_COMMITMENT_TREE_DEPTH = 4_294_967_296 := by
  unfold maxCapacity ORCHARD_NOTE_COMMITMENT_TREE_DEPTH
  decide

/-- **T4 (max capacity is positive).** Even an empty tree has room for at
least one leaf, so the append-on-empty operation always succeeds. -/
theorem maxCapacity_pos (depth : Nat) : 0 < maxCapacity depth := by
  unfold maxCapacity
  exact Nat.two_pow_pos depth

/-- **T5 (full tree is identified by capacity).** A tree of depth 32 with
exactly `2^32` leaves is full. -/
theorem sapling_full_at_max :
    isFull SAPLING_NOTE_COMMITMENT_TREE_DEPTH 4_294_967_296 := by
  unfold isFull
  rw [sapling_max_capacity]

/-- **T6 (Orchard counterpart of T5).** -/
theorem orchard_full_at_max :
    isFull ORCHARD_NOTE_COMMITMENT_TREE_DEPTH 4_294_967_296 := by
  unfold isFull
  rw [orchard_max_capacity]

/-- **T7 (append succeeds below capacity).** -/
theorem append_some (depth count : Nat) (h : count < maxCapacity depth) :
    append depth count = some (count + 1) := by
  unfold append
  simp [h]

/-- **T8 (append fails at capacity — the `FullTree` rule).** Inserting into a
full tree returns `None`, modelling `Err(FullTree)` at
`zebra-chain/src/sapling/tree.rs:216`. -/
theorem append_full_none (depth count : Nat) (h : isFull depth count) :
    append depth count = none := by
  unfold append isFull at *
  rw [h]
  simp

/-- **T9 (concrete: append into a 2^32-leaf Sapling tree fails).** -/
theorem sapling_append_full :
    append SAPLING_NOTE_COMMITMENT_TREE_DEPTH 4_294_967_296 = none :=
  append_full_none _ _ sapling_full_at_max

/-- **T10 (concrete: append into a 2^32-leaf Orchard tree fails).** -/
theorem orchard_append_full :
    append ORCHARD_NOTE_COMMITMENT_TREE_DEPTH 4_294_967_296 = none :=
  append_full_none _ _ orchard_full_at_max

/-- **T11 (append into empty tree succeeds for any depth).** A fresh tree has
0 leaves, and `maxCapacity > 0`, so the first append produces a tree of size 1. -/
theorem append_empty (depth : Nat) :
    append depth 0 = some 1 := by
  have : 0 < maxCapacity depth := maxCapacity_pos depth
  exact append_some depth 0 this

/-- **T12 (append iff not full).** `append` returns `Some` exactly when the
tree is not yet full. -/
theorem append_isSome_iff (depth count : Nat) :
    (append depth count).isSome ↔ count < maxCapacity depth := by
  unfold append
  by_cases h : count < maxCapacity depth <;> simp [h]

/-- **T13 (append result is bounded).** The new leaf count never exceeds the
tree's capacity. -/
theorem append_result_bounded (depth count : Nat) (r : Nat)
    (heq : append depth count = some r) : r ≤ maxCapacity depth := by
  unfold append at heq
  split_ifs at heq with hcond
  simp only [Option.some.injEq] at heq
  omega

/-- **T14 (append result strictly grows the tree by exactly 1).** Every
successful append adds exactly one leaf. -/
theorem append_increments (depth count : Nat) (r : Nat)
    (heq : append depth count = some r) : r = count + 1 := by
  unfold append at heq
  split_ifs at heq
  simp only [Option.some.injEq] at heq
  omega

/-- **T15 (count after `2^depth` appends saturates the tree).** Starting from
an empty tree, applying `append` exactly `maxCapacity depth` times fills it. -/
theorem countAfter_max_isFull (depth : Nat) :
    isFull depth (countAfter (maxCapacity depth)) := by
  unfold isFull countAfter
  rfl

/-- **T16 (depth-32 trees have capacity 2^32).** A direct, unfolded
restatement of the `2^32` bound for both Sapling and Orchard. -/
theorem depth_32_capacity : maxCapacity 32 = 2 ^ 32 := rfl

/-- **T17 (capacity grows with depth).** Deeper trees admit at least as many
leaves. (Models the structural property that the consensus rule pins capacity
to `2^depth`, monotone in `depth`.) -/
theorem maxCapacity_monotone (d₁ d₂ : Nat) (h : d₁ ≤ d₂) :
    maxCapacity d₁ ≤ maxCapacity d₂ := by
  unfold maxCapacity
  exact Nat.pow_le_pow_right (by norm_num) h

/-- **T18 (above-capacity counts are full or invalid).** A tree cannot have
more leaves than its capacity; if `count ≥ maxCapacity`, then `append` fails. -/
theorem append_none_above_capacity (depth count : Nat)
    (h : maxCapacity depth ≤ count) : append depth count = none := by
  unfold append
  have : ¬ count < maxCapacity depth := Nat.not_lt.mpr h
  simp [this]

/-- **T19 (non-vacuous range).** Every depth admits at least one slot
(append-from-empty succeeds), and every depth has a saturation point
(append-from-max fails). -/
theorem append_dichotomy (depth : Nat) :
    (append depth 0).isSome ∧ append depth (maxCapacity depth) = none := by
  refine ⟨?_, ?_⟩
  · rw [append_empty]; simp
  · exact append_full_none _ _ rfl

/-- **T20 (sapling and orchard append agree).** Because their depths and
capacities are identical, the two trees accept and reject exactly the same
appends and produce the same incremented counts. This pins the
"sapling and orchard are structurally aligned" property of the spec. -/
theorem sapling_orchard_append_agree (count : Nat) :
    append SAPLING_NOTE_COMMITMENT_TREE_DEPTH count =
      append ORCHARD_NOTE_COMMITMENT_TREE_DEPTH count := by
  rw [sapling_depth_eq_orchard_depth]

end Zebra.NoteCommitmentTreeDepth
