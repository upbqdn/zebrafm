import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# History tree append-only invariant
(`zebra-chain/src/history_tree.rs`, `zebra-chain/src/primitives/zcash_history.rs`)

The Zcash chain history tree (ZIP-221) is a Merkle Mountain Range over the
block-by-block leaves of the chain. The Rust implementation in
`zebra-chain/src/history_tree.rs` exposes only one mutating operation:
`NonEmptyHistoryTree::push`, which calls into
`primitives/zcash_history.rs::Tree::append_leaf`. There is no public truncation
or rewrite API outside of the activation-block reset path.

The full Merkle Mountain Range structure (peak pruning, peak rebuilding,
internal-node hashing) is out of scope for this arithmetic module; we model
only the *append-only* abstract property over the leaf sequence:

  * a tree is a `List Nat` of committed leaf hashes,
  * `append leaf t := t ++ [leaf]` is the only growth operation,
  * the only fact we care about is that previously-committed leaves stay at
    their original indices forever.

This captures the load-bearing invariant: anything `append_leaf` does to the
shape of the MMR, it cannot rewrite a leaf that has already been published
to the chain. The actual MMR proof structure is in librustzcash's
`zcash_history` crate.

Citations:
  * `Tree::append_leaf` —
    `zebra-chain/src/primitives/zcash_history.rs:176`
  * `NonEmptyHistoryTree::push` —
    `zebra-chain/src/history_tree.rs:222`
  * `NonEmptyHistoryTree::from_block` —
    `zebra-chain/src/history_tree.rs:148`
-/

namespace Zebra.HistoryTreeAppendOnly

/-- The abstract history tree: a sequence of committed leaf hashes, modelled
as a `List Nat`. Each list element is one Heartwood-onward block leaf.
Source: `zebra-chain/src/history_tree.rs:59` (`pub struct NonEmptyHistoryTree`) -/
abbrev Tree := List Nat

/-- The empty (pre-Heartwood) tree.
Source: `zebra-chain/src/history_tree.rs:449`
(`pub struct HistoryTree(Option<NonEmptyHistoryTree>)`) -/
def empty : Tree := []

/-- Single-leaf tree, modelling `NonEmptyHistoryTree::from_block`.
Source: `zebra-chain/src/history_tree.rs:148` -/
def singleton (leaf : Nat) : Tree := [leaf]

/-- Append a new leaf to the tree. This is the *only* growth operation
exposed by the Rust API: `NonEmptyHistoryTree::push` calls
`zcash_history::Tree::append_leaf`, which extends the leaf set by one
without rewriting earlier leaves.
Source: `zebra-chain/src/primitives/zcash_history.rs:176` (`append_leaf`)
Source: `zebra-chain/src/history_tree.rs:222` (`push`) -/
def append (leaf : Nat) (t : Tree) : Tree := t ++ [leaf]

/-- Number of committed leaves in the tree. Mirrors the abstract notion of
"tree size" — the MMR also tracks a `size: u32` field, but that one counts
*nodes* including internal peaks; we count *leaves* here.
Source: `zebra-chain/src/history_tree.rs:67` -/
def numLeaves (t : Tree) : Nat := t.length

/-- The leaf at index `i`, if any. Returns `none` for out-of-range. -/
def leafAt (i : Nat) (t : Tree) : Option Nat := t[i]?

/-- A tree "at height `h`" must hold at least `h + 1` leaves. The genesis-from-Heartwood
block is at height 0 and yields a singleton; height `h` requires `h + 1` total
leaves to have been pushed in.
Source: `zebra-chain/src/history_tree.rs:148` (`from_block` at the activation height)
Source: `zebra-chain/src/history_tree.rs:222` (`push` requires `prev_height + 1`) -/
def atHeight (h : Nat) (t : Tree) : Prop := h + 1 ≤ numLeaves t

/-- Append a list of leaves in order. Models a sequence of `push` calls. -/
def appendMany (leaves : List Nat) (t : Tree) : Tree := t ++ leaves

/-! ## Theorems -/

/-- **T1 (append grows length by exactly 1).** Mirrors the Rust invariant that
`append_leaf` adds exactly one *leaf* to the tree (it may add internal peak
nodes too, but those are accounted separately in `size`). -/
theorem append_length (leaf : Nat) (t : Tree) :
    numLeaves (append leaf t) = numLeaves t + 1 := by
  unfold append numLeaves
  simp

/-- **T2 (append preserves previously-committed leaves at their indices).**
This is *the* append-only property: for any `i < numLeaves t`, the leaf
returned by `leafAt i (append leaf t)` equals `leafAt i t`. No prior leaf is
ever rewritten. -/
theorem append_preserves_leaves (leaf : Nat) (t : Tree) (i : Nat)
    (hi : i < numLeaves t) :
    leafAt i (append leaf t) = leafAt i t := by
  unfold append leafAt numLeaves at *
  rw [List.getElem?_append_left hi]

/-- **T3 (no shrinkage).** Appending never decreases the leaf count. -/
theorem append_no_shrink (leaf : Nat) (t : Tree) :
    numLeaves t ≤ numLeaves (append leaf t) := by
  rw [append_length]
  omega

/-- **T4 (a tree "at height h" has length ≥ h + 1).** This is the no-shrinkage
property in the height/length direction: a tree that has reached height `h`
must have `h + 1` or more leaves. -/
theorem atHeight_length (h : Nat) (t : Tree) (hath : atHeight h t) :
    h + 1 ≤ numLeaves t := hath

/-- **T5 (a tree "at height h" has length ≥ h).** The weaker form requested
by the prompt — a tree at height `h` has at least `h` leaves. Follows from
T4 by `h ≤ h + 1`. -/
theorem atHeight_length_ge (h : Nat) (t : Tree) (hath : atHeight h t) :
    h ≤ numLeaves t := by
  have := atHeight_length h t hath
  omega

/-- **T6 (height-preservation under append).** If a tree is at height `h`,
then after one append it is still at height `h`. -/
theorem append_preserves_atHeight (h : Nat) (t : Tree) (leaf : Nat)
    (hath : atHeight h t) :
    atHeight h (append leaf t) := by
  unfold atHeight
  have hlen := atHeight_length h t hath
  rw [append_length]
  omega

/-- **T7 (height grows under append).** After appending one leaf to a tree
at height `h`, the result is at height `h + 1`. -/
theorem append_grows_height (h : Nat) (t : Tree) (leaf : Nat)
    (hath : atHeight h t) :
    atHeight (h + 1) (append leaf t) := by
  unfold atHeight
  have hlen := atHeight_length h t hath
  rw [append_length]
  omega

/-- **T8 (singleton is a tree at height 0).** Mirrors the Rust
`NonEmptyHistoryTree::from_block` precondition: the activation block creates
a tree with one leaf, at the Heartwood activation height (relative height 0
within this tree). -/
theorem singleton_atHeight (leaf : Nat) : atHeight 0 (singleton leaf) := by
  unfold atHeight singleton numLeaves
  simp

/-- **T9 (appended leaf is at the last index).** The newly-appended leaf
sits at index `numLeaves t`, the very next slot. -/
theorem append_leafAt_last (leaf : Nat) (t : Tree) :
    leafAt (numLeaves t) (append leaf t) = some leaf := by
  unfold append leafAt numLeaves
  rw [List.getElem?_append_right (by omega)]
  simp

/-- **T10 (out-of-range leafAt is `none`).** A leaf index past the end has
no committed value. -/
theorem leafAt_out_of_range (i : Nat) (t : Tree)
    (hi : numLeaves t ≤ i) : leafAt i t = none := by
  unfold leafAt numLeaves at *
  exact List.getElem?_eq_none hi

/-- **T11 (appendMany length).** Appending `n` leaves grows the length by `n`. -/
theorem appendMany_length (leaves : List Nat) (t : Tree) :
    numLeaves (appendMany leaves t) = numLeaves t + leaves.length := by
  unfold appendMany numLeaves
  simp

/-- **T12 (appendMany preserves prior leaves at their indices).** The
append-only property generalised to a batch of leaves. -/
theorem appendMany_preserves_leaves (leaves : List Nat) (t : Tree) (i : Nat)
    (hi : i < numLeaves t) :
    leafAt i (appendMany leaves t) = leafAt i t := by
  unfold appendMany leafAt numLeaves at *
  rw [List.getElem?_append_left hi]

/-- **T13 (appendMany never shrinks).** -/
theorem appendMany_no_shrink (leaves : List Nat) (t : Tree) :
    numLeaves t ≤ numLeaves (appendMany leaves t) := by
  rw [appendMany_length]
  omega

/-- **T14 (numLeaves is monotone in append).** A repeated-append claim:
for any `t₁` that is a prefix of `t₂` (i.e. `t₂ = appendMany _ t₁`),
the leaf count grows. -/
theorem numLeaves_monotone_appendMany (leaves : List Nat) (t : Tree) :
    numLeaves t ≤ numLeaves (appendMany leaves t) :=
  appendMany_no_shrink leaves t

/-- **T15 (height monotone under appendMany).** If a tree is at height `h`,
then after appending any list of leaves it is still at (at least) height `h`. -/
theorem appendMany_preserves_atHeight (h : Nat) (t : Tree) (leaves : List Nat)
    (hath : atHeight h t) :
    atHeight h (appendMany leaves t) := by
  unfold atHeight
  have hlen := atHeight_length h t hath
  rw [appendMany_length]
  omega

/-- **T16 (empty has no leaves).** -/
theorem empty_numLeaves : numLeaves empty = 0 := rfl

/-- **T17 (singleton has one leaf).** -/
theorem singleton_numLeaves (leaf : Nat) : numLeaves (singleton leaf) = 1 := rfl

/-- **T18 (singleton's leaf is at index 0).** -/
theorem singleton_leafAt_zero (leaf : Nat) :
    leafAt 0 (singleton leaf) = some leaf := rfl

/-- **T19 (append associativity over appendMany).** Appending one leaf then
a batch equals appending the batch with the leaf prepended. Useful for
reasoning about chains of pushes. -/
theorem append_appendMany (leaf : Nat) (leaves : List Nat) (t : Tree) :
    appendMany leaves (append leaf t) = appendMany (leaf :: leaves) t := by
  unfold append appendMany
  simp

/-- **T20 (append is `appendMany` of a singleton).** Single appends are a
special case of batch appends. -/
theorem append_eq_appendMany_singleton (leaf : Nat) (t : Tree) :
    append leaf t = appendMany [leaf] t := rfl

/-- **T21 (universal append-only over a batch).** After appending any batch,
the leaf at every previously-occupied index is unchanged from its original
value. This is the strongest append-only statement: the entire prior tree
is preserved as a prefix of the new tree. -/
theorem appendMany_prefix (leaves : List Nat) (t : Tree) (i : Nat)
    (hi : i < numLeaves t) :
    leafAt i (appendMany leaves t) = leafAt i t :=
  appendMany_preserves_leaves leaves t i hi

end Zebra.HistoryTreeAppendOnly
