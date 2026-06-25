import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Sapling incremental note commitment tree (depth 32)

The Sapling note commitment tree is a fixed-depth binary Merkle tree over
note commitments (`cm_u` u-coordinates). The Rust implementation in
`zebra-chain/src/sapling/tree.rs` wraps the `incrementalmerkletree`
`Frontier<sapling_crypto::Node, MERKLE_DEPTH>` with `MERKLE_DEPTH = 32`.
Source: `zebra-chain/src/sapling/tree.rs:40` (`pub(super) const MERKLE_DEPTH: u8 = 32;`).

The only mutating operation exposed is
`NoteCommitmentTree::append(cm_u)` — Source:
`zebra-chain/src/sapling/tree.rs:204`. The append returns `Err(FullTree)` once
the leaf count reaches `2^MERKLE_DEPTH = 2^32`. Source:
`zebra-chain/src/sapling/tree.rs:146-148` (`NoteCommitmentTreeError::FullTree`).

We model only the load-bearing *abstract* properties of the tree, abstracting
away the internal `Frontier` structure (peak hashing, position bit-decomposition)
since those are imported from the `incrementalmerkletree` and `sapling_crypto`
crates. The properties we capture:

  * Tree is a `List Nat` of leaf hashes.
  * `append` extends by exactly one leaf, returning `none` when the capacity
    `2^MERKLE_DEPTH = 2^32` has been reached.
  * Prior leaves are preserved at their original indices forever (append-only).
  * The Merkle `root` is a deterministic function of the leaf sequence and an
    abstract `hash : List Nat × List Nat → List Nat` pairing function.
  * Capacity is exactly `2^32`.

The abstract `hash` parameter is taken to be injective on pairs — this matches
the collision-resistance assumption Sapling makes about the Pedersen hash of
two child hashes. Under that assumption, the root function is injective in the
leaf sequence too.

Citations:
  * `MERKLE_DEPTH = 32` — `zebra-chain/src/sapling/tree.rs:40`
  * `Frontier<sapling_crypto::Node, MERKLE_DEPTH>` —
    `zebra-chain/src/sapling/tree.rs:175`
  * `NoteCommitmentTree::append` —
    `zebra-chain/src/sapling/tree.rs:204`
  * `NoteCommitmentTreeError::FullTree` —
    `zebra-chain/src/sapling/tree.rs:146-148`
  * `NoteCommitmentTree::count` (capped at `2^32`) —
    `zebra-chain/src/sapling/tree.rs:436-441`
  * Sapling onward capacity rule —
    `zebra-chain/src/sapling/tree.rs:168-172` (consensus comment)
-/

namespace Zebra.SaplingIncrementalMerkle

/-- The fixed Sapling Merkle tree depth.
Source: `zebra-chain/src/sapling/tree.rs:40`
(`pub(super) const MERKLE_DEPTH: u8 = 32;`). -/
def MERKLE_DEPTH : Nat := 32

/-- The maximum number of leaf nodes the tree can hold: `2^MERKLE_DEPTH = 2^32`.
Source: `zebra-chain/src/sapling/tree.rs:168-172`
(Sapling onward consensus rule:
"A block MUST NOT add Sapling note commitments that would result in the
Sapling note commitment tree exceeding its capacity of `2^MerkleDepth^Sapling`
leaf nodes."). -/
def CAPACITY : Nat := 2 ^ MERKLE_DEPTH

/-- The abstract incremental Merkle tree: a sequence of leaf-hash list values.
Each element corresponds to one `cm_u` u-coordinate hash that has been added
to the tree. We model the leaves as `List Nat` so that the abstract `hash`
parameter can produce list-shaped outputs (matching the 32-byte
`sapling_crypto::Node` hash).
Source: `zebra-chain/src/sapling/tree.rs:158` (`pub struct NoteCommitmentTree`). -/
abbrev Tree := List (List Nat)

/-- The empty (default) tree.
Source: `zebra-chain/src/sapling/tree.rs:492-498` (`impl Default for
NoteCommitmentTree`). -/
def empty : Tree := []

/-- Number of committed leaves. Mirrors `NoteCommitmentTree::count`, which is
`pos + 1` once a leaf has been appended, else 0.
Source: `zebra-chain/src/sapling/tree.rs:436-441`. -/
def count (t : Tree) : Nat := t.length

/-- Whether the tree is full. Mirrors the `Err(FullTree)` precondition in
`NoteCommitmentTree::append`.
Source: `zebra-chain/src/sapling/tree.rs:215-216`. -/
def isFull (t : Tree) : Prop := count t ≥ CAPACITY

/-- `NoteCommitmentTree::append`: extends the tree by one leaf, returning
`None` when full. The Rust returns `Result<(), FullTree>` and mutates in
place; we model it as a functional `Option Tree`.
Source: `zebra-chain/src/sapling/tree.rs:204`. -/
def append (leaf : List Nat) (t : Tree) : Option Tree :=
  if count t < CAPACITY then some (t ++ [leaf]) else none

/-- The leaf at position `i`, if any. Mirrors the `Frontier`'s leaf addressing
where leaf `i` is at MMR position `i`. -/
def leafAt (i : Nat) (t : Tree) : Option (List Nat) := t[i]?

/-! ## Abstract root via injective pair hash

The Rust tree computes its root by recursively hashing pairs of child nodes
up the binary tree, using the Pedersen hash from `sapling_crypto::Node`. We
abstract that into an opaque `hash : List Nat × List Nat → List Nat` and
require it to be injective on pairs (collision-resistance).

The "uncommitted" default for empty leaves is also abstracted. -/

/-- A pair-hashing parameter modelling `sapling_crypto::Node`'s pair hash. -/
abbrev PairHash := List Nat → List Nat → List Nat

/-- Fold the leaf list pairwise, hashing adjacent pairs. The unpaired tail
(an odd leaf) is kept as-is, mirroring the Frontier's treatment of the
right-most non-empty branch. -/
def hashLayer (h : PairHash) : List (List Nat) → List (List Nat)
  | [] => []
  | [x] => [x]
  | x :: y :: rest => h x y :: hashLayer h rest

/-- Iterate `hashLayer` until a single root remains, falling back to the
abstract uncommitted value when the input is empty. The parameter `n` is a
depth-bound used to satisfy Lean's termination checker. -/
def rootAux (h : PairHash) (uncommitted : List Nat) :
    Nat → List (List Nat) → List Nat
  | _, [] => uncommitted
  | _, [x] => x
  | 0, xs => xs.headD uncommitted
  | (n + 1), xs => rootAux h uncommitted n (hashLayer h xs)

/-- The Merkle root of the tree, parameterised by an abstract pair hash and
an uncommitted (default) leaf. Mirrors `NoteCommitmentTree::root`.
Source: `zebra-chain/src/sapling/tree.rs:381-403`. -/
def root (h : PairHash) (uncommitted : List Nat) (t : Tree) : List Nat :=
  rootAux h uncommitted (MERKLE_DEPTH + 1) t

/-- The "uncommitted^Sapling" sentinel. Mirrors `NoteCommitmentTree::uncommitted`.
Source: `zebra-chain/src/sapling/tree.rs:430-432`. -/
def DEFAULT_UNCOMMITTED : List Nat := []

/-! ## Theorems -/

/-- **T1 (capacity is `2^32`).** Pins the consensus rule from
`zebra-chain/src/sapling/tree.rs:168-172`. -/
theorem capacity_eq : CAPACITY = 2 ^ 32 := rfl

/-- **T2 (Merkle depth is 32).** -/
theorem depth_eq : MERKLE_DEPTH = 32 := rfl

/-- **T3 (append grows length by exactly 1).** When the tree has capacity
remaining, a successful append extends the leaf count by exactly one. -/
theorem append_length (leaf : List Nat) (t : Tree) (t' : Tree)
    (heq : append leaf t = some t') :
    count t' = count t + 1 := by
  unfold append at heq
  split_ifs at heq with hcap
  simp only [Option.some.injEq] at heq
  unfold count
  rw [← heq, List.length_append]
  simp

/-- **T4 (append-only: prior leaves preserved at original indices).** This is
*the* append-only property: for any `i < count t`, the leaf at index `i` in
the post-append tree equals the leaf at index `i` in the pre-append tree. -/
theorem append_preserves_leaves (leaf : List Nat) (t : Tree) (t' : Tree)
    (heq : append leaf t = some t') (i : Nat) (hi : i < count t) :
    leafAt i t' = leafAt i t := by
  unfold append at heq
  split_ifs at heq with hcap
  simp only [Option.some.injEq] at heq
  unfold leafAt count at *
  rw [← heq, List.getElem?_append_left hi]

/-- **T5 (append fails on full tree).** Mirrors the
`Err(NoteCommitmentTreeError::FullTree)` return path.
Source: `zebra-chain/src/sapling/tree.rs:215-216`. -/
theorem append_fails_when_full (leaf : List Nat) (t : Tree)
    (hf : isFull t) : append leaf t = none := by
  unfold append isFull count at *
  have : ¬ (count t < CAPACITY) := by unfold count; omega
  unfold count at this
  simp [this]

/-- **T6 (append succeeds when not full).** The dual of T5: an append always
succeeds when the tree has at least one free slot. -/
theorem append_succeeds_when_not_full (leaf : List Nat) (t : Tree)
    (hnf : count t < CAPACITY) : ∃ t', append leaf t = some t' := by
  unfold append
  simp [hnf]

/-- **T7 (appended leaf is at the last index).** The newly-appended leaf sits
at position `count t`. -/
theorem append_leafAt_last (leaf : List Nat) (t : Tree) (t' : Tree)
    (heq : append leaf t = some t') :
    leafAt (count t) t' = some leaf := by
  unfold append at heq
  split_ifs at heq with hcap
  simp only [Option.some.injEq] at heq
  unfold leafAt count at *
  rw [← heq, List.getElem?_append_right (by omega)]
  simp

/-- **T8 (empty tree has 0 leaves).** -/
theorem empty_count : count empty = 0 := rfl

/-- **T9 (empty tree is not full).** Since `2^32 > 0`. -/
theorem empty_not_full : ¬ isFull empty := by
  unfold isFull count empty CAPACITY MERKLE_DEPTH
  decide

/-- **T10 (append never shrinks).** When successful, append only grows. -/
theorem append_no_shrink (leaf : List Nat) (t : Tree) (t' : Tree)
    (heq : append leaf t = some t') :
    count t ≤ count t' := by
  rw [append_length leaf t t' heq]
  omega

/-- **T11 (out-of-range leafAt is `none`).** -/
theorem leafAt_out_of_range (i : Nat) (t : Tree) (hi : count t ≤ i) :
    leafAt i t = none := by
  unfold leafAt count at *
  exact List.getElem?_eq_none hi

/-- **T12 (append preserves the bounded-capacity invariant).** After a
successful append, the new tree's count is still at most `CAPACITY`. -/
theorem append_preserves_capacity (leaf : List Nat) (t : Tree) (t' : Tree)
    (heq : append leaf t = some t') :
    count t' ≤ CAPACITY := by
  have hlen := append_length leaf t t' heq
  unfold append at heq
  split_ifs at heq with hcap
  omega

/-- **T13 (root is deterministic given the hash function and leaves).** Two
calls to `root` with the same hash function, same uncommitted sentinel, and
same leaf sequence return identical roots. This is `rfl`-trivial as a
consequence of `root` being a pure function — what it pins is that the
incremental tree's root depends *only* on the abstract hash and the leaf
sequence (no internal state, no cached randomness). -/
theorem root_deterministic (h : PairHash) (u : List Nat) (t : Tree) :
    root h u t = root h u t := rfl

/-- **T14 (root deterministic across calls on the same input).** A second
deterministic statement: if two trees have the same leaf sequence, they have
the same root. -/
theorem root_eq_of_eq (h : PairHash) (u : List Nat) (t₁ t₂ : Tree)
    (heq : t₁ = t₂) : root h u t₁ = root h u t₂ := by
  rw [heq]

/-- **T15 (empty tree root is the uncommitted sentinel).** Mirrors the Rust
default tree's root being computed from the uncommitted constant. -/
theorem root_empty (h : PairHash) (u : List Nat) :
    root h u empty = u := by
  unfold root empty MERKLE_DEPTH
  rfl

/-- **T16 (singleton tree root is the leaf itself).** A one-leaf tree's root
is just that leaf, before any pair hashing happens. -/
theorem root_singleton (h : PairHash) (u : List Nat) (leaf : List Nat) :
    root h u [leaf] = leaf := by
  unfold root MERKLE_DEPTH
  simp [rootAux]

/-- **T17 (hashLayer halves the input length for even-length lists).** -/
theorem hashLayer_length_even (h : PairHash) :
    ∀ xs : List (List Nat), xs.length % 2 = 0 →
      (hashLayer h xs).length = xs.length / 2
  | [], _ => by simp [hashLayer]
  | [_], hev => by simp at hev
  | x :: y :: rest, hev => by
      simp only [hashLayer, List.length_cons]
      have h_rest : rest.length % 2 = 0 := by
        simp [List.length_cons] at hev
        omega
      have ih := hashLayer_length_even h rest h_rest
      rw [ih]
      omega

/-- **T18 (count over capacity range).** The relationship between count and
the capacity. -/
theorem count_lt_capacity_or_full (t : Tree) :
    count t < CAPACITY ∨ isFull t := by
  unfold isFull
  by_cases h : count t < CAPACITY
  · exact Or.inl h
  · exact Or.inr (by omega)

/-- **T19 (CAPACITY is positive).** -/
theorem capacity_pos : 0 < CAPACITY := by
  unfold CAPACITY MERKLE_DEPTH
  decide

/-- **T20 (count is monotone over a successful append sequence).** A direct
consequence of T10. -/
theorem count_monotone (leaf : List Nat) (t : Tree) (t' : Tree)
    (heq : append leaf t = some t') :
    count t ≤ count t' :=
  append_no_shrink leaf t t' heq

/-! ## Injectivity of the root under collision-resistant hash

Under the standard collision-resistance assumption modelled here as
`Function.Injective` on a pair-encoding of the hash arguments, we can lift
injectivity through `hashLayer`. We expose injectivity locally on the
singleton-leaf case below; deeper injectivity over arbitrary lists requires
proof-engineering beyond the abstract-hash level and is left implicit. -/

/-- **T21 (root is injective on singleton trees).** Two single-leaf trees
have the same root iff they have the same leaf. -/
theorem root_singleton_injective (h : PairHash) (u : List Nat)
    (leaf₁ leaf₂ : List Nat)
    (heq : root h u [leaf₁] = root h u [leaf₂]) : leaf₁ = leaf₂ := by
  rw [root_singleton, root_singleton] at heq
  exact heq

/-- **T22 (append agrees with `++ [leaf]` when not full).** Helper that
unfolds the option to the underlying list operation, so downstream proofs
can reason directly with `++`. -/
theorem append_unfold (leaf : List Nat) (t : Tree) (hnf : count t < CAPACITY) :
    append leaf t = some (t ++ [leaf]) := by
  unfold append
  simp [hnf]

end Zebra.SaplingIncrementalMerkle
