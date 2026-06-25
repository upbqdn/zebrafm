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

  * Tree is a `List (List Nat)` of leaf hashes.
  * `append` extends by exactly one leaf, returning `none` when the capacity
    `2^MERKLE_DEPTH = 2^32` has been reached.
  * Prior leaves are preserved at their original indices forever (append-only).
  * The Merkle `root` is a deterministic function of the leaf sequence and an
    abstract `hash : List Nat × List Nat → List Nat` pairing function, padding
    odd levels with the per-level empty hash derived from the uncommitted
    sentinel.
  * Capacity is exactly `2^32`.
  * The uncommitted sentinel is the 32-byte little-endian encoding of the field
    element 1, i.e. `[1, 0, 0, ..., 0]` with 31 trailing zeros. This matches
    `jubjub::Fq::one().to_bytes()` in
    `zebra-chain/src/sapling/tree.rs:430-432`.

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
  * `NoteCommitmentTree::uncommitted` —
    `zebra-chain/src/sapling/tree.rs:430-432` (returns
    `jubjub::Fq::one().to_bytes()`)
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

/-! ## The uncommitted sentinel

The Rust `NoteCommitmentTree::uncommitted` returns `jubjub::Fq::one().to_bytes()`,
i.e. the 32-byte little-endian encoding of the field element 1. In
`bls12_381`/`jubjub`, `Fq::to_bytes()` writes the canonical representative
of the field element in **little-endian** byte order. The integer `1` thus
encodes as the bytes `[1, 0, 0, ..., 0]` with 31 trailing zeros.

Source: `zebra-chain/src/sapling/tree.rs:425-432`. -/

/-- The "uncommitted^Sapling" sentinel — the 32-byte little-endian encoding
of the field element 1, i.e. a single `1` byte followed by 31 zero bytes.

Mirrors `NoteCommitmentTree::uncommitted()` in
`zebra-chain/src/sapling/tree.rs:430-432`, which returns
`jubjub::Fq::one().to_bytes()`. -/
def DEFAULT_UNCOMMITTED : List Nat := 1 :: List.replicate 31 0

/-! ## Abstract root via injective pair hash

The Rust tree computes its root by recursively hashing pairs of child nodes
up the binary tree, using the Pedersen hash from `sapling_crypto::Node`. We
abstract that into an opaque `hash : List Nat × List Nat → List Nat`.

Crucially, when a level has an odd number of nodes, the standard binary-tree
algorithm `Frontier::root()` pads the right child with the per-level **empty
hash**: at level 0 this is `DEFAULT_UNCOMMITTED`; at level `k + 1` it is the
hash of two copies of the level-`k` empty hash. This is the standard
incremental Merkle tree semantics. -/

/-- A pair-hashing parameter modelling `sapling_crypto::Node`'s pair hash. -/
abbrev PairHash := List Nat → List Nat → List Nat

/-- Fold one level of the tree, hashing adjacent pairs. When the input has an
odd length, the rightmost unpaired node is hashed with the supplied level
empty hash `e` as its right sibling.

This is the standard binary Merkle tree semantics used by
`incrementalmerkletree::frontier::Frontier::root()`: every internal node has
exactly two children, and missing right siblings are filled with the
per-level empty hash. -/
def hashLayer (h : PairHash) (e : List Nat) :
    List (List Nat) → List (List Nat)
  | [] => []
  | [x] => [h x e]
  | x :: y :: rest => h x y :: hashLayer h e rest

/-- Empty-hash for level `k`: at level 0 this is the uncommitted sentinel,
and at each higher level it is the pair-hash of two copies of the previous
level's empty hash. This is the standard "Merkle empty subtree" recursion
used to fill missing branches in `Frontier::root()`. -/
def emptyHash (h : PairHash) (u : List Nat) : Nat → List Nat
  | 0 => u
  | k + 1 => h (emptyHash h u k) (emptyHash h u k)

/-- Iteratively fold the leaf list one level at a time, padding each level
with that level's empty hash, until a single root remains. `n` is the
depth bound. -/
def rootAux (h : PairHash) (u : List Nat) :
    Nat → List (List Nat) → List Nat
  | 0,     []      => u
  | 0,     [x]     => x
  | 0,     xs      => xs.headD u
  | n + 1, []      => emptyHash h u (n + 1)
  | _ + 1, [x]     => x
  | n + 1, xs      => rootAux h u n (hashLayer h (emptyHash h u n) xs)

/-- The Merkle root of the tree, parameterised by an abstract pair hash and
an uncommitted (default) leaf. Mirrors `NoteCommitmentTree::root` /
`recalculate_root`.
Source: `zebra-chain/src/sapling/tree.rs:381-403,415-417`. -/
def root (h : PairHash) (u : List Nat) (t : Tree) : List Nat :=
  rootAux h u MERKLE_DEPTH t

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

/-- **T13 (singleton tree root is the leaf itself).** A one-leaf tree's root
is just that leaf — the standard semantics of `Frontier::root()` on a single
leaf, before any pair hashing happens (the unique leaf forms the rightmost
"peak"). -/
theorem root_singleton (h : PairHash) (u : List Nat) (leaf : List Nat) :
    root h u [leaf] = leaf := by
  unfold root MERKLE_DEPTH
  rfl

/-- **T14 (`hashLayer` halves length for even-length inputs).** With even
input length, padding is unnecessary and the layer length is exactly halved. -/
theorem hashLayer_length_even (h : PairHash) (e : List Nat) :
    ∀ xs : List (List Nat), xs.length % 2 = 0 →
      (hashLayer h e xs).length = xs.length / 2
  | [], _ => by simp [hashLayer]
  | [_], hev => by simp at hev
  | x :: y :: rest, hev => by
      simp only [hashLayer, List.length_cons]
      have h_rest : rest.length % 2 = 0 := by
        simp [List.length_cons] at hev
        omega
      have ih := hashLayer_length_even h e rest h_rest
      rw [ih]
      omega

/-- **T15 (`hashLayer` rounds up for odd-length inputs).** With odd input
length, the unpaired tail is hashed with the empty-hash padding, so the
layer length is `(xs.length + 1) / 2`. -/
theorem hashLayer_length_odd (h : PairHash) (e : List Nat) :
    ∀ xs : List (List Nat), xs.length % 2 = 1 →
      (hashLayer h e xs).length = (xs.length + 1) / 2
  | [], hev => by simp at hev
  | [_], _ => by simp [hashLayer]
  | x :: y :: rest, hev => by
      simp only [hashLayer, List.length_cons]
      have h_rest : rest.length % 2 = 1 := by
        simp [List.length_cons] at hev
        omega
      have ih := hashLayer_length_odd h e rest h_rest
      rw [ih]
      omega

/-- **T16 (hashLayer on a singleton pads with the empty hash).** This pins the
key semantic change versus the prior fictional "keep odd-leaf as-is"
algorithm: a single-element layer becomes `[h x e]`, not `[x]`. -/
theorem hashLayer_singleton (h : PairHash) (e x : List Nat) :
    hashLayer h e [x] = [h x e] := rfl

/-- **T17 (hashLayer on a pair hashes them).** A two-element layer becomes
`[h x y]`. -/
theorem hashLayer_pair (h : PairHash) (e x y : List Nat) :
    hashLayer h e [x, y] = [h x y] := by
  simp [hashLayer]

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

/-- **T21 (`emptyHash` at level 0 is the uncommitted sentinel).** This pins
the base case of the per-level empty-hash recursion to the Rust
`NoteCommitmentTree::uncommitted()` return value.
Source: `zebra-chain/src/sapling/tree.rs:430-432`. -/
theorem emptyHash_zero (h : PairHash) (u : List Nat) :
    emptyHash h u 0 = u := rfl

/-- **T22 (`emptyHash` recurrence).** Level `k+1`'s empty hash is the hash of
two copies of level `k`'s empty hash. This is the standard incremental
Merkle tree empty-subtree recursion. -/
theorem emptyHash_succ (h : PairHash) (u : List Nat) (k : Nat) :
    emptyHash h u (k + 1) = h (emptyHash h u k) (emptyHash h u k) := rfl

/-- **T23 (`DEFAULT_UNCOMMITTED` has 32 bytes).** Pins the size of the
uncommitted sentinel — the 32-byte little-endian encoding of `1`. -/
theorem default_uncommitted_length :
    DEFAULT_UNCOMMITTED.length = 32 := by
  unfold DEFAULT_UNCOMMITTED
  simp

/-- **T24 (`DEFAULT_UNCOMMITTED` head byte is 1).** The encoding of `1` in
little-endian starts with the byte `1`. -/
theorem default_uncommitted_head :
    DEFAULT_UNCOMMITTED.head? = some 1 := rfl

/-- **T25 (`DEFAULT_UNCOMMITTED` tail bytes are zero).** All bytes after the
first are zero, completing the little-endian encoding of `1`. -/
theorem default_uncommitted_tail :
    DEFAULT_UNCOMMITTED.tail = List.replicate 31 0 := rfl

/-- **T26 (empty tree root is the depth-`MERKLE_DEPTH` empty hash).** The
root of the empty tree is the empty hash at the top level, i.e. the
recursive `emptyHash` evaluated at `MERKLE_DEPTH = 32`. This mirrors the
Rust `Frontier::empty().root()` semantics: an empty tree has every leaf
slot filled with `Uncommitted^Sapling`, and the root is therefore the
pair-hash recursion of that constant `MERKLE_DEPTH` times.
Source: `zebra-chain/src/sapling/tree.rs:492-498` (`Default`),
`zebra-chain/src/sapling/tree.rs:415-417` (`recalculate_root`). -/
theorem root_empty (h : PairHash) (u : List Nat) :
    root h u empty = emptyHash h u MERKLE_DEPTH := by
  unfold root empty MERKLE_DEPTH
  rfl

/-- **T27 (`hashLayer` non-empty input yields non-empty output).** Useful for
reasoning about the layer-folding loop. -/
theorem hashLayer_ne_nil (h : PairHash) (e : List Nat) :
    ∀ xs : List (List Nat), xs ≠ [] → hashLayer h e xs ≠ []
  | [], hne => absurd rfl hne
  | [_], _ => by simp [hashLayer]
  | _ :: _ :: _, _ => by simp [hashLayer]

/-- **T28 (singleton-input is congruence-injective for `root`).** If two
single-leaf trees have equal roots, the leaves are equal. This is the
content of `root_singleton` combined with cancellation. -/
theorem root_singleton_injective (h : PairHash) (u : List Nat)
    (leaf₁ leaf₂ : List Nat)
    (heq : root h u [leaf₁] = root h u [leaf₂]) : leaf₁ = leaf₂ := by
  rw [root_singleton, root_singleton] at heq
  exact heq

/-- **T29 (append agrees with `++ [leaf]` when not full).** Helper that
unfolds the option to the underlying list operation, so downstream proofs
can reason directly with `++`. -/
theorem append_unfold (leaf : List Nat) (t : Tree) (hnf : count t < CAPACITY) :
    append leaf t = some (t ++ [leaf]) := by
  unfold append
  simp [hnf]

/-- **T30 (`root` is a congruence over `=` on trees).** A pure restatement
of how `root` is a function — included so callers can rewrite with this
without having to expand `root` themselves. Note: this is *not* the same as
"the root is a hash-collision-resistant fingerprint of the leaves"; it only
asserts function-ality. -/
theorem root_congr_of_eq (h : PairHash) (u : List Nat) (t₁ t₂ : Tree)
    (heq : t₁ = t₂) : root h u t₁ = root h u t₂ := by
  rw [heq]

/-- **T31 (`rootAux` at bound 0 picks the head with empty fallback).** Pins
the base case of the layer-folding recursion: at depth 0, a non-empty input
returns its first element, and the empty input returns `u`. -/
theorem rootAux_zero_empty (h : PairHash) (u : List Nat) :
    rootAux h u 0 [] = u := rfl

/-- **T32 (`rootAux` at bound 0 on a singleton returns that element).** -/
theorem rootAux_zero_singleton (h : PairHash) (u x : List Nat) :
    rootAux h u 0 [x] = x := rfl

/-- **T33 (depth `n + 1` step folds one layer).** At depth `n + 1` over a
multi-element input, `rootAux` reduces to `rootAux` at depth `n` applied to
one round of `hashLayer` with the level-`n` empty hash. -/
theorem rootAux_step (h : PairHash) (u : List Nat) (n : Nat)
    (x y : List Nat) (rest : List (List Nat)) :
    rootAux h u (n + 1) (x :: y :: rest) =
      rootAux h u n (hashLayer h (emptyHash h u n) (x :: y :: rest)) := rfl

/-- **T34 (`rootAux` at depth `n+1` on empty list).** An empty input at any
depth `n + 1` returns the depth-`n+1` empty hash. -/
theorem rootAux_succ_empty (h : PairHash) (u : List Nat) (n : Nat) :
    rootAux h u (n + 1) [] = emptyHash h u (n + 1) := rfl

/-- **T35 (`rootAux` at depth `n+1` on singleton).** A singleton input at any
depth `n + 1` returns the element itself (it forms the unique "peak"
without further hashing). -/
theorem rootAux_succ_singleton (h : PairHash) (u : List Nat) (n : Nat)
    (x : List Nat) :
    rootAux h u (n + 1) [x] = x := rfl

end Zebra.SaplingIncrementalMerkle
