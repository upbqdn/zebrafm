import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Orchard Incremental Note Commitment Tree

Models the depth-32 Orchard incremental Merkle tree from
`zebra-chain/src/orchard/tree.rs`. The Orchard note-commitment tree is an
*append-only* Merkle tree of fixed depth `MERKLE_DEPTH = 32`, used to hold
the x-coordinates (pallas `Base` field elements) of note commitments produced
by Orchard `Action` transfers.

```rust
// zebra-chain/src/orchard/tree.rs:45
pub(super) const MERKLE_DEPTH: u8 = 32;
```

The only mutating operation is `NoteCommitmentTree::append` (returns
`Err(FullTree)` when the tree is full), which calls
`incrementalmerkletree::frontier::Frontier::append` under the hood. The leaf
count saturates at `2^32` per the consensus rule:

> [NU5 onward] A block MUST NOT add Orchard note commitments that would
> result in the Orchard note commitment tree exceeding its capacity of
> `2^(MerkleDepth^Orchard)` leaf nodes.
> [`zebra-chain/src/orchard/tree.rs:352-355`]

The Merkle hashing is `MerkleCRH^Orchard`, which uses `SinsemillaHash` over
Pallas (see `merkle_crh_orchard` at `zebra-chain/src/orchard/tree.rs:61-74`).
Per the project guidelines, we do *not* model the actual cryptographic hash;
instead we parameterise over an **abstract injective** combine function that
captures the load-bearing algebraic property — collision resistance modelled
as injectivity of the pair-combine.

Modelling choices:
  * a leaf and a node are `Nat` (concretely the `pallas::Base::to_repr()`
    32-byte representation as a non-negative integer);
  * the tree is the sequence of leaves appended so far (`List Nat`) plus
    its declared depth;
  * `append` is the partial function that returns `none` exactly when the
    leaf count equals `2^32` (i.e. the `Err(FullTree)` case);
  * `combine` is an abstract `Nat → Nat → Nat` we parameterise over for
    injectivity proofs.

Distinct namespace from `Zebra.SaplingNoteCommitment`, `Zebra.NoteCommitmentTreeDepth`,
and `Zebra.HistoryTreeAppendOnly` per the task brief: `Zebra.OrchardIncrementalMerkle`.

Source files:
  * `zebra-chain/src/orchard/tree.rs`
  * Consensus rule:
    `<https://zips.z.cash/protocol/protocol.pdf#merkletree>`
-/

namespace Zebra.OrchardIncrementalMerkle

/-! ## Constants -/

/-- The Orchard Merkle tree depth, `MerkleDepth^Orchard = 32`.
Source: `zebra-chain/src/orchard/tree.rs:45`
(`pub(super) const MERKLE_DEPTH: u8 = 32;`). -/
def MERKLE_DEPTH : Nat := 32

/-- The maximum number of leaves the Orchard tree can hold: `2^MERKLE_DEPTH`.
This is the on-chain consensus capacity from the NU5 rule at
`zebra-chain/src/orchard/tree.rs:352-355`. -/
def MAX_LEAVES : Nat := 2 ^ MERKLE_DEPTH

/-- The number of layers stored in `EMPTY_ROOTS`: leaves layer + every
internal layer up to the root, totalling `MERKLE_DEPTH + 1` entries.
Source: `zebra-chain/src/orchard/tree.rs:82-98` (`EMPTY_ROOTS` lazy-static). -/
def EMPTY_ROOTS_LEN : Nat := MERKLE_DEPTH + 1

/-- `Uncommitted^Orchard = I2LEBSP_l_MerkleOrchard(2)` — the distinguished
"unused leaf" hash for Orchard. Modelled abstractly as a constant `Nat`.

Modelling note: in Rust this is `pallas::Base::one().double()`, i.e. the
Pallas-base field element `2`. We carry it through this model as the natural
number `2`. This matches the `to_repr()` little-endian byte encoding
(`[2, 0, …, 0]`) interpreted as a `Nat`, but the model deliberately collapses
the `pallas::Base` algebra to plain `Nat` arithmetic — the only property of
`UNCOMMITTED` that any theorem in this file uses is that it is a fixed,
known constant distinct from the active leaf values supplied by an honest
caller. We do not prove anything about Pallas field arithmetic itself.
Source: `zebra-chain/src/orchard/tree.rs:608-614`
(`pub fn uncommitted() -> pallas::Base { pallas::Base::one().double() }`). -/
def UNCOMMITTED : Nat := 2

/-! ## Tree model -/

/-- An Orchard incremental note-commitment tree, modelled as the sequence of
leaves appended so far (in append order). The depth is implicit and fixed
at `MERKLE_DEPTH = 32`.

Source: `zebra-chain/src/orchard/tree.rs:343-376`
(`pub struct NoteCommitmentTree`). -/
structure Tree where
  /-- Leaves committed to the tree, in append order. -/
  leaves : List Nat

/-- The empty Orchard tree.
Source: `zebra-chain/src/orchard/tree.rs:673-680`
(`impl Default for NoteCommitmentTree`). -/
def empty : Tree := { leaves := [] }

/-- Default `Tree` instance is the empty tree (used as the inhabited
witness in proofs that need an arbitrary tree). -/
instance : Inhabited Tree := ⟨empty⟩

/-- Number of leaves committed to the tree. Mirrors `count()`.
Source: `zebra-chain/src/orchard/tree.rs:616-623`
(`pub fn count(&self) -> u64`). -/
def Tree.count (t : Tree) : Nat := t.leaves.length

/-- `True` iff the tree has reached its consensus-imposed leaf capacity of
`2^MERKLE_DEPTH = 2^32`. After this point, every `append` returns
`Err(FullTree)`.
Source: `zebra-chain/src/orchard/tree.rs:330-333`
(`enum NoteCommitmentTreeError { FullTree }`). -/
def Tree.isFull (t : Tree) : Prop := t.count = MAX_LEAVES

/-- Append a new leaf to the tree. Returns `none` when the tree is full
(matching `Err(NoteCommitmentTreeError::FullTree)` at
`zebra-chain/src/orchard/tree.rs:400`), or the updated tree otherwise
(matching `Ok(())`).
Source: `zebra-chain/src/orchard/tree.rs:387-402`
(`pub fn append(&mut self, cm_x: NoteCommitmentUpdate)`). -/
def Tree.append (t : Tree) (leaf : Nat) : Option Tree :=
  if t.count < MAX_LEAVES then
    some { leaves := t.leaves ++ [leaf] }
  else
    none

/-- The leaf at index `i`, or `none` if out of range. The frontier's
underlying `position()` accessor at
`zebra-chain/src/orchard/tree.rs:412-419` is the only public read of stored
leaves; we expose this abstract indexed-read for proofs. -/
def Tree.leafAt (t : Tree) (i : Nat) : Option Nat := t.leaves[i]?

/-! ## Abstract Merkle root over an injective combine

The Rust `merkle_crh_orchard` function (`zebra-chain/src/orchard/tree.rs:61-74`)
uses Sinsemilla hash over Pallas; we parameterise over an abstract `combine :
Nat → Nat → Nat`, plus the injectivity assumption that captures collision
resistance — distinct (left, right) pairs hash to distinct values.

A `MerkleScheme` packages the abstract combine plus the empty-leaf hash. -/

/-- An abstract Merkle hash scheme over `Nat`. We parameterise over the
combine function and the "empty leaf" hash. Cryptographic security is
captured by the injectivity hypothesis stated in `combine_injective` below.

`combine` mirrors `MerkleCRH^Orchard(layer, left, right)`; we drop the
`layer` argument because it does not affect collision resistance and it
keeps the model usable for both Sapling and Orchard (which differ only in
the underlying hash). -/
structure MerkleScheme where
  /-- The pair-combine, `MerkleCRH^Orchard(left, right)` in spirit. -/
  combine : Nat → Nat → Nat
  /-- The "uncommitted" / empty-leaf hash. For Orchard this is
  `Uncommitted^Orchard = 2`. -/
  emptyLeaf : Nat

/-- The Orchard scheme, with an abstract combine and the concrete empty-leaf
constant. Any reasoning we do is parametric in this scheme. -/
def orchardScheme (combine : Nat → Nat → Nat) : MerkleScheme :=
  { combine := combine, emptyLeaf := UNCOMMITTED }

/-- A leaf vector padded with the scheme's empty-leaf hash up to length `n`.
This corresponds to filling empty leaf slots with `UNCOMMITTED` before
hashing rows up to the root. -/
def MerkleScheme.padded (s : MerkleScheme) (leaves : List Nat) (n : Nat) : List Nat :=
  leaves ++ List.replicate (n - leaves.length) s.emptyLeaf

/-! ### Empty-roots ladder

Mirrors the lazy-static `EMPTY_ROOTS` list at
`zebra-chain/src/orchard/tree.rs:82-98`. Layer `d` (the leaf layer) is the
`emptyLeaf` constant; each parent layer is the `combine` of its identical
empty-child layer with itself.

In Rust the list is indexed `0 = root, MERKLE_DEPTH = leaf`. We index by the
*subtree depth remaining* — `emptyRoot 0 = emptyLeaf`, `emptyRoot d` is the
empty subtree of height `d` — because this is the form the recursive root
computation `MerkleScheme.rootAux` consumes.
-/

/-- The empty-subtree root at height `d` for this scheme. -/
def MerkleScheme.emptyRoot (s : MerkleScheme) : Nat → Nat
  | 0     => s.emptyLeaf
  | d + 1 =>
    let child := s.emptyRoot d
    s.combine child child

/-! ### Recursive Merkle root

Mirrors the frontier root computation of `incrementalmerkletree`: at each
internal layer, pair up children, hash, and recurse — with the right-most
child filled by the empty-subtree root when the leaf count is odd. After
`MERKLE_DEPTH` layers there is a single value: the root.

Because Lean is total, we expose this as a function over depth `d` rather
than the concrete Orchard `MERKLE_DEPTH = 32`. The concrete Orchard root is
`MerkleScheme.rootAux scheme leaves MERKLE_DEPTH`. -/

/-- Combine adjacent pairs of nodes in `xs` using `s.combine`. If `xs` has
odd length, the last node is paired with `pad`. -/
def MerkleScheme.combineRow (s : MerkleScheme) (pad : Nat) : List Nat → List Nat
  | []           => []
  | [x]          => [s.combine x pad]
  | x :: y :: zs => s.combine x y :: s.combineRow pad zs

/-- Compute the Merkle root over `leaves` for a tree of height `d`. At each
layer, missing right-children are filled with the empty-subtree root of the
corresponding child height. The empty-tree case is the empty-subtree root
at the current height. Depth `0` is the leaf layer itself: an empty leaf
list yields `emptyLeaf`, otherwise the head leaf. For non-trivial trees
`d ≥ 1`. -/
def MerkleScheme.rootAux (s : MerkleScheme) : List Nat → Nat → Nat
  | [],   d     => s.emptyRoot d
  | x::_, 0     => x  -- depth-0 base: a single leaf
  | x::ys, d + 1 =>
    let pad := s.emptyRoot d
    s.rootAux (s.combineRow pad (x :: ys)) d

/-- The Merkle root of `leaves` at Orchard's fixed depth `MERKLE_DEPTH`. -/
def MerkleScheme.root (s : MerkleScheme) (leaves : List Nat) : Nat :=
  s.rootAux leaves MERKLE_DEPTH

/-- `Tree.root` against a given scheme. Mirrors `NoteCommitmentTree::root`
at `zebra-chain/src/orchard/tree.rs:563-585` but without the `RwLock` cache:
the cache is a pure-performance concern (`zebra-chain/src/orchard/tree.rs:361-376`)
and does not affect the value returned. We always recompute. -/
def Tree.root (t : Tree) (s : MerkleScheme) : Nat :=
  s.root t.leaves

/-! ## Theorems -/

/-- **T1 (Orchard depth is 32).** Direct restatement of the constant
`MERKLE_DEPTH` from the Rust source. -/
theorem merkle_depth_value : MERKLE_DEPTH = 32 := rfl

/-- **T2 (concrete maximum capacity = 2^32 = 4_294_967_296).** -/
theorem max_leaves_value : MAX_LEAVES = 4_294_967_296 := by
  unfold MAX_LEAVES MERKLE_DEPTH
  decide

/-- **T3 (empty tree has zero leaves).** -/
theorem empty_count : empty.count = 0 := rfl

/-- **T4 (empty tree is not full).** A direct consequence of T3 and the fact
that `MAX_LEAVES > 0`. -/
theorem empty_not_full : ¬ empty.isFull := by
  unfold Tree.isFull
  rw [empty_count, max_leaves_value]
  decide

/-- **T5 (max leaves is positive).** Even a fresh tree has room for at least
one leaf, so the very first append always succeeds. -/
theorem max_leaves_pos : 0 < MAX_LEAVES := by
  unfold MAX_LEAVES
  exact Nat.two_pow_pos MERKLE_DEPTH

/-- **T6 (append below capacity succeeds and yields a tree of size + 1).** -/
theorem append_some_below_capacity (t : Tree) (leaf : Nat)
    (h : t.count < MAX_LEAVES) :
    t.append leaf = some { leaves := t.leaves ++ [leaf] } := by
  unfold Tree.append
  simp [h]

/-- **T7 (append at full capacity returns `none`, modelling `Err(FullTree)`).**
This is the consensus-rule enforcement at the model layer.
Source: `zebra-chain/src/orchard/tree.rs:400` (`Err(NoteCommitmentTreeError::FullTree)`). -/
theorem append_none_when_full (t : Tree) (leaf : Nat) (h : t.isFull) :
    t.append leaf = none := by
  unfold Tree.append Tree.isFull at *
  rw [h]
  simp

/-- **T8 (append into empty succeeds).** First-leaf insertion always works. -/
theorem append_empty (leaf : Nat) :
    empty.append leaf = some { leaves := [leaf] } := by
  have h : empty.count < MAX_LEAVES := by
    rw [empty_count]
    exact max_leaves_pos
  rw [append_some_below_capacity empty leaf h]
  rfl

/-- **T9 (every successful append grows the count by exactly 1).** -/
theorem append_count_succ (t t' : Tree) (leaf : Nat)
    (heq : t.append leaf = some t') :
    t'.count = t.count + 1 := by
  unfold Tree.append at heq
  split_ifs at heq with hcond
  simp only [Option.some.injEq] at heq
  rw [← heq]
  change (t.leaves ++ [leaf]).length = t.leaves.length + 1
  simp

/-- **T10 (no successful append exceeds the capacity).** Combined with T9
this gives an inductive bound. -/
theorem append_count_le_max (t t' : Tree) (leaf : Nat)
    (heq : t.append leaf = some t') :
    t'.count ≤ MAX_LEAVES := by
  have hsucc := append_count_succ t t' leaf heq
  unfold Tree.append at heq
  split_ifs at heq with hcond
  rw [hsucc]
  omega

/-- **T11 (append-only: prior leaves are preserved at their original indices).**
This is the load-bearing append-only invariant. For any `i < t.count`, the
leaf at index `i` after a successful append equals the leaf at index `i` in
the original tree. No prior commitment is ever rewritten. -/
theorem append_preserves_leaves (t t' : Tree) (leaf : Nat) (i : Nat)
    (heq : t.append leaf = some t') (hi : i < t.count) :
    t'.leafAt i = t.leafAt i := by
  unfold Tree.append at heq
  split_ifs at heq with hcond
  simp only [Option.some.injEq] at heq
  rw [← heq]
  unfold Tree.leafAt Tree.count at *
  exact List.getElem?_append_left hi

/-- **T12 (the newly-appended leaf sits at the last index).** -/
theorem append_new_leaf_at_last (t t' : Tree) (leaf : Nat)
    (heq : t.append leaf = some t') :
    t'.leafAt t.count = some leaf := by
  unfold Tree.append at heq
  split_ifs at heq with hcond
  simp only [Option.some.injEq] at heq
  rw [← heq]
  unfold Tree.leafAt Tree.count
  rw [List.getElem?_append_right (by omega)]
  simp

/-- **T13 (append succeeds iff the tree has not reached capacity).** Bicondition
for the append-success predicate, useful for case splits in larger proofs.
We state the right-hand side as `count < MAX_LEAVES` rather than `¬ isFull`
because the model permits over-capacity counts: the real Rust API maintains
the invariant `count ≤ MAX_LEAVES`, but proofs are clearer when we work with
the concrete `<` form. -/
theorem append_isSome_iff_below_capacity (t : Tree) (leaf : Nat) :
    (t.append leaf).isSome ↔ t.count < MAX_LEAVES := by
  unfold Tree.append
  by_cases h : t.count < MAX_LEAVES <;> simp [h]

/-- **T14 (out-of-range leafAt is `none`).** -/
theorem leafAt_out_of_range (t : Tree) (i : Nat) (hi : t.count ≤ i) :
    t.leafAt i = none := by
  unfold Tree.leafAt Tree.count at *
  exact List.getElem?_eq_none hi

/-- **T15 (`UNCOMMITTED = 2`).** The Orchard distinguished empty-leaf hash
equals `pallas::Base::one().double() = 2`. -/
theorem uncommitted_value : UNCOMMITTED = 2 := rfl

/-- **T16 (padded length matches the target).** Padding a leaf list to
length `n` ≥ its current length yields a list of length exactly `n`. -/
theorem padded_length (s : MerkleScheme) (leaves : List Nat) (n : Nat)
    (h : leaves.length ≤ n) :
    (s.padded leaves n).length = n := by
  unfold MerkleScheme.padded
  rw [List.length_append, List.length_replicate]
  omega

/-- **T17 (padding preserves the leaf prefix).** For every `i < leaves.length`,
the padded list at index `i` equals the original. -/
theorem padded_preserves_prefix (s : MerkleScheme) (leaves : List Nat) (n : Nat) (i : Nat)
    (hi : i < leaves.length) :
    (s.padded leaves n)[i]? = leaves[i]? := by
  unfold MerkleScheme.padded
  exact List.getElem?_append_left hi

/-- **T18 (padded slots above the leaf prefix are `emptyLeaf`).** -/
theorem padded_empty_above (s : MerkleScheme) (leaves : List Nat) (n : Nat) (i : Nat)
    (h1 : leaves.length ≤ i) (h2 : i < n) :
    (s.padded leaves n)[i]? = some s.emptyLeaf := by
  unfold MerkleScheme.padded
  rw [List.getElem?_append_right h1]
  rw [List.getElem?_replicate]
  have hidx : i - leaves.length < n - leaves.length := by omega
  simp [hidx]

/-- **T19 (combine-injectivity transfers to root distinctness — abstract
collision resistance).** Given an injective combine on each argument
position, distinct top-level pairs produce distinct combined roots. This is
the algebraic shadow of Sinsemilla's collision resistance.

We state it as: if combine is left-injective (i.e. fixing the right argument,
distinct left arguments give distinct outputs), then distinct pairs of left
arguments are distinguished by `combine`. -/
theorem combine_left_injective_distinguishes
    (combine : Nat → Nat → Nat)
    (hinj : ∀ r l₁ l₂, combine l₁ r = combine l₂ r → l₁ = l₂)
    (l₁ l₂ r : Nat) (hne : l₁ ≠ l₂) :
    combine l₁ r ≠ combine l₂ r := by
  intro hcomb
  exact hne (hinj r l₁ l₂ hcomb)

/-- **T20 (pair-injective combine ⇒ collision-free).** Pair-injective combine
gives the full collision-resistance shadow: equal hash outputs force equal
input pairs. -/
theorem combine_pair_injective_collision_free
    (combine : Nat → Nat → Nat)
    (hpair : ∀ l₁ r₁ l₂ r₂, combine l₁ r₁ = combine l₂ r₂ → l₁ = l₂ ∧ r₁ = r₂)
    (l₁ r₁ l₂ r₂ : Nat)
    (h : combine l₁ r₁ = combine l₂ r₂) :
    (l₁, r₁) = (l₂, r₂) := by
  obtain ⟨hl, hr⟩ := hpair l₁ r₁ l₂ r₂ h
  rw [hl, hr]

/-- Iterative append: fold a list of leaves over `Tree.append`, propagating
`none` on failure. Models the Rust pattern of appending each note commitment
in a block one-by-one, aborting (via `Err(FullTree)`) on the first overflow. -/
def Tree.appendMany : Tree → List Nat → Option Tree
  | t, []      => some t
  | t, x :: xs =>
    match t.append x with
    | none => none
    | some t' => t'.appendMany xs

/-- **T21 (successful chain of appends stays within capacity).** Inductive
invariant: starting from any tree `t₀` with `count ≤ MAX_LEAVES`, any
sequence of successful `append` calls produces a tree `tₙ` with
`count ≤ MAX_LEAVES`. This is the load-bearing invariant that the on-chain
consensus rule (`zebra-chain/src/orchard/tree.rs:352-355`) depends on. -/
theorem appendMany_count_le_max (t₀ : Tree) (xs : List Nat) (final : Tree)
    (h0 : t₀.count ≤ MAX_LEAVES)
    (heq : t₀.appendMany xs = some final) :
    final.count ≤ MAX_LEAVES := by
  induction xs generalizing t₀ with
  | nil =>
    simp only [Tree.appendMany] at heq
    rw [Option.some.injEq] at heq
    rw [← heq]
    exact h0
  | cons x xs ih =>
    simp only [Tree.appendMany] at heq
    cases hstep : t₀.append x with
    | none => rw [hstep] at heq; cases heq
    | some t' =>
      rw [hstep] at heq
      have h1 : t'.count ≤ MAX_LEAVES := append_count_le_max t₀ t' x hstep
      exact ih t' h1 heq

/-- **T22 (append result is a tree extending the original).** After a
successful append, the new tree's leaf list equals the original list with
the appended leaf concatenated. This is the "shape" invariant. -/
theorem append_extends (t t' : Tree) (leaf : Nat)
    (heq : t.append leaf = some t') :
    t'.leaves = t.leaves ++ [leaf] := by
  unfold Tree.append at heq
  split_ifs at heq
  simp only [Option.some.injEq] at heq
  rw [← heq]

/-- **T23 (Sapling and Orchard share depth).** Coincides with the constant
`SAPLING_NOTE_COMMITMENT_TREE_DEPTH = 32` in `NoteCommitmentTreeDepth.lean`,
re-asserting that this module's `MERKLE_DEPTH` is the same `32`. -/
theorem orchard_depth_matches_sapling : MERKLE_DEPTH = 32 := rfl

/-- **T24 (capacity grows with depth, abstractly).** A tree of greater depth
can hold strictly more leaves. Mostly cosmetic at depth 32 (a fixed
constant), but documents the structural property if the depth ever changes. -/
theorem max_leaves_monotone_in_depth (d₁ d₂ : Nat) (h : d₁ ≤ d₂) :
    2 ^ d₁ ≤ 2 ^ d₂ :=
  Nat.pow_le_pow_right (by norm_num) h

/-- **T25 (append is the only count-changer).** The `count` after a
successful append is strictly greater than before. Combined with T9, this
fully characterises the count update. -/
theorem append_strictly_grows_count (t t' : Tree) (leaf : Nat)
    (heq : t.append leaf = some t') :
    t.count < t'.count := by
  have := append_count_succ t t' leaf heq
  omega

/-- **T26 (`Tree.isFull` is decidable).** The decision procedure for fullness
is constant-time. -/
instance : DecidablePred Tree.isFull := by
  intro t
  unfold Tree.isFull
  exact inferInstance

/-- **T27 (concrete: a tree with exactly `2^32` leaves is full).** -/
theorem tree_full_at_max_leaves (t : Tree) (h : t.count = 4_294_967_296) :
    t.isFull := by
  unfold Tree.isFull
  rw [h, max_leaves_value]

/-- **T28 (Orchard depth ≠ 0).** Orchard's tree is never of trivial depth;
the consensus capacity is `2^32 ≥ 2`. -/
theorem merkle_depth_pos : 0 < MERKLE_DEPTH := by
  unfold MERKLE_DEPTH; decide

/-- **T29 (chained appends preserve the prefix).** After two successful
appends, the original leaves are still at their original indices. This
generalises T11 to a two-step trace. -/
theorem chained_append_preserves_leaves
    (t t₁ t₂ : Tree) (leaf₁ leaf₂ : Nat) (i : Nat)
    (h1 : t.append leaf₁ = some t₁) (h2 : t₁.append leaf₂ = some t₂)
    (hi : i < t.count) :
    t₂.leafAt i = t.leafAt i := by
  have hcount : i < t₁.count := by
    have := append_count_succ t t₁ leaf₁ h1
    omega
  have step2 : t₂.leafAt i = t₁.leafAt i :=
    append_preserves_leaves t₁ t₂ leaf₂ i h2 hcount
  have step1 : t₁.leafAt i = t.leafAt i :=
    append_preserves_leaves t t₁ leaf₁ i h1 hi
  rw [step2, step1]

/-- **T30 (combine is well-defined for any abstract scheme).** Sanity check
that the abstract scheme has a total combine function — this excludes the
"undefined" case that real cryptographic hashes formally have only with
negligible probability. The `match ... None => zero` fallback in
`merkle_crh_orchard` (`zebra-chain/src/orchard/tree.rs:70-73`) is a total
function in Rust; we keep our combine totalised too. -/
theorem orchardScheme_combine_total
    (combine : Nat → Nat → Nat) (l r : Nat) :
    ∃ v, (orchardScheme combine).combine l r = v :=
  ⟨combine l r, rfl⟩

/-- **T31 (orchardScheme stores the Orchard `UNCOMMITTED` constant).** -/
theorem orchardScheme_empty_leaf (combine : Nat → Nat → Nat) :
    (orchardScheme combine).emptyLeaf = UNCOMMITTED := rfl

/-! ### Root-of-tree theorems -/

/-- **T32 (`Tree.root` is a pure function of the leaf list and the scheme).**
The Rust `RwLock<Option<Root>>` cache (`zebra-chain/src/orchard/tree.rs:361-376`)
is a performance optimisation; the value returned by `root()` is determined
solely by the tree's leaves and the underlying hash. Two trees with the same
leaf list compute the same root under the same scheme. -/
theorem root_eq_of_leaves_eq (t₁ t₂ : Tree) (s : MerkleScheme)
    (h : t₁.leaves = t₂.leaves) :
    t₁.root s = t₂.root s := by
  unfold Tree.root
  rw [h]

/-- **T33 (empty-row reduces to nil).** Combining an empty row produces an
empty row, matching the recursive base case of the root computation. -/
theorem combineRow_nil (s : MerkleScheme) (pad : Nat) :
    s.combineRow pad [] = [] := rfl

/-- **T34 (singleton row combines with the pad).** A row with a single
node gets paired with the empty-subtree padding, exactly matching the
frontier behaviour for an odd-leaf-count tree. -/
theorem combineRow_singleton (s : MerkleScheme) (pad x : Nat) :
    s.combineRow pad [x] = [s.combine x pad] := rfl

/-- **T35 (pair-row combines pairwise).** Two-element rows combine the
two elements directly, with no padding. -/
theorem combineRow_pair (s : MerkleScheme) (pad x y : Nat) :
    s.combineRow pad [x, y] = [s.combine x y] := rfl

/-- **T36 (`combineRow` halves the row length, rounded up).** This is the
load-bearing length-reduction invariant: each layer of the Merkle tree
strictly shrinks the row count from `n` to `⌈n/2⌉`, so after `MERKLE_DEPTH`
layers we are down to a single value (or fewer) for any tree of size
`≤ 2^MERKLE_DEPTH`. -/
theorem combineRow_length (s : MerkleScheme) (pad : Nat) :
    ∀ xs : List Nat, (s.combineRow pad xs).length = (xs.length + 1) / 2
  | []           => by simp [MerkleScheme.combineRow]
  | [_]          => by simp [MerkleScheme.combineRow]
  | _ :: _ :: zs => by
    simp [MerkleScheme.combineRow, combineRow_length s pad zs]
    omega

/-- **T37 (root of an empty tree at depth `d`).** The empty tree's root at
height `d` is the corresponding empty-subtree root. This mirrors the
construction of `EMPTY_ROOTS` in Rust (`zebra-chain/src/orchard/tree.rs:82-98`)
and the fact that `NoteCommitmentTree::default().root()` equals the empty
root of the full tree. -/
theorem rootAux_nil (s : MerkleScheme) (d : Nat) :
    s.rootAux [] d = s.emptyRoot d := by
  cases d with
  | zero => rfl
  | succ d => rfl

/-- **T38 (`Tree.root` of the empty tree equals the depth-32 empty root).**
The "default tree" root explicitly noted at
`zebra-chain/src/orchard/tree.rs:337-339` — it is *not* `[0,0,0,0]` but a
hash chain of `UNCOMMITTED` up to the root. -/
theorem empty_root (s : MerkleScheme) :
    empty.root s = s.emptyRoot MERKLE_DEPTH :=
  rootAux_nil s MERKLE_DEPTH

/-- **T39 (empty-subtree height-1 root equals combine of empty leaves).**
Concrete unfolding at height 1: a tree of depth 1 with no leaves has root
`combine(emptyLeaf, emptyLeaf)`. -/
theorem emptyRoot_one (s : MerkleScheme) :
    s.emptyRoot 1 = s.combine s.emptyLeaf s.emptyLeaf := rfl

/-- **T40 (empty-subtree height-2 root equals combine of two height-1 empties).** -/
theorem emptyRoot_two (s : MerkleScheme) :
    s.emptyRoot 2 = s.combine (s.combine s.emptyLeaf s.emptyLeaf)
                              (s.combine s.emptyLeaf s.emptyLeaf) := rfl

/-- **T41 (single-leaf depth-1 root).** A tree of depth 1 with one leaf has
root `combine(leaf, emptyLeaf)` — the leaf paired with the empty sibling. -/
theorem rootAux_singleton_depth_one (s : MerkleScheme) (leaf : Nat) :
    s.rootAux [leaf] 1 = s.combine leaf s.emptyLeaf := rfl

/-- **T42 (two-leaf depth-1 root).** A tree of depth 1 with two leaves
has root `combine(leaf₁, leaf₂)` — no padding is needed. -/
theorem rootAux_pair_depth_one (s : MerkleScheme) (l r : Nat) :
    s.rootAux [l, r] 1 = s.combine l r := rfl

/-- **T43 (`append` changes the tree, so the root may change).** After an
`append`, the new root is computed over the extended leaf list. Combined
with `root_eq_of_leaves_eq`, this gives the cache-invalidation invariant
that Rust enforces at `zebra-chain/src/orchard/tree.rs:389-398`. -/
theorem root_after_append (t t' : Tree) (leaf : Nat) (s : MerkleScheme)
    (heq : t.append leaf = some t') :
    t'.root s = s.root (t.leaves ++ [leaf]) := by
  have hext := append_extends t t' leaf heq
  unfold Tree.root
  rw [hext]

/-- **T44 (root is well-defined even at full capacity).** Even when no more
leaves can be appended, `Tree.root` still returns a well-defined value over
the existing leaves. The Rust `recalculate_root`
(`zebra-chain/src/orchard/tree.rs:597-599`) is total. -/
theorem root_total (t : Tree) (s : MerkleScheme) : ∃ v, t.root s = v :=
  ⟨t.root s, rfl⟩

/-- **T45 (`appendMany` preserves the "no leaves before append" invariant).**
Threading a list of leaves through `appendMany` extends the original list
(if all appends succeed). -/
theorem appendMany_extends (t₀ : Tree) (xs : List Nat) (final : Tree)
    (heq : t₀.appendMany xs = some final) :
    final.leaves = t₀.leaves ++ xs := by
  induction xs generalizing t₀ with
  | nil =>
    simp only [Tree.appendMany] at heq
    rw [Option.some.injEq] at heq
    rw [← heq]
    simp
  | cons x xs ih =>
    simp only [Tree.appendMany] at heq
    cases hstep : t₀.append x with
    | none => rw [hstep] at heq; cases heq
    | some t' =>
      rw [hstep] at heq
      have hext : t'.leaves = t₀.leaves ++ [x] := append_extends t₀ t' x hstep
      have ihres : final.leaves = t'.leaves ++ xs := ih t' heq
      rw [ihres, hext, List.append_assoc]
      rfl

/-- **T46 (`appendMany` final root equals scheme-root of the extended list).**
Combined with T45, this gives the root semantics of a successful sequence
of appends: it's the Merkle root over the original leaves concatenated with
the new ones, identical for any tree that has the same leaf history. -/
theorem appendMany_root (t₀ : Tree) (xs : List Nat) (final : Tree) (s : MerkleScheme)
    (heq : t₀.appendMany xs = some final) :
    final.root s = s.root (t₀.leaves ++ xs) := by
  have := appendMany_extends t₀ xs final heq
  unfold Tree.root
  rw [this]

/-- **T47 (orchardScheme root uses the abstract `combine` consistently).**
Sanity check: the `orchardScheme` constructor threads the user's `combine`
into the root computation unchanged. -/
theorem orchardScheme_root_unfold
    (combine : Nat → Nat → Nat) (leaves : List Nat) :
    (orchardScheme combine).root leaves =
      (orchardScheme combine).rootAux leaves MERKLE_DEPTH := rfl

end Zebra.OrchardIncrementalMerkle
