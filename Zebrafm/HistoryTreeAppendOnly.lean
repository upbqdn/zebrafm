import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Zebrafm.NetworkUpgrade

/-!
# History tree append-only invariant
(`zebra-chain/src/history_tree.rs`, `zebra-chain/src/primitives/zcash_history.rs`)

The Zcash chain history tree (ZIP-221) is a Merkle Mountain Range over the
block-by-block leaves of the chain. The Rust implementation in
`zebra-chain/src/history_tree.rs` exposes only one mutating operation,
`NonEmptyHistoryTree::push` (`history_tree.rs:222`), which delegates to
`primitives/zcash_history.rs::Tree::append_leaf` (`zcash_history.rs:176`).
There is no public truncation or rewrite API outside of the activation-block
reset path that `push` performs internally.

The full Merkle Mountain Range structure (peak pruning, peak rebuilding,
internal-node hashing) is out of scope for this arithmetic module; we model
only the *append-only* abstract property over the leaf sequence, together
with the structural invariants and panics enforced by `push`:

  * The wrapper `HistoryTree` is `Option<NonEmptyHistoryTree>` (`history_tree.rs:449`).
    It is `none` before Heartwood activation; thereafter it is `some t`. There
    is no public API to go back to `none`.
  * A `NonEmptyHistoryTree` carries a `network_upgrade` tag (`history_tree.rs:61`).
    `Tree::append_leaf` *panics* (`zcash_history.rs:187-192`) if the incoming
    block's network upgrade differs from the tag.
  * `push` enforces that the new block's height is `current_height + 1`
    (`history_tree.rs:235-240`); a panic otherwise.
  * When the new block's height triggers a network upgrade (`history_tree.rs:243-251`),
    `push` *resets* the tree by replacing `*self` with `from_block`, instead
    of calling `append_leaf`. So the leaf set is not appended to across the
    boundary — it restarts.
  * `from_block` *panics* for pre-Heartwood upgrades (`history_tree.rs:159-164`).

Citations:
  * `Tree::append_leaf` —
    `zebra-chain/src/primitives/zcash_history.rs:176-211` (NU panic at 187-192)
  * `NonEmptyHistoryTree::push` —
    `zebra-chain/src/history_tree.rs:222-269`
    (height panic at 235-240; activation reset at 243-251)
  * `NonEmptyHistoryTree::from_block` —
    `zebra-chain/src/history_tree.rs:148-210` (pre-Heartwood panic at 159-164)
  * `HistoryTree` (wrapper) —
    `zebra-chain/src/history_tree.rs:449`
-/

namespace Zebra.HistoryTreeAppendOnly

open Zebra.NetworkUpgrade

/-- The network upgrades that admit a history tree. Pre-Heartwood activations
have no history tree (`history_tree.rs:159-164` panics for them). -/
def NU.heartwoodOrLater (nu : NU) : Prop :=
  nu.toOrd ≥ NU.heartwood.toOrd

instance : DecidablePred NU.heartwoodOrLater := by
  intro nu; unfold NU.heartwoodOrLater
  exact Nat.decLe _ _

/-- Abstract leaf hash (the librustzcash `NodeData` payload of a leaf entry,
modelled as a `Nat` here — we do not interpret the underlying bytes). -/
abbrev Leaf := Nat

/-- A non-empty history tree, mirroring `NonEmptyHistoryTree`
(`history_tree.rs:59-73`). The Rust struct carries `network`, `network_upgrade`,
`inner`, `size`, `peaks`, `current_height`. For the append-only fragment we
keep the four state fields that *the public API observes or panics on*:

  * `nu`        — the `network_upgrade` tag (the panic key in
                  `zcash_history.rs:187-192`),
  * `startHeight` — the height of the first leaf in this tree segment
                    (Rust uses `current_height - size + 1` implicitly via
                    `from_block` and the height-monotonicity invariant of
                    `push`),
  * `leaves`    — the sequence of committed leaf hashes (the MMR's leaf
                  count drives `size` in Rust; the leaf sequence is the only
                  thing the append-only property is about),
  * `currentHeight` — the height of the most-recently-appended leaf
                      (`history_tree.rs:72`).

We do not carry the `peaks` map or the internal MMR cursor; those are
implementation details of the librustzcash `zcash_history` MMR, not part of
the append-only semantic contract. -/
structure NonEmptyHistoryTree where
  nu : NU
  startHeight : Nat
  leaves : List Leaf
  currentHeight : Nat
  /-- A `NonEmptyHistoryTree` is non-empty by construction (`from_block`
  starts at `size = 1`; `push` only ever increases `size`). -/
  nonempty : leaves ≠ []
  /-- The current height is the start height plus the (zero-based) index of
  the last leaf. Equivalent to Rust's invariant `current_height =
  start_height + size - 1` when no peak pruning has occurred. -/
  heightConsistent : currentHeight + 1 = startHeight + leaves.length

/-- The Heartwood-or-later precondition is recorded *outside* the struct so
that we can talk about both well-formed trees and pre-Heartwood "no tree
exists" states uniformly. The struct above doesn't itself enforce the
precondition — the *constructors* (`fromBlock`, `push`) do. -/
def NonEmptyHistoryTree.wellFormed (t : NonEmptyHistoryTree) : Prop :=
  NU.heartwoodOrLater t.nu

/-- The wrapper type from `history_tree.rs:449`:
`pub struct HistoryTree(Option<NonEmptyHistoryTree>)`.
Pre-Heartwood this is `none`; post-Heartwood it is `some _`. -/
def HistoryTree := Option NonEmptyHistoryTree

/-- The default (empty, pre-Heartwood) `HistoryTree`. Mirrors
`HistoryTree::default()` which produces `HistoryTree(None)`. -/
def HistoryTree.empty : HistoryTree := none

/-- The canonical successful `fromBlock` result struct. Factored out as a
separate definition so that theorems can refer to it without re-stating the
proofs of `nonempty` and `heightConsistent`. -/
def fromBlockResult (nu : NU) (height : Nat) (leaf : Leaf) :
    NonEmptyHistoryTree :=
  { nu := nu
    startHeight := height
    leaves := [leaf]
    currentHeight := height
    nonempty := by simp
    heightConsistent := by simp }

/-- The canonical successful `appendLeaf` result struct. -/
def appendLeafResult (t : NonEmptyHistoryTree) (newLeaf : Leaf) :
    NonEmptyHistoryTree :=
  { nu := t.nu
    startHeight := t.startHeight
    leaves := t.leaves ++ [newLeaf]
    currentHeight := t.currentHeight + 1
    nonempty := by intro h; simpa using congrArg List.length h
    heightConsistent := by
      have hh := t.heightConsistent
      simp [List.length_append]
      omega }

/-- Create a single-leaf `NonEmptyHistoryTree` from a block. Mirrors
`NonEmptyHistoryTree::from_block` (`history_tree.rs:148-210`). The Rust
function *panics* for pre-Heartwood NUs (`history_tree.rs:159-164`); we
model that as an `Option` returning `none` when the NU is pre-Heartwood. -/
def fromBlock (nu : NU) (height : Nat) (leaf : Leaf) :
    Option NonEmptyHistoryTree :=
  if NU.heartwoodOrLater nu then some (fromBlockResult nu height leaf) else none

/-- Append a single leaf to an existing tree, without changing the NU. Mirrors
the *non-reset* branch of `NonEmptyHistoryTree::push` (`history_tree.rs:253-268`)
which calls `Tree::append_leaf` (`zcash_history.rs:176-211`). The Rust
`Tree::append_leaf` panics (`zcash_history.rs:187-192`) when the block's NU
differs from `self.network_upgrade`; we model that as a guarded `Option`
returning `none` on NU mismatch. The height-contiguity panic
(`history_tree.rs:235-240`, `prev_height + 1 == new_height`) is also
modelled here. -/
def appendLeaf (t : NonEmptyHistoryTree) (newNU : NU) (newHeight : Nat)
    (newLeaf : Leaf) : Option NonEmptyHistoryTree :=
  if newNU = t.nu ∧ newHeight = t.currentHeight + 1 then
    some (appendLeafResult t newLeaf)
  else
    none

/-- Top-level `push`. Mirrors `NonEmptyHistoryTree::push` (`history_tree.rs:222-269`)
when called on a wrapped `HistoryTree`:

  * If the wrapped tree is `none` (pre-Heartwood) and the new block is
    Heartwood-or-later, this is the *creation* path — it would correspond to
    `HistoryTree::from_block`. We model creation explicitly.
  * If the wrapped tree is `some t` and the new block's NU differs from
    `t.nu`, this is the *activation-block reset* (`history_tree.rs:243-251`):
    `*self = Self::from_block(...)`. The old leaves are dropped.
  * If the wrapped tree is `some t` and the NU matches, this is `append_leaf`
    proper.

Returns `none` if the operation would panic (height-discontiguity, or a
pre-Heartwood block trying to create the tree). -/
def push (ht : HistoryTree) (newNU : NU) (newHeight : Nat) (newLeaf : Leaf) :
    Option HistoryTree :=
  match ht with
  | none =>
      (fromBlock newNU newHeight newLeaf).map some
  | some t =>
      if newHeight = t.currentHeight + 1 then
        if newNU = t.nu then
          (appendLeaf t newNU newHeight newLeaf).map some
        else
          (fromBlock newNU newHeight newLeaf).map some
      else
        none

/-- Number of leaves currently committed in a tree. Note this counts *leaves*,
not MMR *nodes* (Rust's `size` field, `history_tree.rs:67`, counts nodes
including internal peaks). -/
def numLeaves (t : NonEmptyHistoryTree) : Nat := t.leaves.length

/-- The leaf at index `i`, if any. Returns `none` for out-of-range. -/
def leafAt (i : Nat) (t : NonEmptyHistoryTree) : Option Leaf := t.leaves[i]?

/-! ## Theorems

This module models the load-bearing invariants of the Rust `push` API:

  * append-only (no leaf rewriting),
  * NU-tag guard (no leaf added under wrong NU without a reset),
  * height-contiguity guard (no leaf added at a non-successor height),
  * Heartwood-or-later precondition for tree existence,
  * activation-block reset semantics.
-/

/-- **T1 (fromBlock returns the canonical singleton).** A successful
`fromBlock` returns a single-leaf tree with `currentHeight = startHeight =
height` and the NU field equal to the input NU. -/
theorem fromBlock_success (nu : NU) (height : Nat) (leaf : Leaf)
    (hnu : NU.heartwoodOrLater nu) :
    fromBlock nu height leaf = some (fromBlockResult nu height leaf) := by
  unfold fromBlock
  simp [hnu]

/-- **T2 (fromBlock panics pre-Heartwood).** For any NU strictly earlier than
Heartwood, `fromBlock` returns `none` — the Rust function panics in this
case (`history_tree.rs:159-164`). -/
theorem fromBlock_none_pre_heartwood (nu : NU) (height : Nat) (leaf : Leaf)
    (hnu : ¬ NU.heartwoodOrLater nu) :
    fromBlock nu height leaf = none := by
  unfold fromBlock
  simp [hnu]

/-- **T3 (appendLeaf NU guard).** `appendLeaf` *requires* the incoming NU to
equal the tree's stored NU. With a different NU, it returns `none` — the
Rust `Tree::append_leaf` panics in this case (`zcash_history.rs:187-192`). -/
theorem appendLeaf_nu_mismatch (t : NonEmptyHistoryTree) (newNU : NU)
    (newHeight : Nat) (newLeaf : Leaf) (hnu : newNU ≠ t.nu) :
    appendLeaf t newNU newHeight newLeaf = none := by
  unfold appendLeaf
  simp [hnu]

/-- **T4 (appendLeaf height-contiguity guard).** `appendLeaf` requires the
incoming height to be exactly `currentHeight + 1`. Otherwise it returns
`none` — the Rust `push` panics in this case (`history_tree.rs:235-240`). -/
theorem appendLeaf_height_gap (t : NonEmptyHistoryTree) (newHeight : Nat)
    (newLeaf : Leaf) (hgap : newHeight ≠ t.currentHeight + 1) :
    appendLeaf t t.nu newHeight newLeaf = none := by
  unfold appendLeaf
  simp [hgap]

/-- **T5 (appendLeaf success returns the canonical result).** When the NU
and height guards are both satisfied, `appendLeaf` returns the canonical
extended struct. -/
theorem appendLeaf_success (t : NonEmptyHistoryTree) (newLeaf : Leaf) :
    appendLeaf t t.nu (t.currentHeight + 1) newLeaf =
      some (appendLeafResult t newLeaf) := by
  unfold appendLeaf
  simp

/-! ### Properties of the canonical `appendLeafResult` -/

/-- **T6 (appendLeaf grows length by exactly 1).** Mirrors the Rust invariant
that `append_leaf` adds exactly one *leaf* to the tree (it may add internal
peak nodes too, but those are accounted separately in `size`). -/
theorem appendLeafResult_length (t : NonEmptyHistoryTree) (newLeaf : Leaf) :
    numLeaves (appendLeafResult t newLeaf) = numLeaves t + 1 := by
  unfold numLeaves appendLeafResult
  simp

/-- **T7 (appendLeaf preserves NU).** Mirrors the fact that `Tree::append_leaf`
in Rust *cannot* change the tree's `network_upgrade` field (it asserts it
matches and then proceeds). -/
theorem appendLeafResult_preserves_nu (t : NonEmptyHistoryTree) (newLeaf : Leaf) :
    (appendLeafResult t newLeaf).nu = t.nu := rfl

/-- **T8 (appendLeaf preserves startHeight).** The first leaf of the segment
does not move when we append at the end. -/
theorem appendLeafResult_preserves_startHeight (t : NonEmptyHistoryTree)
    (newLeaf : Leaf) :
    (appendLeafResult t newLeaf).startHeight = t.startHeight := rfl

/-- **T9 (appendLeaf preserves previously-committed leaves at their indices).**
*The* append-only property: for any `i < numLeaves t`, the leaf at index `i`
after an append is identical to the leaf at index `i` before. No prior leaf
is ever rewritten. -/
theorem appendLeafResult_preserves_leaves (t : NonEmptyHistoryTree)
    (newLeaf : Leaf) (i : Nat) (hi : i < numLeaves t) :
    leafAt i (appendLeafResult t newLeaf) = leafAt i t := by
  unfold leafAt appendLeafResult numLeaves at *
  simp [List.getElem?_append_left hi]

/-- **T10 (appendLeaf's new leaf is at the last index).** The just-appended
leaf sits at index `numLeaves t`, the very next slot. -/
theorem appendLeafResult_new_at_last (t : NonEmptyHistoryTree)
    (newLeaf : Leaf) :
    leafAt (numLeaves t) (appendLeafResult t newLeaf) = some newLeaf := by
  unfold leafAt appendLeafResult numLeaves
  simp

/-- **T11 (appendLeaf advances currentHeight by 1).** Mirrors
`history_tree.rs:267` (`self.current_height = height`) given the contiguity
constraint at line 235. -/
theorem appendLeafResult_advances_height (t : NonEmptyHistoryTree)
    (newLeaf : Leaf) :
    (appendLeafResult t newLeaf).currentHeight = t.currentHeight + 1 := rfl

/-! ### Properties of `push` -/

/-- **T12 (push from `none` requires Heartwood-or-later).** Mirrors
`history_tree.rs:159-164`: the very first block to populate the tree must be
at Heartwood-or-later, otherwise the Rust constructor panics. -/
theorem push_empty_pre_heartwood (newNU : NU) (newHeight : Nat) (newLeaf : Leaf)
    (hnu : ¬ NU.heartwoodOrLater newNU) :
    push HistoryTree.empty newNU newHeight newLeaf = none := by
  unfold push HistoryTree.empty
  rw [fromBlock_none_pre_heartwood newNU newHeight newLeaf hnu]
  rfl

/-- **T13 (push from `none` succeeds with Heartwood-or-later).** When the
wrapped tree is empty and the block's NU is Heartwood-or-later, `push`
produces a single-leaf tree. -/
theorem push_empty_success (newNU : NU) (newHeight : Nat) (newLeaf : Leaf)
    (hnu : NU.heartwoodOrLater newNU) :
    push HistoryTree.empty newNU newHeight newLeaf =
      some (some (fromBlockResult newNU newHeight newLeaf)) := by
  unfold push HistoryTree.empty
  rw [fromBlock_success newNU newHeight newLeaf hnu]
  rfl

/-- **T14 (push height-discontiguity panic).** When the new block's height
is not `currentHeight + 1`, `push` returns `none` — the Rust function
panics (`history_tree.rs:235-240`). -/
theorem push_height_gap (t : NonEmptyHistoryTree) (newNU : NU) (newHeight : Nat)
    (newLeaf : Leaf) (hgap : newHeight ≠ t.currentHeight + 1) :
    push (some t) newNU newHeight newLeaf = none := by
  unfold push
  simp [hgap]

/-- **T15 (push same-NU is appendLeaf).** When the NU matches and heights are
contiguous, `push` returns the wrapped `appendLeafResult`. -/
theorem push_same_nu_eq_appendLeaf (t : NonEmptyHistoryTree) (newLeaf : Leaf) :
    push (some t) t.nu (t.currentHeight + 1) newLeaf =
      some (some (appendLeafResult t newLeaf)) := by
  unfold push
  simp [appendLeaf_success]
  rfl

/-- **T16 (push same-NU preserves leaves).** When `push` succeeds without an
activation reset, every previously-committed leaf remains at its original
index. This is the *full* append-only property through the `push` API. -/
theorem push_same_nu_preserves_leaves (t : NonEmptyHistoryTree) (newLeaf : Leaf)
    (i : Nat) (hi : i < numLeaves t)
    (ht' : NonEmptyHistoryTree)
    (hpush : push (some t) t.nu (t.currentHeight + 1) newLeaf
              = some (some ht')) :
    leafAt i ht' = leafAt i t := by
  rw [push_same_nu_eq_appendLeaf] at hpush
  have hht' : appendLeafResult t newLeaf = ht' :=
    Option.some.inj (Option.some.inj hpush)
  rw [← hht']
  exact appendLeafResult_preserves_leaves t newLeaf i hi

/-- **T17 (push activation reset drops the old leaves).** When `push` is
called with a *different* NU and the height is `currentHeight + 1`, the
result is a fresh single-leaf tree — the previous leaves are gone. This is
the Rust `*self = Self::from_block(...)` branch (`history_tree.rs:244-250`).
The reset only succeeds when the new NU is Heartwood-or-later (otherwise
`from_block` panics). -/
theorem push_activation_reset (t : NonEmptyHistoryTree) (newNU : NU)
    (newLeaf : Leaf) (hne : newNU ≠ t.nu)
    (hnu : NU.heartwoodOrLater newNU) :
    push (some t) newNU (t.currentHeight + 1) newLeaf =
      some (some (fromBlockResult newNU (t.currentHeight + 1) newLeaf)) := by
  unfold push
  simp [hne, fromBlock_success newNU (t.currentHeight + 1) newLeaf hnu]
  rfl

/-- **T18 (push activation reset to pre-Heartwood is impossible).** No
forward-running chain can transition from a Heartwood-or-later upgrade back
to a pre-Heartwood upgrade — but as a defensive theorem we record that
even if such a transition were attempted, `push` returns `none` (because
`fromBlock` returns `none`). -/
theorem push_activation_reset_pre_heartwood
    (t : NonEmptyHistoryTree) (newNU : NU) (newLeaf : Leaf)
    (hne : newNU ≠ t.nu) (hnu : ¬ NU.heartwoodOrLater newNU) :
    push (some t) newNU (t.currentHeight + 1) newLeaf = none := by
  unfold push
  simp [hne, fromBlock_none_pre_heartwood newNU (t.currentHeight + 1) newLeaf hnu]

/-- **T19 (push same-NU grows length by exactly 1).** If `push` succeeds
without an activation reset, the resulting tree has one more leaf than the
previous one. -/
theorem push_same_nu_grows (t : NonEmptyHistoryTree) (newLeaf : Leaf)
    (ht' : NonEmptyHistoryTree)
    (hpush : push (some t) t.nu (t.currentHeight + 1) newLeaf
              = some (some ht')) :
    numLeaves ht' = numLeaves t + 1 := by
  rw [push_same_nu_eq_appendLeaf] at hpush
  have hht' : appendLeafResult t newLeaf = ht' :=
    Option.some.inj (Option.some.inj hpush)
  rw [← hht']
  exact appendLeafResult_length t newLeaf

/-- **T20 (push same-NU preserves the NU tag).** Mirrors that the Rust
`append_leaf` path leaves `self.network_upgrade` unchanged. -/
theorem push_same_nu_preserves_nu (t : NonEmptyHistoryTree) (newLeaf : Leaf)
    (ht' : NonEmptyHistoryTree)
    (hpush : push (some t) t.nu (t.currentHeight + 1) newLeaf
              = some (some ht')) :
    ht'.nu = t.nu := by
  rw [push_same_nu_eq_appendLeaf] at hpush
  have hht' : appendLeafResult t newLeaf = ht' :=
    Option.some.inj (Option.some.inj hpush)
  rw [← hht']
  exact appendLeafResult_preserves_nu t newLeaf

/-- **T21 (push same-NU preserves the startHeight).** No reset means the
segment's first leaf is unchanged. Combined with T20, this means *the entire
prefix is preserved*: the new tree extends the old one. -/
theorem push_same_nu_preserves_startHeight (t : NonEmptyHistoryTree)
    (newLeaf : Leaf) (ht' : NonEmptyHistoryTree)
    (hpush : push (some t) t.nu (t.currentHeight + 1) newLeaf
              = some (some ht')) :
    ht'.startHeight = t.startHeight := by
  rw [push_same_nu_eq_appendLeaf] at hpush
  have hht' : appendLeafResult t newLeaf = ht' :=
    Option.some.inj (Option.some.inj hpush)
  rw [← hht']
  exact appendLeafResult_preserves_startHeight t newLeaf

/-- **T22 (number of leaves equals height span).** From the
`heightConsistent` invariant, `numLeaves t = currentHeight - startHeight + 1`.
This ties the leaf-count abstraction to the block-height abstraction. -/
theorem numLeaves_eq_height_span (t : NonEmptyHistoryTree) :
    numLeaves t = t.currentHeight + 1 - t.startHeight := by
  have h := t.heightConsistent
  unfold numLeaves
  omega

/-- **T23 (currentHeight ≥ startHeight).** Consequence of the
`heightConsistent` invariant and `leaves` being non-empty. -/
theorem currentHeight_ge_startHeight (t : NonEmptyHistoryTree) :
    t.currentHeight ≥ t.startHeight := by
  have h := t.heightConsistent
  have hlen : t.leaves.length ≥ 1 := by
    rcases List.length_pos_iff.mpr t.nonempty with hp
    omega
  omega

/-- **T24 (singleton from_block has currentHeight = startHeight).**
The single-leaf case witnesses the boundary of T23. -/
theorem fromBlockResult_single_height_eq (nu : NU) (height : Nat) (leaf : Leaf) :
    (fromBlockResult nu height leaf).currentHeight =
      (fromBlockResult nu height leaf).startHeight := rfl

/-- **T25 (push of empty never produces an empty result).** Whenever `push`
succeeds on an empty (`none`) tree, the result is a `some _` wrapped tree.
This codifies the one-way nature of the wrapper: pre-Heartwood → empty;
Heartwood-or-later → non-empty, with no public path back. -/
theorem push_empty_never_empty (newNU : NU) (newHeight : Nat) (newLeaf : Leaf)
    (ht : HistoryTree)
    (hresult : push HistoryTree.empty newNU newHeight newLeaf = some ht) :
    ht ≠ none := by
  by_cases hnu : NU.heartwoodOrLater newNU
  · rw [push_empty_success newNU newHeight newLeaf hnu] at hresult
    have : some (fromBlockResult newNU newHeight newLeaf) = ht :=
      Option.some.inj hresult
    rw [← this]; simp
  · rw [push_empty_pre_heartwood newNU newHeight newLeaf hnu] at hresult
    exact absurd hresult (by simp)

/-- **T26 (push of `some t` never produces an empty result).** Symmetric to
T25 for the non-empty case: a successful `push` on `some t` is `some (some _)`,
never `some none`. The tree, once non-empty, can never be made empty by the
public API. -/
theorem push_some_never_empty (t : NonEmptyHistoryTree) (newNU : NU)
    (newHeight : Nat) (newLeaf : Leaf) (ht : HistoryTree)
    (hresult : push (some t) newNU newHeight newLeaf = some ht) :
    ht ≠ none := by
  by_cases hgap : newHeight = t.currentHeight + 1
  case neg =>
    rw [push_height_gap t newNU newHeight newLeaf hgap] at hresult
    exact absurd hresult (by simp)
  case pos =>
    subst hgap
    by_cases hnu_eq : newNU = t.nu
    case pos =>
      subst hnu_eq
      rw [push_same_nu_eq_appendLeaf] at hresult
      have : some (appendLeafResult t newLeaf) = ht := Option.some.inj hresult
      rw [← this]; simp
    case neg =>
      by_cases hnu_hw : NU.heartwoodOrLater newNU
      · rw [push_activation_reset t newNU newLeaf hnu_eq hnu_hw] at hresult
        have : some (fromBlockResult newNU (t.currentHeight + 1) newLeaf) = ht :=
          Option.some.inj hresult
        rw [← this]; simp
      · rw [push_activation_reset_pre_heartwood t newNU newLeaf hnu_eq hnu_hw]
          at hresult
        exact absurd hresult (by simp)

/-- **T27 (push is monotone in NU ordering).** Forward-running chain: a
successful `push` either keeps the NU the same (append) or moves it strictly
forward (activation reset). The NU never regresses through `push`. -/
theorem push_nu_monotone (t : NonEmptyHistoryTree) (newNU : NU) (newLeaf : Leaf)
    (hnu_forward : t.nu.toOrd ≤ newNU.toOrd)
    (ht' : NonEmptyHistoryTree)
    (hpush : push (some t) newNU (t.currentHeight + 1) newLeaf
              = some (some ht')) :
    t.nu.toOrd ≤ ht'.nu.toOrd := by
  by_cases hnu_eq : newNU = t.nu
  case pos =>
    -- Same NU: ht'.nu = t.nu, equality follows.
    subst hnu_eq
    have := push_same_nu_preserves_nu t newLeaf ht' hpush
    rw [this]
  case neg =>
    -- Different NU: activation reset. Need ht'.nu = newNU, and use hnu_forward.
    by_cases hnu_hw : NU.heartwoodOrLater newNU
    case pos =>
      rw [push_activation_reset t newNU newLeaf hnu_eq hnu_hw] at hpush
      have : fromBlockResult newNU (t.currentHeight + 1) newLeaf = ht' :=
        Option.some.inj (Option.some.inj hpush)
      rw [← this]
      exact hnu_forward
    case neg =>
      -- Pre-Heartwood reset: impossible, `push` returns `none`.
      rw [push_activation_reset_pre_heartwood t newNU newLeaf hnu_eq hnu_hw]
        at hpush
      exact absurd hpush (by simp)

/-- **T28 (empty wrapper is `none`).** The wrapper-level empty tree is `none`.
This is a definitional unfolding witness for clients who treat `HistoryTree`
as opaque. -/
theorem HistoryTree.empty_is_none : HistoryTree.empty = none := rfl

/-- **T29 (history tree segment height range).** The set of heights covered
by a non-empty tree is exactly `[startHeight, currentHeight]`, with one leaf
per height. From the `heightConsistent` invariant and non-emptiness, this
range has `currentHeight + 1 - startHeight = numLeaves` heights, witnessing
the one-block-per-leaf property of ZIP-221. -/
theorem segment_height_range (t : NonEmptyHistoryTree) :
    t.startHeight ≤ t.currentHeight ∧
    t.currentHeight + 1 - t.startHeight = numLeaves t := by
  refine ⟨currentHeight_ge_startHeight t, ?_⟩
  rw [numLeaves_eq_height_span]

end Zebra.HistoryTreeAppendOnly
