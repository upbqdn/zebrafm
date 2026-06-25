import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Sapling / Orchard anchor validity

Models the consensus check from
`zebra-state/src/service/check/anchors.rs:24-128`:

> The anchor of each Spend description MUST refer to some earlier block's
> final Sapling treestate.
> The anchorOrchard field of the transaction, whenever it exists (i.e. when
> there are any Action descriptions), MUST refer to some earlier block's
> final Orchard treestate.

A Sapling anchor is the root of a Sapling note commitment tree
(`zebra-chain/src/sapling/tree.rs:42-49`); an Orchard anchor is the root of an
Orchard note commitment tree (`zebra-chain/src/orchard/tree.rs:1-12`). Both are
serialised as 32 bytes (`LEBS2OSP256(rt)` for Sapling; canonical Pallas-base
repr for Orchard) and the consensus check is a membership test against the
parent chain's known final treestate roots (`Chain::sapling_anchors`,
`Chain::orchard_anchors`) and the finalized state's `sapling_anchors` /
`orchard_anchors` column families. Concretely Zebra validates:

```rust
if !parent_chain
    .map(|chain| chain.sapling_anchors.contains(&anchor))
    .unwrap_or(false)
    && !finalized_state.contains_sapling_anchor(&anchor)
{
    return Err(ValidateContextError::UnknownSaplingAnchor { ... });
}
```
(Source: `zebra-state/src/service/check/anchors.rs:49-69`.)

So the abstract object the validator works with is just a *known-roots set*
of 32-byte digests; the underlying tree machinery is not consensus-critical
for this particular check. We model the digest as `List Nat` of length 32
(same convention as `Nullifiers.lean`) and `knownRoots` as a `List` of such
digests. The validator predicate is membership; we prove monotonicity of the
predicate as new final treestates are added, decidability of the check, and
that an unknown anchor is rejected.
-/

namespace Zebra.AnchorValidity

/-- The fixed digest width in bytes: 32, matching `[u8; 32]` for both
`sapling::tree::Root` and `orchard::tree::Root`.
Source: `zebra-chain/src/sapling/tree.rs:69-73`,
`zebra-chain/src/orchard/tree.rs` (`From<Root> for [u8; 32]`). -/
def DIGEST_BYTES : Nat := 32

/-- An anchor is a 32-byte digest (the byte repr of a Sapling or Orchard
treestate root).
Source: `zebra-chain/src/sapling/tree.rs:42-49`,
`zebra-chain/src/orchard/tree.rs`. -/
abbrev Anchor : Type := List Nat

/-- The length invariant carried by the Rust `[u8; 32]` representation of a
treestate root. Source: `zebra-chain/src/sapling/tree.rs:69-73`. -/
def IsAnchor (a : Anchor) : Prop := a.length = DIGEST_BYTES

/-- The validator's known-roots set, modelled as a `List` of digests. In
Zebra this is the union of `Chain::sapling_anchors` (a multiset of
non-finalized final treestate roots) and the finalized column family
`sapling_anchors` (resp. `orchard_anchors`).
Source: `zebra-state/src/service/check/anchors.rs:58-62, 99-106`. -/
abbrev KnownRoots : Type := List Anchor

/-- The empty known-roots set, modelled as the empty list. The
`Default::default()` `NoteCommitmentTree` has its own root, but the
known-roots *set* starts out empty before the genesis block is finalized
(no final treestate has been observed yet). -/
def empty : KnownRoots := []

/-- The anchor validity predicate.

This is the Lean mirror of the `&&`-of-`contains` check in
`sapling_orchard_anchors_refer_to_final_treestates`:
the anchor is valid iff it appears in the known-roots set built from the
parent chain *and* the finalized state.
Source: `zebra-state/src/service/check/anchors.rs:58-69`. -/
def isValidAnchor (knownRoots : KnownRoots) (a : Anchor) : Prop :=
  a ∈ knownRoots

/-- Boolean version, mirroring `Vec::contains` / `HashSet::contains` in Rust.
Source: `zebra-state/src/service/check/anchors.rs:59`. -/
def isValidAnchorBool (knownRoots : KnownRoots) (a : Anchor) : Bool :=
  knownRoots.contains a

/-- Adding a new final treestate root to the known-roots set
(`Chain::update_chain_tip_with` pushes new tree roots into
`sapling_anchors` / `orchard_anchors` as each block is committed). -/
def addRoot (knownRoots : KnownRoots) (r : Anchor) : KnownRoots :=
  r :: knownRoots

/-! ## Theorems -/

/-- **T1 (empty set rejects every anchor).** Before any final treestate has
been observed, no anchor is valid. This matches the Rust check returning
`UnknownSaplingAnchor` (resp. `UnknownOrchardAnchor`) when both the parent
chain's anchor set and the finalized state are empty. -/
theorem empty_rejects (a : Anchor) : ¬ isValidAnchor empty a := by
  unfold isValidAnchor empty
  exact List.not_mem_nil

/-- **T2 (`addRoot` makes the new root valid).** A freshly-appended treestate
root is immediately accepted. -/
theorem addRoot_new_is_valid (knownRoots : KnownRoots) (r : Anchor) :
    isValidAnchor (addRoot knownRoots r) r := by
  unfold isValidAnchor addRoot
  exact List.mem_cons_self

/-- **T3 (monotonicity in `knownRoots`).** Appending a new root preserves
validity of every previously-valid anchor. This is the append-only invariant
of the known-roots set: as the chain extends, the set of valid anchors only
grows. -/
theorem addRoot_monotone (knownRoots : KnownRoots) (r a : Anchor)
    (hv : isValidAnchor knownRoots a) :
    isValidAnchor (addRoot knownRoots r) a := by
  unfold isValidAnchor addRoot at *
  exact List.mem_cons_of_mem _ hv

/-- **T4 (iterated monotonicity).** After appending any sequence of roots,
every originally-valid anchor remains valid. -/
theorem addRoots_monotone (knownRoots : KnownRoots) (rs : List Anchor)
    (a : Anchor) (hv : isValidAnchor knownRoots a) :
    isValidAnchor (rs ++ knownRoots) a := by
  unfold isValidAnchor at *
  induction rs with
  | nil => exact hv
  | cons r rs ih =>
    simp only [List.cons_append, List.mem_cons]
    exact Or.inr ih

/-- **T5 (decidability of the membership check).** The validator's check is
computable: anchor membership in a `List` of digests is decidable, matching
the `Vec::contains` / `HashSet::contains` Rust call. -/
instance decidable_isValidAnchor (knownRoots : KnownRoots) (a : Anchor) :
    Decidable (isValidAnchor knownRoots a) := by
  unfold isValidAnchor
  exact inferInstance

/-- **T6 (boolean / propositional check agree).** The decidable `Bool`
version of the validator matches the `Prop` version on every input. -/
theorem isValidAnchorBool_iff (knownRoots : KnownRoots) (a : Anchor) :
    isValidAnchorBool knownRoots a = true ↔ isValidAnchor knownRoots a := by
  unfold isValidAnchorBool isValidAnchor
  exact List.contains_iff_mem

/-- **T7 (the freshly-added root is `true` under the boolean check).** -/
theorem addRoot_new_isValidBool (knownRoots : KnownRoots) (r : Anchor) :
    isValidAnchorBool (addRoot knownRoots r) r = true := by
  rw [isValidAnchorBool_iff]
  exact addRoot_new_is_valid knownRoots r

/-- **T8 (unknown anchor is rejected).** An anchor that is provably absent
from the known-roots set is rejected. This is the contrapositive of T1 / T2
and matches Zebra's `UnknownSaplingAnchor` / `UnknownOrchardAnchor` error
path. -/
theorem unknown_is_rejected (knownRoots : KnownRoots) (a : Anchor)
    (h : a ∉ knownRoots) :
    ¬ isValidAnchor knownRoots a := by
  unfold isValidAnchor
  exact h

/-- **T9 (rejection is monotone in absence).** If a digest is absent from a
larger set, it is also absent from any smaller (sub-list) set. Concretely:
removing the most-recently-added root preserves rejection. -/
theorem rejection_monotone_pop (knownRoots : KnownRoots) (r a : Anchor)
    (h : ¬ isValidAnchor (addRoot knownRoots r) a) :
    ¬ isValidAnchor knownRoots a := by
  unfold isValidAnchor addRoot at *
  intro ha
  exact h (List.mem_cons_of_mem _ ha)

/-- **T10 (empty + add = single-element).** Starting from the empty set and
appending a single root produces a singleton list containing only that root,
so the boolean check returns `true` exactly for that root. -/
theorem empty_addRoot_valid (r : Anchor) :
    isValidAnchor (addRoot empty r) r := by
  apply addRoot_new_is_valid

/-- **T11 (singleton rejects different anchors).** From the singleton set
`{r}`, an anchor `a ≠ r` is rejected. -/
theorem singleton_rejects_other (r a : Anchor) (h : a ≠ r) :
    ¬ isValidAnchor (addRoot empty r) a := by
  unfold isValidAnchor addRoot empty
  intro hm
  simp only [List.mem_singleton] at hm
  exact h hm

/-- **T12 (anchor validity is order-independent in the known-roots set).**
Swapping two roots in the known-roots list does not change which anchors are
valid; only set-membership matters. This justifies modelling `KnownRoots` as
a multiset / set in higher-level reasoning even though we use `List` here. -/
theorem isValidAnchor_swap (rest : KnownRoots) (r₁ r₂ a : Anchor) :
    isValidAnchor (r₁ :: r₂ :: rest) a ↔
      isValidAnchor (r₂ :: r₁ :: rest) a := by
  unfold isValidAnchor
  simp only [List.mem_cons]
  tauto

/-- **T13 (anchor validity is preserved under list concatenation, RHS).**
If an anchor is valid in `knownRoots`, it is valid in `knownRoots ++ extra`.
-/
theorem isValidAnchor_append_right (knownRoots extra : KnownRoots)
    (a : Anchor) (hv : isValidAnchor knownRoots a) :
    isValidAnchor (knownRoots ++ extra) a := by
  unfold isValidAnchor at *
  exact List.mem_append_left _ hv

/-- **T14 (anchor validity is preserved under list concatenation, LHS).**
If an anchor is valid in `extra`, it is valid in `knownRoots ++ extra`. -/
theorem isValidAnchor_append_left (knownRoots extra : KnownRoots)
    (a : Anchor) (hv : isValidAnchor extra a) :
    isValidAnchor (knownRoots ++ extra) a := by
  unfold isValidAnchor at *
  exact List.mem_append_right _ hv

/-- **T15 (`DIGEST_BYTES` is concretely 32).** Pin the constant: consensus
code reads `[u8; 32]` directly. -/
theorem digest_bytes_eq : DIGEST_BYTES = 32 := rfl

/-- **T16 (a valid anchor must satisfy the digest-width invariant, given
the known-roots set does).** If every digest in the known-roots set is a
valid 32-byte digest, then any anchor accepted by the validator is itself a
valid 32-byte digest. This is the "well-typed inputs give well-typed
outputs" invariant of the consensus check. -/
theorem valid_anchor_has_digest_width (knownRoots : KnownRoots) (a : Anchor)
    (hAll : ∀ r ∈ knownRoots, IsAnchor r)
    (hv : isValidAnchor knownRoots a) :
    IsAnchor a := by
  unfold isValidAnchor at hv
  exact hAll a hv

end Zebra.AnchorValidity
