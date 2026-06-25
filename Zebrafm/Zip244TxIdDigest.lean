import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

set_option linter.style.header false

/-!
# ZIP-244 NU5 transaction-ID digest tree

For V5 transactions, the txid is the root of a multi-level digest tree, as
specified in ZIP-244 and ZIP-225. Each intermediate node is a BLAKE2b-256
hash whose 16-byte personalisation string is folded into the BLAKE2b IV
(NOT prepended to the payload — see Finding 55 below). Zebra delegates V5
txid computation to librustzcash:

```rust
fn txid_v5(self) -> Option<Hash> {
    let nu = self.trans.network_upgrade()?;
    Some(Hash(*self.trans.to_librustzcash(nu).ok()?.txid().as_ref()))
}
```
Source: `zebra-chain/src/transaction/txid.rs:47-52`.

The ZIP-244 tree (top level) is:

```
txid = H_root( headerDigest ‖ transparentDigest
              ‖ saplingDigest ‖ orchardDigest )
```

with each section digest itself defined as a hash of sub-digests under its
own personalisation tag. Concretely (librustzcash `txid.rs:395-433`):

```
H_root  = BLAKE2b-256 personal = "ZcashTxHash_" ‖ branch_id (4 LE)
header  = BLAKE2b-256 personal = "ZTxIdHeadersHash"
transp  = BLAKE2b-256 personal = "ZTxIdTranspaHash"     (level-1)
              over: prevouts ‖ sequence ‖ outputs       (level-2)
sapling = BLAKE2b-256 personal = "ZTxIdSaplingHash"     (level-1)
              over: spends ‖ outputs ‖ value_balance    (level-2)
orchard = BLAKE2b-256 personal = "ZTxIdOrcHash" (per ZIP-244)
```

with level-2 children themselves personalised
(`ZTxIdPrevoutHash`, `ZTxIdSequencHash`, `ZTxIdOutputsHash`,
 `ZTxIdSSpendsHash`, `ZTxIdSOutputHash`, …).

This module models the *structural* properties of this tree:

  * Personalisation tags are identified by `TagId : Nat`. The abstract
    hash is a *family* `H : TagId → List Nat → List Nat` — i.e. each
    personal yields its own injective hash. This faithfully captures
    BLAKE2b-personal-in-IV semantics: distinct personals are independent
    random oracles, so collisions across personals are infeasible. (The
    earlier model `H (tag ++ payload)` collapsed the two-argument hash
    family to a single hash with a prefix, which has a *different*
    collision profile — see Finding 55.)

  * The top-level root tag carries the `consensus_branch_id`, modelling
    `ZcashTxHash_` ‖ `branchId_le32`.

  * Section sub-digests are nested: each section leaf at the top tree
    is itself the output of a hash over level-2 sub-digests.

  * The hash family is jointly injective: equal outputs imply equal
    `(tag, payload)`. This is the abstract counterpart of BLAKE2b's
    conjectured collision resistance.

The load-bearing claims we prove:

  1. **Cross-personal domain separation.** Different `TagId`s give
     distinct digests on the same payload (T2).
  2. **Within-section payload injectivity.** Same tag, distinct payloads
     give distinct digests (T1).
  3. **Top-level leaf-only dependence + injectivity** (T6–T8, T13).
  4. **Branch-id binding into the root.** Different `consensus_branch_id`s
     yield different txids on the same sections (T14).
  5. **Sub-digest injectivity for each section** (T16–T19): collisions in
     a section's level-2 inputs propagate to the section digest.
  6. **Recursive end-to-end injectivity from level-2 inputs to txid**
     (T20): full transparent/sapling/orchard sub-inputs determine the
     txid (assuming matching widths at the leaves).

We do *not* model BLAKE2b at the byte level — these are the abstract
algebraic properties on which the consensus-correctness argument depends.

Source: <https://zips.z.cash/zip-0244#specification>
Source: `zebra-chain/src/transaction/txid.rs:44-52`.
Source: librustzcash `zcash_primitives/src/transaction/txid.rs:34-69, 395-452`.
-/

namespace Zebra.Zip244TxIdDigest

/-! ## Domain-separation tags

ZIP-244 uses 16-byte BLAKE2b personalisation strings to separate the
hash-family used at each tree node. We identify each personal with an
opaque `TagId : Nat` (an index into the tag table). The point of the
abstraction is that distinct ids correspond to distinct personals, hence
to *independent* injective hash families.

The level-1 (top) ids are `header`, `transparent`, `sapling`, `orchard`.
The level-2 ids appear under transparent and sapling. Orchard's level-2
structure is hidden inside `orchard::commitments::hash_bundle_txid_*` in
librustzcash and modelled here as a single sub-payload — extending to a
finer orchard tree is a future refinement. -/

/-- The five top-level + six level-2 personalisation slots used in the
ZIP-244 txid tree. They are kept abstract (just `Nat` ids) so that
distinctness, not byte content, is the structural input. -/
structure TagIds where
  /-- Root tag `"ZcashTxHash_"` (the branch-id is supplied separately). -/
  root : Nat
  /-- Header section level-1 tag `"ZTxIdHeadersHash"`. -/
  header : Nat
  /-- Transparent section level-1 tag `"ZTxIdTranspaHash"`. -/
  transparent : Nat
  /-- Sapling section level-1 tag `"ZTxIdSaplingHash"`. -/
  sapling : Nat
  /-- Orchard section level-1 tag `"ZTxIdOrcHash"`. -/
  orchard : Nat
  /-- Transparent level-2 prevouts tag `"ZTxIdPrevoutHash"`. -/
  prevouts : Nat
  /-- Transparent level-2 sequence tag `"ZTxIdSequencHash"`. -/
  sequence : Nat
  /-- Transparent level-2 outputs tag `"ZTxIdOutputsHash"`. -/
  outputs : Nat
  /-- Sapling level-2 spends tag `"ZTxIdSSpendsHash"`. -/
  saplingSpends : Nat
  /-- Sapling level-2 outputs tag `"ZTxIdSOutputHash"`. -/
  saplingOutputs : Nat
  /-- Sapling level-2 value-balance tag (modelled abstractly). -/
  saplingValueBalance : Nat
  deriving Repr

/-- Pairwise distinctness of all eleven tag ids — the structural
condition that makes BLAKE2b-personal-in-IV give independent hash
families across all tree nodes. -/
def TagIds.Distinct (t : TagIds) : Prop :=
  let ids : List Nat :=
    [t.root, t.header, t.transparent, t.sapling, t.orchard,
     t.prevouts, t.sequence, t.outputs,
     t.saplingSpends, t.saplingOutputs, t.saplingValueBalance]
  ids.Nodup

/-- Helper: extract the top-level (root/section-1) distinctness facts. -/
theorem TagIds.Distinct.top_level (t : TagIds) (hT : t.Distinct) :
    t.root ≠ t.header ∧ t.root ≠ t.transparent ∧
    t.root ≠ t.sapling ∧ t.root ≠ t.orchard ∧
    t.header ≠ t.transparent ∧ t.header ≠ t.sapling ∧
    t.header ≠ t.orchard ∧
    t.transparent ≠ t.sapling ∧ t.transparent ≠ t.orchard ∧
    t.sapling ≠ t.orchard := by
  -- Unfold the `List.Nodup` definition and read off the disequalities.
  simp only [TagIds.Distinct, List.nodup_cons, List.mem_cons,
             List.not_mem_nil, or_false, not_or] at hT
  -- hT is now a deeply nested conjunction; destructure to get the
  -- individual disequalities for the five top-level ids.
  obtain ⟨hroot, hheader, htrans, hsap, horc, _⟩ := hT
  obtain ⟨h_r_h, h_r_t, h_r_s, h_r_o, _, _, _⟩ := hroot
  obtain ⟨h_h_t, h_h_s, h_h_o, _, _, _⟩ := hheader
  obtain ⟨h_t_s, h_t_o, _, _, _⟩ := htrans
  obtain ⟨h_s_o, _, _, _⟩ := hsap
  refine ⟨h_r_h, h_r_t, h_r_s, h_r_o, h_h_t, h_h_s, h_h_o, h_t_s, h_t_o, h_s_o⟩

/-! ## Abstract hash family

BLAKE2b with a 16-byte personalisation is, conceptually, an indexed
*family* of hash functions, one per personal. We model this with
`AbstractHashFamily.hash : Nat → List Nat → List Nat` and assume the
function (as a whole, *including* the tag argument) is injective in
`(tag, payload)`. That is exactly the cross-personal collision resistance
property used by the ZIP-244 correctness argument.

Note: this differs from the older model `H (tag ++ payload)`, which
collapses to a single one-argument hash and therefore admits structural
collisions like `H ("ab" ++ "c") = H ("a" ++ "bc")`. BLAKE2b
personal-in-IV does NOT have that property, so the two-argument hash
family is the faithful model. -/

/-- An abstract BLAKE2b-like keyed hash family: each `tag : Nat`
selects an injective hash function. Jointly injective in `(tag, payload)`
captures cross-personal collision resistance. -/
structure AbstractHashFamily where
  /-- The hash, indexed by the personalisation tag id. -/
  hash : Nat → List Nat → List Nat
  /-- Joint injectivity: distinct `(tag, payload)` pairs give distinct
  digests. -/
  inj : ∀ {t₁ t₂ : Nat} {p₁ p₂ : List Nat},
    hash t₁ p₁ = hash t₂ p₂ → t₁ = t₂ ∧ p₁ = p₂

/-- Within a fixed tag, the hash is injective in the payload. -/
theorem AbstractHashFamily.inj_payload (H : AbstractHashFamily)
    (t : Nat) {p₁ p₂ : List Nat} (h : H.hash t p₁ = H.hash t p₂) :
    p₁ = p₂ :=
  (H.inj h).2

/-- For a fixed payload, the hash is injective in the tag. -/
theorem AbstractHashFamily.inj_tag (H : AbstractHashFamily)
    {t₁ t₂ : Nat} (p : List Nat) (h : H.hash t₁ p = H.hash t₂ p) :
    t₁ = t₂ :=
  (H.inj h).1

/-! ## Level-2 (section sub-digest) payloads

ZIP-244 splits each non-trivial section into smaller sub-digests:

  * Transparent: `prevouts ‖ sequence ‖ outputs` (each itself BLAKE2b'd).
  * Sapling:     `spends ‖ outputs ‖ value_balance` (spends/outputs
                 themselves BLAKE2b'd, value_balance is 8-byte LE).
  * Orchard:     a `hash_bundle_txid_data`-style payload (modelled
                 abstractly as a single `List Nat`).

We model the raw level-2 inputs as `List Nat` per slot. -/

/-- Transparent sub-inputs: raw payloads that get hashed at level 2 to
form the prevouts/sequence/outputs sub-digests. -/
structure TransparentInputs where
  prevoutsPayload : List Nat
  sequencePayload : List Nat
  outputsPayload : List Nat
  deriving Repr

/-- Sapling sub-inputs: raw payloads for the spends/outputs sub-digests,
plus the 8-byte LE value_balance bytes. -/
structure SaplingInputs where
  spendsPayload : List Nat
  outputsPayload : List Nat
  valueBalancePayload : List Nat
  deriving Repr

/-- Orchard sub-inputs: the librustzcash `hash_bundle_txid_data` payload,
modelled as a single byte list. (Refining to the full orchard sub-tree
is future work — Finding 56 future refinement.) -/
structure OrchardInputs where
  bundlePayload : List Nat
  deriving Repr

/-! ## Level-1 (top-level) sections

The four top-level section leaves: each is itself the digest of a
level-2 hash, except for `header`, which we model as a raw payload
(the librustzcash header digest is a single BLAKE2b over a small fixed
tuple of fields and has no inner tree). -/

/-- Header sub-input: the raw payload that gets hashed under
`ZTxIdHeadersHash` to form the header section digest. -/
structure HeaderInputs where
  /-- Concatenation of `(version, version-group-id, consensus-branch-id,
  lock-time, expiry-height)` bytes per ZIP-244. -/
  headerPayload : List Nat
  deriving Repr

/-! ## Hashing functions

We now define each level of the tree as an explicit function. Each name
mirrors the corresponding librustzcash function. -/

/-- Apply the keyed hash with a given tag id and payload. Replaces the
prefix-byte `personalisedHash` of the prior model. -/
@[inline] def keyedHash (H : AbstractHashFamily) (tag : Nat) (payload : List Nat) :
    List Nat :=
  H.hash tag payload

/-- Level-2: transparent prevouts sub-digest. -/
def prevoutsDigest (H : AbstractHashFamily) (t : TagIds)
    (inputs : TransparentInputs) : List Nat :=
  keyedHash H t.prevouts inputs.prevoutsPayload

/-- Level-2: transparent sequence sub-digest. -/
def sequenceDigest (H : AbstractHashFamily) (t : TagIds)
    (inputs : TransparentInputs) : List Nat :=
  keyedHash H t.sequence inputs.sequencePayload

/-- Level-2: transparent outputs sub-digest. -/
def outputsDigest (H : AbstractHashFamily) (t : TagIds)
    (inputs : TransparentInputs) : List Nat :=
  keyedHash H t.outputs inputs.outputsPayload

/-- Level-2: sapling spends sub-digest. -/
def saplingSpendsDigest (H : AbstractHashFamily) (t : TagIds)
    (inputs : SaplingInputs) : List Nat :=
  keyedHash H t.saplingSpends inputs.spendsPayload

/-- Level-2: sapling outputs sub-digest. -/
def saplingOutputsDigest (H : AbstractHashFamily) (t : TagIds)
    (inputs : SaplingInputs) : List Nat :=
  keyedHash H t.saplingOutputs inputs.outputsPayload

/-- Level-1: header section digest. -/
def headerDigest (H : AbstractHashFamily) (t : TagIds) (inputs : HeaderInputs) :
    List Nat :=
  keyedHash H t.header inputs.headerPayload

/-- Level-1: transparent section digest. Hashes the concatenation of the
three level-2 sub-digests under `ZTxIdTranspaHash`. -/
def transparentDigest (H : AbstractHashFamily) (t : TagIds)
    (inputs : TransparentInputs) : List Nat :=
  keyedHash H t.transparent
    (prevoutsDigest H t inputs ++ sequenceDigest H t inputs
      ++ outputsDigest H t inputs)

/-- Level-1: sapling section digest. Hashes
`spends ‖ outputs ‖ value_balance` under `ZTxIdSaplingHash`. -/
def saplingDigest (H : AbstractHashFamily) (t : TagIds)
    (inputs : SaplingInputs) : List Nat :=
  keyedHash H t.sapling
    (saplingSpendsDigest H t inputs ++ saplingOutputsDigest H t inputs
      ++ inputs.valueBalancePayload)

/-- Level-1: orchard section digest. Modelled abstractly as a single
keyed hash over `OrchardInputs.bundlePayload`. -/
def orchardDigest (H : AbstractHashFamily) (t : TagIds)
    (inputs : OrchardInputs) : List Nat :=
  keyedHash H t.orchard inputs.bundlePayload

/-! ## Root construction

The ZIP-244 root uses personalisation
`"ZcashTxHash_" ‖ branch_id_le32`. We model `branchId : Nat` and stipulate
that the *effective* tag id at the root is determined by the combination
of the textual prefix tag `t.root` and the branch id.

Concretely: we model `rootTagFor branchId t.root` as an injective
function of the branch id (per-prefix), so that different branch ids give
different effective tag ids — exactly the structural property used by
the consensus argument to bind the branch id into the txid.

We don't pin a specific encoding here (Cantor pairing or
`Nat.pair`-style would work); we just demand a per-prefix injection
`branchId ↦ effective tag id` via the `BranchIdBinding` structure. -/

/-- An injective per-prefix mapping from `(branchId, prefix-tag-id)` to
the effective BLAKE2b personalisation slot. Captures the
`"ZcashTxHash_" ‖ branch_id_le32` byte concatenation in the IV at the
abstract level: distinct branch ids under the same `ZcashTxHash_` prefix
give distinct keys, and the prefix is fixed (so we just need injectivity
in the branch id). -/
structure BranchIdBinding where
  /-- Effective tag id for the root personalisation given a branch id. -/
  effectiveRootTag : Nat → Nat
  /-- Branch ids inject into effective tag ids. -/
  inj : Function.Injective effectiveRootTag

/-- The full top-level digest. Hashes
`headerDigest ‖ transparentDigest ‖ saplingDigest ‖ orchardDigest` under
the branch-id-bound root personalisation. -/
def txidRoot
    (H : AbstractHashFamily) (t : TagIds) (B : BranchIdBinding)
    (branchId : Nat)
    (hIn : HeaderInputs) (tIn : TransparentInputs)
    (sIn : SaplingInputs) (oIn : OrchardInputs) : List Nat :=
  H.hash (B.effectiveRootTag branchId)
    (headerDigest H t hIn ++ transparentDigest H t tIn
      ++ saplingDigest H t sIn ++ orchardDigest H t oIn)

/-! ## Theorems -/

/-- **T1 (keyed hash: payload injective at fixed tag).** Within a fixed
personalisation tag, the keyed hash is injective in its payload. This is
the "domain separation within a section" property. -/
theorem keyedHash_inj_payload (H : AbstractHashFamily) (tag : Nat)
    (p₁ p₂ : List Nat) (h : keyedHash H tag p₁ = keyedHash H tag p₂) :
    p₁ = p₂ := by
  unfold keyedHash at h
  exact H.inj_payload tag h

/-- **T2 (cross-personal domain separation).** Distinct tag ids on the
same payload yield distinct digests. This is the precise structural
counterpart of the ZIP-244 / BLAKE2b-personal-in-IV claim that distinct
personalisation strings give independent hash families. -/
theorem domain_separation_eq_payload (H : AbstractHashFamily)
    (t₁ t₂ : Nat) (payload : List Nat) (hne : t₁ ≠ t₂) :
    keyedHash H t₁ payload ≠ keyedHash H t₂ payload := by
  intro heq
  unfold keyedHash at heq
  exact hne (H.inj_tag payload heq)

/-- **T3 (header vs transparent domain separation).** With distinct
top-level tag ids, the header and transparent section digests differ
even when the underlying inputs serialise to the same payload. -/
theorem header_ne_transparent (H : AbstractHashFamily) (t : TagIds)
    (hT : t.Distinct) (hIn : HeaderInputs) (tIn : TransparentInputs)
    (hEqPayload :
      hIn.headerPayload =
        (prevoutsDigest H t tIn ++ sequenceDigest H t tIn
          ++ outputsDigest H t tIn)) :
    headerDigest H t hIn ≠ transparentDigest H t tIn := by
  obtain ⟨_, _, _, _, h_ht, _, _, _, _, _⟩ := hT.top_level
  unfold headerDigest transparentDigest
  rw [hEqPayload]
  exact domain_separation_eq_payload H _ _ _ h_ht

/-- **T4 (sapling vs orchard domain separation).** -/
theorem sapling_ne_orchard (H : AbstractHashFamily) (t : TagIds)
    (hT : t.Distinct) (sIn : SaplingInputs) (oIn : OrchardInputs)
    (hEqPayload :
      (saplingSpendsDigest H t sIn ++ saplingOutputsDigest H t sIn
        ++ sIn.valueBalancePayload) = oIn.bundlePayload) :
    saplingDigest H t sIn ≠ orchardDigest H t oIn := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h_s_o⟩ := hT.top_level
  unfold saplingDigest orchardDigest
  rw [hEqPayload]
  exact domain_separation_eq_payload H _ _ _ h_s_o

/-- **T5 (top-level tags pairwise distinct ⇒ digests pairwise distinct
on equal payloads).** All four top-level section tags give pairwise
distinct hash outputs when applied to the same payload bytes. -/
theorem all_top_level_pairwise_distinct (H : AbstractHashFamily)
    (t : TagIds) (hT : t.Distinct) (payload : List Nat) :
    keyedHash H t.header payload ≠ keyedHash H t.transparent payload ∧
    keyedHash H t.header payload ≠ keyedHash H t.sapling payload ∧
    keyedHash H t.header payload ≠ keyedHash H t.orchard payload ∧
    keyedHash H t.transparent payload ≠ keyedHash H t.sapling payload ∧
    keyedHash H t.transparent payload ≠ keyedHash H t.orchard payload ∧
    keyedHash H t.sapling payload ≠ keyedHash H t.orchard payload := by
  obtain ⟨_, _, _, _, h_ht, h_hs, h_ho, h_ts, h_to, h_so⟩ := hT.top_level
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply domain_separation_eq_payload H _ _ _
  · exact h_ht
  · exact h_hs
  · exact h_ho
  · exact h_ts
  · exact h_to
  · exact h_so

/-- **T6 (txid is a function of root inputs).** Equal inputs ⇒ equal
txid; the txid is fully determined by `(H, t, B, branchId, hIn, tIn,
sIn, oIn)`. -/
theorem txid_function_of_inputs (H : AbstractHashFamily) (t : TagIds)
    (B : BranchIdBinding) (branchId : Nat)
    (hIn hIn' : HeaderInputs) (tIn tIn' : TransparentInputs)
    (sIn sIn' : SaplingInputs) (oIn oIn' : OrchardInputs)
    (hh : hIn = hIn') (ht : tIn = tIn') (hs : sIn = sIn')
    (ho : oIn = oIn') :
    txidRoot H t B branchId hIn tIn sIn oIn =
      txidRoot H t B branchId hIn' tIn' sIn' oIn' := by
  subst hh; subst ht; subst hs; subst ho; rfl

/-- **T7 (txid injective in concatenated section leaves).** Two
top-level input tuples with equal concatenated section digests (under
the same branch id) yield equal txids; conversely equal txids force
the concatenated section digests to coincide. -/
theorem txid_inj_section_concat (H : AbstractHashFamily) (t : TagIds)
    (B : BranchIdBinding) (branchId : Nat)
    (hIn₁ hIn₂ : HeaderInputs)
    (tIn₁ tIn₂ : TransparentInputs)
    (sIn₁ sIn₂ : SaplingInputs)
    (oIn₁ oIn₂ : OrchardInputs)
    (h : txidRoot H t B branchId hIn₁ tIn₁ sIn₁ oIn₁ =
         txidRoot H t B branchId hIn₂ tIn₂ sIn₂ oIn₂) :
    headerDigest H t hIn₁ ++ transparentDigest H t tIn₁
      ++ saplingDigest H t sIn₁ ++ orchardDigest H t oIn₁ =
    headerDigest H t hIn₂ ++ transparentDigest H t tIn₂
      ++ saplingDigest H t sIn₂ ++ orchardDigest H t oIn₂ := by
  unfold txidRoot at h
  exact H.inj_payload _ h

/-- **T8 (section digests determine the txid; section-injective under
matching widths).** If the four section digests have matching lengths
and equal concatenations under the same branch id, the *section
digests* are componentwise equal. -/
theorem txid_inj_section_digests (H : AbstractHashFamily) (t : TagIds)
    (B : BranchIdBinding) (branchId : Nat)
    (hIn₁ hIn₂ : HeaderInputs)
    (tIn₁ tIn₂ : TransparentInputs)
    (sIn₁ sIn₂ : SaplingInputs)
    (oIn₁ oIn₂ : OrchardInputs)
    (lh : (headerDigest H t hIn₁).length = (headerDigest H t hIn₂).length)
    (lt : (transparentDigest H t tIn₁).length =
            (transparentDigest H t tIn₂).length)
    (ls : (saplingDigest H t sIn₁).length = (saplingDigest H t sIn₂).length)
    (h : txidRoot H t B branchId hIn₁ tIn₁ sIn₁ oIn₁ =
         txidRoot H t B branchId hIn₂ tIn₂ sIn₂ oIn₂) :
    headerDigest H t hIn₁ = headerDigest H t hIn₂ ∧
    transparentDigest H t tIn₁ = transparentDigest H t tIn₂ ∧
    saplingDigest H t sIn₁ = saplingDigest H t sIn₂ ∧
    orchardDigest H t oIn₁ = orchardDigest H t oIn₂ := by
  have hcat := txid_inj_section_concat H t B branchId
                 hIn₁ hIn₂ tIn₁ tIn₂ sIn₁ sIn₂ oIn₁ oIn₂ h
  -- Strip orchard (lengths match: the concat lengths of the first three
  -- section digests must coincide for the final orchard slice to align).
  have hHTSLen :
      (headerDigest H t hIn₁ ++ transparentDigest H t tIn₁
        ++ saplingDigest H t sIn₁).length =
      (headerDigest H t hIn₂ ++ transparentDigest H t tIn₂
        ++ saplingDigest H t sIn₂).length := by
    simp [List.length_append, lh, lt, ls]
  have hOrc := List.append_inj hcat hHTSLen
  -- Strip sapling: header ++ transparent lengths match.
  have hHTLen :
      (headerDigest H t hIn₁ ++ transparentDigest H t tIn₁).length =
      (headerDigest H t hIn₂ ++ transparentDigest H t tIn₂).length := by
    simp [List.length_append, lh, lt]
  have hSap := List.append_inj hOrc.1 hHTLen
  -- Strip transparent: header lengths match.
  have hHdr := List.append_inj hSap.1 lh
  refine ⟨hHdr.1, hHdr.2, hSap.2, hOrc.2⟩

/-- **T9 (cross-personal hash never collides on different tag,payload
pairs).** Direct consequence of `H.inj`; restated so callers needn't
reach into the structure. -/
theorem hash_no_cross_collision (H : AbstractHashFamily)
    {t₁ t₂ : Nat} {p₁ p₂ : List Nat} (h : (t₁, p₁) ≠ (t₂, p₂)) :
    H.hash t₁ p₁ ≠ H.hash t₂ p₂ := by
  intro heq
  obtain ⟨ht, hp⟩ := H.inj heq
  exact h (by simp [ht, hp])

/-- **T10 (changing only the orchard sub-input changes the txid).** If
the four section digests on the right agree on header/transparent/
sapling but differ on orchard, the txids differ. -/
theorem orchard_change_changes_txid (H : AbstractHashFamily) (t : TagIds)
    (B : BranchIdBinding) (branchId : Nat)
    (hIn : HeaderInputs) (tIn : TransparentInputs) (sIn : SaplingInputs)
    (oIn₁ oIn₂ : OrchardInputs) (hne : oIn₁.bundlePayload ≠ oIn₂.bundlePayload) :
    txidRoot H t B branchId hIn tIn sIn oIn₁ ≠
      txidRoot H t B branchId hIn tIn sIn oIn₂ := by
  intro heq
  have hcat := txid_inj_section_concat H t B branchId
                 hIn hIn tIn tIn sIn sIn oIn₁ oIn₂ heq
  -- Both sides share the prefix `headerDigest ++ transparentDigest ++
  -- saplingDigest`; cancel and reduce to `orchardDigest H t oIn₁ =
  -- orchardDigest H t oIn₂`.
  have horc : orchardDigest H t oIn₁ = orchardDigest H t oIn₂ :=
    List.append_cancel_left hcat
  -- Unfold orchardDigest = keyedHash on the bundle payloads and invert.
  unfold orchardDigest keyedHash at horc
  exact hne (H.inj_payload _ horc)

/-- **T11 (per-section payload injectivity).** Distinct payloads in any
section's keyed hash give distinct section digests — the section-level
counterpart of T1. -/
theorem section_payload_injective (H : AbstractHashFamily) (t : TagIds)
    (p₁ p₂ : List Nat) (hne : p₁ ≠ p₂) :
    keyedHash H t.header p₁ ≠ keyedHash H t.header p₂ ∧
    keyedHash H t.transparent p₁ ≠ keyedHash H t.transparent p₂ ∧
    keyedHash H t.sapling p₁ ≠ keyedHash H t.sapling p₂ ∧
    keyedHash H t.orchard p₁ ≠ keyedHash H t.orchard p₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · intro h
      exact hne (keyedHash_inj_payload H _ _ _ h)

/-- **T12 (txid ↔ inputs iff matching widths).** Combined functional +
section-injective statement: two txid computations agree iff the four
section-digest tuples coincide (componentwise) — assuming matching
section-digest widths. -/
theorem txid_iff_section_digests (H : AbstractHashFamily) (t : TagIds)
    (B : BranchIdBinding) (branchId : Nat)
    (hIn₁ hIn₂ : HeaderInputs)
    (tIn₁ tIn₂ : TransparentInputs)
    (sIn₁ sIn₂ : SaplingInputs)
    (oIn₁ oIn₂ : OrchardInputs)
    (lh : (headerDigest H t hIn₁).length = (headerDigest H t hIn₂).length)
    (lt : (transparentDigest H t tIn₁).length =
            (transparentDigest H t tIn₂).length)
    (ls : (saplingDigest H t sIn₁).length = (saplingDigest H t sIn₂).length) :
    txidRoot H t B branchId hIn₁ tIn₁ sIn₁ oIn₁ =
      txidRoot H t B branchId hIn₂ tIn₂ sIn₂ oIn₂ ↔
    headerDigest H t hIn₁ = headerDigest H t hIn₂ ∧
    transparentDigest H t tIn₁ = transparentDigest H t tIn₂ ∧
    saplingDigest H t sIn₁ = saplingDigest H t sIn₂ ∧
    orchardDigest H t oIn₁ = orchardDigest H t oIn₂ := by
  refine ⟨?_, ?_⟩
  · exact txid_inj_section_digests H t B branchId
            hIn₁ hIn₂ tIn₁ tIn₂ sIn₁ sIn₂ oIn₁ oIn₂ lh lt ls
  · intro ⟨hh, hht, hs, ho⟩
    unfold txidRoot
    rw [hh, hht, hs, ho]

/-- **T13 (branch-id binding into the root).** Different
`consensus_branch_id`s yield different txids on byte-for-byte identical
section digests. This is the "the root personalisation
`ZcashTxHash_ ‖ branchId` matters" property — replaying a transaction
on a different branch (NU activation) is a structural collision the txid
must distinguish.

Previously the model elided the branch id (hidden in a single opaque
`t.root`), so this theorem was unstateable. -/
theorem distinct_branch_ids_distinct_txid (H : AbstractHashFamily)
    (t : TagIds) (B : BranchIdBinding)
    (branchId₁ branchId₂ : Nat)
    (hIn : HeaderInputs) (tIn : TransparentInputs) (sIn : SaplingInputs)
    (oIn : OrchardInputs) (hne : branchId₁ ≠ branchId₂) :
    txidRoot H t B branchId₁ hIn tIn sIn oIn ≠
      txidRoot H t B branchId₂ hIn tIn sIn oIn := by
  intro heq
  unfold txidRoot at heq
  obtain ⟨htag, _⟩ := H.inj heq
  exact hne (B.inj htag)

/-- **T14 (txid root recipe — replaces former T15).** The txid is, by
construction, `H.hash (rootTag branchId)` applied to the concatenation
of the four section digests. Stated as `rfl` for use as a *rewrite
lemma* in proofs that unfold the root construction; the meaningful
deterministic-txid claim is captured by T13 (branch-id binding) and T6
(input-functional). -/
theorem txid_root_recipe (H : AbstractHashFamily) (t : TagIds)
    (B : BranchIdBinding) (branchId : Nat)
    (hIn : HeaderInputs) (tIn : TransparentInputs) (sIn : SaplingInputs)
    (oIn : OrchardInputs) :
    txidRoot H t B branchId hIn tIn sIn oIn =
      H.hash (B.effectiveRootTag branchId)
        (headerDigest H t hIn ++ transparentDigest H t tIn
          ++ saplingDigest H t sIn ++ orchardDigest H t oIn) :=
  rfl

/-! ## Sub-digest theorems

These theorems address Finding 56 (the prior model only proved
properties of the top-level tree). Each section-level digest is itself
the hash of structured level-2 inputs; collisions in those inputs
propagate to the section digest, and ultimately to the txid. -/

/-- **T15 (level-2 transparent injectivity in concatenated sub-inputs).**
Equal transparent section digests force the *concatenation* of the
three level-2 sub-digests to coincide. -/
theorem transparent_section_inj_concat (H : AbstractHashFamily)
    (t : TagIds) (tIn₁ tIn₂ : TransparentInputs)
    (h : transparentDigest H t tIn₁ = transparentDigest H t tIn₂) :
    prevoutsDigest H t tIn₁ ++ sequenceDigest H t tIn₁
      ++ outputsDigest H t tIn₁ =
    prevoutsDigest H t tIn₂ ++ sequenceDigest H t tIn₂
      ++ outputsDigest H t tIn₂ := by
  unfold transparentDigest at h
  exact H.inj_payload _ h

/-- **T16 (level-2 sapling injectivity in concatenated sub-inputs).**
Equal sapling section digests force the *concatenation* of the three
level-2 sub-payloads (spends ‖ outputs ‖ value_balance) to coincide. -/
theorem sapling_section_inj_concat (H : AbstractHashFamily)
    (t : TagIds) (sIn₁ sIn₂ : SaplingInputs)
    (h : saplingDigest H t sIn₁ = saplingDigest H t sIn₂) :
    saplingSpendsDigest H t sIn₁ ++ saplingOutputsDigest H t sIn₁
      ++ sIn₁.valueBalancePayload =
    saplingSpendsDigest H t sIn₂ ++ saplingOutputsDigest H t sIn₂
      ++ sIn₂.valueBalancePayload := by
  unfold saplingDigest at h
  exact H.inj_payload _ h

/-- **T17 (transparent sub-digests determine `TransparentInputs` under
matching widths).** Given matching sub-digest lengths, equal transparent
section digests imply equal level-2 *payloads*, hence equal
`TransparentInputs`. -/
theorem transparent_sub_inputs_injective (H : AbstractHashFamily)
    (t : TagIds) (tIn₁ tIn₂ : TransparentInputs)
    (lpre : (prevoutsDigest H t tIn₁).length =
              (prevoutsDigest H t tIn₂).length)
    (lseq : (sequenceDigest H t tIn₁).length =
              (sequenceDigest H t tIn₂).length)
    (h : transparentDigest H t tIn₁ = transparentDigest H t tIn₂) :
    tIn₁ = tIn₂ := by
  have hcat := transparent_section_inj_concat H t tIn₁ tIn₂ h
  -- Strip outputs slice off the right.
  have hPSLen :
      (prevoutsDigest H t tIn₁ ++ sequenceDigest H t tIn₁).length =
      (prevoutsDigest H t tIn₂ ++ sequenceDigest H t tIn₂).length := by
    simp [List.length_append, lpre, lseq]
  have hOut := List.append_inj hcat hPSLen
  have hSeq := List.append_inj hOut.1 lpre
  have hPreDig : prevoutsDigest H t tIn₁ = prevoutsDigest H t tIn₂ := hSeq.1
  have hSeqDig : sequenceDigest H t tIn₁ = sequenceDigest H t tIn₂ := hSeq.2
  have hOutDig : outputsDigest H t tIn₁ = outputsDigest H t tIn₂ := hOut.2
  -- Unfold each sub-digest = keyedHash, then invert with H.inj_payload.
  unfold prevoutsDigest keyedHash at hPreDig
  unfold sequenceDigest keyedHash at hSeqDig
  unfold outputsDigest keyedHash at hOutDig
  have hPrePayload :
      tIn₁.prevoutsPayload = tIn₂.prevoutsPayload :=
    H.inj_payload _ hPreDig
  have hSeqPayload :
      tIn₁.sequencePayload = tIn₂.sequencePayload :=
    H.inj_payload _ hSeqDig
  have hOutPayload :
      tIn₁.outputsPayload = tIn₂.outputsPayload :=
    H.inj_payload _ hOutDig
  cases tIn₁; cases tIn₂; simp_all

/-- **T18 (sapling sub-digests determine `SaplingInputs` under matching
widths).** Given matching sub-digest lengths *and* matching
value-balance widths, equal sapling section digests imply equal
`SaplingInputs`. -/
theorem sapling_sub_inputs_injective (H : AbstractHashFamily)
    (t : TagIds) (sIn₁ sIn₂ : SaplingInputs)
    (lspe : (saplingSpendsDigest H t sIn₁).length =
              (saplingSpendsDigest H t sIn₂).length)
    (lout : (saplingOutputsDigest H t sIn₁).length =
              (saplingOutputsDigest H t sIn₂).length)
    (h : saplingDigest H t sIn₁ = saplingDigest H t sIn₂) :
    sIn₁ = sIn₂ := by
  have hcat := sapling_section_inj_concat H t sIn₁ sIn₂ h
  -- Strip value_balance slice off the right.
  have hSpOLen :
      (saplingSpendsDigest H t sIn₁ ++ saplingOutputsDigest H t sIn₁).length =
      (saplingSpendsDigest H t sIn₂ ++ saplingOutputsDigest H t sIn₂).length := by
    simp [List.length_append, lspe, lout]
  have hVB := List.append_inj hcat hSpOLen
  have hOuts := List.append_inj hVB.1 lspe
  unfold saplingSpendsDigest saplingOutputsDigest keyedHash at hOuts
  have hSpPayload :
      sIn₁.spendsPayload = sIn₂.spendsPayload :=
    H.inj_payload _ hOuts.1
  have hOuPayload :
      sIn₁.outputsPayload = sIn₂.outputsPayload :=
    H.inj_payload _ hOuts.2
  cases sIn₁; cases sIn₂; simp_all

/-- **T19 (orchard sub-input injectivity).** Equal orchard section
digests force equal `OrchardInputs.bundlePayload`. -/
theorem orchard_sub_inputs_injective (H : AbstractHashFamily)
    (t : TagIds) (oIn₁ oIn₂ : OrchardInputs)
    (h : orchardDigest H t oIn₁ = orchardDigest H t oIn₂) :
    oIn₁ = oIn₂ := by
  unfold orchardDigest keyedHash at h
  have := H.inj_payload _ h
  cases oIn₁; cases oIn₂; simp_all

/-- **T20 (recursive end-to-end injectivity).** Given matching widths at
all leaves and equal txids under the same branch id, the *full* tuple of
level-2 inputs (transparent prevouts/sequence/outputs payloads, sapling
spends/outputs/value_balance payloads, orchard bundle payload, plus the
header payload) coincides. This is the recursive sub-digest injectivity
claim flagged by Finding 56. -/
theorem txid_recursive_injectivity (H : AbstractHashFamily) (t : TagIds)
    (B : BranchIdBinding) (branchId : Nat)
    (hIn₁ hIn₂ : HeaderInputs)
    (tIn₁ tIn₂ : TransparentInputs)
    (sIn₁ sIn₂ : SaplingInputs)
    (oIn₁ oIn₂ : OrchardInputs)
    (lh : (headerDigest H t hIn₁).length = (headerDigest H t hIn₂).length)
    (lt : (transparentDigest H t tIn₁).length =
            (transparentDigest H t tIn₂).length)
    (ls : (saplingDigest H t sIn₁).length = (saplingDigest H t sIn₂).length)
    (lpre : (prevoutsDigest H t tIn₁).length =
              (prevoutsDigest H t tIn₂).length)
    (lseq : (sequenceDigest H t tIn₁).length =
              (sequenceDigest H t tIn₂).length)
    (lspe : (saplingSpendsDigest H t sIn₁).length =
              (saplingSpendsDigest H t sIn₂).length)
    (lsout : (saplingOutputsDigest H t sIn₁).length =
              (saplingOutputsDigest H t sIn₂).length)
    (h : txidRoot H t B branchId hIn₁ tIn₁ sIn₁ oIn₁ =
         txidRoot H t B branchId hIn₂ tIn₂ sIn₂ oIn₂) :
    hIn₁ = hIn₂ ∧ tIn₁ = tIn₂ ∧ sIn₁ = sIn₂ ∧ oIn₁ = oIn₂ := by
  obtain ⟨hh, hht, hs, ho⟩ :=
    txid_inj_section_digests H t B branchId
      hIn₁ hIn₂ tIn₁ tIn₂ sIn₁ sIn₂ oIn₁ oIn₂ lh lt ls h
  have hHdrIn : hIn₁ = hIn₂ := by
    unfold headerDigest keyedHash at hh
    have := H.inj_payload _ hh
    cases hIn₁; cases hIn₂; simp_all
  have hTrIn : tIn₁ = tIn₂ :=
    transparent_sub_inputs_injective H t tIn₁ tIn₂ lpre lseq hht
  have hSaIn : sIn₁ = sIn₂ :=
    sapling_sub_inputs_injective H t sIn₁ sIn₂ lspe lsout hs
  have hOrIn : oIn₁ = oIn₂ :=
    orchard_sub_inputs_injective H t oIn₁ oIn₂ ho
  exact ⟨hHdrIn, hTrIn, hSaIn, hOrIn⟩

/-- **T21 (changing a single level-2 transparent payload changes the
txid).** If two transactions agree everywhere except in their level-2
transparent prevouts payload, the txids differ. A focused corollary of
T20 plus T17 — exhibits the sub-digest binding the prior model could
not state. -/
theorem prevouts_change_changes_txid (H : AbstractHashFamily) (t : TagIds)
    (B : BranchIdBinding) (branchId : Nat)
    (hIn : HeaderInputs) (sIn : SaplingInputs) (oIn : OrchardInputs)
    (tIn₁ tIn₂ : TransparentInputs)
    (hOther₁ : tIn₁.sequencePayload = tIn₂.sequencePayload)
    (hOther₂ : tIn₁.outputsPayload = tIn₂.outputsPayload)
    (hne : tIn₁.prevoutsPayload ≠ tIn₂.prevoutsPayload) :
    txidRoot H t B branchId hIn tIn₁ sIn oIn ≠
      txidRoot H t B branchId hIn tIn₂ sIn oIn := by
  intro heq
  have hcat := txid_inj_section_concat H t B branchId
                 hIn hIn tIn₁ tIn₂ sIn sIn oIn oIn heq
  -- Cancel header prefix (identical).
  have hcat1 :
      transparentDigest H t tIn₁ ++ saplingDigest H t sIn
        ++ orchardDigest H t oIn =
      transparentDigest H t tIn₂ ++ saplingDigest H t sIn
        ++ orchardDigest H t oIn := by
    have := hcat
    -- Rewrite `headerDigest H t hIn` on both sides and use `append_cancel_left`.
    have left :
        headerDigest H t hIn ++
          (transparentDigest H t tIn₁ ++ saplingDigest H t sIn
            ++ orchardDigest H t oIn) =
        headerDigest H t hIn ++ transparentDigest H t tIn₁
          ++ saplingDigest H t sIn ++ orchardDigest H t oIn := by
      simp [List.append_assoc]
    have right :
        headerDigest H t hIn ++
          (transparentDigest H t tIn₂ ++ saplingDigest H t sIn
            ++ orchardDigest H t oIn) =
        headerDigest H t hIn ++ transparentDigest H t tIn₂
          ++ saplingDigest H t sIn ++ orchardDigest H t oIn := by
      simp [List.append_assoc]
    exact List.append_cancel_left (left.trans (this.trans right.symm))
  -- Cancel sapling ++ orchard suffix (identical).
  have htdEq : transparentDigest H t tIn₁ = transparentDigest H t tIn₂ := by
    have hlen :
        (transparentDigest H t tIn₁).length =
          (transparentDigest H t tIn₂).length := by
      -- Both transparent digests have the same length because they're the same hash output.
      -- We can derive it from hcat1 via list-length symmetries, but a cleaner approach:
      -- both sides of hcat1 have the same length, so the lengths of corresponding
      -- prefixes match.
      have hL :
          (transparentDigest H t tIn₁ ++ saplingDigest H t sIn
              ++ orchardDigest H t oIn).length =
          (transparentDigest H t tIn₂ ++ saplingDigest H t sIn
              ++ orchardDigest H t oIn).length := by
        rw [hcat1]
      simp [List.length_append] at hL
      omega
    have hAssoc1 :
        transparentDigest H t tIn₁ ++ saplingDigest H t sIn
          ++ orchardDigest H t oIn =
        transparentDigest H t tIn₁ ++
          (saplingDigest H t sIn ++ orchardDigest H t oIn) := by
      simp [List.append_assoc]
    have hAssoc2 :
        transparentDigest H t tIn₂ ++ saplingDigest H t sIn
          ++ orchardDigest H t oIn =
        transparentDigest H t tIn₂ ++
          (saplingDigest H t sIn ++ orchardDigest H t oIn) := by
      simp [List.append_assoc]
    have hReassoc :
        transparentDigest H t tIn₁ ++
          (saplingDigest H t sIn ++ orchardDigest H t oIn) =
        transparentDigest H t tIn₂ ++
          (saplingDigest H t sIn ++ orchardDigest H t oIn) :=
      hAssoc1.symm.trans (hcat1.trans hAssoc2)
    exact (List.append_inj hReassoc hlen).1
  -- Two equal transparent digests with matching prevouts/sequence widths
  -- imply equal TransparentInputs (T17). But T17 requires per-sub-digest
  -- widths to match. The level-2 hash outputs have unspecified abstract
  -- lengths; in the model they need not coincide unless we assume so.
  -- We bypass T17 by using injectivity directly on the transparent-section
  -- payload, then on the prevouts payload via append-cancel.
  have hPay :
      prevoutsDigest H t tIn₁ ++ sequenceDigest H t tIn₁
        ++ outputsDigest H t tIn₁ =
      prevoutsDigest H t tIn₂ ++ sequenceDigest H t tIn₂
        ++ outputsDigest H t tIn₂ :=
    transparent_section_inj_concat H t tIn₁ tIn₂ htdEq
  -- `sequencePayload` and `outputsPayload` are equal on both sides, so
  -- the corresponding `sequenceDigest` and `outputsDigest` are equal too.
  have hSeqEq : sequenceDigest H t tIn₁ = sequenceDigest H t tIn₂ := by
    unfold sequenceDigest; rw [hOther₁]
  have hOutEq : outputsDigest H t tIn₁ = outputsDigest H t tIn₂ := by
    unfold outputsDigest; rw [hOther₂]
  -- Rewrite hPay so the right-hand factors match, then cancel from the right.
  rw [hSeqEq, hOutEq] at hPay
  -- hPay : prevoutsDigest H t tIn₁ ++ X ++ Y = prevoutsDigest H t tIn₂ ++ X ++ Y
  -- Use append_left_inj-style cancellation on the right via list reassociation.
  have hPay' :
      prevoutsDigest H t tIn₁ ++ (sequenceDigest H t tIn₂ ++ outputsDigest H t tIn₂) =
      prevoutsDigest H t tIn₂ ++ (sequenceDigest H t tIn₂ ++ outputsDigest H t tIn₂) := by
    have l : prevoutsDigest H t tIn₁
              ++ sequenceDigest H t tIn₂ ++ outputsDigest H t tIn₂ =
             prevoutsDigest H t tIn₁
              ++ (sequenceDigest H t tIn₂ ++ outputsDigest H t tIn₂) := by
      simp [List.append_assoc]
    have r : prevoutsDigest H t tIn₂
              ++ sequenceDigest H t tIn₂ ++ outputsDigest H t tIn₂ =
             prevoutsDigest H t tIn₂
              ++ (sequenceDigest H t tIn₂ ++ outputsDigest H t tIn₂) := by
      simp [List.append_assoc]
    exact l.symm.trans (hPay.trans r)
  have hPreEq : prevoutsDigest H t tIn₁ = prevoutsDigest H t tIn₂ :=
    (List.append_left_inj _).mp hPay'
  unfold prevoutsDigest keyedHash at hPreEq
  exact hne (H.inj_payload _ hPreEq)

end Zebra.Zip244TxIdDigest
