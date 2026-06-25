import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# ZIP-244 NU5 transaction-ID digest tree

For V5 transactions, the txid is the root of a 5-level digest tree, as
specified in ZIP-244 and ZIP-225. Each intermediate node is a BLAKE2b-256
hash personalised with a distinct domain-separation tag, applied to the
concatenation of its child digests. Zebra delegates V5 txid computation to
librustzcash:

```rust
fn txid_v5(self) -> Option<Hash> {
    let nu = self.trans.network_upgrade()?;
    Some(Hash(*self.trans.to_librustzcash(nu).ok()?.txid().as_ref()))
}
```
Source: `zebra-chain/src/transaction/txid.rs:47-52`.

The ZIP-244 tree structure is:

```
txid = H[ZcashTxHash_]( headerDigest || transparentDigest
                       || saplingDigest || orchardDigest )
```

with each section digest itself defined as a hash of sub-digests under its
own personalisation tag. We model the *structural* properties of this tree
abstractly:

  * Tags are arbitrary `List Nat` (BLAKE2b personalisation strings); we
    only require they are pairwise distinct.
  * The hash function is abstract, parameterised as an injective
    `List Nat → List Nat`. This captures the cryptographic assumption
    used in the consensus-correctness argument *without* modelling the
    actual BLAKE2b primitive.
  * Each section produces a fixed-length leaf digest; the tree composition
    is `concat` of (tag :: leaves), then hash.

The load-bearing claims modelled here:

  1. **Domain separation.** Different domain-separation tags applied to
     the same payload yield distinct intermediate digests. Concretely,
     prepending distinct tags before an injective hash gives distinct
     outputs.
  2. **Leaf-only dependence.** The txid is a pure function of the four
     section leaves (plus the fixed tag tree).
  3. **Injectivity in section inputs.** Under the abstract injective-hash
     assumption, the V5 txid uniquely determines the tuple of section
     leaves.

We do *not* model BLAKE2b or any actual byte-level structure — these are
the abstract algebraic properties that the consensus-correctness argument
relies on.

Source: <https://zips.z.cash/zip-0244#specification>
Source: `zebra-chain/src/transaction/txid.rs:44-52`.
-/

namespace Zebra.Zip244TxIdDigest

/-! ## Domain-separation tags

ZIP-244 specifies a 16-byte BLAKE2b personalisation string for each
intermediate hash:

  * `ZcashTxHash_<branchId>` — the root txid hash
  * `ZTxIdHeadersHash`       — header digest
  * `ZTxIdTranspaHash`       — transparent digest
  * `ZTxIdSAllHash`          — sapling digest
  * `ZTxIdOrcAllHash`        — orchard digest

We treat each tag as an arbitrary byte list and demand only that the five
tags used at the root + four sections are pairwise distinct. -/

/-- The five domain-separation tags used by the ZIP-244 txid tree:
root, header, transparent, sapling, orchard. -/
structure Tags where
  root : List Nat
  header : List Nat
  transparent : List Nat
  sapling : List Nat
  orchard : List Nat
  deriving Repr

/-- Pairwise distinctness of the five ZIP-244 tags — the structural
condition that makes domain separation work. -/
def Tags.Distinct (t : Tags) : Prop :=
  t.root ≠ t.header ∧ t.root ≠ t.transparent ∧
  t.root ≠ t.sapling ∧ t.root ≠ t.orchard ∧
  t.header ≠ t.transparent ∧ t.header ≠ t.sapling ∧
  t.header ≠ t.orchard ∧
  t.transparent ≠ t.sapling ∧ t.transparent ≠ t.orchard ∧
  t.sapling ≠ t.orchard

/-! ## Section leaves

The four section digests are the leaves of the top-level tree. Each is a
`List Nat` (BLAKE2b-256 produces 32 bytes; we don't pin the length here
since the structural properties are length-agnostic). -/

/-- The four ZIP-244 section leaves: header, transparent, sapling,
orchard. These are themselves digests of sub-trees, but at the top level
we only need their values. -/
structure Sections where
  header : List Nat
  transparent : List Nat
  sapling : List Nat
  orchard : List Nat
  deriving DecidableEq, Repr

/-! ## Abstract hash model

We parameterise over an arbitrary hash function `List Nat → List Nat`
and assume it is injective. BLAKE2b is conjectured collision-resistant,
which abstractly is the injectivity assumption modulo the negligible
probability of collisions — exactly what the consensus argument uses. -/

/-- An abstract injective hash function (i.e. collision-free).
This captures the BLAKE2b assumption used in the ZIP-244 correctness
argument. -/
structure AbstractHash where
  hash : List Nat → List Nat
  inj : Function.Injective hash

/-! ## Tree composition

The ZIP-244 txid is `H_root(headerDigest || transparentDigest ||
saplingDigest || orchardDigest)`, with the personalisation tag baked into
`H_root`. We model the personalisation by prepending the tag bytes to the
payload before applying the abstract injective hash. -/

/-- Apply a personalised hash: prepend the tag, then run the abstract
hash. This is the abstract structural counterpart of BLAKE2b with a
personalisation string. -/
def personalisedHash (H : AbstractHash) (tag payload : List Nat) : List Nat :=
  H.hash (tag ++ payload)

/-- The ZIP-244 top-level digest tree: hash the concatenation of the four
section leaves under the root tag.

The librustzcash implementation feeds each leaf in turn into the BLAKE2b
state initialised with the root personalisation; structurally this is
equivalent to hashing the concatenation. -/
def txidRoot (H : AbstractHash) (t : Tags) (s : Sections) : List Nat :=
  personalisedHash H t.root (s.header ++ s.transparent ++ s.sapling ++ s.orchard)

/-- The header section digest. ZIP-244 defines this as a tag-personalised
hash of the (version, version-group-id, consensus-branch-id, lock-time,
expiry-height) tuple; we abstract over the tuple as a `List Nat`. -/
def headerDigest (H : AbstractHash) (t : Tags) (headerPayload : List Nat) : List Nat :=
  personalisedHash H t.header headerPayload

/-- The transparent section digest. -/
def transparentDigest (H : AbstractHash) (t : Tags)
    (transparentPayload : List Nat) : List Nat :=
  personalisedHash H t.transparent transparentPayload

/-- The sapling section digest. -/
def saplingDigest (H : AbstractHash) (t : Tags) (saplingPayload : List Nat) : List Nat :=
  personalisedHash H t.sapling saplingPayload

/-- The orchard section digest. -/
def orchardDigest (H : AbstractHash) (t : Tags) (orchardPayload : List Nat) : List Nat :=
  personalisedHash H t.orchard orchardPayload

/-! ## Theorems -/

/-- **T1 (personalised hash injective in payload, fixed tag).** For a
fixed personalisation tag, the personalised hash is injective in its
payload. This is the "domain separation within a section" property — two
distinct payloads under the same tag give distinct digests. -/
theorem personalisedHash_inj_payload (H : AbstractHash) (tag : List Nat)
    (p₁ p₂ : List Nat)
    (h : personalisedHash H tag p₁ = personalisedHash H tag p₂) : p₁ = p₂ := by
  unfold personalisedHash at h
  exact List.append_cancel_left (H.inj h)

/-- **T2 (domain separation: distinct tags ⇒ distinct digests on equal
payload).** If two tags are unequal, then prepending them before the
abstract injective hash on the same payload produces distinct outputs.

This is the precise abstract counterpart of the ZIP-244 claim that
personalisation strings give independent hash families. -/
theorem domain_separation_eq_payload (H : AbstractHash)
    (tag₁ tag₂ payload : List Nat) (hne : tag₁ ≠ tag₂) :
    personalisedHash H tag₁ payload ≠ personalisedHash H tag₂ payload := by
  intro heq
  unfold personalisedHash at heq
  have hcat := H.inj heq
  -- `tag₁ ++ payload = tag₂ ++ payload` ⇒ `tag₁ = tag₂` by `append_left_inj`.
  exact hne ((List.append_left_inj payload).mp hcat)

/-- **T3 (header vs transparent domain separation).** With distinct tags,
the header and transparent intermediate digests differ even when applied
to the same payload. -/
theorem header_ne_transparent (H : AbstractHash) (t : Tags)
    (hT : t.Distinct) (payload : List Nat) :
    headerDigest H t payload ≠ transparentDigest H t payload := by
  unfold headerDigest transparentDigest
  exact domain_separation_eq_payload H _ _ payload hT.2.2.2.2.1

/-- **T4 (sapling vs orchard domain separation).** -/
theorem sapling_ne_orchard (H : AbstractHash) (t : Tags)
    (hT : t.Distinct) (payload : List Nat) :
    saplingDigest H t payload ≠ orchardDigest H t payload := by
  unfold saplingDigest orchardDigest
  exact domain_separation_eq_payload H _ _ payload hT.2.2.2.2.2.2.2.2.2

/-- **T5 (every pairwise section tag differs).** All four section
digests, when applied to the same payload, are pairwise distinct under
`Distinct` tags. -/
theorem all_sections_pairwise_distinct (H : AbstractHash) (t : Tags)
    (hT : t.Distinct) (payload : List Nat) :
    headerDigest H t payload ≠ transparentDigest H t payload ∧
    headerDigest H t payload ≠ saplingDigest H t payload ∧
    headerDigest H t payload ≠ orchardDigest H t payload ∧
    transparentDigest H t payload ≠ saplingDigest H t payload ∧
    transparentDigest H t payload ≠ orchardDigest H t payload ∧
    saplingDigest H t payload ≠ orchardDigest H t payload := by
  obtain ⟨_, _, _, _, h_ht, h_hs, h_ho, h_ts, h_to, h_so⟩ := hT
  unfold headerDigest transparentDigest saplingDigest orchardDigest
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact domain_separation_eq_payload H _ _ payload h_ht
  · exact domain_separation_eq_payload H _ _ payload h_hs
  · exact domain_separation_eq_payload H _ _ payload h_ho
  · exact domain_separation_eq_payload H _ _ payload h_ts
  · exact domain_separation_eq_payload H _ _ payload h_to
  · exact domain_separation_eq_payload H _ _ payload h_so

/-- **T6 (txid depends only on section leaves and tags).** The root txid
is a pure function of `Tags` and `Sections` (given the hash). Equal tags
+ equal sections ⇒ equal txids. This is the leaf-only-dependence claim
formalised as the obvious congruence. -/
theorem txid_function_of_sections (H : AbstractHash) (t : Tags) (s₁ s₂ : Sections)
    (h : s₁ = s₂) : txidRoot H t s₁ = txidRoot H t s₂ := by
  rw [h]

/-- **T7 (txid injective in concatenated leaves).** Under the abstract
injective-hash assumption, if two `Sections` tuples produce the same
concatenated payload `header ++ transparent ++ sapling ++ orchard`, they
yield the same txid; and conversely, equal txids force the concatenated
payloads to be equal. -/
theorem txid_inj_concat (H : AbstractHash) (t : Tags) (s₁ s₂ : Sections)
    (h : txidRoot H t s₁ = txidRoot H t s₂) :
    s₁.header ++ s₁.transparent ++ s₁.sapling ++ s₁.orchard =
      s₂.header ++ s₂.transparent ++ s₂.sapling ++ s₂.orchard := by
  unfold txidRoot at h
  exact personalisedHash_inj_payload H t.root _ _ h

/-- **T8 (txid injective in sections, fixed-length leaves).** If the
sections agree on each leaf length (which BLAKE2b-256 guarantees: every
leaf is exactly 32 bytes), then equal txids force equal sections.

This is the load-bearing "injectivity in the section inputs" claim of
ZIP-244 — the V5 txid identifies the section-leaf tuple uniquely. -/
theorem txid_inj_sections (H : AbstractHash) (t : Tags) (s₁ s₂ : Sections)
    (hH : s₁.header.length = s₂.header.length)
    (hT : s₁.transparent.length = s₂.transparent.length)
    (hS : s₁.sapling.length = s₂.sapling.length)
    (h : txidRoot H t s₁ = txidRoot H t s₂) :
    s₁ = s₂ := by
  have hcat := txid_inj_concat H t s₁ s₂ h
  -- Strip orchard: `(a ++ b) = (c ++ d)` with `length a = length c` ⇒ `a = c ∧ b = d`.
  have hOrcLen : (s₁.header ++ s₁.transparent ++ s₁.sapling).length =
                 (s₂.header ++ s₂.transparent ++ s₂.sapling).length := by
    simp [List.length_append, hH, hT, hS]
  have hOrc := List.append_inj hcat hOrcLen
  -- Strip sapling:
  have hSapLen : (s₁.header ++ s₁.transparent).length =
                 (s₂.header ++ s₂.transparent).length := by
    simp [List.length_append, hH, hT]
  have hSap := List.append_inj hOrc.1 hSapLen
  -- Strip transparent:
  have hHdr := List.append_inj hSap.1 hH
  -- Reassemble the four equalities into a Sections equality.
  cases s₁ with
  | mk h₁ t₁ sa₁ o₁ =>
    cases s₂ with
    | mk h₂ t₂ sa₂ o₂ =>
      simp_all

/-- **T9 (the abstract hash never collides on different inputs).** Direct
consequence of `H.inj`; restated so callers needn't reach into the
structure for the cryptographic content. -/
theorem abstract_hash_no_collision (H : AbstractHash) (x y : List Nat)
    (hne : x ≠ y) : H.hash x ≠ H.hash y := by
  intro h
  exact hne (H.inj h)

/-- **T10 (distinct sections ⇒ distinct txids, given matching lengths).**
The contrapositive form of T8: two non-equal section tuples with leaves
of matching widths produce different V5 txids. This is the collision-
resistance of the ZIP-244 txid at the structural level. -/
theorem distinct_sections_distinct_txid (H : AbstractHash) (t : Tags)
    (s₁ s₂ : Sections)
    (hH : s₁.header.length = s₂.header.length)
    (hT : s₁.transparent.length = s₂.transparent.length)
    (hS : s₁.sapling.length = s₂.sapling.length)
    (hne : s₁ ≠ s₂) :
    txidRoot H t s₁ ≠ txidRoot H t s₂ := by
  intro h
  exact hne (txid_inj_sections H t s₁ s₂ hH hT hS h)

/-- **T11 (changing only the orchard leaf changes the txid).** If two
section tuples agree on the first three leaves but differ on orchard, the
txids differ. A focused consequence of T10 for orchard updates. -/
theorem orchard_change_changes_txid (H : AbstractHash) (t : Tags)
    (s : Sections) (newOrchard : List Nat)
    (hne : s.orchard ≠ newOrchard) :
    txidRoot H t s ≠
      txidRoot H t { s with orchard := newOrchard } := by
  intro heq
  have hcat := txid_inj_concat H t _ _ heq
  -- `hcat : s.header ++ s.transparent ++ s.sapling ++ s.orchard
  --        = s.header ++ s.transparent ++ s.sapling ++ newOrchard`
  -- The left side is the same prefix on both sides; apply `append_cancel_left`.
  exact hne (List.append_cancel_left hcat)

/-- **T12 (no leaf can mimic a different leaf within the same section).**
For any section's intermediate digest, distinct payloads give distinct
digests (T1 specialised to each section tag). Together with T5 this gives
the full domain-separation picture: distinct payloads within a section
*and* distinct sections both produce distinct digests. -/
theorem section_payload_injective (H : AbstractHash) (t : Tags)
    (p₁ p₂ : List Nat) (hne : p₁ ≠ p₂) :
    headerDigest H t p₁ ≠ headerDigest H t p₂ ∧
    transparentDigest H t p₁ ≠ transparentDigest H t p₂ ∧
    saplingDigest H t p₁ ≠ saplingDigest H t p₂ ∧
    orchardDigest H t p₁ ≠ orchardDigest H t p₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · intro h
      apply hne
      exact personalisedHash_inj_payload H _ _ _ h

/-- **T13 (txid uniquely determined by tags and sections).** Combined
"functional + injective" statement: two txid computations agree iff the
section tuples are equal (under matching leaf widths). -/
theorem txid_iff_sections (H : AbstractHash) (t : Tags) (s₁ s₂ : Sections)
    (hH : s₁.header.length = s₂.header.length)
    (hT : s₁.transparent.length = s₂.transparent.length)
    (hS : s₁.sapling.length = s₂.sapling.length) :
    txidRoot H t s₁ = txidRoot H t s₂ ↔ s₁ = s₂ := by
  refine ⟨?_, ?_⟩
  · exact txid_inj_sections H t s₁ s₂ hH hT hS
  · intro h; rw [h]

/-- **T14 (changing root tag changes the txid on the same leaves).** If
two `Tags` structures differ in their root tag, applying them to the same
section tuple yields distinct txids. This is "the root domain-separation
tag matters" — choosing a different consensus-branch-id (which is baked
into `ZcashTxHash_<branchId>`) yields a different txid even when the
underlying transaction bytes are byte-for-byte identical. -/
theorem distinct_root_tags_distinct_txid (H : AbstractHash) (t₁ t₂ : Tags)
    (s : Sections) (hne : t₁.root ≠ t₂.root) :
    txidRoot H t₁ s ≠ txidRoot H t₂ s := by
  unfold txidRoot
  exact domain_separation_eq_payload H _ _ _ hne

/-- **T15 (txid is a deterministic function of `(H, t, s)`).** Restated
explicitly: the txid is fully determined by the abstract hash, the tag
structure, and the section tuple. There's no hidden state. (This is
trivially `rfl`-true by construction; we record it for completeness.) -/
theorem txid_deterministic (H : AbstractHash) (t : Tags) (s : Sections) :
    txidRoot H t s =
      H.hash (t.root ++ (s.header ++ s.transparent ++ s.sapling ++ s.orchard)) :=
  rfl

end Zebra.Zip244TxIdDigest
