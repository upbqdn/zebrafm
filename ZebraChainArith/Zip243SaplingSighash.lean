import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# ZIP-243 Sapling sighash composition

ZIP-243 (<https://zips.z.cash/zip-0243>) defines the Sapling-era transaction
signature hash for `nVersion >= 4` (V4) transactions. The preimage is a
fixed ordered concatenation of 12 per-section byte strings:

```text
sighash_preimage =
    header           ‖  -- 4 bytes (nVersionGroupId-style header tag)
    hashPrevouts     ‖  -- 32-byte BLAKE2b digest of transparent prevouts
    hashSequence     ‖  -- 32-byte BLAKE2b digest of input sequence numbers
    hashOutputs      ‖  -- 32-byte BLAKE2b digest of transparent outputs
    hashJoinSplits   ‖  -- 32-byte BLAKE2b digest of Sprout JoinSplits
    hashShieldedSpends   ‖  -- 32-byte BLAKE2b digest of Sapling Spend descs
    hashShieldedOutputs  ‖  -- 32-byte BLAKE2b digest of Sapling Output descs
    lock_time        ‖  -- 4-byte LE u32
    expiry_height    ‖  -- 4-byte LE u32
    valueBalanceSapling  ‖  -- 8-byte LE i64
    hash_type        ‖  -- 4-byte LE u32
    input               -- transparent input being signed (or `[]` for shielded)
```

The final sighash is `BLAKE2b-256` of this preimage with a personalisation
constructed from the consensus branch id.

This module models the *composition step only*: given the 12 per-section
byte strings, the preimage is their `List.append` in the prescribed order
and the sighash is an abstract injective hash of that preimage. We do not
model BLAKE2b — only that the abstract hash is injective on inputs, which
is the cryptographic assumption the consensus rules rely on.

We prove:

  * **Sensitivity**: changing *any single section* changes the preimage,
    and therefore (by injectivity of the hash) changes the digest.
  * **Domain separation by hash_type**: distinct `hash_type` values give
    distinct preimages and digests, so the SIGHASH flag space is encoded
    faithfully.
  * **Determinism**: the digest is a function of the 12 sections — the same
    inputs always give the same digest, no hidden state.
  * **Length & structural laws**: well-formed preimages have the canonical
    `4 + 32*6 + 4 + 4 + 8 + 4 + |input| = 216 + |input|` bytes; section
    order is load-bearing (commutativity fails).

Each section is modelled as `List Nat`; composition is `List.append`; the
abstract hash is parameterised as an arbitrary `List Nat → List Nat`
together with an `Injective` hypothesis when needed.

Source: <https://zips.z.cash/zip-0243#notation> and
`zebra-chain/src/transaction/sighash.rs:53` (Zebra's `SigHash` type wraps
the 32-byte BLAKE2b digest); the actual preimage construction lives in
`librustzcash` (delegated to via `crate::primitives::zcash_primitives::sighash`).
-/

namespace Zebra.Zip243SaplingSighash

/-! ## Constants and section types -/

/-- BLAKE2b-256 output and per-section digest length in bytes.
ZIP-243 fixes each per-section digest at 32 bytes. -/
def DIGEST_BYTES : Nat := 32

/-- The 4-byte header tag length (`nVersionGroupId` byte-level encoding).
Source: ZIP-243 §"Notation". -/
def HEADER_BYTES : Nat := 4

/-- The 4-byte `lock_time` field length. -/
def LOCK_TIME_BYTES : Nat := 4

/-- The 4-byte `expiry_height` field length. -/
def EXPIRY_HEIGHT_BYTES : Nat := 4

/-- The 8-byte `valueBalanceSapling` field length (LE i64). -/
def VALUE_BALANCE_BYTES : Nat := 8

/-- The 4-byte serialised `hash_type` field length (LE u32).
Source: see `SighashTypes.encodeU32LE`. -/
def HASH_TYPE_BYTES : Nat := 4

/-- The 12 per-section byte strings that ZIP-243 composes into the Sapling
sighash preimage. Field order matches the spec exactly.
Source: ZIP-243 §"Notation" / "Specification". -/
structure SighashSections where
  header : List Nat
  hashPrevouts : List Nat
  hashSequence : List Nat
  hashOutputs : List Nat
  hashJoinSplits : List Nat
  hashShieldedSpends : List Nat
  hashShieldedOutputs : List Nat
  lockTime : List Nat
  expiryHeight : List Nat
  valueBalanceSapling : List Nat
  hashType : List Nat
  input : List Nat
  deriving Repr

/-- The ZIP-243 sighash preimage: byte concatenation of the 12 sections in
spec order. -/
def preimage (s : SighashSections) : List Nat :=
  s.header
    ++ s.hashPrevouts
    ++ s.hashSequence
    ++ s.hashOutputs
    ++ s.hashJoinSplits
    ++ s.hashShieldedSpends
    ++ s.hashShieldedOutputs
    ++ s.lockTime
    ++ s.expiryHeight
    ++ s.valueBalanceSapling
    ++ s.hashType
    ++ s.input

/-- Well-formedness: every section has its canonical ZIP-243 byte length.
The transparent `input` slot is bounded only by the transaction-level
limits — its length is whatever the script code produces — so we leave it
unconstrained here. -/
structure WellFormed (s : SighashSections) : Prop where
  headerLen : s.header.length = HEADER_BYTES
  prevoutsLen : s.hashPrevouts.length = DIGEST_BYTES
  sequenceLen : s.hashSequence.length = DIGEST_BYTES
  outputsLen : s.hashOutputs.length = DIGEST_BYTES
  joinSplitsLen : s.hashJoinSplits.length = DIGEST_BYTES
  shieldedSpendsLen : s.hashShieldedSpends.length = DIGEST_BYTES
  shieldedOutputsLen : s.hashShieldedOutputs.length = DIGEST_BYTES
  lockTimeLen : s.lockTime.length = LOCK_TIME_BYTES
  expiryHeightLen : s.expiryHeight.length = EXPIRY_HEIGHT_BYTES
  valueBalanceLen : s.valueBalanceSapling.length = VALUE_BALANCE_BYTES
  hashTypeLen : s.hashType.length = HASH_TYPE_BYTES

/-! ## Abstract hash interface

We parameterise over an abstract hash function `H : List Nat → List Nat`.
For the cryptographically-meaningful claims (sensitivity, hash_type
domain separation) we additionally assume `H` is injective. This mirrors
the consensus assumption on BLAKE2b-256: distinct preimages give distinct
digests with overwhelming probability, which the protocol-level
arguments treat as an absolute. -/

/-- The ZIP-243 Sapling sighash: an abstract hash of the spec-ordered
preimage. The actual Rust implementation calls
`zp_tx::sighash::signature_hash` which evaluates BLAKE2b-256 with the
consensus-branch-id personalisation. -/
def sighash (H : List Nat → List Nat) (s : SighashSections) : List Nat :=
  H (preimage s)

/-! ## Theorems

We prove twelve substantive theorems on this composition.
-/

/-- **T1 (preimage length, canonical input-less form).** For a well-formed
section bundle with an empty transparent-input slot (the "shielded input"
case in `SigHasher::sighash`), the preimage has the spec-prescribed
`4 + 6·32 + 4 + 4 + 8 + 4 = 216` bytes. -/
theorem preimage_length_no_input (s : SighashSections) (hw : WellFormed s)
    (hInput : s.input = []) :
    (preimage s).length =
      HEADER_BYTES + 6 * DIGEST_BYTES + LOCK_TIME_BYTES + EXPIRY_HEIGHT_BYTES
        + VALUE_BALANCE_BYTES + HASH_TYPE_BYTES := by
  unfold preimage
  simp [List.length_append, hw.headerLen, hw.prevoutsLen, hw.sequenceLen,
        hw.outputsLen, hw.joinSplitsLen, hw.shieldedSpendsLen,
        hw.shieldedOutputsLen, hw.lockTimeLen, hw.expiryHeightLen,
        hw.valueBalanceLen, hw.hashTypeLen, hInput]
  rfl

/-- **T2 (preimage length, general form).** With an arbitrary transparent
input slot, the well-formed preimage length is the constant-section sum
plus `s.input.length`. -/
theorem preimage_length (s : SighashSections) (hw : WellFormed s) :
    (preimage s).length =
      HEADER_BYTES + 6 * DIGEST_BYTES + LOCK_TIME_BYTES + EXPIRY_HEIGHT_BYTES
        + VALUE_BALANCE_BYTES + HASH_TYPE_BYTES + s.input.length := by
  unfold preimage
  simp [List.length_append, hw.headerLen, hw.prevoutsLen, hw.sequenceLen,
        hw.outputsLen, hw.joinSplitsLen, hw.shieldedSpendsLen,
        hw.shieldedOutputsLen, hw.lockTimeLen, hw.expiryHeightLen,
        hw.valueBalanceLen, hw.hashTypeLen]
  ring

/-- **T3 (full injectivity of preimage).** When both bundles are well-formed
(so every fixed-width section has the canonical length), identical
preimages imply componentwise equality on the 12 sections. The proof
peels off each section from the left using `List.append_inj`. -/
theorem preimage_injective (s₁ s₂ : SighashSections)
    (hw₁ : WellFormed s₁) (hw₂ : WellFormed s₂)
    (heq : preimage s₁ = preimage s₂) :
    s₁.header = s₂.header ∧
    s₁.hashPrevouts = s₂.hashPrevouts ∧
    s₁.hashSequence = s₂.hashSequence ∧
    s₁.hashOutputs = s₂.hashOutputs ∧
    s₁.hashJoinSplits = s₂.hashJoinSplits ∧
    s₁.hashShieldedSpends = s₂.hashShieldedSpends ∧
    s₁.hashShieldedOutputs = s₂.hashShieldedOutputs ∧
    s₁.lockTime = s₂.lockTime ∧
    s₁.expiryHeight = s₂.expiryHeight ∧
    s₁.valueBalanceSapling = s₂.valueBalanceSapling ∧
    s₁.hashType = s₂.hashType ∧
    s₁.input = s₂.input := by
  -- Reassociate to right-associated form so peeling from the left works.
  unfold preimage at heq
  have hreassoc : ∀ (a b c d e f g h i j k l : List Nat),
      a ++ b ++ c ++ d ++ e ++ f ++ g ++ h ++ i ++ j ++ k ++ l =
        a ++ (b ++ (c ++ (d ++ (e ++ (f ++ (g ++ (h ++ (i ++ (j ++ (k ++ l))))))))))
    := by
    intros; simp [List.append_assoc]
  rw [hreassoc, hreassoc] at heq
  -- Peel header.
  have hlenH : s₁.header.length = s₂.header.length := by
    rw [hw₁.headerLen, hw₂.headerLen]
  obtain ⟨hH, heq⟩ := List.append_inj heq hlenH
  -- Peel prevouts.
  have hlenP : s₁.hashPrevouts.length = s₂.hashPrevouts.length := by
    rw [hw₁.prevoutsLen, hw₂.prevoutsLen]
  obtain ⟨hP, heq⟩ := List.append_inj heq hlenP
  -- Peel sequence.
  have hlenSeq : s₁.hashSequence.length = s₂.hashSequence.length := by
    rw [hw₁.sequenceLen, hw₂.sequenceLen]
  obtain ⟨hSeq, heq⟩ := List.append_inj heq hlenSeq
  -- Peel outputs.
  have hlenO : s₁.hashOutputs.length = s₂.hashOutputs.length := by
    rw [hw₁.outputsLen, hw₂.outputsLen]
  obtain ⟨hO, heq⟩ := List.append_inj heq hlenO
  -- Peel joinSplits.
  have hlenJ : s₁.hashJoinSplits.length = s₂.hashJoinSplits.length := by
    rw [hw₁.joinSplitsLen, hw₂.joinSplitsLen]
  obtain ⟨hJ, heq⟩ := List.append_inj heq hlenJ
  -- Peel shieldedSpends.
  have hlenSS : s₁.hashShieldedSpends.length = s₂.hashShieldedSpends.length := by
    rw [hw₁.shieldedSpendsLen, hw₂.shieldedSpendsLen]
  obtain ⟨hSS, heq⟩ := List.append_inj heq hlenSS
  -- Peel shieldedOutputs.
  have hlenSO : s₁.hashShieldedOutputs.length = s₂.hashShieldedOutputs.length := by
    rw [hw₁.shieldedOutputsLen, hw₂.shieldedOutputsLen]
  obtain ⟨hSO, heq⟩ := List.append_inj heq hlenSO
  -- Peel lockTime.
  have hlenL : s₁.lockTime.length = s₂.lockTime.length := by
    rw [hw₁.lockTimeLen, hw₂.lockTimeLen]
  obtain ⟨hL, heq⟩ := List.append_inj heq hlenL
  -- Peel expiryHeight.
  have hlenE : s₁.expiryHeight.length = s₂.expiryHeight.length := by
    rw [hw₁.expiryHeightLen, hw₂.expiryHeightLen]
  obtain ⟨hE, heq⟩ := List.append_inj heq hlenE
  -- Peel valueBalance.
  have hlenV : s₁.valueBalanceSapling.length = s₂.valueBalanceSapling.length := by
    rw [hw₁.valueBalanceLen, hw₂.valueBalanceLen]
  obtain ⟨hV, heq⟩ := List.append_inj heq hlenV
  -- Peel hashType. The remaining suffix is `s.hashType ++ s.input`.
  have hlenHT : s₁.hashType.length = s₂.hashType.length := by
    rw [hw₁.hashTypeLen, hw₂.hashTypeLen]
  obtain ⟨hHT, hIn⟩ := List.append_inj heq hlenHT
  exact ⟨hH, hP, hSeq, hO, hJ, hSS, hSO, hL, hE, hV, hHT, hIn⟩

/-- **T4 (determinism).** The sighash is a pure function of the section
bundle: identical bundles always give identical digests, regardless of the
abstract hash function `H`. This is what lets consensus nodes recompute
the digest reproducibly. -/
theorem sighash_deterministic (H : List Nat → List Nat) (s₁ s₂ : SighashSections)
    (heq : s₁ = s₂) :
    sighash H s₁ = sighash H s₂ := by
  rw [heq]

/-- **T5 (header sensitivity).** Changing the `header` section while
keeping the other 11 fixed changes the preimage; combined with `H`
injectivity, this changes the digest. -/
theorem sighash_sensitive_header (H : List Nat → List Nat)
    (hInj : Function.Injective H)
    (s₁ s₂ : SighashSections)
    (hw₁ : WellFormed s₁) (hw₂ : WellFormed s₂)
    (_hRest : s₁.hashPrevouts = s₂.hashPrevouts ∧
              s₁.hashSequence = s₂.hashSequence ∧
              s₁.hashOutputs = s₂.hashOutputs ∧
              s₁.hashJoinSplits = s₂.hashJoinSplits ∧
              s₁.hashShieldedSpends = s₂.hashShieldedSpends ∧
              s₁.hashShieldedOutputs = s₂.hashShieldedOutputs ∧
              s₁.lockTime = s₂.lockTime ∧
              s₁.expiryHeight = s₂.expiryHeight ∧
              s₁.valueBalanceSapling = s₂.valueBalanceSapling ∧
              s₁.hashType = s₂.hashType ∧
              s₁.input = s₂.input)
    (hDiff : s₁.header ≠ s₂.header) :
    sighash H s₁ ≠ sighash H s₂ := by
  intro habs
  have hpre : preimage s₁ = preimage s₂ := hInj habs
  have hcomp := preimage_injective s₁ s₂ hw₁ hw₂ hpre
  exact hDiff hcomp.1

/-- **T6 (hash_type domain separation).** Two bundles that agree on every
section except `hashType` produce different digests. This is the property
that makes the six valid SIGHASH bytes (`ALL`, `NONE`, `SINGLE`, and their
`ANYONECANPAY` combinations) yield six distinct sighashes per transaction,
which is the foundational ZIP-243 / ZIP-143 domain-separation claim. -/
theorem sighash_sensitive_hash_type (H : List Nat → List Nat)
    (hInj : Function.Injective H)
    (s₁ s₂ : SighashSections)
    (hw₁ : WellFormed s₁) (hw₂ : WellFormed s₂)
    (_hRest : s₁.header = s₂.header ∧
              s₁.hashPrevouts = s₂.hashPrevouts ∧
              s₁.hashSequence = s₂.hashSequence ∧
              s₁.hashOutputs = s₂.hashOutputs ∧
              s₁.hashJoinSplits = s₂.hashJoinSplits ∧
              s₁.hashShieldedSpends = s₂.hashShieldedSpends ∧
              s₁.hashShieldedOutputs = s₂.hashShieldedOutputs ∧
              s₁.lockTime = s₂.lockTime ∧
              s₁.expiryHeight = s₂.expiryHeight ∧
              s₁.valueBalanceSapling = s₂.valueBalanceSapling ∧
              s₁.input = s₂.input)
    (hDiff : s₁.hashType ≠ s₂.hashType) :
    sighash H s₁ ≠ sighash H s₂ := by
  intro habs
  have hpre : preimage s₁ = preimage s₂ := hInj habs
  have hcomp := preimage_injective s₁ s₂ hw₁ hw₂ hpre
  exact hDiff hcomp.2.2.2.2.2.2.2.2.2.2.1

/-- **T7 (shielded-spends sensitivity).** Changing the
`hashShieldedSpends` digest while keeping the rest fixed changes the
sighash. This is the property that makes any modification of the Sapling
spend bundle detectable in the sighash, preventing malleation of the
signed transaction's shielded inputs. -/
theorem sighash_sensitive_shielded_spends (H : List Nat → List Nat)
    (hInj : Function.Injective H)
    (s₁ s₂ : SighashSections)
    (hw₁ : WellFormed s₁) (hw₂ : WellFormed s₂)
    (_hRest : s₁.header = s₂.header ∧
              s₁.hashPrevouts = s₂.hashPrevouts ∧
              s₁.hashSequence = s₂.hashSequence ∧
              s₁.hashOutputs = s₂.hashOutputs ∧
              s₁.hashJoinSplits = s₂.hashJoinSplits ∧
              s₁.hashShieldedOutputs = s₂.hashShieldedOutputs ∧
              s₁.lockTime = s₂.lockTime ∧
              s₁.expiryHeight = s₂.expiryHeight ∧
              s₁.valueBalanceSapling = s₂.valueBalanceSapling ∧
              s₁.hashType = s₂.hashType ∧
              s₁.input = s₂.input)
    (hDiff : s₁.hashShieldedSpends ≠ s₂.hashShieldedSpends) :
    sighash H s₁ ≠ sighash H s₂ := by
  intro habs
  have hpre : preimage s₁ = preimage s₂ := hInj habs
  have hcomp := preimage_injective s₁ s₂ hw₁ hw₂ hpre
  exact hDiff hcomp.2.2.2.2.2.1

/-- **T8 (valueBalance sensitivity).** Changing the `valueBalanceSapling`
section changes the sighash. The Sapling net value flow is signed-into the
sighash, preventing modification of the `valueBalance` field on an
authorised transaction. -/
theorem sighash_sensitive_value_balance (H : List Nat → List Nat)
    (hInj : Function.Injective H)
    (s₁ s₂ : SighashSections)
    (hw₁ : WellFormed s₁) (hw₂ : WellFormed s₂)
    (_hRest : s₁.header = s₂.header ∧
              s₁.hashPrevouts = s₂.hashPrevouts ∧
              s₁.hashSequence = s₂.hashSequence ∧
              s₁.hashOutputs = s₂.hashOutputs ∧
              s₁.hashJoinSplits = s₂.hashJoinSplits ∧
              s₁.hashShieldedSpends = s₂.hashShieldedSpends ∧
              s₁.hashShieldedOutputs = s₂.hashShieldedOutputs ∧
              s₁.lockTime = s₂.lockTime ∧
              s₁.expiryHeight = s₂.expiryHeight ∧
              s₁.hashType = s₂.hashType ∧
              s₁.input = s₂.input)
    (hDiff : s₁.valueBalanceSapling ≠ s₂.valueBalanceSapling) :
    sighash H s₁ ≠ sighash H s₂ := by
  intro habs
  have hpre : preimage s₁ = preimage s₂ := hInj habs
  have hcomp := preimage_injective s₁ s₂ hw₁ hw₂ hpre
  exact hDiff hcomp.2.2.2.2.2.2.2.2.2.1

/-- **T9 (every section contributes — combined statement).** A
"sensitivity in all 12 slots" theorem: if any single section differs
between two well-formed bundles, the digests differ. This is the
componentwise sensitivity claim for the full preimage composition.

We state the contrapositive: equal sighashes (with `H` injective) force
all 12 sections to match. -/
theorem sighash_collision_implies_all_sections_equal (H : List Nat → List Nat)
    (hInj : Function.Injective H)
    (s₁ s₂ : SighashSections)
    (hw₁ : WellFormed s₁) (hw₂ : WellFormed s₂)
    (heq : sighash H s₁ = sighash H s₂) :
    s₁.header = s₂.header ∧
    s₁.hashPrevouts = s₂.hashPrevouts ∧
    s₁.hashSequence = s₂.hashSequence ∧
    s₁.hashOutputs = s₂.hashOutputs ∧
    s₁.hashJoinSplits = s₂.hashJoinSplits ∧
    s₁.hashShieldedSpends = s₂.hashShieldedSpends ∧
    s₁.hashShieldedOutputs = s₂.hashShieldedOutputs ∧
    s₁.lockTime = s₂.lockTime ∧
    s₁.expiryHeight = s₂.expiryHeight ∧
    s₁.valueBalanceSapling = s₂.valueBalanceSapling ∧
    s₁.hashType = s₂.hashType ∧
    s₁.input = s₂.input := by
  have hpre : preimage s₁ = preimage s₂ := hInj heq
  exact preimage_injective s₁ s₂ hw₁ hw₂ hpre

/-- **T10 (commutativity fails — section order is load-bearing).** Swapping
the `hashPrevouts` and `hashOutputs` sections produces a different
preimage. Combined with `H` injectivity, this gives a different sighash.
This is the formal sense in which ZIP-243's field order is part of the
specification — `prevouts` and `outputs` are not interchangeable. -/
theorem preimage_order_matters :
    ∃ (s₁ s₂ : SighashSections),
      WellFormed s₁ ∧ WellFormed s₂ ∧
      preimage s₁ ≠ preimage s₂ ∧
      -- Same multi-set of digests, swapped slot assignment.
      s₁.hashPrevouts = s₂.hashOutputs ∧
      s₁.hashOutputs = s₂.hashPrevouts := by
  let z : List Nat := List.replicate DIGEST_BYTES 0
  let o : List Nat := List.replicate DIGEST_BYTES 1
  let h : List Nat := List.replicate HEADER_BYTES 0
  let lt : List Nat := List.replicate LOCK_TIME_BYTES 0
  let eh : List Nat := List.replicate EXPIRY_HEIGHT_BYTES 0
  let vb : List Nat := List.replicate VALUE_BALANCE_BYTES 0
  let ht : List Nat := List.replicate HASH_TYPE_BYTES 0
  have hzlen : z.length = DIGEST_BYTES := List.length_replicate
  have holen : o.length = DIGEST_BYTES := List.length_replicate
  have hhlen : h.length = HEADER_BYTES := List.length_replicate
  have hltlen : lt.length = LOCK_TIME_BYTES := List.length_replicate
  have hehlen : eh.length = EXPIRY_HEIGHT_BYTES := List.length_replicate
  have hvblen : vb.length = VALUE_BALANCE_BYTES := List.length_replicate
  have hhtlen : ht.length = HASH_TYPE_BYTES := List.length_replicate
  refine ⟨
    { header := h, hashPrevouts := o, hashSequence := z, hashOutputs := z,
      hashJoinSplits := z, hashShieldedSpends := z, hashShieldedOutputs := z,
      lockTime := lt, expiryHeight := eh, valueBalanceSapling := vb,
      hashType := ht, input := [] },
    { header := h, hashPrevouts := z, hashSequence := z, hashOutputs := o,
      hashJoinSplits := z, hashShieldedSpends := z, hashShieldedOutputs := z,
      lockTime := lt, expiryHeight := eh, valueBalanceSapling := vb,
      hashType := ht, input := [] },
    ⟨hhlen, holen, hzlen, hzlen, hzlen, hzlen, hzlen,
     hltlen, hehlen, hvblen, hhtlen⟩,
    ⟨hhlen, hzlen, hzlen, holen, hzlen, hzlen, hzlen,
     hltlen, hehlen, hvblen, hhtlen⟩,
    ?_, rfl, rfl⟩
  -- If the preimages were equal, full injectivity would force the prevouts
  -- digests to match — but bundle 1 has prevouts = o, bundle 2 has prevouts
  -- = z, and o ≠ z (they differ at index 0).
  intro habs
  have hcomp := preimage_injective
    { header := h, hashPrevouts := o, hashSequence := z, hashOutputs := z,
      hashJoinSplits := z, hashShieldedSpends := z, hashShieldedOutputs := z,
      lockTime := lt, expiryHeight := eh, valueBalanceSapling := vb,
      hashType := ht, input := [] }
    { header := h, hashPrevouts := z, hashSequence := z, hashOutputs := o,
      hashJoinSplits := z, hashShieldedSpends := z, hashShieldedOutputs := z,
      lockTime := lt, expiryHeight := eh, valueBalanceSapling := vb,
      hashType := ht, input := [] }
    ⟨hhlen, holen, hzlen, hzlen, hzlen, hzlen, hzlen,
     hltlen, hehlen, hvblen, hhtlen⟩
    ⟨hhlen, hzlen, hzlen, holen, hzlen, hzlen, hzlen,
     hltlen, hehlen, hvblen, hhtlen⟩
    habs
  have ho_eq_z : o = z := hcomp.2.1
  have ho0 : o[0]? = some 1 := by
    change (List.replicate DIGEST_BYTES 1)[0]? = some 1
    rw [List.getElem?_replicate]; decide
  have hz0 : z[0]? = some 0 := by
    change (List.replicate DIGEST_BYTES 0)[0]? = some 0
    rw [List.getElem?_replicate]; decide
  rw [ho_eq_z] at ho0
  rw [hz0] at ho0
  exact absurd ho0 (by decide)

/-- **T11 (preimage length, abstract).** Without the well-formedness
hypothesis, the preimage length is the sum of the 12 section lengths.
This is the basic input shape for length-based ZIP-243 reasoning. -/
theorem preimage_length_eq_sum (s : SighashSections) :
    (preimage s).length =
      s.header.length + s.hashPrevouts.length + s.hashSequence.length
        + s.hashOutputs.length + s.hashJoinSplits.length
        + s.hashShieldedSpends.length + s.hashShieldedOutputs.length
        + s.lockTime.length + s.expiryHeight.length
        + s.valueBalanceSapling.length + s.hashType.length + s.input.length := by
  unfold preimage
  simp [List.length_append]
  ring

/-- **T12 (determinism via section equality).** Strengthening T4: if two
bundles agree on every section, their sighashes agree, regardless of the
abstract hash function. The proof is by `rfl` once we observe that
componentwise equality forces structural equality. -/
theorem sighash_componentwise_det (H : List Nat → List Nat)
    (s₁ s₂ : SighashSections)
    (h1 : s₁.header = s₂.header)
    (h2 : s₁.hashPrevouts = s₂.hashPrevouts)
    (h3 : s₁.hashSequence = s₂.hashSequence)
    (h4 : s₁.hashOutputs = s₂.hashOutputs)
    (h5 : s₁.hashJoinSplits = s₂.hashJoinSplits)
    (h6 : s₁.hashShieldedSpends = s₂.hashShieldedSpends)
    (h7 : s₁.hashShieldedOutputs = s₂.hashShieldedOutputs)
    (h8 : s₁.lockTime = s₂.lockTime)
    (h9 : s₁.expiryHeight = s₂.expiryHeight)
    (h10 : s₁.valueBalanceSapling = s₂.valueBalanceSapling)
    (h11 : s₁.hashType = s₂.hashType)
    (h12 : s₁.input = s₂.input) :
    sighash H s₁ = sighash H s₂ := by
  unfold sighash preimage
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

/-- **T13 (six SIGHASH bytes give six distinct digests).** A concrete
application of T6: when the 11 non-`hashType` sections are fixed and
`hashType` ranges over six distinct values, the sighash takes six
distinct values. This is the formal statement of ZIP-243 SIGHASH domain
separation. -/
theorem six_hash_types_six_sighashes (H : List Nat → List Nat)
    (hInj : Function.Injective H)
    (template : SighashSections) (hw : WellFormed template)
    (ht₁ ht₂ : List Nat)
    (hLen₁ : ht₁.length = HASH_TYPE_BYTES)
    (hLen₂ : ht₂.length = HASH_TYPE_BYTES)
    (hDiff : ht₁ ≠ ht₂) :
    sighash H { template with hashType := ht₁ } ≠
      sighash H { template with hashType := ht₂ } := by
  apply sighash_sensitive_hash_type H hInj
    { template with hashType := ht₁ }
    { template with hashType := ht₂ }
    { hw with hashTypeLen := hLen₁ }
    { hw with hashTypeLen := hLen₂ }
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact hDiff

/-- **T14 (uniform digest preimage).** When every digest section is the
same byte string `d` (and the fixed-width fields are zero), the preimage
is `header ‖ d⁶ ‖ lt ‖ eh ‖ vb ‖ ht ‖ input`. A degenerate but
useful sanity check on the composition. -/
theorem preimage_uniform_digests
    (header lt eh vb ht input d : List Nat) :
    preimage
      { header := header, hashPrevouts := d, hashSequence := d, hashOutputs := d,
        hashJoinSplits := d, hashShieldedSpends := d, hashShieldedOutputs := d,
        lockTime := lt, expiryHeight := eh, valueBalanceSapling := vb,
        hashType := ht, input := input } =
      header ++ d ++ d ++ d ++ d ++ d ++ d ++ lt ++ eh ++ vb ++ ht ++ input := by
  rfl

end Zebra.Zip243SaplingSighash
