import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# ZIP-243 Sapling sighash composition

ZIP-243 (<https://zips.z.cash/zip-0243>) defines the Sapling-era transaction
signature hash for `nVersion >= 4` (V4) transactions. The preimage is a
fixed ordered concatenation of 12 fixed sections plus an optional
transparent-input section (13 sections total in the spec):

```text
sighash_preimage =
    header                 ‖  -- 4 bytes  (transaction header LE u32)
    nVersionGroupId        ‖  -- 4 bytes  (LE u32, distinct from header)
    hashPrevouts           ‖  -- 32-byte BLAKE2b digest (or zeros if masked)
    hashSequence           ‖  -- 32-byte BLAKE2b digest (or zeros if masked)
    hashOutputs            ‖  -- 32-byte BLAKE2b digest (or zeros if masked)
    hashJoinSplits         ‖  -- 32-byte BLAKE2b digest of Sprout JoinSplits
    hashShieldedSpends     ‖  -- 32-byte BLAKE2b digest (only if Sapling)
    hashShieldedOutputs    ‖  -- 32-byte BLAKE2b digest (only if Sapling)
    lock_time              ‖  -- 4-byte LE u32
    expiry_height          ‖  -- 4-byte LE u32
    valueBalanceSapling    ‖  -- 8-byte LE i64 (only if Sapling)
    hash_type              ‖  -- 4-byte LE u32
    input                     -- transparent input being signed (or `[]` for shielded)
```

The final sighash is `BLAKE2b-256` of this preimage with a personalisation
constructed from the consensus branch id.

This module models the *composition step only*: given the per-section byte
strings, the preimage is their `List.append` in the prescribed order and
the sighash is an abstract injective hash of that preimage. We do not
model BLAKE2b — only that the abstract hash is injective on inputs, which
is the cryptographic assumption the consensus rules rely on.

We model three semantically distinct shapes corresponding to the Rust
`v4_signature_hash` implementation (librustzcash
`zcash_primitives/src/transaction/sighash_v4.rs`):

  * **Sapling V4 (`preimage`)** — the full 12 fixed sections + input,
    matching `tx.version.has_sapling() == true` with no hash-type masking
    applied (the `SIGHASH_ALL` case);
  * **Pre-Sapling V3 (`preimageV3`)** — omits `hashShieldedSpends`,
    `hashShieldedOutputs`, and the 8-byte `valueBalanceSapling` (8 + 32 +
    32 = 72 fewer bytes), matching `!tx.version.has_sapling()`;
  * **Hash-type masked (`preimageMasked`)** — applies the
    `update_hash!`-style replacement that zeroes specific 32-byte sections
    based on the SIGHASH flag bits (`ANYONECANPAY` zeros `prevouts` and
    `sequence`; `SINGLE`/`NONE` additionally zero `sequence` and reshape
    `outputs`). The masked variant still produces a fixed-width preimage
    (the gated 32-byte slots are replaced with `[0; 32]`, not omitted),
    matching the `update_hash!` macro on lines 26-34 of `sighash_v4.rs`.

We prove:

  * **Sensitivity**: changing *any single section* changes the preimage,
    and therefore (by injectivity of the hash) changes the digest.
  * **Domain separation by hash_type**: distinct `hash_type` values give
    distinct preimages and digests, so the SIGHASH flag space is encoded
    faithfully.
  * **Determinism**: the digest is a function of the section bundle — the
    same inputs always give the same digest, no hidden state.
  * **Length & structural laws**: well-formed Sapling V4 preimages have
    `4 + 4 + 32*6 + 4 + 4 + 8 + 4 + |input| = 220 + |input|` bytes;
    well-formed pre-Sapling V3 preimages have `220 - 72 + |input| = 148 +
    |input|` bytes; section order is load-bearing (commutativity fails).

Each section is modelled as `List Nat`; composition is `List.append`; the
abstract hash is parameterised as an arbitrary `List Nat → List Nat`
together with an `Injective` hypothesis when needed.

Source: <https://zips.z.cash/zip-0243#specification> (the spec lists 13
numbered sections — 12 fixed-width plus the optional transparent input
suffix), `zebra-chain/src/transaction/sighash.rs:53` (Zebra's `SigHash`
type wraps the 32-byte BLAKE2b digest), and librustzcash
`zcash_primitives/src/transaction/sighash_v4.rs:131-264` (the actual
`v4_signature_hash` implementation Zebra delegates to via
`crate::primitives::zcash_primitives::sighash`).
-/

namespace Zebra.Zip243SaplingSighash

/-! ## Constants and section types -/

/-- BLAKE2b-256 output and per-section digest length in bytes.
ZIP-243 fixes each per-section digest at 32 bytes. -/
def DIGEST_BYTES : Nat := 32

/-- The 4-byte `header` field length (LE encoding of `tx.version.header()`,
i.e. `fOverwintered | version`). Spec field #1.
Source: ZIP-243 §"Specification", librustzcash `sighash_v4.rs:149`. -/
def HEADER_BYTES : Nat := 4

/-- The 4-byte `nVersionGroupId` field length (LE u32). Spec field #2,
distinct from `header`. Source: ZIP-243 §"Specification" line 2,
librustzcash `sighash_v4.rs:150`. -/
def VERSION_GROUP_ID_BYTES : Nat := 4

/-- The 4-byte `lock_time` field length. Spec field #9. -/
def LOCK_TIME_BYTES : Nat := 4

/-- The 4-byte `expiry_height` field length. Spec field #10. -/
def EXPIRY_HEIGHT_BYTES : Nat := 4

/-- The 8-byte `valueBalanceSapling` field length (LE i64). Spec field
#11. Present only when `tx.version.has_sapling()`; pre-Sapling V3
transactions omit this slot entirely. Source: librustzcash
`sighash_v4.rs:227-229`. -/
def VALUE_BALANCE_BYTES : Nat := 8

/-- The 4-byte serialised `hash_type` field length (LE u32). Spec field
#12. The on-wire byte is a `u8` (see librustzcash
`zcash_transparent/src/sighash.rs:7-11`), but `sighash_v4.rs:230` widens
it to LE u32 before hashing. -/
def HASH_TYPE_BYTES : Nat := 4

/-! ### SIGHASH flag-byte constants

Mirroring `zcash_transparent/src/sighash.rs:7-11`. Used by
`hashTypeAnyonecanpay`, `hashTypeMaskMatches`, and `preimageMasked` to
decide which 32-byte sections get replaced by `[0; 32]`. -/

/-- `SIGHASH_ALL = 0x01`. Source: librustzcash
`zcash_transparent/src/sighash.rs:7`. -/
def SIGHASH_ALL : Nat := 0x01

/-- `SIGHASH_NONE = 0x02`. Source: librustzcash
`zcash_transparent/src/sighash.rs:8`. -/
def SIGHASH_NONE : Nat := 0x02

/-- `SIGHASH_SINGLE = 0x03`. Source: librustzcash
`zcash_transparent/src/sighash.rs:9`. -/
def SIGHASH_SINGLE : Nat := 0x03

/-- `SIGHASH_MASK = 0x1f`. Source: librustzcash
`zcash_transparent/src/sighash.rs:10`. -/
def SIGHASH_MASK : Nat := 0x1f

/-- `SIGHASH_ANYONECANPAY = 0x80`. Source: librustzcash
`zcash_transparent/src/sighash.rs:11`. -/
def SIGHASH_ANYONECANPAY : Nat := 0x80

/-- The 13 per-section byte strings that ZIP-243 composes into the
Sapling-V4 sighash preimage. Field order matches the spec exactly:
`header` and `nVersionGroupId` are two separate 4-byte LE u32 fields, not
one combined header tag (cf. ZIP-243 spec lines 1 and 2). Spec field #13
(the optional transparent-input slot) is held by `input`. -/
structure SighashSections where
  /-- Spec field #1: `header` LE u32 (4 bytes). -/
  header : List Nat
  /-- Spec field #2: `nVersionGroupId` LE u32 (4 bytes), distinct from
  `header`. -/
  versionGroupId : List Nat
  /-- Spec field #3: 32-byte BLAKE2b digest of transparent prevouts.
  Replaced with `[0; 32]` when `SIGHASH_ANYONECANPAY` is set
  (`sighash_v4.rs:151-159`). -/
  hashPrevouts : List Nat
  /-- Spec field #4: 32-byte BLAKE2b digest of input sequence numbers.
  Replaced with `[0; 32]` when `ANYONECANPAY`, `SINGLE`, or `NONE` is set
  (`sighash_v4.rs:160-170`). -/
  hashSequence : List Nat
  /-- Spec field #5: 32-byte BLAKE2b digest of transparent outputs.
  Reshaped per `SINGLE`/`NONE` flag (`sighash_v4.rs:172-192`). -/
  hashOutputs : List Nat
  /-- Spec field #6: 32-byte BLAKE2b digest of Sprout JoinSplits.
  Replaced with `[0; 32]` if there is no JoinSplit bundle
  (`sighash_v4.rs:194-207`). -/
  hashJoinSplits : List Nat
  /-- Spec field #7: 32-byte BLAKE2b digest of Sapling Spend descs.
  Sapling-only — omitted from the V3 shape. -/
  hashShieldedSpends : List Nat
  /-- Spec field #8: 32-byte BLAKE2b digest of Sapling Output descs.
  Sapling-only — omitted from the V3 shape. -/
  hashShieldedOutputs : List Nat
  /-- Spec field #9: `nLockTime` LE u32 (4 bytes). -/
  lockTime : List Nat
  /-- Spec field #10: `nExpiryHeight` LE u32 (4 bytes). -/
  expiryHeight : List Nat
  /-- Spec field #11: `valueBalanceSapling` LE i64 (8 bytes). Sapling-only
  — omitted from the V3 shape. -/
  valueBalanceSapling : List Nat
  /-- Spec field #12: `hash_type` widened to LE u32 (4 bytes). -/
  hashType : List Nat
  /-- Spec field #13: optional transparent-input slot; `[]` for shielded
  inputs. -/
  input : List Nat
  deriving Repr

/-- The ZIP-243 Sapling-V4 sighash preimage: byte concatenation of the 13
sections in spec order. This matches the `tx.version.has_sapling() ==
true` path of `v4_signature_hash` with `SIGHASH_ALL` (no masking). For
hash-type masking, see `preimageMasked`. For pre-Sapling V3, see
`preimageV3`. -/
def preimage (s : SighashSections) : List Nat :=
  s.header
    ++ s.versionGroupId
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

/-- Well-formedness for Sapling-V4: every fixed-width section has its
canonical ZIP-243 byte length. The transparent `input` slot is bounded
only by the transaction-level limits — its length is whatever the script
code produces — so we leave it unconstrained here. -/
structure WellFormed (s : SighashSections) : Prop where
  headerLen : s.header.length = HEADER_BYTES
  versionGroupIdLen : s.versionGroupId.length = VERSION_GROUP_ID_BYTES
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

/-! ### Pre-Sapling V3 preimage shape

For `!tx.version.has_sapling()` (i.e. V3 transactions on the Overwinter
branch), librustzcash `sighash_v4.rs` skips three sections:

  * `hashShieldedSpends` and `hashShieldedOutputs` are not appended (the
    `if tx.version.has_sapling()` block on lines 209-224 is not entered);
  * `valueBalanceSapling` is not appended (the `if tx.version.has_sapling()`
    guard on lines 227-229 is not entered).

The other 10 sections are unchanged. -/

/-- The pre-Sapling V3 preimage: the 10 sections that are present when
`tx.version.has_sapling() == false`. Compared with `preimage`, this omits
`hashShieldedSpends`, `hashShieldedOutputs`, and `valueBalanceSapling`.
Source: librustzcash `sighash_v4.rs:209-229`. -/
def preimageV3 (s : SighashSections) : List Nat :=
  s.header
    ++ s.versionGroupId
    ++ s.hashPrevouts
    ++ s.hashSequence
    ++ s.hashOutputs
    ++ s.hashJoinSplits
    ++ s.lockTime
    ++ s.expiryHeight
    ++ s.hashType
    ++ s.input

/-! ### Hash-type masking shape

`sighash_v4.rs` uses the `update_hash!` macro (lines 26-34) to conditionally
replace 32-byte digest slots with `[0; 32]`:

```rust
macro_rules! update_hash {
    ($h:expr, $cond:expr, $value:expr) => {
        if $cond { $h.update(&$value.as_ref()); }
        else      { $h.update(&[0; 32]); }
    };
}
```

The conditions (lines 151-192) are derived from `hash_type`:

  * `prevouts`  : zero out when `hash_type & ANYONECANPAY != 0`;
  * `sequence`  : zero out when `ANYONECANPAY` is set, or when
                  `hash_type & MASK ∈ {SINGLE, NONE}`;
  * `outputs`   : when `hash_type & MASK ∈ {SINGLE, NONE}`, the
                  `outputs_hash` is replaced (zero for `NONE`, or a
                  single-output hash for `SINGLE` indexed by the signed
                  input — modelled here as an opaque replacement).
-/

/-- `hash_type & SIGHASH_ANYONECANPAY != 0`. Mirrors the Rust check on
`sighash_v4.rs:153`. -/
def hashTypeAnyonecanpay (ht : Nat) : Bool := (ht &&& SIGHASH_ANYONECANPAY) != 0

/-- `(hash_type & SIGHASH_MASK) == SIGHASH_SINGLE`. Mirrors
`sighash_v4.rs:163,183`. -/
def hashTypeSingle (ht : Nat) : Bool := (ht &&& SIGHASH_MASK) == SIGHASH_SINGLE

/-- `(hash_type & SIGHASH_MASK) == SIGHASH_NONE`. Mirrors
`sighash_v4.rs:164,173`. -/
def hashTypeNone (ht : Nat) : Bool := (ht &&& SIGHASH_MASK) == SIGHASH_NONE

/-- The 32-byte zero slot used by `update_hash!` when its gating
condition is false. -/
def ZERO_DIGEST : List Nat := List.replicate DIGEST_BYTES 0

/-- The masked Sapling-V4 preimage: the same 13-section shape as
`preimage`, with three 32-byte slots conditionally replaced by
`ZERO_DIGEST` according to the `hash_type` flag byte. This matches the
`update_hash!`-driven path of `v4_signature_hash`:

  * `hashPrevouts` is zeroed when `ANYONECANPAY` is set;
  * `hashSequence` is zeroed when `ANYONECANPAY`, `SINGLE`, or `NONE` is set;
  * `hashOutputs` is replaced by `outputsReplacement` when
    `SINGLE`/`NONE` is set (the Rust code picks zero for `NONE`, or a
    `single_output_hash` for `SINGLE`; we abstract that as an
    opaque 32-byte slot the caller supplies).

The `hash_type` byte itself is not masked.

Source: librustzcash `sighash_v4.rs:151-192`. -/
def preimageMasked (s : SighashSections) (ht : Nat) (outputsReplacement : List Nat) :
    List Nat :=
  let prev := if hashTypeAnyonecanpay ht then ZERO_DIGEST else s.hashPrevouts
  let seq :=
    if hashTypeAnyonecanpay ht || hashTypeSingle ht || hashTypeNone ht then
      ZERO_DIGEST
    else
      s.hashSequence
  let out :=
    if hashTypeSingle ht || hashTypeNone ht then outputsReplacement else s.hashOutputs
  s.header
    ++ s.versionGroupId
    ++ prev
    ++ seq
    ++ out
    ++ s.hashJoinSplits
    ++ s.hashShieldedSpends
    ++ s.hashShieldedOutputs
    ++ s.lockTime
    ++ s.expiryHeight
    ++ s.valueBalanceSapling
    ++ s.hashType
    ++ s.input

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

We prove fifteen substantive theorems on this composition, covering: (a)
the full 13-section Sapling V4 shape; (b) the pre-Sapling V3 truncated
shape; and (c) the hash-type masking semantics.
-/

/-- **T1 (Sapling V4 preimage length, canonical input-less form).** For a
well-formed Sapling V4 section bundle with an empty transparent-input
slot (the "shielded input" case in `SigHasher::sighash`), the preimage has
the spec-prescribed `4 + 4 + 6·32 + 4 + 4 + 8 + 4 = 220` bytes. (Compare
ZIP-143's 217-byte V3 sighash preimage and ZIP-243's 220-byte V4
preimage; the +3 vs. the V3 size accounts for the two new shielded-bundle
digests minus the V3 header layout.) -/
theorem preimage_length_no_input (s : SighashSections) (hw : WellFormed s)
    (hInput : s.input = []) :
    (preimage s).length =
      HEADER_BYTES + VERSION_GROUP_ID_BYTES + 6 * DIGEST_BYTES + LOCK_TIME_BYTES
        + EXPIRY_HEIGHT_BYTES + VALUE_BALANCE_BYTES + HASH_TYPE_BYTES := by
  unfold preimage
  simp [List.length_append, hw.headerLen, hw.versionGroupIdLen, hw.prevoutsLen,
        hw.sequenceLen, hw.outputsLen, hw.joinSplitsLen, hw.shieldedSpendsLen,
        hw.shieldedOutputsLen, hw.lockTimeLen, hw.expiryHeightLen,
        hw.valueBalanceLen, hw.hashTypeLen, hInput]
  rfl

/-- **T2 (Sapling V4 preimage length, general form).** With an arbitrary
transparent input slot, the well-formed Sapling V4 preimage length is the
constant-section sum (220) plus `s.input.length`. -/
theorem preimage_length (s : SighashSections) (hw : WellFormed s) :
    (preimage s).length =
      HEADER_BYTES + VERSION_GROUP_ID_BYTES + 6 * DIGEST_BYTES + LOCK_TIME_BYTES
        + EXPIRY_HEIGHT_BYTES + VALUE_BALANCE_BYTES + HASH_TYPE_BYTES
        + s.input.length := by
  unfold preimage
  simp [List.length_append, hw.headerLen, hw.versionGroupIdLen, hw.prevoutsLen,
        hw.sequenceLen, hw.outputsLen, hw.joinSplitsLen, hw.shieldedSpendsLen,
        hw.shieldedOutputsLen, hw.lockTimeLen, hw.expiryHeightLen,
        hw.valueBalanceLen, hw.hashTypeLen]
  ring

/-- **T3 (full Sapling V4 injectivity of preimage).** When both bundles
are well-formed (so every fixed-width section has the canonical length),
identical preimages imply componentwise equality on all 13 sections,
including the newly-split `header` and `versionGroupId`. The proof peels
off each section from the left using `List.append_inj`. -/
theorem preimage_injective (s₁ s₂ : SighashSections)
    (hw₁ : WellFormed s₁) (hw₂ : WellFormed s₂)
    (heq : preimage s₁ = preimage s₂) :
    s₁.header = s₂.header ∧
    s₁.versionGroupId = s₂.versionGroupId ∧
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
  have hreassoc : ∀ (a b c d e f g h i j k l m : List Nat),
      a ++ b ++ c ++ d ++ e ++ f ++ g ++ h ++ i ++ j ++ k ++ l ++ m =
        a ++ (b ++ (c ++ (d ++ (e ++ (f ++ (g ++ (h ++ (i ++ (j ++ (k ++ (l ++ m)))))))))))
    := by
    intros; simp [List.append_assoc]
  rw [hreassoc, hreassoc] at heq
  -- Peel header.
  have hlenH : s₁.header.length = s₂.header.length := by
    rw [hw₁.headerLen, hw₂.headerLen]
  obtain ⟨hH, heq⟩ := List.append_inj heq hlenH
  -- Peel versionGroupId.
  have hlenVG : s₁.versionGroupId.length = s₂.versionGroupId.length := by
    rw [hw₁.versionGroupIdLen, hw₂.versionGroupIdLen]
  obtain ⟨hVG, heq⟩ := List.append_inj heq hlenVG
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
  exact ⟨hH, hVG, hP, hSeq, hO, hJ, hSS, hSO, hL, hE, hV, hHT, hIn⟩

/-- **T4 (determinism).** The sighash is a pure function of the section
bundle: identical bundles always give identical digests, regardless of the
abstract hash function `H`. This is what lets consensus nodes recompute
the digest reproducibly. -/
theorem sighash_deterministic (H : List Nat → List Nat) (s₁ s₂ : SighashSections)
    (heq : s₁ = s₂) :
    sighash H s₁ = sighash H s₂ := by
  rw [heq]

/-- **T5 (header sensitivity).** Changing the `header` section while
keeping the other 12 fixed changes the preimage; combined with `H`
injectivity, this changes the digest. -/
theorem sighash_sensitive_header (H : List Nat → List Nat)
    (hInj : Function.Injective H)
    (s₁ s₂ : SighashSections)
    (hw₁ : WellFormed s₁) (hw₂ : WellFormed s₂)
    (_hRest : s₁.versionGroupId = s₂.versionGroupId ∧
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
              s₁.versionGroupId = s₂.versionGroupId ∧
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
  exact hDiff hcomp.2.2.2.2.2.2.2.2.2.2.2.1

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
              s₁.versionGroupId = s₂.versionGroupId ∧
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
  exact hDiff hcomp.2.2.2.2.2.2.1

/-- **T8 (valueBalance sensitivity).** Changing the `valueBalanceSapling`
section changes the sighash. The Sapling net value flow is signed into
the sighash, preventing modification of the `valueBalance` field on an
authorised transaction. -/
theorem sighash_sensitive_value_balance (H : List Nat → List Nat)
    (hInj : Function.Injective H)
    (s₁ s₂ : SighashSections)
    (hw₁ : WellFormed s₁) (hw₂ : WellFormed s₂)
    (_hRest : s₁.header = s₂.header ∧
              s₁.versionGroupId = s₂.versionGroupId ∧
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
  exact hDiff hcomp.2.2.2.2.2.2.2.2.2.2.1

/-- **T9 (every section contributes — combined statement).** A
"sensitivity in all 13 slots" theorem: if any single section differs
between two well-formed bundles, the digests differ. This is the
componentwise sensitivity claim for the full Sapling V4 preimage
composition.

We state the contrapositive: equal sighashes (with `H` injective) force
all 13 sections to match. -/
theorem sighash_collision_implies_all_sections_equal (H : List Nat → List Nat)
    (hInj : Function.Injective H)
    (s₁ s₂ : SighashSections)
    (hw₁ : WellFormed s₁) (hw₂ : WellFormed s₂)
    (heq : sighash H s₁ = sighash H s₂) :
    s₁.header = s₂.header ∧
    s₁.versionGroupId = s₂.versionGroupId ∧
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
  let vg : List Nat := List.replicate VERSION_GROUP_ID_BYTES 0
  let lt : List Nat := List.replicate LOCK_TIME_BYTES 0
  let eh : List Nat := List.replicate EXPIRY_HEIGHT_BYTES 0
  let vb : List Nat := List.replicate VALUE_BALANCE_BYTES 0
  let ht : List Nat := List.replicate HASH_TYPE_BYTES 0
  have hzlen : z.length = DIGEST_BYTES := List.length_replicate
  have holen : o.length = DIGEST_BYTES := List.length_replicate
  have hhlen : h.length = HEADER_BYTES := List.length_replicate
  have hvglen : vg.length = VERSION_GROUP_ID_BYTES := List.length_replicate
  have hltlen : lt.length = LOCK_TIME_BYTES := List.length_replicate
  have hehlen : eh.length = EXPIRY_HEIGHT_BYTES := List.length_replicate
  have hvblen : vb.length = VALUE_BALANCE_BYTES := List.length_replicate
  have hhtlen : ht.length = HASH_TYPE_BYTES := List.length_replicate
  refine ⟨
    { header := h, versionGroupId := vg,
      hashPrevouts := o, hashSequence := z, hashOutputs := z,
      hashJoinSplits := z, hashShieldedSpends := z, hashShieldedOutputs := z,
      lockTime := lt, expiryHeight := eh, valueBalanceSapling := vb,
      hashType := ht, input := [] },
    { header := h, versionGroupId := vg,
      hashPrevouts := z, hashSequence := z, hashOutputs := o,
      hashJoinSplits := z, hashShieldedSpends := z, hashShieldedOutputs := z,
      lockTime := lt, expiryHeight := eh, valueBalanceSapling := vb,
      hashType := ht, input := [] },
    ⟨hhlen, hvglen, holen, hzlen, hzlen, hzlen, hzlen, hzlen,
     hltlen, hehlen, hvblen, hhtlen⟩,
    ⟨hhlen, hvglen, hzlen, hzlen, holen, hzlen, hzlen, hzlen,
     hltlen, hehlen, hvblen, hhtlen⟩,
    ?_, rfl, rfl⟩
  -- If the preimages were equal, full injectivity would force the prevouts
  -- digests to match — but bundle 1 has prevouts = o, bundle 2 has prevouts
  -- = z, and o ≠ z (they differ at index 0).
  intro habs
  have hcomp := preimage_injective
    { header := h, versionGroupId := vg,
      hashPrevouts := o, hashSequence := z, hashOutputs := z,
      hashJoinSplits := z, hashShieldedSpends := z, hashShieldedOutputs := z,
      lockTime := lt, expiryHeight := eh, valueBalanceSapling := vb,
      hashType := ht, input := [] }
    { header := h, versionGroupId := vg,
      hashPrevouts := z, hashSequence := z, hashOutputs := o,
      hashJoinSplits := z, hashShieldedSpends := z, hashShieldedOutputs := z,
      lockTime := lt, expiryHeight := eh, valueBalanceSapling := vb,
      hashType := ht, input := [] }
    ⟨hhlen, hvglen, holen, hzlen, hzlen, hzlen, hzlen, hzlen,
     hltlen, hehlen, hvblen, hhtlen⟩
    ⟨hhlen, hvglen, hzlen, hzlen, holen, hzlen, hzlen, hzlen,
     hltlen, hehlen, hvblen, hhtlen⟩
    habs
  -- After splitting header, hashPrevouts is the 3rd component (.2.2.1).
  have ho_eq_z : o = z := hcomp.2.2.1
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
hypothesis, the Sapling V4 preimage length is the sum of all 13 section
lengths (including the now-split `versionGroupId`). This is the basic
input shape for length-based ZIP-243 reasoning. -/
theorem preimage_length_eq_sum (s : SighashSections) :
    (preimage s).length =
      s.header.length + s.versionGroupId.length + s.hashPrevouts.length
        + s.hashSequence.length + s.hashOutputs.length
        + s.hashJoinSplits.length + s.hashShieldedSpends.length
        + s.hashShieldedOutputs.length
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
    (h2 : s₁.versionGroupId = s₂.versionGroupId)
    (h3 : s₁.hashPrevouts = s₂.hashPrevouts)
    (h4 : s₁.hashSequence = s₂.hashSequence)
    (h5 : s₁.hashOutputs = s₂.hashOutputs)
    (h6 : s₁.hashJoinSplits = s₂.hashJoinSplits)
    (h7 : s₁.hashShieldedSpends = s₂.hashShieldedSpends)
    (h8 : s₁.hashShieldedOutputs = s₂.hashShieldedOutputs)
    (h9 : s₁.lockTime = s₂.lockTime)
    (h10 : s₁.expiryHeight = s₂.expiryHeight)
    (h11 : s₁.valueBalanceSapling = s₂.valueBalanceSapling)
    (h12 : s₁.hashType = s₂.hashType)
    (h13 : s₁.input = s₂.input) :
    sighash H s₁ = sighash H s₂ := by
  unfold sighash preimage
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

/-- **T13 (six SIGHASH bytes give six distinct digests).** A concrete
application of T6: when the 12 non-`hashType` sections are fixed and
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
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact hDiff

/-- **T14 (versionGroupId sensitivity — Finding 52 closure).** Changing
the `versionGroupId` section while keeping the other 12 fixed changes the
preimage; combined with `H` injectivity, this changes the digest. This
theorem only makes sense because we now model `versionGroupId` as a
separate field from `header`; with the previous 12-section conflation,
this property could not be stated. Matches the Rust code at
`sighash_v4.rs:149-150` where `tx.version.header()` and
`tx.version.version_group_id()` are hashed as two distinct LE u32 fields. -/
theorem sighash_sensitive_version_group_id (H : List Nat → List Nat)
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
              s₁.hashType = s₂.hashType ∧
              s₁.input = s₂.input)
    (hDiff : s₁.versionGroupId ≠ s₂.versionGroupId) :
    sighash H s₁ ≠ sighash H s₂ := by
  intro habs
  have hpre : preimage s₁ = preimage s₂ := hInj habs
  have hcomp := preimage_injective s₁ s₂ hw₁ hw₂ hpre
  exact hDiff hcomp.2.1

/-- **T15 (uniform digest preimage — sanity check).** When every digest
section is the same byte string `d` (and the fixed-width fields are
zero), the Sapling V4 preimage is `header ‖ vg ‖ d⁶ ‖ lt ‖ eh ‖ vb ‖ ht
‖ input`. A degenerate but useful sanity check on the composition. -/
theorem preimage_uniform_digests
    (header vg lt eh vb ht input d : List Nat) :
    preimage
      { header := header, versionGroupId := vg,
        hashPrevouts := d, hashSequence := d, hashOutputs := d,
        hashJoinSplits := d, hashShieldedSpends := d, hashShieldedOutputs := d,
        lockTime := lt, expiryHeight := eh, valueBalanceSapling := vb,
        hashType := ht, input := input } =
      header ++ vg ++ d ++ d ++ d ++ d ++ d ++ d ++ lt ++ eh ++ vb ++ ht ++ input := by
  rfl

/-! ## Pre-Sapling V3 theorems (Finding 54 closure)

These theorems characterise the `preimageV3` shape that omits
`hashShieldedSpends`, `hashShieldedOutputs`, and `valueBalanceSapling`,
matching the `!tx.version.has_sapling()` path of librustzcash
`sighash_v4.rs:209-229`. -/

/-- **T16 (V3 preimage length, no input).** The well-formed pre-Sapling
V3 preimage with an empty transparent-input slot has `4 + 4 + 4·32 + 4 +
4 + 4 = 148` bytes — that is, exactly 220 minus the omitted (8 +
2·32) = 72 bytes of Sapling-only sections. -/
theorem preimageV3_length_no_input (s : SighashSections) (hw : WellFormed s)
    (hInput : s.input = []) :
    (preimageV3 s).length =
      HEADER_BYTES + VERSION_GROUP_ID_BYTES + 4 * DIGEST_BYTES + LOCK_TIME_BYTES
        + EXPIRY_HEIGHT_BYTES + HASH_TYPE_BYTES := by
  unfold preimageV3
  simp [List.length_append, hw.headerLen, hw.versionGroupIdLen, hw.prevoutsLen,
        hw.sequenceLen, hw.outputsLen, hw.joinSplitsLen, hw.lockTimeLen,
        hw.expiryHeightLen, hw.hashTypeLen, hInput]
  rfl

/-- **T17 (V3 preimage shorter than V4 by 72 bytes).** The well-formed
pre-Sapling V3 preimage is shorter than the corresponding Sapling V4
preimage by exactly `VALUE_BALANCE_BYTES + 2 * DIGEST_BYTES = 8 + 64 =
72` bytes, regardless of the transparent input length. -/
theorem preimageV3_length_diff (s : SighashSections) (hw : WellFormed s) :
    (preimage s).length =
      (preimageV3 s).length + VALUE_BALANCE_BYTES + 2 * DIGEST_BYTES := by
  unfold preimage preimageV3
  simp [List.length_append, hw.shieldedSpendsLen, hw.shieldedOutputsLen,
        hw.valueBalanceLen]
  ring

/-- **T18 (V3 preimage is invariant under Sapling-only sections).**
Modifying `hashShieldedSpends`, `hashShieldedOutputs`, or
`valueBalanceSapling` does not change the V3 preimage — these fields
simply do not appear in the V3 hash, matching the Rust gating on
`tx.version.has_sapling()`. This is the formal sense in which V3
transactions cannot bind to a Sapling bundle. -/
theorem preimageV3_invariant_under_sapling_fields
    (s : SighashSections) (newSpends newOutputs newVb : List Nat) :
    preimageV3 { s with hashShieldedSpends := newSpends,
                        hashShieldedOutputs := newOutputs,
                        valueBalanceSapling := newVb } =
      preimageV3 s := by
  unfold preimageV3
  rfl

/-! ## Hash-type masking theorems (Finding 53 closure)

These theorems characterise the `preimageMasked` shape that mirrors the
`update_hash!`-driven section zeroing in librustzcash
`sighash_v4.rs:151-192`. -/

/-- **T19 (SIGHASH_ALL → no masking).** When `hash_type = SIGHASH_ALL =
0x01`, none of the three maskable conditions trigger: the masked preimage
collapses to the canonical `preimage`. (`outputs_hash` is unchanged
because neither `SINGLE` nor `NONE` is set.) This is the formal sense in
which `SIGHASH_ALL` is the "no masking" sighash. -/
theorem preimageMasked_sighash_all_eq_preimage
    (s : SighashSections) (outputsReplacement : List Nat) :
    preimageMasked s SIGHASH_ALL outputsReplacement = preimage s := by
  unfold preimageMasked preimage hashTypeAnyonecanpay hashTypeSingle hashTypeNone
  simp [SIGHASH_ALL, SIGHASH_ANYONECANPAY, SIGHASH_MASK, SIGHASH_SINGLE,
        SIGHASH_NONE]

/-- **T20 (ANYONECANPAY zeros prevouts and sequence).** With
`hash_type = ALL | ANYONECANPAY = 0x81`, the `hashPrevouts` and
`hashSequence` 32-byte slots are replaced with `ZERO_DIGEST`, but
`hashOutputs` is unchanged (since `MASK ∩ ALL = ALL`, neither `SINGLE`
nor `NONE`). This matches the `update_hash!` predicates on
`sighash_v4.rs:153,162`.

Concretely: the masked preimage's `hashPrevouts` slot is `ZERO_DIGEST`
regardless of the bundle's `hashPrevouts`, and likewise for
`hashSequence`. -/
theorem preimageMasked_anyonecanpay_zeros_prevouts_and_sequence
    (s : SighashSections) (outputsReplacement : List Nat) :
    preimageMasked s (SIGHASH_ALL ||| SIGHASH_ANYONECANPAY) outputsReplacement =
      s.header
        ++ s.versionGroupId
        ++ ZERO_DIGEST
        ++ ZERO_DIGEST
        ++ s.hashOutputs
        ++ s.hashJoinSplits
        ++ s.hashShieldedSpends
        ++ s.hashShieldedOutputs
        ++ s.lockTime
        ++ s.expiryHeight
        ++ s.valueBalanceSapling
        ++ s.hashType
        ++ s.input := by
  unfold preimageMasked hashTypeAnyonecanpay hashTypeSingle hashTypeNone
  simp [SIGHASH_ALL, SIGHASH_ANYONECANPAY, SIGHASH_MASK, SIGHASH_SINGLE,
        SIGHASH_NONE]

/-- **T21 (SINGLE/NONE zero the sequence slot).** With either
`SIGHASH_SINGLE` or `SIGHASH_NONE` set in the lower mask bits (and no
`ANYONECANPAY`), the `hashSequence` slot is zeroed and `hashOutputs` is
replaced by the caller-supplied `outputsReplacement`. For `NONE` the
real Rust code passes `[0; 32]` (`sighash_v4.rs:191`); for `SINGLE` it
passes a `single_output_hash` of the signed input
(`sighash_v4.rs:186-189`). The `hashPrevouts` slot is unchanged. -/
theorem preimageMasked_single_zeros_sequence_replaces_outputs
    (s : SighashSections) (outputsReplacement : List Nat) :
    preimageMasked s SIGHASH_SINGLE outputsReplacement =
      s.header
        ++ s.versionGroupId
        ++ s.hashPrevouts
        ++ ZERO_DIGEST
        ++ outputsReplacement
        ++ s.hashJoinSplits
        ++ s.hashShieldedSpends
        ++ s.hashShieldedOutputs
        ++ s.lockTime
        ++ s.expiryHeight
        ++ s.valueBalanceSapling
        ++ s.hashType
        ++ s.input := by
  unfold preimageMasked hashTypeAnyonecanpay hashTypeSingle hashTypeNone
  simp [SIGHASH_SINGLE, SIGHASH_ANYONECANPAY, SIGHASH_MASK, SIGHASH_NONE]

/-- **T22 (masked preimage length is fixed-width regardless of hash_type).**
Provided the bundle is well-formed and `outputsReplacement` has exactly
32 bytes, every masked preimage has the same length as the unmasked
Sapling V4 preimage. The `update_hash!` macro never changes the byte
count — it only swaps in `[0; 32]` for the gated 32-byte slot. -/
theorem preimageMasked_length (s : SighashSections) (hw : WellFormed s)
    (ht : Nat) (outputsReplacement : List Nat)
    (hRepLen : outputsReplacement.length = DIGEST_BYTES) :
    (preimageMasked s ht outputsReplacement).length =
      HEADER_BYTES + VERSION_GROUP_ID_BYTES + 6 * DIGEST_BYTES + LOCK_TIME_BYTES
        + EXPIRY_HEIGHT_BYTES + VALUE_BALANCE_BYTES + HASH_TYPE_BYTES
        + s.input.length := by
  unfold preimageMasked
  have hZero : ZERO_DIGEST.length = DIGEST_BYTES := by
    unfold ZERO_DIGEST; exact List.length_replicate
  -- Case-split on the three boolean gates and use the fact that whichever
  -- branch fires, the resulting list has length `DIGEST_BYTES`.
  by_cases h1 : hashTypeAnyonecanpay ht
  all_goals by_cases h2 : hashTypeSingle ht
  all_goals by_cases h3 : hashTypeNone ht
  all_goals simp [h1, h2, h3, List.length_append, hw.headerLen,
                  hw.versionGroupIdLen, hw.prevoutsLen, hw.sequenceLen,
                  hw.outputsLen, hw.joinSplitsLen, hw.shieldedSpendsLen,
                  hw.shieldedOutputsLen, hw.lockTimeLen, hw.expiryHeightLen,
                  hw.valueBalanceLen, hw.hashTypeLen, hZero, hRepLen]
  all_goals ring

end Zebra.Zip243SaplingSighash
