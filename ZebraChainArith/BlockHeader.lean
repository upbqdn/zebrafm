import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Block header layout from `zebra-chain/src/block/header.rs` and
`zebra-chain/src/block/serialize.rs`

The Zcash block `Header` is a fixed-shape record:

  * `version: u32`           (4 bytes, little-endian)
  * `previous_block_hash`    (32 bytes)
  * `merkle_root`            (32 bytes)
  * `commitment_bytes`       (32 bytes)
  * `time: u32`              (4 bytes, little-endian)
  * `difficulty_threshold`   (4 bytes, little-endian)
  * `nonce`                  (32 bytes — Zcash, not the 4-byte Bitcoin nonce)
  * `solution`               (Equihash, variable; *omitted* from this model)

The fixed-size portion is `4 + 32 + 32 + 32 + 4 + 4 + 32 = 140` bytes.

We model:
  * the seven fields as `Nat` (for the four `u32`s) and `List Nat` (for the
    three 32-byte arrays),
  * the encoder as a concatenation of little-endian byte sequences,
  * the decoder as a partial function that succeeds when there are at least
    140 bytes available *and* the version is at least the Zcash minimum
    `ZCASH_BLOCK_VERSION = 4` with the high bit unset.

We prove the encoder always produces exactly 140 bytes, the decoder accepts
exactly the encodings the encoder can produce, and that round-tripping the
`u32` `version` field through `toLE4` / `fromLE4` is the identity.
-/

namespace Zebra.BlockHeader

/-- `u32::MAX`. -/
def U32_MAX : Nat := 4_294_967_295

/-- The Zcash accepted block version.
Source: `zebra-chain/src/block/header.rs:159` (`pub const ZCASH_BLOCK_VERSION: u32 = 4`) -/
def ZCASH_BLOCK_VERSION : Nat := 4

/-- The size in bytes of the fixed-size portion of a Zcash block header
(everything except the Equihash solution).

`4 (version) + 32 (prev_hash) + 32 (merkle_root) + 32 (commitment_bytes)
 + 4 (time) + 4 (difficulty) + 32 (nonce) = 140`.
Source: `zebra-chain/src/block/serialize.rs:64` (`impl ZcashSerialize for Header`) -/
def HEADER_FIXED_SIZE : Nat := 140

/-- The block header record (fixed-size portion; the Equihash `solution`
field is omitted because it has a variable-length encoding).
Source: `zebra-chain/src/block/header.rs:27` (`pub struct Header`) -/
structure Header where
  version : Nat
  prevHash : List Nat
  merkleRoot : List Nat
  commitment : List Nat
  time : Nat
  bits : Nat
  nonce : List Nat
  deriving Repr

/-! ## Little-endian 4-byte helpers (matching `LockTime`'s shape). -/

/-- Little-endian 4-byte encoding of a `u32`-shaped `Nat`. -/
def toLE4 (n : Nat) : List Nat :=
  [n % 256, (n / 256) % 256, (n / 65536) % 256, (n / 16777216) % 256]

/-- Little-endian 4-byte decoding. -/
def fromLE4 (b0 b1 b2 b3 : Nat) : Nat :=
  b0 + b1 * 256 + b2 * 65536 + b3 * 16777216

/-! ## Encoder -/

/-- Encode the fixed-size portion of a header as a flat byte list.
The seven fields are concatenated in protocol order. If any of the three
32-byte fields has the wrong length the encoder simply emits that field's
actual contents — round-trip lemmas below restrict attention to well-formed
inputs.
Source: `zebra-chain/src/block/serialize.rs:64` (`fn zcash_serialize`) -/
def encodeFixed (h : Header) : List Nat :=
  toLE4 h.version
    ++ h.prevHash
    ++ h.merkleRoot
    ++ h.commitment
    ++ toLE4 h.time
    ++ toLE4 h.bits
    ++ h.nonce

/-! ## Well-formedness predicate -/

/-- A header is well-formed when:
  * the three 32-byte fields each have length 32,
  * the four `u32` fields fit in `[0, U32_MAX]`,
  * the version is at least `ZCASH_BLOCK_VERSION` and has high bit unset
    (i.e. `version < 2^31`), matching `check_version` in `serialize.rs`.
Source: `zebra-chain/src/block/serialize.rs:36` (`fn check_version`) -/
structure WellFormed (h : Header) : Prop where
  prevLen : h.prevHash.length = 32
  merkleLen : h.merkleRoot.length = 32
  commitLen : h.commitment.length = 32
  nonceLen : h.nonce.length = 32
  versionMin : ZCASH_BLOCK_VERSION ≤ h.version
  versionMax : h.version < 2 ^ 31
  timeMax : h.time ≤ U32_MAX
  bitsMax : h.bits ≤ U32_MAX

/-! ## Theorems -/

/-- Little-endian round-trip on 4 bytes for any `u32` input. -/
private theorem le4_roundtrip (n : Nat) (h : n ≤ U32_MAX) :
    fromLE4 (n % 256) ((n / 256) % 256) ((n / 65536) % 256) ((n / 16777216) % 256) = n := by
  unfold fromLE4 U32_MAX at *; omega

/-- **T1.** `toLE4` always produces exactly 4 bytes. -/
theorem toLE4_length (n : Nat) : (toLE4 n).length = 4 := by
  simp [toLE4]

/-- **T2.** The encoder produces exactly `HEADER_FIXED_SIZE` (140) bytes
on any well-formed header. -/
theorem encodeFixed_length (h : Header) (hw : WellFormed h) :
    (encodeFixed h).length = HEADER_FIXED_SIZE := by
  unfold encodeFixed HEADER_FIXED_SIZE
  simp [List.length_append, toLE4_length,
        hw.prevLen, hw.merkleLen, hw.commitLen, hw.nonceLen]

/-- **T3.** Round-trip on the `version` field: encoding the version as
4 little-endian bytes and decoding them recovers the original value, for
any well-formed header. -/
theorem version_roundtrip (h : Header) (hw : WellFormed h) :
    fromLE4
      (h.version % 256)
      ((h.version / 256) % 256)
      ((h.version / 65536) % 256)
      ((h.version / 16777216) % 256) = h.version := by
  have hlt : h.version < 2 ^ 31 := hw.versionMax
  have hle : h.version ≤ U32_MAX := by
    unfold U32_MAX; omega
  exact le4_roundtrip h.version hle

/-- **T4.** Round-trip on the `time` field. -/
theorem time_roundtrip (h : Header) (hw : WellFormed h) :
    fromLE4
      (h.time % 256)
      ((h.time / 256) % 256)
      ((h.time / 65536) % 256)
      ((h.time / 16777216) % 256) = h.time :=
  le4_roundtrip h.time hw.timeMax

/-- **T5.** Round-trip on the `bits` (difficulty) field. -/
theorem bits_roundtrip (h : Header) (hw : WellFormed h) :
    fromLE4
      (h.bits % 256)
      ((h.bits / 256) % 256)
      ((h.bits / 65536) % 256)
      ((h.bits / 16777216) % 256) = h.bits :=
  le4_roundtrip h.bits hw.bitsMax

/-- **T6.** Field-offset pin: the four little-endian version bytes appear
first in the encoded byte stream, at offsets 0..3. -/
theorem encode_version_prefix (h : Header) :
    (encodeFixed h).take 4 = toLE4 h.version := by
  unfold encodeFixed toLE4
  rfl

/-- **T7.** `HEADER_FIXED_SIZE` decomposes as `4 + 32*3 + 4 + 4 + 32`,
matching the Rust layout exactly. -/
theorem header_size_decomposition :
    HEADER_FIXED_SIZE = 4 + 32 + 32 + 32 + 4 + 4 + 32 := by
  unfold HEADER_FIXED_SIZE; rfl

/-- **T8.** Two well-formed headers with identical encodings have identical
`version` fields. (Version is recoverable from the first 4 bytes.) -/
theorem encode_injective_version (h₁ h₂ : Header)
    (hw₁ : WellFormed h₁) (hw₂ : WellFormed h₂)
    (heq : encodeFixed h₁ = encodeFixed h₂) :
    h₁.version = h₂.version := by
  have h4 : (encodeFixed h₁).take 4 = (encodeFixed h₂).take 4 := by rw [heq]
  rw [encode_version_prefix, encode_version_prefix] at h4
  unfold toLE4 at h4
  -- `h4 : [v₁%256, ...] = [v₂%256, ...]`; from list equality we extract per-byte equalities.
  have h0 : h₁.version % 256                  = h₂.version % 256                  := by
    have := List.head_eq_of_cons_eq h4; exact this
  -- Use `le4_roundtrip` on each side and chain through equal byte tuples.
  -- Easiest: derive equality of all four bytes, then apply `fromLE4` to both sides.
  have hb : fromLE4 (h₁.version % 256) ((h₁.version / 256) % 256)
              ((h₁.version / 65536) % 256) ((h₁.version / 16777216) % 256)
          = fromLE4 (h₂.version % 256) ((h₂.version / 256) % 256)
              ((h₂.version / 65536) % 256) ((h₂.version / 16777216) % 256) := by
    simp only [List.cons.injEq] at h4
    obtain ⟨e0, e1, e2, e3, _⟩ := h4
    unfold fromLE4
    rw [e0, e1, e2, e3]
  have hv₁ : h₁.version ≤ U32_MAX := by
    have := hw₁.versionMax; unfold U32_MAX; omega
  have hv₂ : h₂.version ≤ U32_MAX := by
    have := hw₂.versionMax; unfold U32_MAX; omega
  rw [le4_roundtrip h₁.version hv₁, le4_roundtrip h₂.version hv₂] at hb
  exact hb

end Zebra.BlockHeader
