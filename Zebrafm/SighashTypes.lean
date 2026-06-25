import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# SIGHASH type bytes

Models the `HashType` `bitflags` enum from
`zebra-chain/src/transaction/sighash.rs:15`, as used in ZIP-143/ZIP-243/ZIP-244.

The basic SIGHASH types are:

  * `ALL = 0b0000_0001 = 1`
  * `NONE = 0b0000_0010 = 2`
  * `SINGLE = ALL | NONE = 0b0000_0011 = 3`

The `ANYONECANPAY = 0b1000_0000 = 0x80` high bit can be OR-ed onto any basic
type, yielding six valid `HashType` values total:

  * `ALL`, `NONE`, `SINGLE`,
    `ALL_ANYONECANPAY`, `NONE_ANYONECANPAY`, `SINGLE_ANYONECANPAY`.

## Carrier type

Rust `HashType` is a `bitflags!` over `u32`
(`zebra-chain/src/transaction/sighash.rs:18`). The serialised `hash_type`
field is a little-endian `u32` (4 bytes); every canonical encoding has a
non-zero low byte and three zero upper bytes. We model bytes/words as `Nat`
and track the relevant ranges explicitly.

## Two decoding regimes

There are two ways Rust decodes a transparent-input SIGHASH byte:

  1. **Canonical** — `TryFrom<HashType> for SighashType`
     (`zebra-chain/src/transaction/sighash.rs:37`): accepts only the six
     canonical values; any other `u32` returns `Err(())`. This is used on the
     V5+ ZIP-244 path via `SigHasher::sighash`.

  2. **Raw V4** — `SigHasher::sighash_v4_raw`
     (`zebra-chain/src/transaction/sighash.rs:133`, lowering into
     `zebra-chain/src/primitives/zcash_primitives.rs:418` via
     `SighashType::from_raw`): accepts the full `u8` range, preserves the byte
     verbatim in the sighash preimage, and only uses `SIGHASH_MASK = 0x1f` to
     select the basic mode for the selection logic. This matches `zcashd`'s
     pre-V5 semantics where non-canonical bits like `0x41` participate in the
     digest rather than being rejected.

`decodeByte` below models (1). `decodeRawV4` models (2).
-/

namespace Zebra.SighashTypes

/-! ## Type byte constants -/

/-- `SIGHASH_ALL = 0b0000_0001`. -/
def SIGHASH_ALL : Nat := 1

/-- `SIGHASH_NONE = 0b0000_0010`. -/
def SIGHASH_NONE : Nat := 2

/-- `SIGHASH_SINGLE = ALL | NONE = 0b0000_0011`. -/
def SIGHASH_SINGLE : Nat := 3

/-- `SIGHASH_ANYONECANPAY = 0b1000_0000 = 0x80`. The high bit OR-ed onto any
basic type. -/
def SIGHASH_ANYONECANPAY : Nat := 0x80

/-- `SIGHASH_ALL | SIGHASH_ANYONECANPAY = 0x81`. -/
def SIGHASH_ALL_ANYONECANPAY : Nat := SIGHASH_ALL + SIGHASH_ANYONECANPAY

/-- `SIGHASH_NONE | SIGHASH_ANYONECANPAY = 0x82`. -/
def SIGHASH_NONE_ANYONECANPAY : Nat := SIGHASH_NONE + SIGHASH_ANYONECANPAY

/-- `SIGHASH_SINGLE | SIGHASH_ANYONECANPAY = 0x83`. -/
def SIGHASH_SINGLE_ANYONECANPAY : Nat := SIGHASH_SINGLE + SIGHASH_ANYONECANPAY

/-- `SIGHASH_MASK = 0x1f`: low-5-bit mask `zcashd` applies to the raw byte to
select the basic mode in the pre-V5 (V4) sighash. Source:
`zebra-chain/src/primitives/zcash_primitives.rs:411` (doc comment on
`sighash_v4_raw`). -/
def SIGHASH_MASK : Nat := 0x1f

/-- `u32::MAX = 2^32 - 1`. Rust `HashType` is a `bitflags!` over `u32`
(`zebra-chain/src/transaction/sighash.rs:18`). -/
def U32_MAX : Nat := 4294967295

/-- `u8::MAX = 2^8 - 1`. The byte range accepted by `sighash_v4_raw`. -/
def U8_MAX : Nat := 255

/-! ## Modelled type -/

/-- An abstract `HashType`: a basic mode plus an optional ANYONECANPAY flag. -/
inductive Basic
  | all
  | none
  | single
  deriving DecidableEq, Repr

/-- A full `HashType`: basic mode plus the `anyoneCanPay` flag. -/
structure HashType where
  basic : Basic
  anyoneCanPay : Bool
  deriving DecidableEq, Repr

/-- Encode `Basic` to its byte value. -/
def encodeBasic : Basic → Nat
  | .all    => SIGHASH_ALL
  | .none   => SIGHASH_NONE
  | .single => SIGHASH_SINGLE

/-- Encode a `HashType` to a single byte. Uses `+` rather than `Nat.lor`: this
is sound because the basic byte is in `{1,2,3}` (low two bits only) and
`SIGHASH_ANYONECANPAY = 0x80` is the high bit, so the two bit positions are
disjoint. `encodeByte_eq_or` (T_OR) shows the addition agrees with bitwise OR.
Source: `zebra-chain/src/transaction/sighash.rs:15` (`HashType` bitflags
layout) and `TryFrom<HashType> for SighashType` at line 37. -/
def encodeByte (ht : HashType) : Nat :=
  encodeBasic ht.basic + (if ht.anyoneCanPay then SIGHASH_ANYONECANPAY else 0)

/-- The same encoding written with bitwise OR, matching the Rust source
literally (`Self::ALL.bits() | Self::ANYONECANPAY.bits()`). -/
def encodeByteOr (ht : HashType) : Nat :=
  Nat.lor (encodeBasic ht.basic) (if ht.anyoneCanPay then SIGHASH_ANYONECANPAY else 0)

/-- Canonical decoder. Returns `none` for any value outside the six valid
encodings — every other byte is rejected by the Rust `TryFrom<HashType> for
SighashType` impl (`zebra-chain/src/transaction/sighash.rs:37`). This is the
V5+ ZIP-244 path. -/
def decodeByte (b : Nat) : Option HashType :=
  if      b = SIGHASH_ALL                 then some ⟨.all,    false⟩
  else if b = SIGHASH_NONE                then some ⟨.none,   false⟩
  else if b = SIGHASH_SINGLE              then some ⟨.single, false⟩
  else if b = SIGHASH_ALL_ANYONECANPAY    then some ⟨.all,    true⟩
  else if b = SIGHASH_NONE_ANYONECANPAY   then some ⟨.none,   true⟩
  else if b = SIGHASH_SINGLE_ANYONECANPAY then some ⟨.single, true⟩
  else none

/-- Returns `true` iff `b` is one of the six canonical SIGHASH bytes accepted
by `decodeByte`. -/
def isCanonical (b : Nat) : Bool :=
  decide (b = SIGHASH_ALL ∨ b = SIGHASH_NONE ∨ b = SIGHASH_SINGLE ∨
          b = SIGHASH_ALL_ANYONECANPAY ∨ b = SIGHASH_NONE_ANYONECANPAY ∨
          b = SIGHASH_SINGLE_ANYONECANPAY)

/-! ### Raw V4 (pre-V5) decoder

The V4 sighash path (`sighash_v4_raw`) accepts any `u8` and embeds the byte
verbatim into the digest preimage. The selection logic uses
`SIGHASH_MASK = 0x1f` to extract the basic mode, but the full raw byte
participates in the hash. Non-canonical bits (e.g. `0x40` set, giving `0x41`)
are preserved — this is intentional `zcashd` compatibility.

`decodeRawV4` returns the byte itself when it is in the `u8` range, otherwise
`none`. The interpretation under `SIGHASH_MASK` is provided as
`maskedBasic`. -/

/-- Raw V4 decoder: every byte in `[0, 255]` is accepted and returned
verbatim. The byte is the value that goes into the V4 sighash preimage as the
low `u32` LE word. Source:
`zebra-chain/src/primitives/zcash_primitives.rs:418` (`sighash_v4_raw`). -/
def decodeRawV4 (b : Nat) : Option Nat :=
  if b ≤ U8_MAX then some b else none

/-- The basic mode selected from a raw V4 byte via the low-5-bit mask. Returns
`some` only when the masked value is one of `{1, 2, 3}` — outside that range,
`zcashd` would treat the byte as having no defined basic mode. Source:
`zebra-chain/src/primitives/zcash_primitives.rs:411` (doc comment on
`sighash_v4_raw`). -/
def maskedBasic (b : Nat) : Option Basic :=
  let masked := Nat.land b SIGHASH_MASK
  if      masked = SIGHASH_ALL    then some .all
  else if masked = SIGHASH_NONE   then some .none
  else if masked = SIGHASH_SINGLE then some .single
  else none

/-! ## u32 little-endian encoding

The `hash_type` field is serialised as a 4-byte little-endian `u32`. The
underlying carrier type in Rust is `u32` (`HashType: u32`); every canonical
encoding has a non-zero low byte and three zero upper bytes. -/

/-- 4-byte little-endian encoding of a `u32` value `w`. Splits `w` into four
bytes `b0..b3` with `b0` the lowest. For `w < 256` this collapses to
`[w, 0, 0, 0]`. -/
def encodeU32LE (w : Nat) : List Nat :=
  [w % 256, (w / 256) % 256, (w / 65536) % 256, (w / 16777216) % 256]

/-- 4-byte little-endian decoding. -/
def decodeU32LE (b0 b1 b2 b3 : Nat) : Nat :=
  b0 + b1 * 256 + b2 * 65536 + b3 * 16777216

/-! ## Theorems -/

/-- **T1 (basic types are mutually distinct).** No two basic SIGHASH bytes
are equal. -/
theorem basic_types_distinct :
    SIGHASH_ALL ≠ SIGHASH_NONE ∧
    SIGHASH_ALL ≠ SIGHASH_SINGLE ∧
    SIGHASH_NONE ≠ SIGHASH_SINGLE := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **T2 (basic constants match `SINGLE = ALL | NONE`).** Because the `ALL`
and `NONE` bits don't overlap, `SINGLE` equals their numeric sum AND their
bitwise OR. -/
theorem single_eq_all_plus_none :
    SIGHASH_SINGLE = SIGHASH_ALL + SIGHASH_NONE ∧
    SIGHASH_SINGLE = Nat.lor SIGHASH_ALL SIGHASH_NONE := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **T3 (basic constants are in `[1, 3]`).** Every basic byte is a small
positive value strictly less than `ANYONECANPAY`. -/
theorem basic_byte_in_range (bs : Basic) :
    1 ≤ encodeBasic bs ∧ encodeBasic bs < SIGHASH_ANYONECANPAY := by
  cases bs <;> (refine ⟨?_, ?_⟩ <;> decide)

/-- **T4 (ANYONECANPAY is the high bit).** Adding `ANYONECANPAY` does not
change the underlying basic type bits — they're disjoint. The basic byte is
recovered by subtracting `ANYONECANPAY` from the combined byte. -/
theorem anyonecanpay_preserves_basic (bs : Basic) :
    encodeByte ⟨bs, true⟩ - SIGHASH_ANYONECANPAY = encodeBasic bs := by
  unfold encodeByte
  simp

/-- **T5 (ANYONECANPAY adds exactly `0x80`).** The combined byte is the basic
byte plus `0x80` when the flag is set. -/
theorem encodeByte_anyonecanpay_diff (bs : Basic) :
    encodeByte ⟨bs, true⟩ = encodeByte ⟨bs, false⟩ + SIGHASH_ANYONECANPAY := by
  unfold encodeByte
  simp

/-- **T6 (no-flag encoding agrees with `encodeBasic`).** -/
theorem encodeByte_no_flag (bs : Basic) :
    encodeByte ⟨bs, false⟩ = encodeBasic bs := by
  unfold encodeByte
  simp

/-- **T7 (encode is injective).** No two distinct `HashType` values share an
encoding. This is a consensus invariant — collisions would break sighash
domain separation. -/
theorem encodeByte_injective (ht₁ ht₂ : HashType)
    (h : encodeByte ht₁ = encodeByte ht₂) : ht₁ = ht₂ := by
  obtain ⟨b₁, a₁⟩ := ht₁
  obtain ⟨b₂, a₂⟩ := ht₂
  cases b₁ <;> cases b₂ <;> cases a₁ <;> cases a₂ <;>
    first
      | rfl
      | (exfalso; revert h
         unfold encodeByte encodeBasic SIGHASH_ALL SIGHASH_NONE SIGHASH_SINGLE
                SIGHASH_ANYONECANPAY
         decide)

/-- **T8 (round-trip: every `HashType` decodes from its encoding).** -/
theorem decode_encode (ht : HashType) :
    decodeByte (encodeByte ht) = some ht := by
  obtain ⟨bs, ac⟩ := ht
  cases bs <;> cases ac <;> decide

/-- **T9 (decoder accepts exactly six bytes).** Every byte that decodes
successfully is one of the six valid SIGHASH bytes. -/
theorem decode_range (b : Nat) (ht : HashType) (h : decodeByte b = some ht) :
    b = SIGHASH_ALL ∨ b = SIGHASH_NONE ∨ b = SIGHASH_SINGLE ∨
    b = SIGHASH_ALL_ANYONECANPAY ∨ b = SIGHASH_NONE_ANYONECANPAY ∨
    b = SIGHASH_SINGLE_ANYONECANPAY := by
  unfold decodeByte at h
  by_cases h1 : b = SIGHASH_ALL
  · exact Or.inl h1
  by_cases h2 : b = SIGHASH_NONE
  · exact Or.inr (Or.inl h2)
  by_cases h3 : b = SIGHASH_SINGLE
  · exact Or.inr (Or.inr (Or.inl h3))
  by_cases h4 : b = SIGHASH_ALL_ANYONECANPAY
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  by_cases h5 : b = SIGHASH_NONE_ANYONECANPAY
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  by_cases h6 : b = SIGHASH_SINGLE_ANYONECANPAY
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6))))
  · simp [h1, h2, h3, h4, h5, h6] at h

/-- **T10 (canonical decoder rejects 0).** The 0 byte is not a valid SIGHASH
type under the V5+ ZIP-244 path. (Note: under V4 raw, `0x00` is accepted
verbatim into the preimage — see `decodeRawV4_zero`.) -/
theorem decode_zero : decodeByte 0 = none := by decide

/-- **T11 (canonical decoder rejects 4).** No basic SIGHASH type is `4`. -/
theorem decode_four : decodeByte 4 = none := by decide

/-- **T12 (canonical decoder rejects bare `ANYONECANPAY` = 0x80).** `0x80` is
not a valid encoding — `ANYONECANPAY` must combine with a basic type. -/
theorem decode_bare_anyonecanpay : decodeByte SIGHASH_ANYONECANPAY = none := by
  decide

/-- **T13 (canonical decoder rejects 0x84).** Any combined byte must have a
basic type in the low nibble. -/
theorem decode_invalid_combined : decodeByte 0x84 = none := by decide

/-- **T14 (encoded byte is `< 256`).** Every canonical encoding fits in a
single byte; in particular it fits in `u32` (and `u8`). -/
theorem encodeByte_lt_256 (ht : HashType) : encodeByte ht < 256 := by
  obtain ⟨bs, ac⟩ := ht
  cases bs <;> cases ac <;> decide

/-- **T15 (u32 LE round-trip on `w < 2^32`).** Decoding the LE bytes produced
by `encodeU32LE w` recovers `w` exactly, for any `u32` value. -/
theorem u32_roundtrip (w : Nat) (hlt : w < 4294967296) :
    decodeU32LE
      (w % 256)
      ((w / 256) % 256)
      ((w / 65536) % 256)
      ((w / 16777216) % 256) = w := by
  unfold decodeU32LE
  omega

/-- **T16 (u32 LE encoding has length 4).** -/
theorem encodeU32LE_length (w : Nat) : (encodeU32LE w).length = 4 := rfl

/-- **T17 (canonical encoding fits in the low byte).** For any `HashType`, all
three upper LE bytes are zero. This is the property the previous T17 was
trying to express; we restate it as a real equality on the modular bytes
rather than a definitional unfold. -/
theorem encodeU32LE_canonical_upper_zero (ht : HashType) :
    let b := encodeByte ht
    (b / 256) % 256 = 0 ∧ (b / 65536) % 256 = 0 ∧ (b / 16777216) % 256 = 0 := by
  have h := encodeByte_lt_256 ht
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- **T18 (canonical u32 LE = `[b, 0, 0, 0]`).** The list form of T17:
serialising the canonical byte gives a 4-byte list whose tail is all zeros. -/
theorem encodeU32LE_canonical_list (ht : HashType) :
    encodeU32LE (encodeByte ht) = [encodeByte ht, 0, 0, 0] := by
  have h := encodeByte_lt_256 ht
  unfold encodeU32LE
  have h0 : encodeByte ht % 256 = encodeByte ht := Nat.mod_eq_of_lt h
  have h1 : (encodeByte ht / 256) % 256 = 0 := by
    have : encodeByte ht / 256 = 0 := Nat.div_eq_of_lt h
    simp [this]
  have h2 : (encodeByte ht / 65536) % 256 = 0 := by
    have : encodeByte ht / 65536 = 0 := Nat.div_eq_of_lt (by omega)
    simp [this]
  have h3 : (encodeByte ht / 16777216) % 256 = 0 := by
    have : encodeByte ht / 16777216 = 0 := Nat.div_eq_of_lt (by omega)
    simp [this]
  simp [h0, h1, h2, h3]

/-- **T19 (canonical u32 LE round-trip).** Given any `HashType`, serialise to
a u32 LE word and parse it back to the original byte. -/
theorem hash_type_u32_roundtrip (ht : HashType) :
    decodeU32LE (encodeByte ht) 0 0 0 = encodeByte ht := by
  unfold decodeU32LE
  omega

/-- **T20 (canonical full round-trip via u32 LE).** Combines the u32 LE codec
with the byte-level decoder. -/
theorem hash_type_full_roundtrip (ht : HashType) :
    decodeByte (decodeU32LE (encodeByte ht) 0 0 0) = some ht := by
  rw [hash_type_u32_roundtrip]
  exact decode_encode ht

/-- **T21 (canonical decoder rejects all bytes ≥ 4 except the ANYONECANPAY
trio).** -/
theorem decode_rejects_high_invalid (b : Nat)
    (h_ge : 4 ≤ b)
    (h1 : b ≠ SIGHASH_ALL_ANYONECANPAY)
    (h2 : b ≠ SIGHASH_NONE_ANYONECANPAY)
    (h3 : b ≠ SIGHASH_SINGLE_ANYONECANPAY) :
    decodeByte b = none := by
  unfold decodeByte
  have hne1 : b ≠ SIGHASH_ALL := by
    unfold SIGHASH_ALL; omega
  have hne2 : b ≠ SIGHASH_NONE := by
    unfold SIGHASH_NONE; omega
  have hne3 : b ≠ SIGHASH_SINGLE := by
    unfold SIGHASH_SINGLE; omega
  simp [hne1, hne2, hne3, h1, h2, h3]

/-! ### Bitwise-OR equivalence (FINDINGS: "encoding uses +") -/

/-- **T_OR1 (`+` equals `Nat.lor` for the canonical encoding).** The encoder
using addition agrees with the encoder using bitwise OR. This justifies the
use of `+` in `encodeByte`: the basic byte and ANYONECANPAY occupy disjoint
bit positions, so addition coincides with `Nat.lor`. -/
theorem encodeByte_eq_or (ht : HashType) :
    encodeByte ht = encodeByteOr ht := by
  obtain ⟨bs, ac⟩ := ht
  cases bs <;> cases ac <;> decide

/-- **T_OR2 (each basic byte OR-ed with `ANYONECANPAY` equals the
combined constant).** Matches the Rust definition
`Self::ALL.bits() | Self::ANYONECANPAY.bits()`. -/
theorem combined_constants_are_or :
    Nat.lor SIGHASH_ALL SIGHASH_ANYONECANPAY = SIGHASH_ALL_ANYONECANPAY ∧
    Nat.lor SIGHASH_NONE SIGHASH_ANYONECANPAY = SIGHASH_NONE_ANYONECANPAY ∧
    Nat.lor SIGHASH_SINGLE SIGHASH_ANYONECANPAY = SIGHASH_SINGLE_ANYONECANPAY := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ### V4 raw byte semantics (FINDINGS: "preserves non-canonical bits") -/

/-- **T_V41 (V4 raw accepts every `u8`).** The raw V4 decoder returns the byte
verbatim for every value in `[0, 255]`. This models
`SighashType::from_raw(u8) → Self` and the fact that the byte is embedded
unchanged into the V4 sighash preimage. -/
theorem decodeRawV4_total_in_u8 (b : Nat) (h : b ≤ U8_MAX) :
    decodeRawV4 b = some b := by
  unfold decodeRawV4
  simp [h]

/-- **T_V42 (V4 raw accepts non-canonical `0x41`, canonical rejects it).** The
two paths disagree on the byte `0x41` (`SIGHASH_ALL | 0x40`). The V4 path
preserves it for digest computation; the V5+ canonical path rejects it. -/
theorem v4_raw_vs_canonical_0x41 :
    decodeRawV4 0x41 = some 0x41 ∧ decodeByte 0x41 = none := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **T_V43 (V4 raw accepts non-canonical `0xc1`).** `0xc1 = ALL |
ANYONECANPAY | 0x40` — sets the extra `0x40` bit on top of a canonical
combined value. V4 still preserves it; canonical rejects it. -/
theorem v4_raw_vs_canonical_0xc1 :
    decodeRawV4 0xc1 = some 0xc1 ∧ decodeByte 0xc1 = none := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **T_V44 (V4 raw accepts `0x00`, canonical rejects it).** Zero byte: V4 has
no defined basic mode under the mask but still embeds `0x00` into the preimage
(`maskedBasic 0 = none`). -/
theorem v4_raw_vs_canonical_zero :
    decodeRawV4 0 = some 0 ∧ decodeByte 0 = none ∧ maskedBasic 0 = none := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **T_V45 (V4 raw rejects `b ≥ 256`).** Inputs outside the `u8` range are
not representable as a raw sighash byte. -/
theorem decodeRawV4_out_of_range (b : Nat) (h : 256 ≤ b) :
    decodeRawV4 b = none := by
  unfold decodeRawV4 U8_MAX
  simp; omega

/-- **T_V46 (V4 raw vs canonical agree on every canonical byte).** When the
input is one of the six canonical bytes, the two decoders agree on the byte
value: V4 returns the byte, canonical returns the parsed `HashType` whose
re-encoding is the same byte. This is the "equal on the canonical subset"
property. -/
theorem v4_and_canonical_agree_on_canonical (ht : HashType) :
    decodeRawV4 (encodeByte ht) = some (encodeByte ht) ∧
    (decodeByte (encodeByte ht)).map encodeByte = some (encodeByte ht) := by
  refine ⟨?_, ?_⟩
  · apply decodeRawV4_total_in_u8
    have := encodeByte_lt_256 ht
    unfold U8_MAX
    omega
  · rw [decode_encode]
    rfl

/-- **T_V47 (`maskedBasic` agrees with `decodeByte` on canonical no-flag
bytes).** For the three canonical "no-ANYONECANPAY" bytes, the V4 mask
selection recovers the same basic mode the canonical decoder produces. -/
theorem maskedBasic_agrees_no_flag (bs : Basic) :
    maskedBasic (encodeByte ⟨bs, false⟩) = some bs := by
  cases bs <;> decide

/-- **T_V48 (`maskedBasic` strips the ANYONECANPAY high bit).** For the three
canonical "with-ANYONECANPAY" bytes, the V4 mask selection still recovers the
correct basic mode (the `0x80` bit is masked off). -/
theorem maskedBasic_agrees_with_flag (bs : Basic) :
    maskedBasic (encodeByte ⟨bs, true⟩) = some bs := by
  cases bs <;> decide

/-! ### Carrier-type (u32) range (FINDINGS: "byte vs u32 carrier") -/

/-- **T_U321 (canonical encoding fits in `u32`).** Every canonical encoding
fits in the Rust carrier type `u32`. -/
theorem encodeByte_lt_u32 (ht : HashType) : encodeByte ht ≤ U32_MAX := by
  have := encodeByte_lt_256 ht
  unfold U32_MAX
  omega

/-- **T_U322 (canonical encoding fits in `u8`).** Every canonical encoding
fits in `u8`, which is what allows V4 raw and canonical to share the same
on-wire byte for canonical values. -/
theorem encodeByte_lt_u8 (ht : HashType) : encodeByte ht ≤ U8_MAX := by
  have := encodeByte_lt_256 ht
  unfold U8_MAX
  omega

/-- **T_U323 (canonical bytes are a strict subset of `u32`).** There exist
`u32` values that are NOT canonical encodings — for instance `4`, `0x80`,
`0x100`, and `0xffff_ffff`. The canonical decoder rejects them while they
remain representable in the Rust `u32` carrier. This documents the gap
between "any `u32`" and "canonical sighash byte". -/
theorem u32_strict_superset_of_canonical :
    decodeByte 4 = none ∧
    decodeByte 0x80 = none ∧
    decodeByte 0x100 = none ∧
    decodeByte U32_MAX = none ∧
    4 ≤ U32_MAX ∧ 0x80 ≤ U32_MAX ∧ 0x100 ≤ U32_MAX := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **T_U324 (canonical u32 LE encoding is bytewise canonical).** Each byte
of `encodeU32LE (encodeByte ht)` is `< 256`. This is trivially true of the
list-literal form, but the theorem checks it survives the modular
definition for any canonical input. -/
theorem encodeU32LE_canonical_bytewise (ht : HashType) :
    ∀ b ∈ encodeU32LE (encodeByte ht), b < 256 := by
  intro b hb
  rw [encodeU32LE_canonical_list ht] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb
  · rw [hb]; exact encodeByte_lt_256 ht
  · rw [hb]; decide
  · rw [hb]; decide
  · rw [hb]; decide

end Zebra.SighashTypes
