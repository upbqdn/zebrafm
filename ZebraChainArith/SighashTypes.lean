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
type. Yielding six valid `HashType` values total:

  * `ALL`, `NONE`, `SINGLE`,
    `ALL_ANYONECANPAY`, `NONE_ANYONECANPAY`, `SINGLE_ANYONECANPAY`.

We model bytes as `Nat`. The serialised `hash_type` is a `u32` little-endian
4-byte word that fits in the low byte (the upper 24 bits are always zero,
since all encoded values are `< 256`).
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

/-- Encode a `HashType` to a single byte, adding the ANYONECANPAY high bit
when set. Source: `zebra-chain/src/transaction/sighash.rs:15` (`HashType`
bitflags layout) and `TryFrom<HashType> for SighashType` at line 37. -/
def encodeByte (ht : HashType) : Nat :=
  encodeBasic ht.basic + (if ht.anyoneCanPay then SIGHASH_ANYONECANPAY else 0)

/-- Decode a byte back to a `HashType`. Returns `none` for any value outside
the six valid encodings — every other byte is rejected by the Rust
`TryFrom<HashType> for SighashType` impl. -/
def decodeByte (b : Nat) : Option HashType :=
  if      b = SIGHASH_ALL                 then some ⟨.all,    false⟩
  else if b = SIGHASH_NONE                then some ⟨.none,   false⟩
  else if b = SIGHASH_SINGLE              then some ⟨.single, false⟩
  else if b = SIGHASH_ALL_ANYONECANPAY    then some ⟨.all,    true⟩
  else if b = SIGHASH_NONE_ANYONECANPAY   then some ⟨.none,   true⟩
  else if b = SIGHASH_SINGLE_ANYONECANPAY then some ⟨.single, true⟩
  else none

/-! ## u32 little-endian encoding

The `hash_type` is serialised as a 4-byte little-endian `u32`. Since every
valid value is `< 256`, only the lowest byte is non-zero. -/

/-- 4-byte little-endian encoding of a byte value. The Rust transaction
serialiser writes `hash_type as u32` in LE order. -/
def encodeU32LE (b : Nat) : List Nat := [b, 0, 0, 0]

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
and `NONE` bits don't overlap, `SINGLE` equals their numeric sum. -/
theorem single_eq_all_plus_none :
    SIGHASH_SINGLE = SIGHASH_ALL + SIGHASH_NONE := by decide

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

/-- **T10 (decoder rejects 0).** The 0 byte is not a valid SIGHASH type. -/
theorem decode_zero : decodeByte 0 = none := by decide

/-- **T11 (decoder rejects 4).** No basic SIGHASH type is `4`. -/
theorem decode_four : decodeByte 4 = none := by decide

/-- **T12 (decoder rejects bare `ANYONECANPAY` = 0x80).** `0x80` is not a
valid encoding — `ANYONECANPAY` must combine with a basic type. -/
theorem decode_bare_anyonecanpay : decodeByte SIGHASH_ANYONECANPAY = none := by
  decide

/-- **T13 (decoder rejects 0x84).** Any combined byte must have a basic type
in the low nibble. -/
theorem decode_invalid_combined : decodeByte 0x84 = none := by decide

/-- **T14 (encoded byte is `< 256`).** Every valid encoding fits in a single
byte. -/
theorem encodeByte_lt_256 (ht : HashType) : encodeByte ht < 256 := by
  obtain ⟨bs, ac⟩ := ht
  cases bs <;> cases ac <;> decide

/-- **T15 (u32 LE round-trip).** Decoding a u32 LE word with zeroes in the
upper three bytes recovers the low byte exactly. -/
theorem u32_roundtrip (b : Nat) :
    decodeU32LE b 0 0 0 = b := by
  unfold decodeU32LE
  omega

/-- **T16 (u32 LE encoding has length 4).** -/
theorem encodeU32LE_length (b : Nat) : (encodeU32LE b).length = 4 := rfl

/-- **T17 (u32 LE encoding is canonical: upper bytes zero).** All valid
SIGHASH bytes have zero in their three upper LE bytes when serialised as
`u32`. -/
theorem encodeU32LE_zero_upper (ht : HashType) :
    encodeU32LE (encodeByte ht) = [encodeByte ht, 0, 0, 0] := rfl

/-- **T18 (full sighash u32 LE round-trip).** Given any `HashType`, serialise
to a u32 LE word and parse it back to the original byte. -/
theorem hash_type_u32_roundtrip (ht : HashType) :
    decodeU32LE (encodeByte ht) 0 0 0 = encodeByte ht :=
  u32_roundtrip (encodeByte ht)

/-- **T19 (full round-trip via u32 LE).** Combines the u32 LE codec with the
byte-level decoder to give a complete encode/decode cycle. -/
theorem hash_type_full_roundtrip (ht : HashType) :
    decodeByte (decodeU32LE (encodeByte ht) 0 0 0) = some ht := by
  rw [hash_type_u32_roundtrip]
  exact decode_encode ht

/-- **T20 (decoder rejects all bytes ≥ 4 except the ANYONECANPAY trio).** -/
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

end Zebra.SighashTypes
