import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# ZIP-225 NU5 (v5) transaction fixed 20-byte header layout

ZIP-225 introduced the v5 transaction format (active at NU5). The first 20
bytes of every v5 transaction are five `u32` little-endian fields, in order:

  1. `header`             — `u32` LE = `fOverwintered_bit | version`. For v5
     this is `(1 << 31) | 5 = 0x80000005`.
     Source: `zebra-chain/src/transaction/serialize.rs:520-523`.
  2. `nVersionGroupId`    — `u32` LE constant `0x26A7270A` from
     `zebra-chain/src/parameters/transaction.rs:13` (named
     `TX_V5_VERSION_GROUP_ID`).
     Source: `zebra-chain/src/transaction/serialize.rs:680`.
  3. `nConsensusBranchId` — `u32` LE; for NU5 this is `0xC2D6D0B4`.
     Source: `zebra-chain/src/transaction/serialize.rs:683-687`.
  4. `lock_time`          — `u32` LE (same byte layout as `LockTime`).
     Source: `zebra-chain/src/transaction/serialize.rs:690`.
  5. `nExpiryHeight`      — `u32` LE.
     Source: `zebra-chain/src/transaction/serialize.rs:693`.

That is exactly `5 × 4 = 20` bytes of fixed prefix.

This module is complementary to `TransactionV5Header.lean`: it focuses on
the **ZIP-225-specific bit-level structure** of the header word
(`fOverwintered | version` decomposition), proves the byte offsets of each
field, and verifies the layout obeys both the encode/decode round-trip and
its bit-level definition.

We model bytes as `Nat` in `[0, 256)` and the wire as a `List Nat`, the
same convention as `LockTime.lean`.

Source: <https://zips.z.cash/zip-0225#transaction-format>
Source: `zebra-chain/src/transaction/serialize.rs:518-693`
-/

namespace Zebra.Zip225V5Layout

/-! ## Constants -/

/-- `u32::MAX = 2^32 - 1`. -/
def U32_MAX : Nat := 4_294_967_295

/-- `2^31`: the `fOverwintered` bit position (the high bit of a `u32`).
Source: `zebra-chain/src/transaction/serialize.rs:520`
(`if self.is_overwintered() { 1 << 31 } else { 0 }`). -/
def F_OVERWINTERED_BIT : Nat := 2_147_483_648

/-- The v5 transaction `version` number is `5`. ZIP-225 §"Transaction
Format" specifies version 5 for the NU5 v5 transaction. -/
def V5_VERSION : Nat := 5

/-- The v5 transaction header word: `fOverwintered | version`. For v5 this
is `0x80000005 = 2^31 + 5`.
Source: `zebra-chain/src/transaction/serialize.rs:520-523`. -/
def V5_HEADER : Nat := F_OVERWINTERED_BIT + V5_VERSION

/-- `TX_V5_VERSION_GROUP_ID = 0x26A7270A`.
Source: `zebra-chain/src/parameters/transaction.rs:13`. -/
def TX_V5_VERSION_GROUP_ID : Nat := 0x26A7270A

/-- NU5 consensus branch ID = `0xC2D6D0B4`.
Source: `zebra-chain/src/parameters/network_upgrade.rs` (see the
`branch_id` table; NU5 is `0xc2d6d0b4`). -/
def NU5_BRANCH_ID : Nat := 0xC2D6D0B4

/-- The fixed-header byte length: `5 × 4 = 20`. -/
def HEADER_BYTES : Nat := 20

/-! ## Byte offsets of each field within the 20-byte prefix

These offsets are read from the encode/decode order in
`zebra-chain/src/transaction/serialize.rs:680-693`. The header field comes
first (written before the match arm at line 523), and then the V5 arm
writes versionGroupId, branchId, lock_time, expiry_height in that order.
-/

/-- Byte offset (within the 20-byte prefix) of `header`. -/
def OFF_HEADER : Nat := 0
/-- Byte offset of `nVersionGroupId`. -/
def OFF_VGID : Nat := 4
/-- Byte offset of `nConsensusBranchId`. -/
def OFF_BRANCH : Nat := 8
/-- Byte offset of `lock_time`. -/
def OFF_LOCK : Nat := 12
/-- Byte offset of `nExpiryHeight`. -/
def OFF_EXPIRY : Nat := 16

/-! ## The fixed-header record -/

/-- The 20-byte fixed prefix of a Zcash v5 transaction. We do not enforce
the version-group ID or header field values at the type level; instead,
the validity is asserted by predicates and round-trip lemmas below. -/
structure Header where
  header : Nat
  versionGroupId : Nat
  consensusBranchId : Nat
  lockTime : Nat
  expiryHeight : Nat
  deriving DecidableEq, Repr

/-! ## Helpers — same as `LockTime.lean` -/

/-- Little-endian 4-byte encoding. -/
def toLE4 (n : Nat) : List Nat :=
  [n % 256, (n / 256) % 256, (n / 65536) % 256, (n / 16777216) % 256]

/-- Little-endian 4-byte decoding. -/
def fromLE4 (b0 b1 b2 b3 : Nat) : Nat :=
  b0 + b1 * 256 + b2 * 65536 + b3 * 16777216

/-! ## Encoder and decoder -/

/-- Encode the v5 fixed header as 20 LE bytes, in field order. -/
def encode (h : Header) : List Nat :=
  toLE4 h.header ++
  toLE4 h.versionGroupId ++
  toLE4 h.consensusBranchId ++
  toLE4 h.lockTime ++
  toLE4 h.expiryHeight

/-- Decode the v5 fixed header from a byte stream. Returns the parsed
header and the remaining bytes, or `none` if fewer than 20 bytes. -/
def decode (bytes : List Nat) : Option (Header × List Nat) :=
  match bytes with
  | a0 :: a1 :: a2 :: a3 ::
    b0 :: b1 :: b2 :: b3 ::
    c0 :: c1 :: c2 :: c3 ::
    d0 :: d1 :: d2 :: d3 ::
    e0 :: e1 :: e2 :: e3 :: rest =>
    some (
      { header            := fromLE4 a0 a1 a2 a3
        versionGroupId    := fromLE4 b0 b1 b2 b3
        consensusBranchId := fromLE4 c0 c1 c2 c3
        lockTime          := fromLE4 d0 d1 d2 d3
        expiryHeight      := fromLE4 e0 e1 e2 e3 },
      rest)
  | _ => none

/-! ## A canonical NU5 header -/

/-- A canonical v5 header for NU5 with caller-supplied lock-time and expiry. -/
def nu5Header (lockTime expiryHeight : Nat) : Header :=
  { header            := V5_HEADER
    versionGroupId    := TX_V5_VERSION_GROUP_ID
    consensusBranchId := NU5_BRANCH_ID
    lockTime          := lockTime
    expiryHeight      := expiryHeight }

/-! ## A well-formedness predicate -/

/-- A v5 header is *well-formed* iff every field fits in `u32`, the
`header` word is exactly `V5_HEADER`, and the version-group ID is exactly
`TX_V5_VERSION_GROUP_ID`. The consensus branch ID and the two heights are
free to vary across network upgrades / individual transactions.
Source: `zebra-chain/src/transaction/serialize.rs:520-687`. -/
def IsWellFormed (h : Header) : Prop :=
  h.header = V5_HEADER ∧
  h.versionGroupId = TX_V5_VERSION_GROUP_ID ∧
  h.consensusBranchId ≤ U32_MAX ∧
  h.lockTime ≤ U32_MAX ∧
  h.expiryHeight ≤ U32_MAX

/-! ## Theorems -/

/-- Helper: LE round-trip on 4 bytes for any u32 input. -/
private theorem le4_roundtrip (n : Nat) (h : n ≤ U32_MAX) :
    fromLE4 (n % 256) ((n / 256) % 256) ((n / 65536) % 256) ((n / 16777216) % 256) = n := by
  unfold fromLE4 U32_MAX at *; omega

/-! ### Bit-level decomposition of the header word -/

/-- **T1.** The v5 header word is `0x80000005`. This is exactly
`F_OVERWINTERED_BIT | V5_VERSION` because the low 3 bits of `5` do not
overlap the high bit at position `31`. -/
theorem v5_header_value : V5_HEADER = 0x80000005 := by
  unfold V5_HEADER F_OVERWINTERED_BIT V5_VERSION
  decide

/-- **T2.** Bit-level decomposition: `V5_HEADER = F_OVERWINTERED_BIT + V5_VERSION`
and the high bit is *exactly* the overwintered flag.

  * `V5_HEADER / 2^31 = 1` (overwintered bit set)
  * `V5_HEADER % 2^31 = 5` (version is 5)

This proves the v5 wire-format constant decomposes correctly into its two
spec-defined components. -/
theorem v5_header_bit_decomposition :
    V5_HEADER / F_OVERWINTERED_BIT = 1 ∧
    V5_HEADER % F_OVERWINTERED_BIT = V5_VERSION := by
  refine ⟨?_, ?_⟩ <;> · unfold V5_HEADER F_OVERWINTERED_BIT V5_VERSION; decide

/-- **T3.** The header fits in `u32` (it is below `2^32`). -/
theorem v5_header_lt_u32 : V5_HEADER ≤ U32_MAX := by
  unfold V5_HEADER F_OVERWINTERED_BIT V5_VERSION U32_MAX; decide

/-- The version-group ID and the NU5 branch ID are valid `u32` values. -/
theorem v5_vgid_lt_u32 : TX_V5_VERSION_GROUP_ID ≤ U32_MAX := by
  unfold TX_V5_VERSION_GROUP_ID U32_MAX; decide
theorem nu5_branch_lt_u32 : NU5_BRANCH_ID ≤ U32_MAX := by
  unfold NU5_BRANCH_ID U32_MAX; decide

/-! ### Encoder structure -/

/-- **T4.** The encoder always produces exactly 20 bytes — the ZIP-225
fixed-header length. -/
theorem encode_length (h : Header) : (encode h).length = HEADER_BYTES := by
  unfold encode toLE4 HEADER_BYTES
  simp

/-- **T5.** Each 4-byte field encodes to exactly 4 bytes. -/
theorem toLE4_length (n : Nat) : (toLE4 n).length = 4 := by
  unfold toLE4; simp

/-! ### Round-trip -/

/-- **T6.** Round-trip on the abstract layout: decoding an encoded header
recovers it with no leftover, provided every field is u32-bounded. -/
theorem roundtrip (h : Header)
    (h1 : h.header ≤ U32_MAX)
    (h2 : h.versionGroupId ≤ U32_MAX)
    (h3 : h.consensusBranchId ≤ U32_MAX)
    (h4 : h.lockTime ≤ U32_MAX)
    (h5 : h.expiryHeight ≤ U32_MAX) :
    decode (encode h) = some (h, []) := by
  have r1 := le4_roundtrip h.header h1
  have r2 := le4_roundtrip h.versionGroupId h2
  have r3 := le4_roundtrip h.consensusBranchId h3
  have r4 := le4_roundtrip h.lockTime h4
  have r5 := le4_roundtrip h.expiryHeight h5
  change decode (encode h) = some (h, [])
  unfold encode toLE4 decode
  simp [r1, r2, r3, r4, r5]

/-- **T7.** Round-trip with a tail: the decoder consumes exactly 20 bytes
and hands back the remainder. -/
theorem roundtrip_with_tail (h : Header) (tail : List Nat)
    (h1 : h.header ≤ U32_MAX)
    (h2 : h.versionGroupId ≤ U32_MAX)
    (h3 : h.consensusBranchId ≤ U32_MAX)
    (h4 : h.lockTime ≤ U32_MAX)
    (h5 : h.expiryHeight ≤ U32_MAX) :
    decode (encode h ++ tail) = some (h, tail) := by
  have r1 := le4_roundtrip h.header h1
  have r2 := le4_roundtrip h.versionGroupId h2
  have r3 := le4_roundtrip h.consensusBranchId h3
  have r4 := le4_roundtrip h.lockTime h4
  have r5 := le4_roundtrip h.expiryHeight h5
  change decode (encode h ++ tail) = some (h, tail)
  unfold encode toLE4 decode
  simp [r1, r2, r3, r4, r5]

/-- **T8.** Well-formed v5 headers round-trip. This packages the
`IsWellFormed` predicate together with `roundtrip`. -/
theorem wellformed_roundtrip (h : Header) (wf : IsWellFormed h) :
    decode (encode h) = some (h, []) := by
  obtain ⟨hH, hV, hB, hL, hE⟩ := wf
  apply roundtrip
  · rw [hH]; exact v5_header_lt_u32
  · rw [hV]; exact v5_vgid_lt_u32
  · exact hB
  · exact hL
  · exact hE

/-! ### Concrete NU5 instance -/

/-- **T9.** A canonical NU5 header is well-formed for any caller-chosen
lock-time / expiry-height that are u32-bounded. -/
theorem nu5_wellformed (lockTime expiryHeight : Nat)
    (hLT : lockTime ≤ U32_MAX) (hEH : expiryHeight ≤ U32_MAX) :
    IsWellFormed (nu5Header lockTime expiryHeight) := by
  refine ⟨rfl, rfl, ?_, hLT, hEH⟩
  exact nu5_branch_lt_u32

/-- **T10.** The canonical NU5 header round-trips. -/
theorem nu5_roundtrip (lockTime expiryHeight : Nat)
    (hLT : lockTime ≤ U32_MAX) (hEH : expiryHeight ≤ U32_MAX) :
    decode (encode (nu5Header lockTime expiryHeight))
      = some (nu5Header lockTime expiryHeight, []) := by
  exact wellformed_roundtrip _ (nu5_wellformed lockTime expiryHeight hLT hEH)

/-! ### Literal NU5 wire vector

The canonical NU5 header with `lockTime = 0` and `expiryHeight = 0` has
a fully literal 20-byte encoding. The byte layout is:

```
05 00 00 80   header             = 0x80000005   (V5)
0A 27 A7 26   nVersionGroupId    = 0x26A7270A   (TX_V5_VERSION_GROUP_ID)
B4 D0 D6 C2   nConsensusBranchId = 0xC2D6D0B4   (NU5)
00 00 00 00   lock_time          = 0
00 00 00 00   nExpiryHeight      = 0
```
-/
theorem nu5_zero_encoding :
    encode (nu5Header 0 0) =
      [ 0x05, 0x00, 0x00, 0x80,
        0x0A, 0x27, 0xA7, 0x26,
        0xB4, 0xD0, 0xD6, 0xC2,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00 ] := by
  decide

/-! ### Byte-offset addressability

These say: given the canonical 20-byte encoding, the byte at offset
`OFF_HEADER`, `OFF_VGID`, etc. is the low byte of the corresponding field.
-/

/-- **T11.** Field offsets are distinct and span the 20-byte prefix. -/
theorem field_offsets_layout :
    OFF_HEADER = 0 ∧ OFF_VGID = 4 ∧ OFF_BRANCH = 8 ∧
    OFF_LOCK = 12 ∧ OFF_EXPIRY = 16 ∧
    OFF_EXPIRY + 4 = HEADER_BYTES := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold OFF_EXPIRY HEADER_BYTES; rfl

/-- **T12.** The byte at offset `OFF_HEADER` of the canonical NU5 encoding
is `0x05` — the low byte of `V5_HEADER`. -/
theorem nu5_byte_header_lo :
    (encode (nu5Header 0 0))[OFF_HEADER]? = some 0x05 := by
  unfold OFF_HEADER; decide

/-- **T13.** The byte at offset `OFF_HEADER + 3` is `0x80` — the high byte
of `V5_HEADER`, encoding the `fOverwintered` bit at position 31. -/
theorem nu5_byte_header_hi :
    (encode (nu5Header 0 0))[OFF_HEADER + 3]? = some 0x80 := by
  unfold OFF_HEADER; decide

/-- **T14.** The byte at offset `OFF_VGID` is `0x0A`, the low byte of the
v5 version-group ID `0x26A7270A`. -/
theorem nu5_byte_vgid_lo :
    (encode (nu5Header 0 0))[OFF_VGID]? = some 0x0A := by
  unfold OFF_VGID; decide

/-- **T15.** The byte at offset `OFF_BRANCH` is `0xB4`, the low byte of
the NU5 branch ID `0xC2D6D0B4`. -/
theorem nu5_byte_branch_lo :
    (encode (nu5Header 0 0))[OFF_BRANCH]? = some 0xB4 := by
  unfold OFF_BRANCH; decide

/-! ### Decoder rejection -/

/-- **T16.** The decoder rejects empty input. -/
theorem decode_empty : decode [] = none := rfl

/-- **T17.** The decoder rejects a 19-byte input (one short of the fixed
header length). -/
theorem decode_short_19
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
     b10 b11 b12 b13 b14 b15 b16 b17 b18 : Nat) :
    decode [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
            b10, b11, b12, b13, b14, b15, b16, b17, b18] = none := rfl

/-! ### Injectivity -/

/-- **T18.** Encoding is injective on u32-bounded headers: distinct
headers cannot share a wire image. -/
theorem encode_injective (h h' : Header)
    (h1 : h.header ≤ U32_MAX) (h2 : h.versionGroupId ≤ U32_MAX)
    (h3 : h.consensusBranchId ≤ U32_MAX) (h4 : h.lockTime ≤ U32_MAX)
    (h5 : h.expiryHeight ≤ U32_MAX)
    (h1' : h'.header ≤ U32_MAX) (h2' : h'.versionGroupId ≤ U32_MAX)
    (h3' : h'.consensusBranchId ≤ U32_MAX) (h4' : h'.lockTime ≤ U32_MAX)
    (h5' : h'.expiryHeight ≤ U32_MAX)
    (heq : encode h = encode h') : h = h' := by
  have rt  : decode (encode h)  = some (h,  []) := roundtrip h  h1  h2  h3  h4  h5
  have rt' : decode (encode h') = some (h', []) := roundtrip h' h1' h2' h3' h4' h5'
  rw [heq] at rt
  rw [rt] at rt'
  simp only [Option.some.injEq, Prod.mk.injEq, and_true] at rt'
  exact rt'

/-! ### NU6-style branch ID does not affect the layout -/

/-- The NU6 branch ID. The point of T19 is that the **layout** (bit
positions, field offsets) is invariant across network upgrades — only the
branch ID value changes. -/
def NU6_BRANCH_ID : Nat := 0xC8E71055

theorem nu6_branch_lt_u32 : NU6_BRANCH_ID ≤ U32_MAX := by
  unfold NU6_BRANCH_ID U32_MAX; decide

/-- A v5 header for NU6. -/
def nu6Header (lockTime expiryHeight : Nat) : Header :=
  { header            := V5_HEADER
    versionGroupId    := TX_V5_VERSION_GROUP_ID
    consensusBranchId := NU6_BRANCH_ID
    lockTime          := lockTime
    expiryHeight      := expiryHeight }

/-- **T19.** The v5 layout works for any network-upgrade branch ID: an
NU6 v5 header is well-formed and round-trips. -/
theorem nu6_roundtrip (lockTime expiryHeight : Nat)
    (hLT : lockTime ≤ U32_MAX) (hEH : expiryHeight ≤ U32_MAX) :
    decode (encode (nu6Header lockTime expiryHeight))
      = some (nu6Header lockTime expiryHeight, []) := by
  apply roundtrip
  · exact v5_header_lt_u32
  · exact v5_vgid_lt_u32
  · exact nu6_branch_lt_u32
  · exact hLT
  · exact hEH

/-- **T20.** The NU5 and NU6 encodings of a header (with the same lock-time
and expiry) share their first 8 bytes — the `(header, versionGroupId)` pair
is network-upgrade-independent. This is the *prefix* half of the layout
invariance claim; T21/T22/T23 below cover the rest. -/
theorem nu5_nu6_share_prefix :
    (encode (nu5Header 0 0)).take 8 =
    (encode (nu6Header 0 0)).take 8 := by
  decide

/-- **T21.** The branch-id slice of the NU5 and NU6 encodings actually
*differs*. This is the converse of T20 and the substantive content of the
"differ in bytes `[OFF_BRANCH, OFF_BRANCH+4)`" claim: without this lemma,
T20 alone is consistent with the two encodings being equal. -/
theorem nu5_nu6_branch_bytes_differ :
    ((encode (nu5Header 0 0)).drop OFF_BRANCH).take 4 ≠
    ((encode (nu6Header 0 0)).drop OFF_BRANCH).take 4 := by
  unfold OFF_BRANCH; decide

/-- **T22.** The 8-byte suffix (`lockTime ++ expiryHeight`) of the NU5 and
NU6 encodings agrees when the caller-supplied fields agree — the suffix
is network-upgrade-independent. -/
theorem nu5_nu6_share_suffix :
    (encode (nu5Header 0 0)).drop (OFF_BRANCH + 4) =
    (encode (nu6Header 0 0)).drop (OFF_BRANCH + 4) := by
  unfold OFF_BRANCH; decide

/-- **T23.** Pointwise byte-by-byte difference characterization: for every
index `i < 20`, the NU5 and NU6 encodings agree at `i` iff `i` is *outside*
the 4-byte branch-id window `[8, 12)`. Together with T0..T19 this closes
the original "differ exactly in `[OFF_BRANCH, OFF_BRANCH+4)`" claim. -/
theorem nu5_nu6_differ_iff_in_branch_window (i : Nat) (hi : i < HEADER_BYTES) :
    (encode (nu5Header 0 0))[i]? = (encode (nu6Header 0 0))[i]?
      ↔ (i < OFF_BRANCH ∨ OFF_BRANCH + 4 ≤ i) := by
  unfold HEADER_BYTES OFF_BRANCH at *
  interval_cases i <;> decide

/-- **T24.** Wire-level inequality: the full 20-byte NU5 and NU6 encodings
are not equal. This is the high-level "the branch ID is observable on the
wire" claim, derived from T21. -/
theorem nu5_nu6_encode_ne :
    encode (nu5Header 0 0) ≠ encode (nu6Header 0 0) := by
  intro heq
  exact nu5_nu6_branch_bytes_differ (by rw [heq])

end Zebra.Zip225V5Layout
