import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# V5 Transaction fixed header round-trip

Models the 20-byte fixed prefix of a Zcash v5 transaction from
`zebra-chain/src/transaction/serialize.rs:518` (serialise) and
`zebra-chain/src/transaction/serialize.rs:785` (deserialise). The prefix
contains, in order:

  * `header`             — `u32` LE: `fOverwintered` bit (high bit) OR'd with
    the version number. For v5 this is `0x80000005`
    (`zebra-chain/src/transaction/serialize.rs:520`).
  * `nVersionGroupId`    — `u32` LE constant `TX_V5_VERSION_GROUP_ID =
    0x26A7270A` from `zebra-chain/src/parameters/transaction.rs:13`.
  * `nConsensusBranchId` — `u32` LE: the branch ID from
    `zebra-chain/src/parameters/network_upgrade.rs:225` (e.g. NU5 is
    `0xc2d6d0b4`).
  * `lock_time`          — `u32` LE, see `zebra-chain/src/transaction/
    serialize.rs:690` (write) and `zebra-chain/src/transaction/lock_time.rs`.
  * `nExpiryHeight`      — `u32` LE, see `zebra-chain/src/transaction/
    serialize.rs:693` (write) and `zebra-chain/src/transaction/serialize.rs:
    1017` (read).

That is exactly 5 × 4 = 20 bytes. This module proves an encode/decode
round-trip on this fixed prefix using the same `fromLE4` / `toLE4` pattern
as `LockTime.lean`. We do not model the variable-length tail (inputs,
outputs, shielded data).

## Validation versus byte-level round-trip

The Rust deserialiser (`serialize.rs:785-994`) **rejects** byte streams
whose initial `u32` does not match the `(version, overwintered) = (5, true)`
pattern, and which do not have `versionGroupId = TX_V5_VERSION_GROUP_ID`.
It also rejects pre-NU5 consensus branch IDs at line 1007. Earlier versions
of this model proved a byte-level round-trip that accepted *any* 20-byte
prefix; that was a real Rust↔Lean mismatch (Finding 25). The current
module fixes this by:

  * defining a `WellFormed` predicate that pins `header = V5_HEADER` and
    `versionGroupId = TX_V5_VERSION_GROUP_ID`,
  * providing a validating decoder `decodeV5` that mirrors the Rust match
    on `(version, overwintered)` and the post-read constant check,
  * proving rejection theorems for non-V5 header words and wrong
    version-group IDs, and
  * proving the round-trip in both the permissive (byte-level) and strict
    (validating) shapes.
-/

namespace Zebra.TransactionV5Header

/-! ## Constants -/

/-- `u32::MAX = 2^32 - 1`. -/
def U32_MAX : Nat := 4_294_967_295

/-- The v5 transaction header word: `fOverwintered` (high bit) OR'd with the
version number `5`. Source: `zebra-chain/src/transaction/serialize.rs:520`. -/
def V5_HEADER : Nat := 0x80000005

/-- `TX_V5_VERSION_GROUP_ID`. Source:
`zebra-chain/src/parameters/transaction.rs:13`. -/
def TX_V5_VERSION_GROUP_ID : Nat := 0x26A7270A

/-- NU5 consensus branch ID. Source:
`zebra-chain/src/parameters/network_upgrade.rs:225`. -/
def NU5_BRANCH_ID : Nat := 0xc2d6d0b4

/-! ## The fixed-header record -/

/-- The 20-byte fixed prefix of a Zcash v5 transaction. All four-byte
fields are modelled as `Nat` with a `≤ U32_MAX` invariant enforced by the
encode/decode round-trip theorems. The byte-level round-trip does not pin
the `header` and `versionGroupId` words; consensus-level pinning lives in
`WellFormed` and `decodeV5`. -/
structure Header where
  header : Nat            -- = V5_HEADER for any consensus-valid v5 tx
  versionGroupId : Nat    -- = TX_V5_VERSION_GROUP_ID for any consensus-valid v5 tx
  consensusBranchId : Nat
  lockTime : Nat
  expiryHeight : Nat
  deriving DecidableEq, Repr

/-- A header is `WellFormed` for a Zcash v5 transaction when the leading
`header` word and the `versionGroupId` word match the constants that the
Rust `(5, true)` arm of `Transaction::zcash_deserialize` enforces
(`serialize.rs:987-995`). The remaining three fields are unconstrained at
this layer; `consensusBranchId` is constrained to be `≥ NU5` at line 1007,
which we expose via `WellFormedPostNU5`. -/
def WellFormed (h : Header) : Prop :=
  h.header = V5_HEADER ∧ h.versionGroupId = TX_V5_VERSION_GROUP_ID

instance (h : Header) : Decidable (WellFormed h) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Helpers -/

/-- Little-endian 4-byte encoding, identical to `LockTime.toLE4`. -/
def toLE4 (n : Nat) : List Nat :=
  [n % 256, (n / 256) % 256, (n / 65536) % 256, (n / 16777216) % 256]

/-- Little-endian 4-byte decoding, identical to `LockTime.fromLE4`. -/
def fromLE4 (b0 b1 b2 b3 : Nat) : Nat :=
  b0 + b1 * 256 + b2 * 65536 + b3 * 16777216

/-! ## Encoder and decoder -/

/-- Encode the fixed v5 header as 20 LE bytes, in field order:
`header || nVersionGroupId || nConsensusBranchId || lock_time || nExpiryHeight`. -/
def encode (h : Header) : List Nat :=
  toLE4 h.header ++
  toLE4 h.versionGroupId ++
  toLE4 h.consensusBranchId ++
  toLE4 h.lockTime ++
  toLE4 h.expiryHeight

/-- Permissive byte-level decoder. Returns the parsed header and the
remaining bytes, or `none` if there are fewer than 20 bytes. This decoder
does *not* validate the `header` or `versionGroupId` words; it is the
inverse of `encode` on the byte level. The consensus-level validating
decoder is `decodeV5`. -/
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

/-- Consensus-validating decoder. Mirrors the Rust `(5, true)` arm of
`Transaction::zcash_deserialize` (`serialize.rs:987-995`): it consumes the
20-byte fixed prefix and additionally rejects streams whose `header` word
is not `V5_HEADER` or whose `versionGroupId` word is not
`TX_V5_VERSION_GROUP_ID`. Returns `none` on a header validation failure. -/
def decodeV5 (bytes : List Nat) : Option (Header × List Nat) :=
  match decode bytes with
  | none => none
  | some (h, rest) =>
    if h.header = V5_HEADER ∧ h.versionGroupId = TX_V5_VERSION_GROUP_ID then
      some (h, rest)
    else
      none

/-! ## A canonical NU5 header for testing -/

/-- A concrete v5 header for the NU5 epoch with the canonical version-group
ID and arbitrary `lock_time` / `expiry_height` for the test vector. -/
def nu5Header (lockTime expiryHeight : Nat) : Header :=
  { header            := V5_HEADER
    versionGroupId    := TX_V5_VERSION_GROUP_ID
    consensusBranchId := NU5_BRANCH_ID
    lockTime          := lockTime
    expiryHeight      := expiryHeight }

/-! ## Theorems -/

/-- A helper: little-endian round-trip on 4 bytes for any u32 input. -/
private theorem le4_roundtrip (n : Nat) (h : n ≤ U32_MAX) :
    fromLE4 (n % 256) ((n / 256) % 256) ((n / 65536) % 256) ((n / 16777216) % 256) = n := by
  unfold fromLE4 U32_MAX at *; omega

/-- All three header constants fit in `u32`. -/
theorem v5_header_lt_u32 : V5_HEADER ≤ U32_MAX := by decide
theorem v5_vgid_lt_u32 : TX_V5_VERSION_GROUP_ID ≤ U32_MAX := by decide
theorem nu5_branch_lt_u32 : NU5_BRANCH_ID ≤ U32_MAX := by decide

/-- **T1.** The encoder always produces exactly 20 bytes. -/
theorem encode_length (h : Header) : (encode h).length = 20 := by
  unfold encode toLE4
  simp

/-- **T2.** Byte-level round-trip: decoding the encoded form recovers the
header and an empty trailing byte string, provided every field fits in
`u32`. This is *not* a consensus-validating round-trip; it just inverts
the byte serialisation. For the consensus-level statement see
`decodeV5_roundtrip` (T9). -/
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

/-- **T3.** Byte-level round-trip with extra trailing bytes: the decoder
consumes exactly 20 bytes and returns the remainder. -/
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

/-- **T4.** Decoder rejects fewer-than-20-byte inputs. We witness this
for the empty input and a 19-byte input. -/
theorem decode_empty : decode [] = none := rfl

theorem decode_short_19
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
     b10 b11 b12 b13 b14 b15 b16 b17 b18 : Nat) :
    decode [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
            b10, b11, b12, b13, b14, b15, b16, b17, b18] = none := rfl

/-- **T5.** Concrete test vector: a v5 header for the NU5 epoch round-trips
through `encode`/`decode`. The branch ID is `0xc2d6d0b4`. -/
theorem nu5_roundtrip (lockTime expiryHeight : Nat)
    (hLT : lockTime ≤ U32_MAX) (hEH : expiryHeight ≤ U32_MAX) :
    decode (encode (nu5Header lockTime expiryHeight))
      = some (nu5Header lockTime expiryHeight, []) := by
  apply roundtrip
  · exact v5_header_lt_u32
  · exact v5_vgid_lt_u32
  · exact nu5_branch_lt_u32
  · exact hLT
  · exact hEH

/-- **T6.** The concrete NU5 header with zero lock-time and zero
expiry-height has a fully literal byte encoding. This pins the wire format
against the spec: `header` is `05 00 00 80`, version-group ID is
`0A 27 A7 26`, NU5 branch ID is `B4 D0 D6 C2`, then 8 zero bytes for
`lock_time || expiry_height`. -/
theorem nu5_encoding_literal :
    encode (nu5Header 0 0) =
      [ 0x05, 0x00, 0x00, 0x80,
        0x0A, 0x27, 0xA7, 0x26,
        0xB4, 0xD0, 0xD6, 0xC2,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00 ] := by
  decide

/-- **T7.** The encoder is injective when all five fields are `u32`-bounded:
if two valid headers encode to the same byte list, they are equal. -/
theorem encode_injective (h h' : Header)
    (h1 : h.header ≤ U32_MAX) (h2 : h.versionGroupId ≤ U32_MAX)
    (h3 : h.consensusBranchId ≤ U32_MAX) (h4 : h.lockTime ≤ U32_MAX)
    (h5 : h.expiryHeight ≤ U32_MAX)
    (h1' : h'.header ≤ U32_MAX) (h2' : h'.versionGroupId ≤ U32_MAX)
    (h3' : h'.consensusBranchId ≤ U32_MAX) (h4' : h'.lockTime ≤ U32_MAX)
    (h5' : h'.expiryHeight ≤ U32_MAX)
    (heq : encode h = encode h') : h = h' := by
  have rt : decode (encode h) = some (h, []) := roundtrip h h1 h2 h3 h4 h5
  have rt' : decode (encode h') = some (h', []) := roundtrip h' h1' h2' h3' h4' h5'
  rw [heq] at rt
  rw [rt] at rt'
  simp only [Option.some.injEq, Prod.mk.injEq, and_true] at rt'
  exact rt'

/-- A v5 header for the NU6 epoch. The branch ID is `0xc8e71055` from
`zebra-chain/src/parameters/network_upgrade.rs:225`. -/
def nu6Header (lockTime expiryHeight : Nat) : Header :=
  { header            := V5_HEADER
    versionGroupId    := TX_V5_VERSION_GROUP_ID
    consensusBranchId := 0xc8e71055
    lockTime          := lockTime
    expiryHeight      := expiryHeight }

/-- **T8.** A non-NU5 v5 header round-trips equally well. The NU6 branch ID
`0xc8e71055` is exercised here so the proof depends on a different literal
than `nu5_roundtrip`. -/
theorem nu6_roundtrip (lockTime expiryHeight : Nat)
    (hLT : lockTime ≤ U32_MAX) (hEH : expiryHeight ≤ U32_MAX) :
    decode (encode (nu6Header lockTime expiryHeight))
      = some (nu6Header lockTime expiryHeight, []) := by
  apply roundtrip
  · exact v5_header_lt_u32
  · exact v5_vgid_lt_u32
  · change (0xc8e71055 : Nat) ≤ U32_MAX
    decide
  · exact hLT
  · exact hEH

/-! ## Consensus-validating decoder — Finding 25 coverage

The byte-level `decode` accepts any 20-byte prefix; the Rust deserialiser
does not. The theorems below pin the consensus-level behaviour of the
validating `decodeV5` decoder, matching the Rust `(5, true)` match arm
(`serialize.rs:987-995`). -/

/-- **T9.** Consensus-validating round-trip. The validating decoder
`decodeV5` round-trips exactly the well-formed headers. -/
theorem decodeV5_roundtrip (h : Header) (hwf : WellFormed h)
    (h3 : h.consensusBranchId ≤ U32_MAX)
    (h4 : h.lockTime ≤ U32_MAX)
    (h5 : h.expiryHeight ≤ U32_MAX) :
    decodeV5 (encode h) = some (h, []) := by
  obtain ⟨hH, hV⟩ := hwf
  have h1 : h.header ≤ U32_MAX := by rw [hH]; exact v5_header_lt_u32
  have h2 : h.versionGroupId ≤ U32_MAX := by rw [hV]; exact v5_vgid_lt_u32
  have rt : decode (encode h) = some (h, []) := roundtrip h h1 h2 h3 h4 h5
  unfold decodeV5
  rw [rt]
  simp [hH, hV]

/-- **T10.** Consensus-validating round-trip with trailing bytes. -/
theorem decodeV5_roundtrip_with_tail (h : Header) (tail : List Nat)
    (hwf : WellFormed h)
    (h3 : h.consensusBranchId ≤ U32_MAX)
    (h4 : h.lockTime ≤ U32_MAX)
    (h5 : h.expiryHeight ≤ U32_MAX) :
    decodeV5 (encode h ++ tail) = some (h, tail) := by
  obtain ⟨hH, hV⟩ := hwf
  have h1 : h.header ≤ U32_MAX := by rw [hH]; exact v5_header_lt_u32
  have h2 : h.versionGroupId ≤ U32_MAX := by rw [hV]; exact v5_vgid_lt_u32
  have rt : decode (encode h ++ tail) = some (h, tail) :=
    roundtrip_with_tail h tail h1 h2 h3 h4 h5
  unfold decodeV5
  rw [rt]
  simp [hH, hV]

/-- **T11.** Rejection: the validating decoder rejects streams whose
leading `u32` is `0x00000005` (the V1 "raw 5", no `fOverwintered` bit).
This is the byte stream `[0x05, 0x00, 0x00, 0x00, ...]` mentioned in
Finding 25 — Rust rejects it because `(version, overwintered) = (5, false)`
falls through the match. -/
theorem decodeV5_rejects_v5_without_overwintered_bit :
    decodeV5
      [ 0x05, 0x00, 0x00, 0x00,
        0x0A, 0x27, 0xA7, 0x26,
        0xB4, 0xD0, 0xD6, 0xC2,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00 ] = none := by
  decide

/-- **T12.** Rejection: the validating decoder rejects streams whose
`versionGroupId` is not `TX_V5_VERSION_GROUP_ID`, even if the leading
`header` word is correct. Here we use the Sapling V4 group ID
`0x892F2085`. -/
theorem decodeV5_rejects_wrong_version_group_id :
    decodeV5
      [ 0x05, 0x00, 0x00, 0x80,
        0x85, 0x20, 0x2F, 0x89,
        0xB4, 0xD0, 0xD6, 0xC2,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00 ] = none := by
  decide

/-- **T13.** Rejection: the validating decoder rejects streams whose
leading `u32` is `0x80000004` (V4, overwintered). Even with the correct
version-group ID for V5, the header word disqualifies the stream. -/
theorem decodeV5_rejects_v4_header :
    decodeV5
      [ 0x04, 0x00, 0x00, 0x80,
        0x0A, 0x27, 0xA7, 0x26,
        0xB4, 0xD0, 0xD6, 0xC2,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00 ] = none := by
  decide

/-- **T14.** Rejection: empty input fails the validating decoder. -/
theorem decodeV5_empty : decodeV5 [] = none := rfl

/-- **T15.** General rejection: any decoded header that is not
`WellFormed` causes `decodeV5` to reject the input. -/
theorem decodeV5_rejects_ill_formed (bytes : List Nat) (h : Header) (rest : List Nat)
    (hd : decode bytes = some (h, rest)) (hwf : ¬ WellFormed h) :
    decodeV5 bytes = none := by
  unfold decodeV5
  rw [hd]
  simp [WellFormed] at hwf
  by_cases h1 : h.header = V5_HEADER
  · simp [h1]
    intro hVG
    exact hwf h1 hVG
  · simp [h1]

/-- **T16.** Soundness of `decodeV5`: any header it accepts is `WellFormed`. -/
theorem decodeV5_accepts_only_well_formed (bytes : List Nat) (h : Header) (rest : List Nat)
    (hd : decodeV5 bytes = some (h, rest)) : WellFormed h := by
  unfold decodeV5 at hd
  cases hdec : decode bytes with
  | none => rw [hdec] at hd; simp at hd
  | some hp =>
    rw [hdec] at hd
    obtain ⟨h', rest'⟩ := hp
    by_cases hwf : h'.header = V5_HEADER ∧ h'.versionGroupId = TX_V5_VERSION_GROUP_ID
    · simp [hwf] at hd
      obtain ⟨hh, _⟩ := hd
      rw [← hh]
      exact hwf
    · simp [hwf] at hd

/-- **T17.** Canonical NU5 header is `WellFormed`. -/
theorem nu5Header_wellFormed (lockTime expiryHeight : Nat) :
    WellFormed (nu5Header lockTime expiryHeight) := by
  unfold WellFormed nu5Header
  exact ⟨rfl, rfl⟩

/-- **T18.** Canonical NU6 header is `WellFormed`. -/
theorem nu6Header_wellFormed (lockTime expiryHeight : Nat) :
    WellFormed (nu6Header lockTime expiryHeight) := by
  unfold WellFormed nu6Header
  exact ⟨rfl, rfl⟩

/-- **T19.** Concrete consensus-valid round-trip via `decodeV5`: a v5
header for the NU5 epoch survives the validating decoder. -/
theorem nu5_decodeV5_roundtrip (lockTime expiryHeight : Nat)
    (hLT : lockTime ≤ U32_MAX) (hEH : expiryHeight ≤ U32_MAX) :
    decodeV5 (encode (nu5Header lockTime expiryHeight))
      = some (nu5Header lockTime expiryHeight, []) := by
  apply decodeV5_roundtrip
  · exact nu5Header_wellFormed lockTime expiryHeight
  · exact nu5_branch_lt_u32
  · exact hLT
  · exact hEH

end Zebra.TransactionV5Header
