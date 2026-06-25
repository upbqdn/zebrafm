import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# NU6.3 / Ironwood v6 Orchard flags layout

Models the NU6.3 / Ironwood v6 transaction format introduced by experimental PR
#10762 (branch `nu63-ironwood`, gated by `#[cfg(zcash_unstable = "nu6.3")]`).

Under the pre-NU6.3 (v5 Orchard) codec, the `flagsOrchard` byte has the layout

  * bit 0 (`0b00000001`) = `ENABLE_SPENDS`
  * bit 1 (`0b00000010`) = `ENABLE_OUTPUTS`
  * bits 2..7           = reserved, MUST be zero

This matches the existing `Flags` `bitflags!` definition and the consensus rule:

  > [NU5 onward] In a version 5 transaction, the reserved bits 2..7 of the
  > flagsOrchard field MUST be zero.

The PR #10762 NU6.3 codec adds `ENABLE_CROSS_ADDRESS` at bit 2 to the same
`Flags` `bitflags!` enum, and parses it via the `FlagsV6(Flags)` newtype. So:

  * bit 0 = `ENABLE_SPENDS`
  * bit 1 = `ENABLE_OUTPUTS`
  * bit 2 = `ENABLE_CROSS_ADDRESS`   (new in NU6.3)
  * bits 3..7 = reserved, MUST be zero

Both codecs are implemented in Rust by the single function `Flags::from_byte(b,
reserved)`. The v5 path passes `PRE_NU6_3_RESERVED = !(SPENDS | OUTPUTS) =
0b11111100`; the v6 path passes `NU6_3_RESERVED = !(SPENDS | OUTPUTS |
CROSS_ADDRESS) = 0b11111000`. The function rejects `b` iff `b & reserved ≠ 0`.

The same wire byte therefore *parses differently* under the two codecs: under
the v5 codec, bit 2 is reserved and any byte with bit 2 set is rejected; under
the v6 codec, bit 2 carries `enableCrossAddress` and is accepted.

We model the underlying `Flags` as a 3-bit record, the v6 codec as the newtype
`FlagsV6:= Flags`, and the byte parser `Flags.fromByte` as the Rust function.
The NU6.3 activation height is left as a parameter (the upstream Ironwood
activation height has not been ratified at the time of this writing — only the
`Nu6_3` `NetworkUpgrade` enum variant and the placeholder consensus branch ID
`0xffff_ffff` exist on the experimental branch).

We prove:

  * the v5 codec rejects every byte with any of bits 2..7 set;
  * the v6 codec accepts every byte with bits 3..7 clear;
  * the v5 and v6 codecs disagree on `0b00000111 = 7` and on `0b00000100 = 4`;
  * agreement: on bytes with bits 2..7 all zero, the two codecs decode to the
    same `ENABLE_SPENDS` / `ENABLE_OUTPUTS` bits;
  * the `FlagsV6` newtype's `From` projection recovers the underlying `Flags`;
  * v6 transactions are only valid at heights ≥ the (parameterised) NU6.3
    activation height; non-v6 transactions are unconstrained by that gate.
-/

namespace Zebra.NU63IronwoodLayout

/-! ## Bit-level helpers (no `BitVec`) -/

/-- The `k`-th bit of `n` as a `Nat` (0 or 1). -/
def bit (n k : Nat) : Nat := (n / 2 ^ k) % 2

/-- A byte's bit is at most 1. -/
theorem bit_le_one (n k : Nat) : bit n k ≤ 1 := by
  unfold bit
  exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))

/-- A `u8` value is below `256`. -/
def U8_MAX : Nat := 255

/-! ## Bit-mask constants

Source (NU6.3 branch `nu63-ironwood`): `zebra-chain/src/orchard/shielded_data.rs`
inside the `bitflags!` block defining `pub struct Flags: u8 { … }`. -/

/-- `ENABLE_SPENDS = 0b00000001`. -/
def ENABLE_SPENDS : Nat := 0b00000001

/-- `ENABLE_OUTPUTS = 0b00000010`. -/
def ENABLE_OUTPUTS : Nat := 0b00000010

/-- `ENABLE_CROSS_ADDRESS = 0b00000100`. New in NU6.3 (PR #10762). -/
def ENABLE_CROSS_ADDRESS : Nat := 0b00000100

/-- `PRE_NU6_3_RESERVED = !(ENABLE_SPENDS | ENABLE_OUTPUTS) = 0b11111100`.
Source: `Flags::PRE_NU6_3_RESERVED`. Bits 2..7 are reserved in the v5 codec. -/
def PRE_NU6_3_RESERVED : Nat := 0b11111100

/-- `NU6_3_RESERVED = !(ENABLE_SPENDS | ENABLE_OUTPUTS | ENABLE_CROSS_ADDRESS) =
0b11111000`. Source: `Flags::NU6_3_RESERVED`. Bits 3..7 are reserved in the v6
codec. -/
def NU6_3_RESERVED : Nat := 0b11111000

/-- The bitmask of v5 valid bits: bits 0 and 1. -/
def V5_VALID_MASK : Nat := ENABLE_SPENDS + ENABLE_OUTPUTS    -- 0b00000011

/-- The bitmask of v6 valid bits: bits 0, 1, and 2. -/
def V6_VALID_MASK : Nat := ENABLE_SPENDS + ENABLE_OUTPUTS + ENABLE_CROSS_ADDRESS
                                                              -- 0b00000111

/-! ## `Flags` and `FlagsV6` records

Mirrors the `bitflags!` block at `zebra-chain/src/orchard/shielded_data.rs`. The
underlying type is `Flags: u8`, with three named bits. `FlagsV6(Flags)` is a
newtype that carries the *parser variant* in the type — pre-NU6.3 (`Flags`)
treats bit 2 as reserved; NU6.3 (`FlagsV6`) treats bit 2 as the
`ENABLE_CROSS_ADDRESS` flag. -/

/-- The `Flags` `bitflags!` enum. In Rust this is `pub struct Flags: u8` with
the three associated `const`s `ENABLE_SPENDS`, `ENABLE_OUTPUTS`, and (from
NU6.3) `ENABLE_CROSS_ADDRESS`. -/
structure Flags where
  enableSpends       : Bool
  enableOutputs      : Bool
  enableCrossAddress : Bool
  deriving DecidableEq, Repr

/-- The NU6.3 v6 Orchard / Ironwood flag newtype. Mirrors
`pub struct FlagsV6(Flags)` — the wrapper exists purely to select the NU6.3
parser variant. -/
structure FlagsV6 where
  toFlags : Flags
  deriving DecidableEq, Repr

/-- `From<FlagsV6> for Flags`: project the inner `Flags` out of the v6 newtype.
Mirrors the Rust `impl From<FlagsV6> for Flags`. -/
def FlagsV6.toFlagsImpl (f : FlagsV6) : Flags := f.toFlags

/-! ## Byte parser

Mirrors the Rust function

```rust
fn from_byte(byte: u8, reserved: u8) -> Result<Self, SerializationError> {
    if byte & reserved != 0 {
        return Err(...);
    }
    Ok(Self::from_bits_truncate(byte))
}
```

Because Lean doesn't have a primitive `Nat`-bitwise-AND with a friendly
unfolding, we model `byte & reserved = 0` by the equivalent condition "every
bit set in `reserved` is clear in `byte`". For the two concrete masks in use
(`PRE_NU6_3_RESERVED` and `NU6_3_RESERVED`), that reduces to a simple numerical
upper bound on the byte. -/

/-- Decode the named bits out of a byte, ignoring (truncating) any bits outside
positions 0, 1, 2. Mirrors `Flags::from_bits_truncate`. -/
def Flags.fromBitsTruncate (b : Nat) : Flags :=
  { enableSpends       := bit b 0 = 1
    enableOutputs      := bit b 1 = 1
    enableCrossAddress := bit b 2 = 1 }

/-- The v5 (pre-NU6.3) reserved-bit predicate `byte & PRE_NU6_3_RESERVED = 0`,
expressed equivalently as `byte ≤ V5_VALID_MASK = 0b00000011`. -/
def passesV5ReservedCheck (b : Nat) : Bool := decide (b ≤ V5_VALID_MASK)

/-- The v6 (NU6.3) reserved-bit predicate `byte & NU6_3_RESERVED = 0`,
expressed equivalently as `byte ≤ V6_VALID_MASK = 0b00000111`. -/
def passesV6ReservedCheck (b : Nat) : Bool := decide (b ≤ V6_VALID_MASK)

/-! ## V5 codec -/

/-- The v5 Orchard flags decoder. Models `ZcashDeserialize for Flags` calling
`Flags::from_byte(b, PRE_NU6_3_RESERVED)`: rejects any byte whose reserved bits
2..7 are set. -/
def decodeV5 (b : Nat) : Option Flags :=
  if passesV5ReservedCheck b then
    some (Flags.fromBitsTruncate b)
  else none

/-- The v5 Orchard flags encoder. Models `ZcashSerialize for Flags`. -/
def encodeV5 (f : Flags) : Nat :=
  (if f.enableSpends  then ENABLE_SPENDS  else 0) +
  (if f.enableOutputs then ENABLE_OUTPUTS else 0)

/-! ## V6 codec -/

/-- The v6 Orchard / Ironwood flags decoder. Models `ZcashDeserialize for
FlagsV6` calling `Flags::from_byte(b, NU6_3_RESERVED)`: rejects any byte whose
reserved bits 3..7 are set. -/
def decodeV6 (b : Nat) : Option FlagsV6 :=
  if passesV6ReservedCheck b then
    some { toFlags := Flags.fromBitsTruncate b }
  else none

/-- The v6 Orchard / Ironwood flags encoder. -/
def encodeV6 (f : FlagsV6) : Nat :=
  (if f.toFlags.enableSpends       then ENABLE_SPENDS       else 0) +
  (if f.toFlags.enableOutputs      then ENABLE_OUTPUTS      else 0) +
  (if f.toFlags.enableCrossAddress then ENABLE_CROSS_ADDRESS else 0)

/-! ## Transaction validity gate (NU6.3 activation)

The NU6.3 activation height is left as a parameter `hNU6_3 : Nat`. The
experimental upstream branch (`nu63-ironwood`) defines the `Nu6_3`
`NetworkUpgrade` variant and a placeholder consensus branch ID `0xffff_ffff`,
but does **not** assign a concrete activation height on any network — see
`zebra-chain/src/parameters/constants.rs`, where the highest mainnet entry is
`NU6_2`. Encoding a guessed mainnet height here would be wrong. -/

/-- The transaction version. Pre-NU6.3 nodes accept `v1`..`v5`; NU6.3 nodes
also accept `v6`. -/
inductive TxVersion
  | v1 | v2 | v3 | v4 | v5 | v6
  deriving DecidableEq, Repr

/-- Models the height-gated rule from PR #10762: a `v6` transaction is only
valid at heights `≥ hNU6_3` (the parameterised NU6.3 activation height); all
other versions are unconstrained by this gate. -/
def txVersionValidAtHeight (hNU6_3 : Nat) (v : TxVersion) (h : Nat) : Bool :=
  match v with
  | .v6 => h ≥ hNU6_3
  | _   => true

/-! ## Theorems

The bit-level reserved-bit theorems below characterise the v5 and v6 codecs
purely in terms of `bit b k` (the `k`-th bit of `b` as a `Nat`). They are
equivalent to the "byte & reserved = 0" Rust check; the equivalence comes from
the fact that for `b : u8`, the only reserved-bit assignments that pass the
check are those bounded above by the corresponding valid mask. -/

/-- **T1 (v5 rejects any byte with any reserved bit set).** Generalises the
narrow "bit 2" case to all of bits 2..7: any byte whose `k`-th bit is set for
some `k ∈ {2,3,4,5,6,7}` is rejected by the v5 codec. This is the full
pre-NU6.3 reserved-bit rule "bits 2..7 of `flagsOrchard` MUST be zero". -/
theorem decodeV5_rejects_reserved_bit
    (b : Nat) (_hb : b ≤ U8_MAX) (k : Nat)
    (hk_lo : 2 ≤ k) (_hk_hi : k ≤ 7) (hbit : bit b k = 1) :
    decodeV5 b = none := by
  -- bit b k = 1 with k ≥ 2 means b ≥ 2^k ≥ 4, so b > V5_VALID_MASK = 3.
  have hbit' : (b / 2 ^ k) % 2 = 1 := hbit
  have hdivpos : b / 2 ^ k ≥ 1 := by
    rcases Nat.eq_zero_or_pos (b / 2 ^ k) with hzero | hpos
    · simp [hzero] at hbit'
    · exact hpos
  have hpow_le : (4 : Nat) ≤ 2 ^ k :=
    calc (4 : Nat) = 2 ^ 2 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk_lo
  have hbge_pow : (2 ^ k : Nat) ≤ b :=
    calc (2 ^ k : Nat) = 2 ^ k * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ k * (b / 2 ^ k) := Nat.mul_le_mul_left _ hdivpos
      _ ≤ b := Nat.mul_div_le _ _
  have hbge : (4 : Nat) ≤ b := Nat.le_trans hpow_le hbge_pow
  unfold decodeV5 passesV5ReservedCheck V5_VALID_MASK ENABLE_SPENDS ENABLE_OUTPUTS
  have hbg : ¬ b ≤ 1 + 2 := by omega
  simp [hbg]

/-- **T1b (v5 rejects bit-2-set bytes, instance of T1).** The original
narrower statement, recovered as the `k = 2` instance of `decodeV5_rejects_reserved_bit`. -/
theorem decodeV5_rejects_bit2 (b : Nat) (hb : b ≤ U8_MAX) (hbit : bit b 2 = 1) :
    decodeV5 b = none :=
  decodeV5_rejects_reserved_bit b hb 2 (by decide) (by decide) hbit

/-- **T2 (v6 accepts any byte ≤ V6_VALID_MASK).** Any byte at or below
`0b00000111` is accepted by the v6 codec, decoding to the obvious record of
bits 0, 1, 2. -/
theorem decodeV6_accepts_low_byte (b : Nat) (hb : b ≤ V6_VALID_MASK) :
    decodeV6 b = some
      { toFlags := { enableSpends      := bit b 0 = 1
                     enableOutputs     := bit b 1 = 1
                     enableCrossAddress := bit b 2 = 1 } } := by
  unfold decodeV6 passesV6ReservedCheck Flags.fromBitsTruncate
  simp [hb]

/-- **T2b (v6 rejects bytes whose reserved bits 3..7 are set).** Symmetric to
T1: any byte whose `k`-th bit is set for some `k ∈ {3,4,5,6,7}` is rejected by
the v6 codec. -/
theorem decodeV6_rejects_reserved_bit
    (b : Nat) (_hb : b ≤ U8_MAX) (k : Nat)
    (hk_lo : 3 ≤ k) (_hk_hi : k ≤ 7) (hbit : bit b k = 1) :
    decodeV6 b = none := by
  have hbit' : (b / 2 ^ k) % 2 = 1 := hbit
  have hdivpos : b / 2 ^ k ≥ 1 := by
    rcases Nat.eq_zero_or_pos (b / 2 ^ k) with hzero | hpos
    · simp [hzero] at hbit'
    · exact hpos
  have hpow_le : (8 : Nat) ≤ 2 ^ k :=
    calc (8 : Nat) = 2 ^ 3 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk_lo
  have hbge_pow : (2 ^ k : Nat) ≤ b :=
    calc (2 ^ k : Nat) = 2 ^ k * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ k * (b / 2 ^ k) := Nat.mul_le_mul_left _ hdivpos
      _ ≤ b := Nat.mul_div_le _ _
  have hbge : (8 : Nat) ≤ b := Nat.le_trans hpow_le hbge_pow
  unfold decodeV6 passesV6ReservedCheck V6_VALID_MASK
    ENABLE_SPENDS ENABLE_OUTPUTS ENABLE_CROSS_ADDRESS
  have hbg : ¬ b ≤ 1 + 2 + 4 := by omega
  simp [hbg]

/-- **T3 (v6 accepts `0b00000111`).** The NU6.3 wire byte `0b00000111 = 7`
decodes under `FlagsV6` to "all three flags set". -/
theorem decodeV6_seven :
    decodeV6 0b00000111 = some
      { toFlags := { enableSpends      := true
                     enableOutputs     := true
                     enableCrossAddress := true } } := by
  decide

/-- **T4 (v5 rejects `0b00000111`).** Same byte rejected by the v5 codec —
bits 2..7 are reserved. -/
theorem decodeV5_seven : decodeV5 0b00000111 = none := by decide

/-- **T5 (codecs disagree on `0b00000111`).** The same byte parses differently
under the two codecs: v6 accepts and decodes to "all three flags"; v5 rejects.
This is the core wire-compatibility break introduced by PR #10762. -/
theorem codecs_disagree_on_seven :
    (∃ f : FlagsV6, decodeV6 0b00000111 = some f) ∧ decodeV5 0b00000111 = none := by
  refine ⟨?_, ?_⟩
  · exact ⟨_, decodeV6_seven⟩
  · exact decodeV5_seven

/-- **T6 (v5 rejects `0b00000100`).** The byte with only bit 2 set is rejected
under the v5 codec because bit 2 is reserved. -/
theorem decodeV5_four : decodeV5 0b00000100 = none := by decide

/-- **T7 (v6 accepts `0b00000100` as cross-address only).** The byte with only
bit 2 set decodes under the v6 codec to `enableCrossAddress` set and the other
two flags clear. -/
theorem decodeV6_four :
    decodeV6 0b00000100 = some
      { toFlags := { enableSpends      := false
                     enableOutputs     := false
                     enableCrossAddress := true } } := by
  decide

/-! ## Codec agreement on the v5-valid sub-range -/

/-- **T8 (v5 / v6 agree on `enableSpends` / `enableOutputs` for v5-valid
bytes).** On every byte that is valid under both codecs (i.e. bits 2..7 clear),
the two decoders produce the same values for `enableSpends` and
`enableOutputs`. Wire-compatibility statement: a v6 node parsing a v5 byte
sees the same spend/output flags. -/
theorem decodeV6_agrees_on_v5_range (b : Nat) (hb : b ≤ V5_VALID_MASK) :
    ∃ fv5 : Flags, ∃ fv6 : FlagsV6,
      decodeV5 b = some fv5 ∧ decodeV6 b = some fv6 ∧
      fv5.enableSpends   = fv6.toFlags.enableSpends ∧
      fv5.enableOutputs  = fv6.toFlags.enableOutputs := by
  refine
    ⟨{ enableSpends      := bit b 0 = 1
       enableOutputs     := bit b 1 = 1
       enableCrossAddress := bit b 2 = 1 },
     { toFlags := { enableSpends      := bit b 0 = 1
                    enableOutputs     := bit b 1 = 1
                    enableCrossAddress := bit b 2 = 1 } },
     ?_, ?_, rfl, rfl⟩
  · unfold decodeV5 passesV5ReservedCheck Flags.fromBitsTruncate
    simp [hb]
  · unfold decodeV6 passesV6ReservedCheck Flags.fromBitsTruncate
    unfold V5_VALID_MASK ENABLE_SPENDS ENABLE_OUTPUTS at hb
    unfold V6_VALID_MASK ENABLE_SPENDS ENABLE_OUTPUTS ENABLE_CROSS_ADDRESS
    have hb' : b ≤ 7 := by omega
    simp [hb']

/-- **T9 (v6 cross-address bit cleared on v5-valid range).** On every byte
that is valid under the v5 codec (bits 2..7 clear), the v6 decoder reports
`enableCrossAddress = false`. So a v5 byte never accidentally sets the
cross-address flag when re-parsed as v6. -/
theorem decodeV6_no_cross_on_v5_range (b : Nat) (hb : b ≤ V5_VALID_MASK) :
    ∃ fv6 : FlagsV6,
      decodeV6 b = some fv6 ∧ fv6.toFlags.enableCrossAddress = false := by
  have hb' : b ≤ V6_VALID_MASK := by
    unfold V5_VALID_MASK ENABLE_SPENDS ENABLE_OUTPUTS at hb
    unfold V6_VALID_MASK ENABLE_SPENDS ENABLE_OUTPUTS ENABLE_CROSS_ADDRESS
    omega
  refine ⟨_, decodeV6_accepts_low_byte b hb', ?_⟩
  -- bit b 2 = 0 when b ≤ 3 since b / 4 = 0
  unfold bit
  unfold V5_VALID_MASK ENABLE_SPENDS ENABLE_OUTPUTS at hb
  have : b / 4 = 0 := by omega
  simp [this]

/-! ## V6 codec encode / decode round-trip -/

/-- **T10 (v6 round-trip).** Every `FlagsV6` struct encodes to a byte that the
decoder maps back to itself. -/
theorem v6_roundtrip (f : FlagsV6) : decodeV6 (encodeV6 f) = some f := by
  rcases f with ⟨⟨s, o, c⟩⟩
  cases s <;> cases o <;> cases c <;> decide

/-- **T11 (v5 round-trip).** Every `Flags` value with `enableCrossAddress =
false` round-trips through the v5 codec. (Values with `enableCrossAddress =
true` cannot be encoded by the v5 encoder because the v5 codec doesn't carry
that bit.) -/
theorem v5_roundtrip (f : Flags) (hcross : f.enableCrossAddress = false) :
    decodeV5 (encodeV5 f) = some f := by
  rcases f with ⟨s, o, c⟩
  cases s <;> cases o <;> cases c <;> simp_all <;> decide

/-! ## `FlagsV6` newtype projection -/

/-- **T11b (`From<FlagsV6> for Flags` is the identity on the inner field).**
Mirrors the Rust `impl From<FlagsV6> for Flags { fn from(flags: FlagsV6) ->
Self { flags.0 } }`. -/
theorem flagsV6_toFlags (f : FlagsV6) : FlagsV6.toFlagsImpl f = f.toFlags := rfl

/-! ## Height-gated `v6` validity -/

/-- **T12 (v6 invalid below NU6.3).** A `v6` transaction is invalid at every
height strictly below the (parameterised) NU6.3 activation height. -/
theorem v6_invalid_pre_nu6_3 (hNU6_3 h : Nat) (hh : h < hNU6_3) :
    txVersionValidAtHeight hNU6_3 .v6 h = false := by
  unfold txVersionValidAtHeight
  simp [Nat.not_le.mpr hh]

/-- **T13 (v6 valid at and after NU6.3).** A `v6` transaction is valid at and
after the NU6.3 activation height. -/
theorem v6_valid_post_nu6_3 (hNU6_3 h : Nat) (hh : hNU6_3 ≤ h) :
    txVersionValidAtHeight hNU6_3 .v6 h = true := by
  unfold txVersionValidAtHeight
  simp [hh]

/-- **T14 (non-v6 unconstrained).** Any non-`v6` transaction passes the NU6.3
height gate at every height. -/
theorem non_v6_unconstrained (hNU6_3 : Nat) (v : TxVersion) (h : Nat) (hv : v ≠ .v6) :
    txVersionValidAtHeight hNU6_3 v h = true := by
  cases v <;> first | rfl | (exact absurd rfl hv)

/-- **T15 (NU6.3 boundary).** Whenever `hNU6_3 ≥ 1`, a `v6` transaction is
invalid at `hNU6_3 - 1` and valid at `hNU6_3`. -/
theorem v6_boundary (hNU6_3 : Nat) (hpos : 1 ≤ hNU6_3) :
    txVersionValidAtHeight hNU6_3 .v6 (hNU6_3 - 1) = false ∧
    txVersionValidAtHeight hNU6_3 .v6 hNU6_3 = true := by
  refine ⟨?_, ?_⟩
  · apply v6_invalid_pre_nu6_3
    omega
  · exact v6_valid_post_nu6_3 hNU6_3 hNU6_3 (Nat.le_refl _)

/-! ## Combined: v6-flag byte requires height ≥ NU6.3 -/

/-- **T16 (cross-address byte requires NU6.3).** A `v6` transaction whose
`flagsOrchard` byte has bit 2 set (i.e. `enableCrossAddress`) is only valid at
heights `≥ hNU6_3`. Pre-NU6.3, both the height gate fails *and* (if we tried to
parse the byte as v5) the byte itself is rejected. -/
theorem cross_address_requires_nu6_3
    (hNU6_3 h b : Nat) (hb : b ≤ U8_MAX) (hbit : bit b 2 = 1)
    (hpre : h < hNU6_3) :
    txVersionValidAtHeight hNU6_3 .v6 h = false ∧ decodeV5 b = none := by
  refine ⟨v6_invalid_pre_nu6_3 hNU6_3 h hpre, decodeV5_rejects_bit2 b hb hbit⟩

end Zebra.NU63IronwoodLayout
