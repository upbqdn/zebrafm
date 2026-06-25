import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# NU6.3 / Ironwood v6 Orchard flags layout

Models the NU6.3 / Ironwood v6 transaction format introduced by PR #10762.

Under the pre-NU6.3 (v5 Orchard) codec, the `flagsOrchard` byte has the layout

  * bit 0 (`0b00000001`) = `enableSpendsOrchard`
  * bit 1 (`0b00000010`) = `enableOutputsOrchard`
  * bits 2..7           = reserved, MUST be zero

This is the existing `Flags` `bitflags!` definition at
`zebra-chain/src/orchard/shielded_data.rs:241-265` together with the
consensus-rule citation at `zebra-chain/src/orchard/shielded_data.rs:249-250`:

  > [NU5 onward] In a version 5 transaction, the reserved bits 2..7 of the
  > flagsOrchard field MUST be zero.

The PR #10762 v6 codec (`FlagsV6`) re-allocates bit 2 to a new flag
`enableCrossAddress`:

  * bit 0 = `enableSpendsOrchard`
  * bit 1 = `enableOutputsOrchard`
  * bit 2 = `enableCrossAddress`     (new in NU6.3)
  * bits 3..7 = reserved, MUST be zero

The same wire byte therefore *parses differently* under the two codecs: under
the v5 codec, bit 2 is a reserved bit and any byte with bit 2 set is rejected;
under the v6 codec, bit 2 carries `enableCrossAddress` and is accepted.

v6 transactions are only valid at heights ≥ NU6.3 activation; v5 transactions
parse the `flagsOrchard` byte with the v5 codec at any height.

We prove:

  * the v5 codec rejects every byte with bit 2 set;
  * the v6 codec accepts every byte with bit 2 set and bits 3..7 clear;
  * the v5 and v6 codecs disagree on the example byte `0b00000111` (= 7) and on
    `0b00000100` (= 4);
  * agreement: on bytes with bits 2..7 all zero, the two codecs accept the same
    `enableSpends` / `enableOutputs` values;
  * v6 transactions are only valid at heights ≥ NU6.3 activation; a non-v6
    transaction is unconstrained by that activation gate.
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

/-! ## Bit-mask constants from `zebra-chain/src/orchard/shielded_data.rs:261-263`. -/

/-- `ENABLE_SPENDS = 0b00000001`. Source:
`zebra-chain/src/orchard/shielded_data.rs:261`. -/
def ENABLE_SPENDS : Nat := 0b00000001

/-- `ENABLE_OUTPUTS = 0b00000010`. Source:
`zebra-chain/src/orchard/shielded_data.rs:263`. -/
def ENABLE_OUTPUTS : Nat := 0b00000010

/-- `ENABLE_CROSS_ADDRESS = 0b00000100`. New in PR #10762: bit 2 of `FlagsV6`.
Source: NU6.3 / Ironwood v6 transaction format. -/
def ENABLE_CROSS_ADDRESS : Nat := 0b00000100

/-- The bitmask of v5 valid bits: bits 0 and 1. Bits 2..7 are reserved. -/
def V5_VALID_MASK : Nat := ENABLE_SPENDS + ENABLE_OUTPUTS    -- 0b00000011

/-- The bitmask of v6 valid bits: bits 0, 1, and 2. Bits 3..7 are reserved. -/
def V6_VALID_MASK : Nat := ENABLE_SPENDS + ENABLE_OUTPUTS + ENABLE_CROSS_ADDRESS
                                                              -- 0b00000111

/-! ## NU6.3 activation -/

/-- A placeholder NU6.3 mainnet activation height. The actual height will be
ratified along with the Ironwood deployment; this module only depends on its
existence as a `Nat`. -/
def NU6_3 : Nat := 3_500_000

/-! ## Codec types and `Flags` structures -/

/-- The decoded v5 Orchard `Flags` value. Mirrors the `bitflags!` definition at
`zebra-chain/src/orchard/shielded_data.rs:257-264`. -/
structure FlagsV5 where
  enableSpends : Bool
  enableOutputs : Bool
  deriving DecidableEq, Repr

/-- The decoded v6 Orchard `FlagsV6` value introduced by PR #10762: bit 2 is
`enableCrossAddress`. -/
structure FlagsV6 where
  enableSpends : Bool
  enableOutputs : Bool
  enableCrossAddress : Bool
  deriving DecidableEq, Repr

/-! ## V5 codec -/

/-- The v5 Orchard flags decoder. Models `ZcashDeserialize for Flags` at
`zebra-chain/src/orchard/shielded_data.rs:297-305`: rejects any byte whose
reserved bits 2..7 are set. -/
def decodeV5 (b : Nat) : Option FlagsV5 :=
  if b ≤ 0b00000011 then
    some { enableSpends  := bit b 0 = 1
           enableOutputs := bit b 1 = 1 }
  else none

/-- The v5 Orchard flags encoder. Models `ZcashSerialize for Flags` at
`zebra-chain/src/orchard/shielded_data.rs:289-294`: combines the two bits into
a single `u8`. -/
def encodeV5 (f : FlagsV5) : Nat :=
  (if f.enableSpends then ENABLE_SPENDS else 0) +
  (if f.enableOutputs then ENABLE_OUTPUTS else 0)

/-! ## V6 codec -/

/-- The v6 (NU6.3 / Ironwood) Orchard flags decoder. Bits 0..2 are valid;
bits 3..7 are reserved and MUST be zero. Source: PR #10762 introduces
`FlagsV6`. -/
def decodeV6 (b : Nat) : Option FlagsV6 :=
  if b ≤ 0b00000111 then
    some { enableSpends       := bit b 0 = 1
           enableOutputs      := bit b 1 = 1
           enableCrossAddress := bit b 2 = 1 }
  else none

/-- The v6 Orchard flags encoder. -/
def encodeV6 (f : FlagsV6) : Nat :=
  (if f.enableSpends       then ENABLE_SPENDS else 0) +
  (if f.enableOutputs      then ENABLE_OUTPUTS else 0) +
  (if f.enableCrossAddress then ENABLE_CROSS_ADDRESS else 0)

/-! ## Transaction validity gate (NU6.3 activation) -/

/-- The transaction version. Pre-NU6.3 nodes accept `v1`..`v5`; NU6.3 nodes
also accept `v6`. -/
inductive TxVersion
  | v1 | v2 | v3 | v4 | v5 | v6
  deriving DecidableEq, Repr

/-- Models the height-gated rule from PR #10762: a `v6` transaction is only
valid at heights `≥ NU6_3`; all other versions are unconstrained by this
gate (they have their own consensus-rule height gates elsewhere). -/
def txVersionValidAtHeight (v : TxVersion) (h : Nat) : Bool :=
  match v with
  | .v6 => h ≥ NU6_3
  | _   => true

/-! ## Theorems -/

/-- **T1 (v5 rejects bit-2-set bytes).** Any byte whose bit 2 is set (and which
is a `u8`) is rejected by the v5 codec. This is the pre-NU6.3 reserved-bit
rule: bit 2 of `flagsOrchard` must be 0 in a v5 transaction. -/
theorem decodeV5_rejects_bit2 (b : Nat) (_hb : b ≤ U8_MAX) (hbit : bit b 2 = 1) :
    decodeV5 b = none := by
  unfold decodeV5
  -- bit b 2 = 1 means (b / 4) % 2 = 1, so b ≥ 4 > 0b00000011.
  have : ¬ b ≤ 0b00000011 := by
    intro hle
    -- if b ≤ 3 then b / 4 = 0 so (b / 4) % 2 = 0, contradicting hbit
    unfold bit at hbit
    have : b / 4 = 0 := by omega
    omega
  simp [this]

/-- **T2 (v6 accepts bit-2-set bytes when bits 3..7 clear).** Any byte at or
below `0b00000111` is accepted by the v6 codec. In particular, every byte with
bit 2 set and bits 3..7 clear succeeds. -/
theorem decodeV6_accepts_low_byte (b : Nat) (hb : b ≤ 0b00000111) :
    decodeV6 b = some
      { enableSpends := bit b 0 = 1
        enableOutputs := bit b 1 = 1
        enableCrossAddress := bit b 2 = 1 } := by
  unfold decodeV6
  simp [hb]

/-- **T3 (v6 accepts the canonical "all three flags" byte `0b00000111`).** The
NU6.3 wire byte `0b00000111 = 7` decodes under `FlagsV6` to "all three flags
set". -/
theorem decodeV6_seven :
    decodeV6 0b00000111 = some
      { enableSpends := true
        enableOutputs := true
        enableCrossAddress := true } := by
  decide

/-- **T4 (v5 rejects `0b00000111`).** The same byte that the v6 codec accepts
is rejected outright by the v5 codec — bit 2 is reserved. -/
theorem decodeV5_seven : decodeV5 0b00000111 = none := by
  decide

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
      { enableSpends := false
        enableOutputs := false
        enableCrossAddress := true } := by
  decide

/-! ## Codec agreement on the v5-valid sub-range -/

/-- **T8 (v5 / v6 agree on `enableSpends` / `enableOutputs` for v5-valid
bytes).** On every byte that is valid under both codecs (i.e. bits 2..7 clear),
the two decoders produce the same values for `enableSpends` and
`enableOutputs`. This is the wire-compatibility statement: a v6 node parsing a
v5 byte sees the same spend/output flags. -/
theorem decodeV6_agrees_on_v5_range (b : Nat) (hb : b ≤ V5_VALID_MASK) :
    ∃ fv5 fv6, decodeV5 b = some fv5 ∧ decodeV6 b = some fv6 ∧
      fv5.enableSpends  = fv6.enableSpends ∧
      fv5.enableOutputs = fv6.enableOutputs := by
  unfold V5_VALID_MASK ENABLE_SPENDS ENABLE_OUTPUTS at hb
  -- 0b00000011 = 3
  refine
    ⟨{ enableSpends := bit b 0 = 1
       enableOutputs := bit b 1 = 1 },
     { enableSpends := bit b 0 = 1
       enableOutputs := bit b 1 = 1
       enableCrossAddress := bit b 2 = 1 },
     ?_, ?_, rfl, rfl⟩
  · unfold decodeV5
    have hb' : b ≤ 0b00000011 := hb
    simp [hb']
  · unfold decodeV6
    have hb' : b ≤ 0b00000111 := by omega
    simp [hb']

/-- **T9 (v6 cross-address bit isolated by v5-valid range).** On every byte
that is valid under the v5 codec (bits 2..7 clear), the v6 decoder reports
`enableCrossAddress = false`. So a v5 byte never accidentally sets the
cross-address flag when re-parsed as v6. -/
theorem decodeV6_no_cross_on_v5_range (b : Nat) (hb : b ≤ V5_VALID_MASK) :
    ∃ fv6, decodeV6 b = some fv6 ∧ fv6.enableCrossAddress = false := by
  unfold V5_VALID_MASK ENABLE_SPENDS ENABLE_OUTPUTS at hb
  have hb' : b ≤ 0b00000111 := by omega
  refine ⟨_, decodeV6_accepts_low_byte b hb', ?_⟩
  -- bit b 2 = 0 when b ≤ 3 since b / 4 = 0
  unfold bit
  have : b / 4 = 0 := by omega
  simp [this]

/-! ## V6 codec encode / decode round-trip -/

/-- **T10 (v6 round-trip).** The v6 encoder is a left-inverse of the v6
decoder on every value produced by the encoder; equivalently, every `FlagsV6`
struct encodes to a byte that the decoder maps back to itself. -/
theorem v6_roundtrip (f : FlagsV6) : decodeV6 (encodeV6 f) = some f := by
  rcases f with ⟨s, o, c⟩
  cases s <;> cases o <;> cases c <;> decide

/-- **T11 (v5 round-trip).** The v5 encoder is a left-inverse of the v5
decoder. -/
theorem v5_roundtrip (f : FlagsV5) : decodeV5 (encodeV5 f) = some f := by
  rcases f with ⟨s, o⟩
  cases s <;> cases o <;> decide

/-! ## Height-gated `v6` validity -/

/-- **T12 (v6 invalid below NU6.3).** A `v6` transaction is invalid at every
height strictly below NU6.3 activation. -/
theorem v6_invalid_pre_nu6_3 (h : Nat) (hh : h < NU6_3) :
    txVersionValidAtHeight .v6 h = false := by
  unfold txVersionValidAtHeight
  simp [Nat.not_le.mpr hh]

/-- **T13 (v6 valid at and after NU6.3).** A `v6` transaction is valid at
NU6.3 activation and at every height after it. -/
theorem v6_valid_post_nu6_3 (h : Nat) (hh : NU6_3 ≤ h) :
    txVersionValidAtHeight .v6 h = true := by
  unfold txVersionValidAtHeight
  simp [hh]

/-- **T14 (non-v6 unconstrained).** Any non-`v6` transaction passes the NU6.3
height gate at every height (other consensus rules gate `v5`, `v4`, etc.). -/
theorem non_v6_unconstrained (v : TxVersion) (h : Nat) (hv : v ≠ .v6) :
    txVersionValidAtHeight v h = true := by
  cases v <;> first | rfl | (exact absurd rfl hv)

/-- **T15 (NU6.3 boundary).** A `v6` transaction is invalid at `NU6_3 - 1`
and valid at `NU6_3`. -/
theorem v6_boundary :
    txVersionValidAtHeight .v6 (NU6_3 - 1) = false ∧
    txVersionValidAtHeight .v6 NU6_3 = true := by
  refine ⟨?_, ?_⟩
  · apply v6_invalid_pre_nu6_3
    unfold NU6_3
    decide
  · exact v6_valid_post_nu6_3 NU6_3 (Nat.le_refl _)

/-! ## Combined: v6-flag byte requires height ≥ NU6.3 -/

/-- **T16 (cross-address byte requires NU6.3).** A `v6` transaction whose
`flagsOrchard` byte has bit 2 set (i.e. `enableCrossAddress`) is only valid at
heights `≥ NU6_3`. Pre-NU6.3, both the height gate fails *and* (if we tried to
parse the byte as v5) the byte itself is rejected. So at any height
`h < NU6_3`:

  * the v6 height-gate says the tx is invalid; and
  * the v5 codec rejects the byte outright.

Both prongs cannot be satisfied below NU6.3. -/
theorem cross_address_requires_nu6_3
    (h : Nat) (b : Nat) (hb : b ≤ U8_MAX) (hbit : bit b 2 = 1)
    (hpre : h < NU6_3) :
    txVersionValidAtHeight .v6 h = false ∧ decodeV5 b = none := by
  refine ⟨v6_invalid_pre_nu6_3 h hpre, decodeV5_rejects_bit2 b hb hbit⟩

end Zebra.NU63IronwoodLayout
