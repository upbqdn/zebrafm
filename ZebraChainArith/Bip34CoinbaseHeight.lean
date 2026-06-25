import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# BIP-34 coinbase height encoding from `zebra-chain/src/transparent/serialize.rs`

The first item of a non-genesis coinbase `scriptSig` MUST encode the block
height as follows:

  * For `h ∈ {1..16}`: a single byte `0x50 + h` (the OP_1..OP_16 opcodes).
  * Otherwise: let `heightBytes` be the signed little-endian representation of
    `h`, using the minimum nonzero number of bytes such that the most
    significant byte is `< 0x80`. The encoding is `[N, b₀, b₁, ..., b_{N-1}]`
    where `N = heightBytes.length`, with `N ∈ {1..5}`.

Since `Height::MAX = 2^31 − 1`, valid block heights all fit into 4 bytes of
signed little-endian (the 5-byte case is never reached for valid heights). We
model the script bytes as `List Nat` (with each byte implicitly `< 256`) and
the height as `Nat`.

Source: `zebra-chain/src/transparent/serialize.rs:58` (`parse_coinbase_height`).
-/

namespace Zebra.Bip34CoinbaseHeight

/-- The maximum block height: `Height::MAX = u32::MAX / 2 = 2^31 − 1`.
Source: `zebra-chain/src/block/height.rs:67` -/
def MAX_HEIGHT : Nat := 2_147_483_647

/-- The upper bound of the OP_N band: 16. Heights at or above 17 cannot be
encoded with the OP_N opcodes. -/
def OP_N_MAX : Nat := 16

/-- The upper bound of the 1-byte signed LE band: `2^7 − 1 = 127`. -/
def ONE_BYTE_MAX : Nat := 127

/-- The upper bound of the 2-byte signed LE band: `2^15 − 1 = 32_767`. -/
def TWO_BYTE_MAX : Nat := 32_767

/-- The upper bound of the 3-byte signed LE band: `2^23 − 1 = 8_388_607`. -/
def THREE_BYTE_MAX : Nat := 8_388_607

/-- The upper bound of the 4-byte signed LE band: `2^31 − 1 = MAX_HEIGHT`. -/
def FOUR_BYTE_MAX : Nat := 2_147_483_647

/-! ## Encoder -/

/-- Encode a block height `h` (assumed `1 ≤ h ≤ MAX_HEIGHT`) as the BIP-34
coinbase-height script prefix, returning the canonical byte list.
Source: `zebra-chain/src/transparent/serialize.rs:81`
(re-encode via `pattern::push_num`). -/
def encode (h : Nat) : List Nat :=
  if h ≤ OP_N_MAX then
    [0x50 + h]
  else if h ≤ ONE_BYTE_MAX then
    [1, h]
  else if h ≤ TWO_BYTE_MAX then
    [2, h % 256, (h / 256) % 256]
  else if h ≤ THREE_BYTE_MAX then
    [3, h % 256, (h / 256) % 256, (h / 65536) % 256]
  else
    [4, h % 256, (h / 256) % 256, (h / 65536) % 256, (h / 16777216) % 256]

/-- The length of the canonical encoding of `h`. -/
def encodeLen (h : Nat) : Nat :=
  if h ≤ OP_N_MAX then 1
  else if h ≤ ONE_BYTE_MAX then 2
  else if h ≤ TWO_BYTE_MAX then 3
  else if h ≤ THREE_BYTE_MAX then 4
  else 5

/-! ## Decoder

Mirror of `parse_coinbase_height`: read the prefix byte, locate the height
bytes, decode them as little-endian, then canonicity-check via re-encoding. -/

/-- Decode a coinbase-height-prefixed script. Returns `Some (height, rest)`
when the prefix is the canonical BIP-34 encoding of a valid height, else
`None`. -/
def decode (bytes : List Nat) : Option (Nat × List Nat) :=
  match bytes with
  | [] => none
  | b :: rest =>
    -- OP_1 .. OP_16: single byte 0x51..0x60
    if 0x51 ≤ b ∧ b ≤ 0x60 then
      some (b - 0x50, rest)
    -- Length-prefixed: byte is N ∈ {1..5}
    else if b = 1 then
      match rest with
      | [] => none
      | b0 :: rest' =>
        if 17 ≤ b0 ∧ b0 ≤ 127 then some (b0, rest') else none
    else if b = 2 then
      match rest with
      | b0 :: b1 :: rest' =>
        let h := b0 + b1 * 256
        if 127 < h ∧ h ≤ 32767 then some (h, rest') else none
      | _ => none
    else if b = 3 then
      match rest with
      | b0 :: b1 :: b2 :: rest' =>
        let h := b0 + b1 * 256 + b2 * 65536
        if 32767 < h ∧ h ≤ 8388607 then some (h, rest') else none
      | _ => none
    else if b = 4 then
      match rest with
      | b0 :: b1 :: b2 :: b3 :: rest' =>
        let h := b0 + b1 * 256 + b2 * 65536 + b3 * 16777216
        if 8388607 < h ∧ h ≤ 2147483647 then some (h, rest') else none
      | _ => none
    else
      none

/-! ## Theorems -/

/-- **T1.** Encoder length matches `encodeLen` exactly. -/
theorem encode_length (h : Nat) : (encode h).length = encodeLen h := by
  unfold encode encodeLen
  split_ifs <;> rfl

/-- **T2.** Encoded length is in `{1..5}` for any height. -/
theorem encode_length_bounds (h : Nat) :
    1 ≤ (encode h).length ∧ (encode h).length ≤ 5 := by
  rw [encode_length]
  unfold encodeLen
  split_ifs <;> exact ⟨by omega, by omega⟩

/-- **T3.** Round-trip on the OP_N band `1 ≤ h ≤ 16`. -/
theorem roundtrip_op_n (h : Nat) (h1 : 1 ≤ h) (h2 : h ≤ 16) (rest : List Nat) :
    decode (encode h ++ rest) = some (h, rest) := by
  have henc : encode h = [0x50 + h] := by
    unfold encode OP_N_MAX
    simp [h2]
  rw [henc]
  show decode ((0x50 + h) :: rest) = some (h, rest)
  unfold decode
  have hb1 : 0x51 ≤ 0x50 + h := by omega
  have hb2 : 0x50 + h ≤ 0x60 := by omega
  have heq : (0x50 + h) - 0x50 = h := by omega
  simp [hb1, hb2, heq]

/-- **T4.** Round-trip on the 1-byte length-prefixed band `17 ≤ h ≤ 127`. -/
theorem roundtrip_one_byte (h : Nat) (h1 : 17 ≤ h) (h2 : h ≤ 127)
    (rest : List Nat) :
    decode (encode h ++ rest) = some (h, rest) := by
  have henc : encode h = [1, h] := by
    unfold encode OP_N_MAX ONE_BYTE_MAX
    have : ¬ h ≤ 16 := by omega
    simp [this, h2]
  rw [henc]
  show decode (1 :: h :: rest) = some (h, rest)
  unfold decode
  have hb_op_lo : ¬ (0x51 : Nat) ≤ 1 := by decide
  simp [hb_op_lo, h1, h2]

/-- **T5.** Round-trip on the 2-byte length-prefixed band `128 ≤ h ≤ 32_767`. -/
theorem roundtrip_two_byte (h : Nat) (h1 : 128 ≤ h) (h2 : h ≤ 32767)
    (rest : List Nat) :
    decode (encode h ++ rest) = some (h, rest) := by
  have henc : encode h = [2, h % 256, (h / 256) % 256] := by
    unfold encode OP_N_MAX ONE_BYTE_MAX TWO_BYTE_MAX
    have h16 : ¬ h ≤ 16 := by omega
    have h127 : ¬ h ≤ 127 := by omega
    simp [h16, h127, h2]
  rw [henc]
  show decode (2 :: (h % 256) :: ((h / 256) % 256) :: rest) = some (h, rest)
  unfold decode
  have hb_op_lo : ¬ ((0x51 : Nat) ≤ 2 ∧ (2 : Nat) ≤ 0x60) := by
    intro ⟨ha, _⟩; exact absurd ha (by decide)
  have hne1 : (2 : Nat) ≠ 1 := by decide
  have hmod : (h / 256) % 256 = h / 256 := by
    apply Nat.mod_eq_of_lt; omega
  have hrec : h % 256 + (h / 256) % 256 * 256 = h := by
    rw [hmod]; omega
  have hlo : 127 < h := by omega
  simp [hb_op_lo, hne1, hrec, hlo, h2]

/-- **T6.** Round-trip on the 3-byte length-prefixed band. -/
theorem roundtrip_three_byte (h : Nat) (h1 : 32768 ≤ h) (h2 : h ≤ 8388607)
    (rest : List Nat) :
    decode (encode h ++ rest) = some (h, rest) := by
  have henc : encode h = [3, h % 256, (h / 256) % 256, (h / 65536) % 256] := by
    unfold encode OP_N_MAX ONE_BYTE_MAX TWO_BYTE_MAX THREE_BYTE_MAX
    have h16 : ¬ h ≤ 16 := by omega
    have h127 : ¬ h ≤ 127 := by omega
    have h32k : ¬ h ≤ 32767 := by omega
    simp [h16, h127, h32k, h2]
  rw [henc]
  show decode (3 :: (h % 256) :: ((h / 256) % 256) :: ((h / 65536) % 256) :: rest)
       = some (h, rest)
  unfold decode
  have hb_op_lo : ¬ ((0x51 : Nat) ≤ 3 ∧ (3 : Nat) ≤ 0x60) := by
    intro ⟨ha, _⟩; exact absurd ha (by decide)
  have hne1 : (3 : Nat) ≠ 1 := by decide
  have hne2 : (3 : Nat) ≠ 2 := by decide
  have hmod : (h / 65536) % 256 = h / 65536 := by
    apply Nat.mod_eq_of_lt; omega
  have hrec :
      h % 256 + (h / 256) % 256 * 256 + (h / 65536) % 256 * 65536 = h := by
    rw [hmod]; omega
  have hlo : 32767 < h := by omega
  simp [hb_op_lo, hne1, hne2, hrec, hlo, h2]

/-- **T7.** Round-trip on the 4-byte length-prefixed band. -/
theorem roundtrip_four_byte (h : Nat) (h1 : 8388608 ≤ h) (h2 : h ≤ MAX_HEIGHT)
    (rest : List Nat) :
    decode (encode h ++ rest) = some (h, rest) := by
  have h2' : h ≤ 2147483647 := by unfold MAX_HEIGHT at h2; exact h2
  have henc : encode h =
      [4, h % 256, (h / 256) % 256, (h / 65536) % 256, (h / 16777216) % 256] := by
    unfold encode OP_N_MAX ONE_BYTE_MAX TWO_BYTE_MAX THREE_BYTE_MAX
    have h16 : ¬ h ≤ 16 := by omega
    have h127 : ¬ h ≤ 127 := by omega
    have h32k : ¬ h ≤ 32767 := by omega
    have h8m : ¬ h ≤ 8388607 := by omega
    simp [h16, h127, h32k, h8m]
  rw [henc]
  show decode (4 :: (h % 256) :: ((h / 256) % 256) :: ((h / 65536) % 256)
              :: ((h / 16777216) % 256) :: rest) = some (h, rest)
  unfold decode
  have hb_op_lo : ¬ ((0x51 : Nat) ≤ 4 ∧ (4 : Nat) ≤ 0x60) := by
    intro ⟨ha, _⟩; exact absurd ha (by decide)
  have hne1 : (4 : Nat) ≠ 1 := by decide
  have hne2 : (4 : Nat) ≠ 2 := by decide
  have hne3 : (4 : Nat) ≠ 3 := by decide
  have hmod : (h / 16777216) % 256 = h / 16777216 := by
    apply Nat.mod_eq_of_lt; omega
  have hrec :
      h % 256 + (h / 256) % 256 * 256 + (h / 65536) % 256 * 65536
        + (h / 16777216) % 256 * 16777216 = h := by
    rw [hmod]; omega
  have hlo : 8388607 < h := by omega
  simp [hb_op_lo, hne1, hne2, hne3, hrec, hlo, h2']

/-- **T8.** Encoder produces a single byte exactly in the OP_N band. -/
theorem encode_length_op_n (h : Nat) (h2 : h ≤ 16) :
    (encode h).length = 1 := by
  rw [encode_length]
  unfold encodeLen OP_N_MAX
  simp [h2]

/-- **T9.** Encoder produces a length-2 prefix for `17 ≤ h ≤ 127`. -/
theorem encode_length_one_byte (h : Nat) (h1 : 17 ≤ h) (h2 : h ≤ ONE_BYTE_MAX) :
    (encode h).length = 2 := by
  rw [encode_length]
  unfold encodeLen OP_N_MAX
  have : ¬ h ≤ 16 := by omega
  simp [this, h2]

/-- **T10.** Decoder rejects empty input. -/
theorem decode_empty : decode [] = none := rfl

/-- **T11.** Decoder rejects a stray `0x50` (OP_0): not a valid OP_N nor a
length prefix in `{1..5}`. -/
theorem decode_op_0 (rest : List Nat) : decode (0x50 :: rest) = none := by
  unfold decode
  have h1 : ¬ ((0x51 : Nat) ≤ 0x50 ∧ (0x50 : Nat) ≤ 0x60) := by
    intro ⟨ha, _⟩; exact absurd ha (by decide)
  have hne1 : (0x50 : Nat) ≠ 1 := by decide
  have hne2 : (0x50 : Nat) ≠ 2 := by decide
  have hne3 : (0x50 : Nat) ≠ 3 := by decide
  have hne4 : (0x50 : Nat) ≠ 4 := by decide
  simp [h1, hne1, hne2, hne3, hne4]

/-- **T12.** Decoder rejects a length-1 push with sub-OP_N value (non-canonical:
should have been OP_N). E.g. `[1, 5]` could canonically be `0x55`. -/
theorem decode_one_byte_noncanonical (b : Nat) (hb : b ≤ 16) (rest : List Nat) :
    decode (1 :: b :: rest) = none := by
  unfold decode
  have h1 : ¬ ((0x51 : Nat) ≤ 1 ∧ (1 : Nat) ≤ 0x60) := by
    intro ⟨ha, _⟩; exact absurd ha (by decide)
  have hnot17 : ¬ 17 ≤ b := by omega
  simp [h1, hnot17]

/-- **T13.** Decoder rejects unknown prefix bytes (anything outside `{1..4} ∪
{0x51..0x60}`). -/
theorem decode_unknown_prefix (b : Nat) (h5 : 5 ≤ b) (h50 : b < 0x51)
    (rest : List Nat) :
    decode (b :: rest) = none := by
  unfold decode
  have h1 : ¬ ((0x51 : Nat) ≤ b ∧ b ≤ 0x60) := by
    intro ⟨ha, _⟩; omega
  have hne1 : b ≠ 1 := by omega
  have hne2 : b ≠ 2 := by omega
  have hne3 : b ≠ 3 := by omega
  have hne4 : b ≠ 4 := by omega
  simp [h1, hne1, hne2, hne3, hne4]

end Zebra.Bip34CoinbaseHeight
