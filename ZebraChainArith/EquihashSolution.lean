import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import ZebraChainArith.CompactSize

/-!
# Equihash solution serialisation from `zebra-chain/src/work/equihash.rs`

The Zcash mainnet/testnet Equihash `Solution` is a fixed `[u8; 1344]` byte
array. Its wire format is a `CompactSize` length prefix followed by the raw
solution bytes. Because the length is always `1344 = 0x540`, the prefix is
always the three-byte band-2 encoding `[0xfd, 0x40, 0x05]`.

  * `0xfd`  — band-2 tag (length is in `[0xfd, 0xffff]`)
  * `0x40`  — `1344 % 256 = 64`
  * `0x05`  — `1344 / 256 = 5`

The total encoded size is therefore `3 + 1344 = 1347` bytes.

We model:
  * `Solution` as a `List Nat` of length 1344 (each byte modelled as a `Nat`),
  * `encode` as `[0xfd, 0x40, 0x05] ++ bytes`,
  * `decode` as a parser that strips the CompactSize prefix (re-using
    `Zebra.CompactSize.decode`), validates the length, then peels off
    1344 raw bytes.

We prove:
  * the prefix is canonical (band 2 with the documented `(lo, hi)`),
  * decoding the encoded prefix yields `1344`,
  * `decode (encode s) = some s` for every well-formed `s`,
  * the encoded length is exactly 1347 (`3 + 1344`).
-/

namespace Zebra.EquihashSolution

/-- The Equihash solution size in bytes (Mainnet and Testnet).
Source: `zebra-chain/src/work/equihash.rs:31`
(`pub(crate) const SOLUTION_SIZE: usize = 1344`) -/
def SOLUTION_SIZE : Nat := 1344

/-- The Regtest Equihash solution size.
Source: `zebra-chain/src/work/equihash.rs:34`
(`pub(crate) const REGTEST_SOLUTION_SIZE: usize = 36`) -/
def REGTEST_SOLUTION_SIZE : Nat := 36

/-- A Mainnet/Testnet Equihash solution: a fixed-length byte vector.
Source: `zebra-chain/src/work/equihash.rs:47` (`pub enum Solution`,
variant `Common(#[serde(with = "BigArray")] [u8; SOLUTION_SIZE])`) -/
structure Solution where
  bytes : List Nat

/-- A solution is well-formed iff it has the canonical Mainnet/Testnet length.
Source: `zebra-chain/src/work/equihash.rs:96` (`fn from_bytes` — the
`SOLUTION_SIZE` branch). -/
def WellFormed (s : Solution) : Prop := s.bytes.length = SOLUTION_SIZE

/-! ## CompactSize prefix bytes for `1344` -/

/-- The canonical CompactSize band-2 prefix tag: `0xfd`. -/
def PREFIX_TAG : Nat := 0xfd

/-- The low byte of `1344` in little-endian: `1344 % 256 = 64 = 0x40`. -/
def PREFIX_LO : Nat := 0x40

/-- The high byte of `1344` in little-endian: `1344 / 256 = 5 = 0x05`. -/
def PREFIX_HI : Nat := 0x05

/-- The full canonical three-byte CompactSize prefix for a 1344-byte payload. -/
def prefixBytes : List Nat := [PREFIX_TAG, PREFIX_LO, PREFIX_HI]

/-! ## Encoder and decoder -/

/-- `Solution::zcash_serialize`: writes the CompactSize length prefix followed by
the raw solution bytes.
Source: `zebra-chain/src/work/equihash.rs:257`
(`impl ZcashSerialize for Solution`, calls `zcash_serialize_bytes`, which
emits a CompactSize length followed by the bytes themselves). -/
def encode (s : Solution) : List Nat :=
  Zebra.CompactSize.encode s.bytes.length ++ s.bytes

/-- `Solution::zcash_deserialize`: reads a CompactSize length, rejects anything
larger than `SOLUTION_SIZE`, then peels off that many raw bytes and packages
them.
Source: `zebra-chain/src/work/equihash.rs:263`
(`impl ZcashDeserialize for Solution`). -/
def decode (bytes : List Nat) : Option (Solution × List Nat) :=
  match Zebra.CompactSize.decode bytes with
  | none => none
  | some (len, rest) =>
    if len > SOLUTION_SIZE then
      none
    else if rest.length < len then
      none
    else
      some (⟨rest.take len⟩, rest.drop len)

/-! ## Theorems -/

/-- **T1.** `1344` is in the CompactSize band-2 range `[0xfd, 0xffff]`. -/
theorem solution_size_in_band2 :
    0xfd ≤ SOLUTION_SIZE ∧ SOLUTION_SIZE ≤ 0xffff := by
  unfold SOLUTION_SIZE; omega

/-- **T2.** The CompactSize encoder produces exactly the canonical prefix
`[0xfd, 0x40, 0x05]` for the value `1344`. -/
theorem encode_size_is_prefix :
    Zebra.CompactSize.encode SOLUTION_SIZE = prefixBytes := by
  unfold Zebra.CompactSize.encode SOLUTION_SIZE prefixBytes PREFIX_TAG PREFIX_LO PREFIX_HI
  decide

/-- **T3.** The decoder accepts the canonical prefix and yields `1344` plus
whatever follows. -/
theorem decode_prefix (rest : List Nat) :
    Zebra.CompactSize.decode (prefixBytes ++ rest) = some (SOLUTION_SIZE, rest) := by
  unfold prefixBytes PREFIX_TAG PREFIX_LO PREFIX_HI SOLUTION_SIZE
  rfl

/-- **T4.** The total encoded length of a well-formed solution is `3 + 1344 = 1347`
bytes (3 for the CompactSize prefix, 1344 for the payload). -/
theorem encode_length (s : Solution) (hw : WellFormed s) :
    (encode s).length = 3 + SOLUTION_SIZE := by
  unfold encode
  rw [List.length_append, hw, encode_size_is_prefix]
  unfold prefixBytes
  simp

/-- **T5.** The encoder's first three bytes are exactly the canonical prefix
for any well-formed solution. -/
theorem encode_prefix (s : Solution) (hw : WellFormed s) :
    (encode s).take 3 = prefixBytes := by
  unfold encode
  rw [hw, encode_size_is_prefix]
  unfold prefixBytes
  rfl

/-- A helper: `List.take n (l₁ ++ l₂) = l₁` when `l₁.length = n`. -/
private theorem take_length_append (l₁ l₂ : List Nat) :
    (l₁ ++ l₂).take l₁.length = l₁ := by
  induction l₁ with
  | nil => simp
  | cons a as ih => simp [ih]

/-- A helper: `List.drop n (l₁ ++ l₂) = l₂` when `l₁.length = n`. -/
private theorem drop_length_append (l₁ l₂ : List Nat) :
    (l₁ ++ l₂).drop l₁.length = l₂ := by
  induction l₁ with
  | nil => simp
  | cons a as ih => simp [ih]

/-- **T6.** Round-trip: encoding a well-formed solution and then decoding
recovers the original solution, with no leftover bytes. -/
theorem roundtrip (s : Solution) (hw : WellFormed s) :
    decode (encode s) = some (s, []) := by
  unfold encode decode
  rw [hw, encode_size_is_prefix]
  -- The prefix-decode step yields `(SOLUTION_SIZE, s.bytes)`.
  have hp : Zebra.CompactSize.decode (prefixBytes ++ s.bytes)
              = some (SOLUTION_SIZE, s.bytes) := decode_prefix s.bytes
  rw [hp]
  have hlen_le : ¬ SOLUTION_SIZE > SOLUTION_SIZE := by omega
  have hbytes_len : ¬ s.bytes.length < SOLUTION_SIZE := by
    rw [hw]; omega
  simp only [hlen_le, hbytes_len, if_false]
  -- Now we must show `(⟨s.bytes.take SOLUTION_SIZE⟩, s.bytes.drop SOLUTION_SIZE) = (s, [])`.
  have htake : s.bytes.take SOLUTION_SIZE = s.bytes := by
    rw [← hw]; exact List.take_length
  have hdrop : s.bytes.drop SOLUTION_SIZE = [] := by
    rw [← hw]; exact List.drop_length
  rw [htake, hdrop]

/-- **T7.** The decoder rejects oversize CompactSize values: even if the bytes
are otherwise present, any decoded length above `SOLUTION_SIZE` yields `none`.
This is the explicit guard against unbounded-allocation DoS the Rust source
comments warn about. -/
theorem decode_rejects_oversize
    (bytes : List Nat) (len : Nat) (rest : List Nat)
    (hcs : Zebra.CompactSize.decode bytes = some (len, rest))
    (hover : len > SOLUTION_SIZE) :
    decode bytes = none := by
  unfold decode
  rw [hcs]
  simp [hover]

/-- **T8.** Encoder produces a non-empty list. (The CompactSize prefix is
always at least one byte, even before the payload.) -/
theorem encode_nonempty (s : Solution) (hw : WellFormed s) : encode s ≠ [] := by
  intro heq
  have hlen : (encode s).length = 0 := by rw [heq]; rfl
  rw [encode_length s hw] at hlen
  unfold SOLUTION_SIZE at hlen
  omega

/-- **T9.** Concrete shape of the encoded form: it begins with `0xfd, 0x40, 0x05`
followed by the 1344 payload bytes. -/
theorem encode_shape (s : Solution) (hw : WellFormed s) :
    encode s = PREFIX_TAG :: PREFIX_LO :: PREFIX_HI :: s.bytes := by
  unfold encode
  rw [hw, encode_size_is_prefix]
  unfold prefixBytes
  rfl

/-- **T10.** A trivial sanity check: `prefixBytes` has exactly three bytes. -/
theorem prefixBytes_length : prefixBytes.length = 3 := by
  unfold prefixBytes; rfl

/-- **T11.** The `(lo, hi)` pair canonically decodes to `1344` under the
little-endian 2-byte interpretation. -/
theorem prefix_payload_decodes :
    Zebra.CompactSize.fromLE2 PREFIX_LO PREFIX_HI = SOLUTION_SIZE := by
  unfold Zebra.CompactSize.fromLE2 PREFIX_LO PREFIX_HI SOLUTION_SIZE
  decide

end Zebra.EquihashSolution
