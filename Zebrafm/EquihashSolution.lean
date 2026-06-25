import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Zebrafm.CompactSize

/-!
# Equihash solution serialisation from `zebra-chain/src/work/equihash.rs`

The Zcash Equihash `Solution` is a fixed-length byte array. There are two
canonical sizes:

  * `SOLUTION_SIZE = 1344` bytes on Mainnet and Testnet;
  * `REGTEST_SOLUTION_SIZE = 36` bytes on Regtest.

The Rust type is a two-variant enum (`Solution::Common` and `Solution::Regtest`)
discriminated by the byte length:

```rust
pub enum Solution {
    Common(#[serde(with = "BigArray")] [u8; SOLUTION_SIZE]),
    Regtest(#[serde(with = "BigArray")] [u8; REGTEST_SOLUTION_SIZE]),
}
```

The wire format is a `CompactSize` length prefix followed by the raw solution
bytes, and `Solution::from_bytes` rejects any input whose length is not
exactly one of the two canonical sizes.

For the Mainnet/Testnet length of 1344, the CompactSize prefix is always the
three-byte band-2 encoding `[0xfd, 0x40, 0x05]`:

  * `0xfd`  — band-2 tag (length is in `[0xfd, 0xffff]`)
  * `0x40`  — `1344 % 256 = 64`
  * `0x05`  — `1344 / 256 = 5`

For the Regtest length of 36, the CompactSize prefix is the single-byte
band-1 encoding `[0x24]` (since `36 ≤ 0xfc`).

The total encoded sizes are therefore `3 + 1344 = 1347` and `1 + 36 = 37`
bytes respectively.

We model:
  * `Solution` as a sum of `Common` and `Regtest`, each carrying its byte list;
  * `encode` as the CompactSize length prefix followed by the raw bytes;
  * `decode` as a parser that strips the CompactSize prefix, requires the
    length to be exactly `SOLUTION_SIZE` or `REGTEST_SOLUTION_SIZE`, then
    peels off that many raw bytes.

We prove:
  * the canonical prefixes are correct for both lengths,
  * `decode (encode s) = some s` for every well-formed `s` of either variant,
  * the encoded lengths are exactly `3 + 1344 = 1347` and `1 + 36 = 37`,
  * the decoder rejects every CompactSize length other than 1344 and 36
    (this is the explicit DoS-allocation guard in the Rust source).
-/

namespace Zebra.EquihashSolution

/-- The Equihash solution size in bytes (Mainnet and Testnet).
Source: `zebra-chain/src/work/equihash.rs:31`
(`pub(crate) const SOLUTION_SIZE: usize = 1344`) -/
def SOLUTION_SIZE : Nat := 1344

/-- The Regtest Equihash solution size in bytes.
Source: `zebra-chain/src/work/equihash.rs:34`
(`pub(crate) const REGTEST_SOLUTION_SIZE: usize = 36`) -/
def REGTEST_SOLUTION_SIZE : Nat := 36

/-- An Equihash solution. The two variants mirror the Rust enum:
`Common([u8; SOLUTION_SIZE])` for Mainnet/Testnet and
`Regtest([u8; REGTEST_SOLUTION_SIZE])` for Regtest.
Source: `zebra-chain/src/work/equihash.rs:47-52`. -/
inductive Solution
  | common (bytes : List Nat) : Solution
  | regtest (bytes : List Nat) : Solution
  deriving Repr

/-- The raw byte payload of a solution, independent of variant.
Source: `zebra-chain/src/work/equihash.rs:63-68` (`fn value`). -/
def Solution.value : Solution → List Nat
  | .common bs => bs
  | .regtest bs => bs

/-- A solution is well-formed iff its byte length matches the variant's
canonical size. This corresponds to the array-size invariant carried by the
two `[u8; N]` variants on the Rust side.
Source: `zebra-chain/src/work/equihash.rs:47-52`. -/
def WellFormed : Solution → Prop
  | .common bs => bs.length = SOLUTION_SIZE
  | .regtest bs => bs.length = REGTEST_SOLUTION_SIZE

/-! ## CompactSize prefix bytes -/

/-- The canonical CompactSize band-2 prefix tag: `0xfd`. -/
def PREFIX_TAG : Nat := 0xfd

/-- The low byte of `1344` in little-endian: `1344 % 256 = 64 = 0x40`. -/
def PREFIX_LO : Nat := 0x40

/-- The high byte of `1344` in little-endian: `1344 / 256 = 5 = 0x05`. -/
def PREFIX_HI : Nat := 0x05

/-- The full canonical three-byte CompactSize prefix for a 1344-byte payload. -/
def prefixBytes : List Nat := [PREFIX_TAG, PREFIX_LO, PREFIX_HI]

/-- The canonical CompactSize prefix for the 36-byte Regtest payload: a single
byte `[0x24]`, because `36 ≤ 0xfc` falls in band 1. -/
def regtestPrefixBytes : List Nat := [REGTEST_SOLUTION_SIZE]

/-! ## Encoder and decoder -/

/-- `Solution::zcash_serialize`: writes the CompactSize length prefix followed
by the raw solution bytes. The same code path serves both variants because
`value()` already abstracts over them.
Source: `zebra-chain/src/work/equihash.rs:257-261`
(`impl ZcashSerialize for Solution`). -/
def encode (s : Solution) : List Nat :=
  Zebra.CompactSize.encode s.value.length ++ s.value

/-- `Solution::zcash_deserialize`: reads a CompactSize length, rejects anything
larger than `SOLUTION_SIZE`, peels off that many raw bytes, then dispatches to
`Solution::from_bytes`, which itself rejects any length other than
`SOLUTION_SIZE` or `REGTEST_SOLUTION_SIZE`.
Source: `zebra-chain/src/work/equihash.rs:263-280`
(`impl ZcashDeserialize for Solution`), via
`zebra-chain/src/work/equihash.rs:96-113` (`fn from_bytes`). -/
def decode (bytes : List Nat) : Option (Solution × List Nat) :=
  match Zebra.CompactSize.decode bytes with
  | none => none
  | some (len, rest) =>
    -- DoS guard from the Rust deserializer.
    if len > SOLUTION_SIZE then
      none
    -- Bytes-available check from `zcash_deserialize_bytes_external_count`.
    else if rest.length < len then
      none
    -- `Solution::from_bytes` only accepts these two lengths.
    else if len = SOLUTION_SIZE then
      some (.common (rest.take len), rest.drop len)
    else if len = REGTEST_SOLUTION_SIZE then
      some (.regtest (rest.take len), rest.drop len)
    else
      none

/-! ## Theorems — band membership and prefix bytes -/

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

/-- **T2r.** The CompactSize encoder produces the single-byte prefix `[0x24]`
for the Regtest value `36`. -/
theorem encode_regtest_size_is_prefix :
    Zebra.CompactSize.encode REGTEST_SOLUTION_SIZE = regtestPrefixBytes := by
  unfold Zebra.CompactSize.encode REGTEST_SOLUTION_SIZE regtestPrefixBytes
  decide

/-- **T3r.** The decoder accepts the single-byte Regtest prefix and yields `36`
plus whatever follows. -/
theorem decode_regtest_prefix (rest : List Nat) :
    Zebra.CompactSize.decode (regtestPrefixBytes ++ rest)
      = some (REGTEST_SOLUTION_SIZE, rest) := by
  unfold regtestPrefixBytes REGTEST_SOLUTION_SIZE
  rfl

/-! ## Theorems — encoded length -/

/-- **T4.** The total encoded length of a well-formed `Common` solution is
`3 + 1344 = 1347` bytes (3 for the CompactSize prefix, 1344 for the payload). -/
theorem encode_length_common (bs : List Nat)
    (hw : WellFormed (.common bs)) :
    (encode (.common bs)).length = 3 + SOLUTION_SIZE := by
  have hlen : bs.length = SOLUTION_SIZE := hw
  unfold encode Solution.value
  rw [List.length_append, hlen, encode_size_is_prefix]
  unfold prefixBytes
  simp

/-- **T4r.** The total encoded length of a well-formed `Regtest` solution is
`1 + 36 = 37` bytes (1 for the band-1 CompactSize prefix, 36 for the payload). -/
theorem encode_length_regtest (bs : List Nat)
    (hw : WellFormed (.regtest bs)) :
    (encode (.regtest bs)).length = 1 + REGTEST_SOLUTION_SIZE := by
  have hlen : bs.length = REGTEST_SOLUTION_SIZE := hw
  unfold encode Solution.value
  rw [List.length_append, hlen, encode_regtest_size_is_prefix]
  unfold regtestPrefixBytes
  simp

/-! ## Theorems — prefix bytes of the encoded form -/

/-- **T5.** The encoder's first three bytes are exactly the canonical
`[0xfd, 0x40, 0x05]` prefix for any well-formed `Common` solution. -/
theorem encode_prefix_common (bs : List Nat)
    (hw : WellFormed (.common bs)) :
    (encode (.common bs)).take 3 = prefixBytes := by
  have hlen : bs.length = SOLUTION_SIZE := hw
  unfold encode Solution.value
  rw [hlen, encode_size_is_prefix]
  unfold prefixBytes
  rfl

/-- **T5r.** The encoder's first byte is exactly the canonical `[0x24]`
prefix for any well-formed `Regtest` solution. -/
theorem encode_prefix_regtest (bs : List Nat)
    (hw : WellFormed (.regtest bs)) :
    (encode (.regtest bs)).take 1 = regtestPrefixBytes := by
  have hlen : bs.length = REGTEST_SOLUTION_SIZE := hw
  unfold encode Solution.value
  rw [hlen, encode_regtest_size_is_prefix]
  unfold regtestPrefixBytes
  rfl

/-! ## Round-trip -/

/-- **T6.** Round-trip on the `Common` variant: encoding a well-formed
Mainnet/Testnet solution and then decoding recovers the original solution, with
no leftover bytes. -/
theorem roundtrip_common (bs : List Nat)
    (hw : WellFormed (.common bs)) :
    decode (encode (.common bs)) = some (.common bs, []) := by
  have hlen : bs.length = SOLUTION_SIZE := hw
  unfold encode decode Solution.value
  rw [hlen, encode_size_is_prefix]
  -- The prefix-decode step yields `(SOLUTION_SIZE, bs)`.
  have hp : Zebra.CompactSize.decode (prefixBytes ++ bs)
              = some (SOLUTION_SIZE, bs) := decode_prefix bs
  rw [hp]
  have hbytes_len : ¬ bs.length < SOLUTION_SIZE := by omega
  have htake : bs.take SOLUTION_SIZE = bs := by
    rw [← hlen]; exact List.take_length
  have hdrop : bs.drop SOLUTION_SIZE = [] := by
    rw [← hlen]; exact List.drop_length
  simp [hbytes_len, htake, hdrop]

/-- **T6r.** Round-trip on the `Regtest` variant: encoding a well-formed
Regtest solution and then decoding recovers the original solution, with no
leftover bytes. -/
theorem roundtrip_regtest (bs : List Nat)
    (hw : WellFormed (.regtest bs)) :
    decode (encode (.regtest bs)) = some (.regtest bs, []) := by
  have hlen : bs.length = REGTEST_SOLUTION_SIZE := hw
  unfold encode decode Solution.value
  rw [hlen, encode_regtest_size_is_prefix]
  have hp : Zebra.CompactSize.decode (regtestPrefixBytes ++ bs)
              = some (REGTEST_SOLUTION_SIZE, bs) := decode_regtest_prefix bs
  rw [hp]
  have hlen_le : ¬ REGTEST_SOLUTION_SIZE > SOLUTION_SIZE := by
    unfold REGTEST_SOLUTION_SIZE SOLUTION_SIZE; omega
  have hbytes_len : ¬ bs.length < REGTEST_SOLUTION_SIZE := by omega
  have hne_common : REGTEST_SOLUTION_SIZE ≠ SOLUTION_SIZE := by
    unfold REGTEST_SOLUTION_SIZE SOLUTION_SIZE; omega
  have htake : bs.take REGTEST_SOLUTION_SIZE = bs := by
    rw [← hlen]; exact List.take_length
  have hdrop : bs.drop REGTEST_SOLUTION_SIZE = [] := by
    rw [← hlen]; exact List.drop_length
  simp [hlen_le, hbytes_len, hne_common, htake, hdrop]

/-! ## Rejection theorems -/

/-- **T7.** The decoder rejects oversize CompactSize values: any decoded length
above `SOLUTION_SIZE` yields `none`. This is the explicit guard against
unbounded-allocation DoS the Rust source comments warn about. -/
theorem decode_rejects_oversize
    (bytes : List Nat) (len : Nat) (rest : List Nat)
    (hcs : Zebra.CompactSize.decode bytes = some (len, rest))
    (hover : len > SOLUTION_SIZE) :
    decode bytes = none := by
  unfold decode
  rw [hcs]
  simp [hover]

/-- **T7m.** The decoder rejects every CompactSize length that is not exactly
one of the two canonical sizes (`1344` or `36`). This mirrors the
`Solution::from_bytes` "incorrect equihash solution size" rejection in
`zebra-chain/src/work/equihash.rs:109-111`. -/
theorem decode_rejects_non_canonical_length
    (bytes : List Nat) (len : Nat) (rest : List Nat)
    (hcs : Zebra.CompactSize.decode bytes = some (len, rest))
    (hbytes_avail : rest.length ≥ len)
    (hne_common : len ≠ SOLUTION_SIZE)
    (hne_regtest : len ≠ REGTEST_SOLUTION_SIZE) :
    decode bytes = none := by
  unfold decode
  rw [hcs]
  by_cases hover : len > SOLUTION_SIZE
  · simp [hover]
  · have hnot_short : ¬ rest.length < len := by omega
    simp [hover, hnot_short, hne_common, hne_regtest]

/-! ## Shape and sanity theorems -/

/-- **T8.** Encoder produces a non-empty list for either variant. -/
theorem encode_nonempty (s : Solution) (hw : WellFormed s) : encode s ≠ [] := by
  intro heq
  have hlen : (encode s).length = 0 := by rw [heq]; rfl
  cases s with
  | common bs =>
    rw [encode_length_common bs hw] at hlen
    unfold SOLUTION_SIZE at hlen
    omega
  | regtest bs =>
    rw [encode_length_regtest bs hw] at hlen
    unfold REGTEST_SOLUTION_SIZE at hlen
    omega

/-- **T9.** Concrete shape of the encoded `Common` form: it begins with
`0xfd, 0x40, 0x05` followed by the 1344 payload bytes. -/
theorem encode_shape_common (bs : List Nat)
    (hw : WellFormed (.common bs)) :
    encode (.common bs) = PREFIX_TAG :: PREFIX_LO :: PREFIX_HI :: bs := by
  have hlen : bs.length = SOLUTION_SIZE := hw
  unfold encode Solution.value
  rw [hlen, encode_size_is_prefix]
  unfold prefixBytes
  rfl

/-- **T9r.** Concrete shape of the encoded `Regtest` form: it begins with the
single byte `0x24` followed by the 36 payload bytes. -/
theorem encode_shape_regtest (bs : List Nat)
    (hw : WellFormed (.regtest bs)) :
    encode (.regtest bs) = REGTEST_SOLUTION_SIZE :: bs := by
  have hlen : bs.length = REGTEST_SOLUTION_SIZE := hw
  unfold encode Solution.value
  rw [hlen, encode_regtest_size_is_prefix]
  unfold regtestPrefixBytes
  rfl

/-- **T10.** A trivial sanity check: `prefixBytes` has exactly three bytes. -/
theorem prefixBytes_length : prefixBytes.length = 3 := by
  unfold prefixBytes; rfl

/-- **T10r.** A trivial sanity check: `regtestPrefixBytes` has exactly one byte. -/
theorem regtestPrefixBytes_length : regtestPrefixBytes.length = 1 := by
  unfold regtestPrefixBytes; rfl

/-- **T11.** The `(lo, hi)` pair canonically decodes to `1344` under the
little-endian 2-byte interpretation. -/
theorem prefix_payload_decodes :
    Zebra.CompactSize.fromLE2 PREFIX_LO PREFIX_HI = SOLUTION_SIZE := by
  unfold Zebra.CompactSize.fromLE2 PREFIX_LO PREFIX_HI SOLUTION_SIZE
  decide

/-! ## Variant identification by length

These theorems pin the discriminator: the length alone determines whether a
well-formed solution must be `Common` or `Regtest`. They mirror the dispatch
in `Solution::from_bytes` (`equihash.rs:97-108`). -/

/-- **T12.** Every well-formed solution has byte-length 1344 or 36. -/
theorem wellFormed_length (s : Solution) (hw : WellFormed s) :
    s.value.length = SOLUTION_SIZE ∨ s.value.length = REGTEST_SOLUTION_SIZE := by
  cases s with
  | common bs => left; exact hw
  | regtest bs => right; exact hw

/-- **T13.** The Common and Regtest canonical sizes are distinct, so the
length is an unambiguous discriminator. -/
theorem canonical_sizes_distinct :
    SOLUTION_SIZE ≠ REGTEST_SOLUTION_SIZE := by
  unfold SOLUTION_SIZE REGTEST_SOLUTION_SIZE; omega

end Zebra.EquihashSolution
