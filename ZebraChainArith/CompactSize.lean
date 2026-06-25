import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# CompactSize64 from `zebra-chain/src/serialization/compact_size.rs`

Models the Bitcoin/Zcash CompactSize variable-length integer encoding. The
encoder picks one of four bands by magnitude:

  * `[0, 0xfc]`             → 1 byte:  `[n]`
  * `[0xfd, 0xffff]`        → 3 bytes: `[0xfd, lo, hi]`
  * `[0x10000, 0xffffffff]` → 5 bytes: `[0xfe, b0, b1, b2, b3]`
  * `[0x100000000, u64::MAX]` → 9 bytes: `[0xff, b0..b7]`

The decoder is canonicity-checked: every flag byte requires its band to be the
smallest one fitting the value, otherwise it returns an error
("non-canonical CompactSize"). This rejects malleable encodings — the
Bitcoin CVE-2012-2459 class of bug.

We model bytes as `Nat` with the implicit invariant `< 256`. The encoder
produces canonical bytes; the decoder accepts only canonical input.
-/

namespace Zebra.CompactSize

/-! ## Helpers -/

/-- Two-byte little-endian decode. -/
def fromLE2 (b0 b1 : Nat) : Nat := b0 + b1 * 256

/-- Four-byte little-endian decode. -/
def fromLE4 (b0 b1 b2 b3 : Nat) : Nat :=
  b0 + b1 * 256 + b2 * 65536 + b3 * 16777216

/-- Eight-byte little-endian decode. -/
def fromLE8 (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : Nat :=
  b0 + b1 * 256 + b2 * 65536 + b3 * 16777216
    + b4 * 4294967296 + b5 * 1099511627776 + b6 * 281474976710656 + b7 * 72057594037927936

/-- `u64::MAX = 2^64 - 1`. The implicit Rust bound on the encoder's input. -/
def U64_MAX : Nat := 18446744073709551615

/-! ## Encoder and decoder -/

/-- The encoder: produces the canonical CompactSize bytes for `n` (assumed `< 2^64`).
Source: `zebra-chain/src/serialization/compact_size.rs:317`
(`impl ZcashSerialize for CompactSize64`) -/
def encode (n : Nat) : List Nat :=
  if n ≤ 0xfc then
    [n]
  else if n ≤ 0xffff then
    [0xfd, n % 256, (n / 256) % 256]
  else if n ≤ 0xffffffff then
    [0xfe, n % 256, (n / 256) % 256, (n / 65536) % 256, (n / 16777216) % 256]
  else
    [0xff,
     n % 256,
     (n / 256) % 256,
     (n / 65536) % 256,
     (n / 16777216) % 256,
     (n / 4294967296) % 256,
     (n / 1099511627776) % 256,
     (n / 281474976710656) % 256,
     (n / 72057594037927936) % 256]

/-- The decoder. Returns `Some (value, remaining)` or `None` for malformed /
non-canonical input. Models the Rust `zcash_deserialize` with the canonicity
guards in each of the `0xfd`/`0xfe`/`0xff` branches.
Source: `zebra-chain/src/serialization/compact_size.rs:339`
(`impl ZcashDeserialize for CompactSize64`) -/
def decode (bytes : List Nat) : Option (Nat × List Nat) :=
  match bytes with
  | [] => none
  | b :: rest =>
    if b ≤ 0xfc then
      some (b, rest)
    else if b = 0xfd then
      match rest with
      | b0 :: b1 :: rest' =>
        let n := fromLE2 b0 b1
        if n ≥ 0xfd then some (n, rest') else none
      | _ => none
    else if b = 0xfe then
      match rest with
      | b0 :: b1 :: b2 :: b3 :: rest' =>
        let n := fromLE4 b0 b1 b2 b3
        if n ≥ 0x10000 then some (n, rest') else none
      | _ => none
    else if b = 0xff then
      match rest with
      | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest' =>
        let n := fromLE8 b0 b1 b2 b3 b4 b5 b6 b7
        if n ≥ 0x100000000 then some (n, rest') else none
      | _ => none
    else
      none

/-! ## Theorems -/

/-- **T1.** Round-trip on band 1 (`[0, 0xfc]`). -/
theorem roundtrip_band1 (n : Nat) (h : n ≤ 0xfc) :
    decode (encode n) = some (n, []) := by
  unfold encode decode
  simp [h]

/-- **T2.** Round-trip on band 2 (`[0xfd, 0xffff]`). -/
theorem roundtrip_band2 (n : Nat) (h1 : 0xfd ≤ n) (h2 : n ≤ 0xffff) :
    decode (encode n) = some (n, []) := by
  unfold encode decode
  have hlo : ¬ n ≤ 0xfc := by omega
  simp [hlo, h2, fromLE2]
  omega

/-- **T3.** Round-trip on band 3 (`[0x10000, 0xffffffff]`). -/
theorem roundtrip_band3 (n : Nat) (h1 : 0x10000 ≤ n) (h2 : n ≤ 0xffffffff) :
    decode (encode n) = some (n, []) := by
  unfold encode decode
  have h_le_fc : ¬ n ≤ 0xfc := by omega
  have h_le_ffff : ¬ n ≤ 0xffff := by omega
  simp [h_le_fc, h_le_ffff, h2, fromLE4]
  omega

/-- **T4.** Round-trip on band 4 (`[0x100000000, u64::MAX]`). -/
theorem roundtrip_band4 (n : Nat) (h1 : 0x100000000 ≤ n) (h2 : n ≤ U64_MAX) :
    decode (encode n) = some (n, []) := by
  unfold encode decode U64_MAX at *
  have h_le_fc : ¬ n ≤ 0xfc := by omega
  have h_le_ffff : ¬ n ≤ 0xffff := by omega
  have h_le_ffffffff : ¬ n ≤ 0xffffffff := by omega
  simp [h_le_fc, h_le_ffff, h_le_ffffffff, fromLE8]
  omega

/-- **T5.** Encoder length is in `{1, 3, 5, 9}`. -/
theorem encode_length (n : Nat) :
    (encode n).length = 1 ∨ (encode n).length = 3
      ∨ (encode n).length = 5 ∨ (encode n).length = 9 := by
  unfold encode
  by_cases h1 : n ≤ 0xfc
  · simp [h1]
  by_cases h2 : n ≤ 0xffff
  · simp [h1, h2]
  by_cases h3 : n ≤ 0xffffffff
  · simp [h1, h2, h3]
  · simp [h1, h2, h3]

/-- **T6.** The decoder is total: it either returns `Some` or `None` for every
input. In Lean this is trivially true (`decode` is a total function), but the
theorem witnesses it — corresponding to the Rust claim that `zcash_deserialize`
never panics on a malformed input, only returns `Err`. -/
theorem decode_total (bytes : List Nat) :
    (decode bytes).isSome ∨ decode bytes = none := by
  rcases h : decode bytes with _ | _
  · right; rfl
  · left; simp

/-! ## Stretch: canonicity -/

/-- **T7 (canonicity, band 2).** The decoder rejects 3-byte encodings of small
values: a `0xfd`-prefixed bundle whose payload `< 0xfd` is non-canonical
(the value would have fit in band 1). This is the CVE-2012-2459 class of
malleability the Rust source guards against. -/
theorem canonicity_band2 (b0 b1 : Nat) (rest : List Nat)
    (h : fromLE2 b0 b1 < 0xfd) :
    decode (0xfd :: b0 :: b1 :: rest) = none := by
  unfold decode
  have h_fc : ¬ (0xfd : Nat) ≤ 0xfc := by decide
  simp [h_fc, h]

/-- **T8 (canonicity, band 3).** Similarly for `0xfe` with a 4-byte payload
that fits in `≤ 0xffff` (would have been band 1 or 2). -/
theorem canonicity_band3 (b0 b1 b2 b3 : Nat) (rest : List Nat)
    (h : fromLE4 b0 b1 b2 b3 < 0x10000) :
    decode (0xfe :: b0 :: b1 :: b2 :: b3 :: rest) = none := by
  unfold decode
  have h_fc : ¬ (0xfe : Nat) ≤ 0xfc := by decide
  have h_fd : (0xfe : Nat) ≠ 0xfd := by decide
  simp [h_fc, h_fd, h]

/-- **T9 (canonicity, band 4).** Similarly for `0xff` with an 8-byte payload
`≤ 0xffffffff`. -/
theorem canonicity_band4 (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) (rest : List Nat)
    (h : fromLE8 b0 b1 b2 b3 b4 b5 b6 b7 < 0x100000000) :
    decode (0xff :: b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) = none := by
  unfold decode
  have h_fc : ¬ (0xff : Nat) ≤ 0xfc := by decide
  have h_fd : (0xff : Nat) ≠ 0xfd := by decide
  have h_fe : (0xff : Nat) ≠ 0xfe := by decide
  simp [h_fc, h_fd, h_fe, h]

/-! ## CompactSizeMessage cap -/

/-- A typical `MAX_PROTOCOL_MESSAGE_LEN` constant for Zcash (2 MiB). The exact
value here is a model — the production constant is in
`zebra-chain/src/serialization/constraint.rs`. Modelled as a parameter to keep
the proof robust to changes. -/
def MAX_PROTOCOL_MESSAGE_LEN : Nat := 2 * 1024 * 1024

/-- `CompactSizeMessage::try_from<usize>`: succeeds iff the value is in
`[0, MAX_PROTOCOL_MESSAGE_LEN]`. This is the DoS-cap pin from
`zebra-chain/src/serialization/compact_size.rs`. -/
def messageTryFrom (n : Nat) : Option Nat :=
  if n ≤ MAX_PROTOCOL_MESSAGE_LEN then some n else none

/-- **T10 (Message cap).** `messageTryFrom` succeeds iff `n ≤ MAX_PROTOCOL_MESSAGE_LEN`. -/
theorem messageTryFrom_iff (n : Nat) :
    (messageTryFrom n).isSome ↔ n ≤ MAX_PROTOCOL_MESSAGE_LEN := by
  unfold messageTryFrom
  by_cases h : n ≤ MAX_PROTOCOL_MESSAGE_LEN <;> simp [h]

/-- **T11 (Message cap: out-of-range rejected).** Strictly: any oversize value
returns `none`, blocking the memory-DoS preallocation attack the Rust comment
warns about. -/
theorem messageTryFrom_rejects_overlimit (n : Nat) (h : MAX_PROTOCOL_MESSAGE_LEN < n) :
    messageTryFrom n = none := by
  unfold messageTryFrom
  have : ¬ n ≤ MAX_PROTOCOL_MESSAGE_LEN := by omega
  simp [this]

/-! ## Bonus theorems -/

/-- **B1.** `decode []` returns `none` (no input ⇒ no decode). -/
theorem decode_empty : decode [] = none := rfl

/-- **B2.** The encoder's first byte is in `{0..=0xfc} ∪ {0xfd, 0xfe, 0xff}`. -/
theorem encode_first_byte_canonical (n : Nat) :
    ∃ head tail, encode n = head :: tail ∧
      (head ≤ 0xfc ∨ head = 0xfd ∨ head = 0xfe ∨ head = 0xff) := by
  unfold encode
  by_cases h1 : n ≤ 0xfc
  · exact ⟨n, [], by simp [h1], Or.inl h1⟩
  by_cases h2 : n ≤ 0xffff
  · exact ⟨0xfd, [n % 256, (n / 256) % 256],
            by simp [h1, h2], Or.inr (Or.inl rfl)⟩
  by_cases h3 : n ≤ 0xffffffff
  · exact ⟨0xfe,
            [n % 256, (n / 256) % 256, (n / 65536) % 256, (n / 16777216) % 256],
            by simp [h1, h2, h3], Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨0xff,
            [n % 256, (n / 256) % 256, (n / 65536) % 256, (n / 16777216) % 256,
             (n / 4294967296) % 256, (n / 1099511627776) % 256,
             (n / 281474976710656) % 256, (n / 72057594037927936) % 256],
            by simp [h1, h2, h3], Or.inr (Or.inr (Or.inr rfl))⟩

/-- **B3.** The encoder produces a non-empty list. -/
theorem encode_nonempty (n : Nat) : encode n ≠ [] := by
  unfold encode
  by_cases h1 : n ≤ 0xfc
  · simp [h1]
  by_cases h2 : n ≤ 0xffff
  · simp [h1, h2]
  by_cases h3 : n ≤ 0xffffffff
  · simp [h1, h2, h3]
  · simp [h1, h2, h3]

/-- **B4 (universal round-trip).** For every `n ≤ U64_MAX`, encoding then
decoding recovers `(n, [])`. This collapses the four band theorems into one. -/
theorem roundtrip_universal (n : Nat) (h : n ≤ U64_MAX) :
    decode (encode n) = some (n, []) := by
  by_cases h1 : n ≤ 0xfc
  · exact roundtrip_band1 n h1
  by_cases h2 : n ≤ 0xffff
  · exact roundtrip_band2 n (by omega) h2
  by_cases h3 : n ≤ 0xffffffff
  · exact roundtrip_band3 n (by omega) h3
  · exact roundtrip_band4 n (by omega) h

end Zebra.CompactSize
