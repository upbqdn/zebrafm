import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# `getbestblockhash` RPC method

Models the JSON-RPC method `getbestblockhash` exposed by Zebra. The handler is
defined in `zebra-rpc/src/methods.rs` at lines 315-316 (trait definition) and
1568-1573 (impl):

```rust
#[method(name = "getbestblockhash")]
fn get_best_block_hash(&self) -> Result<GetBlockHashResponse>;

fn get_best_block_hash(&self) -> Result<GetBlockHashResponse> {
    self.latest_chain_tip
        .best_tip_hash()
        .map(GetBlockHashResponse)
        .ok_or_misc_error("No blocks in state")
}
```

The response type is `GetBlockHashResponse(#[serde(with = "hex")] pub(crate) block::Hash)`
(`zebra-rpc/src/methods.rs:4099-4101`), so the JSON wire form is a hex string
of the wrapped `block::Hash`.

Hex encoding of a `block::Hash` goes through `impl ToHex for &Hash`
(`zebra-chain/src/block/hash.rs:52-60`):

```rust
fn encode_hex<T: FromIterator<char>>(&self) -> T {
    self.bytes_in_display_order().encode_hex()
}
```

i.e. the bytes are *reversed* (because
`impl BytesInDisplayOrder<true> for block::Hash` at `block/hash.rs:28` sets the
`SHOULD_REVERSE_BYTES_IN_DISPLAY_ORDER` const generic to `true`), and then the
`hex` crate's `encode_hex` produces a lowercase hex string (two chars per byte,
high nibble first).

So `getbestblockhash` returns exactly:

  * `None` when there is no tip (the `ok_or_misc_error("No blocks in state")`
    branch);
  * otherwise the 64-character lowercase hex string of the byte-swapped tip
    hash. This is the zcashd / Bitcoin u256 display convention.

We model bytes as `Nat` with implicit `< 256`, ASCII chars as `Nat` (the ASCII
code point), and hex strings as `List Nat` (a list of ASCII codes). The
`getbestblockhash` model returns `Option (List Nat)` to mirror the Rust
`Result`.
-/

namespace Zebra.RpcGetbestblockhash

/-! ## Constants -/

/-- A `block::Hash` is exactly 32 bytes wide.
Source: `zebra-chain/src/block/hash.rs:26` (`pub struct Hash(pub [u8; 32])`). -/
def HASH_BYTES : Nat := 32

/-- The hex encoding of a 32-byte hash is exactly 64 characters wide
(two ASCII chars per byte). Pinned as a derived constant so the value is
visible in theorem statements. -/
def HEX_LEN : Nat := 64

/-- ASCII `'0' = 48`. -/
def ASCII_ZERO : Nat := 48

/-- ASCII `'9' = 57`. -/
def ASCII_NINE : Nat := 57

/-- ASCII `'a' = 97`. -/
def ASCII_A : Nat := 97

/-- ASCII `'f' = 102`. -/
def ASCII_F : Nat := 102

/-! ## Hex encoding of a nibble / byte / byte sequence

The `hex` crate emits **lowercase** hex by default; `encode_hex` in the
`ToHex` impl on `&Hash` calls the lowercase variant (the uppercase counterpart
`encode_hex_upper` is the separate method on the trait, not used by
`getbestblockhash`). -/

/-- Encode a nibble (`< 16`) as a lowercase ASCII hex digit:
0-9 → ASCII `'0'..'9'`, 10-15 → ASCII `'a'..'f'`. Values outside `[0, 16)`
return `'0'` as a sentinel; the encoder calls this only on values `< 16`. -/
def nibbleToHex (n : Nat) : Nat :=
  if n ≤ 9 then ASCII_ZERO + n
  else if n ≤ 15 then ASCII_A + (n - 10)
  else ASCII_ZERO  -- defensive default; encoder only feeds 0..15

/-- Encode one byte (`< 256`) as two lowercase hex ASCII chars, **high
nibble first** (big-endian per byte). This is the format `hex::encode` /
`ToHex::encode_hex` produce. -/
def byteToHex (b : Nat) : List Nat :=
  [nibbleToHex (b / 16), nibbleToHex (b % 16)]

/-- Encode a byte sequence to lowercase hex by concatenating per-byte
encodings. The output has length `2 * bs.length`. -/
def bytesToHex : List Nat → List Nat
  | [] => []
  | b :: rest => byteToHex b ++ bytesToHex rest

/-! ## Display-order byte swap

`block::Hash` uses `BytesInDisplayOrder<true>`, which reverses the serialised
bytes to obtain display-order bytes (`serialization/display_order.rs:21-27`).
This is the byte-swap that makes Zcash/Bitcoin hashes print in u256 / big-endian
display order. -/

/-- Reverse the bytes (the `SHOULD_REVERSE_BYTES_IN_DISPLAY_ORDER = true`
behaviour of `bytes_in_display_order`).
Source: `zebra-chain/src/serialization/display_order.rs:21-27`,
`zebra-chain/src/block/hash.rs:28`. -/
def bytesInDisplayOrder (bs : List Nat) : List Nat := bs.reverse

/-! ## The RPC handler

The Lean model uses `Option (List Nat)` where Rust uses `Result<GetBlockHashResponse>`:
`some s` for a successful encoding (`s` = the 64-char ASCII hex string of the
display-order tip hash), and `none` for the "No blocks in state" branch. -/

/-- The chain-tip is modelled as an `Option (List Nat)`: `some h` when there is
a best tip (with `h` the 32 raw serialised-order bytes), and `none` otherwise.
This matches `LatestChainTip::best_tip_hash` returning `Option<block::Hash>`.
Source: `zebra-chain/src/chain_tip.rs:32`. -/
def Tip := Option (List Nat)

/-- `getbestblockhash` body:
1. Read the latest chain tip's hash (`None` on empty state).
2. Reverse bytes to display order (`block::Hash`'s `BytesInDisplayOrder<true>`).
3. Hex-encode (lowercase, two chars per byte).
Source: `zebra-rpc/src/methods.rs:1568-1573`. -/
def getBestBlockHash (tip : Tip) : Option (List Nat) :=
  tip.map (fun h => bytesToHex (bytesInDisplayOrder h))

/-! ## Predicates -/

/-- A byte is in range. -/
def IsByte (b : Nat) : Prop := b < 256

/-- A list of bytes is a valid 32-byte hash. -/
def IsHash (bs : List Nat) : Prop := bs.length = HASH_BYTES

/-- An ASCII char code is a lowercase hex digit. -/
def IsLowerHexChar (c : Nat) : Prop :=
  (ASCII_ZERO ≤ c ∧ c ≤ ASCII_NINE) ∨ (ASCII_A ≤ c ∧ c ≤ ASCII_F)

/-! ## Theorems -/

/-- `byteToHex` always emits exactly 2 chars. -/
theorem byteToHex_length (b : Nat) : (byteToHex b).length = 2 := rfl

/-- `bytesToHex` emits exactly `2 * bs.length` chars. -/
theorem bytesToHex_length (bs : List Nat) :
    (bytesToHex bs).length = 2 * bs.length := by
  induction bs with
  | nil => decide
  | cons b rest ih =>
    unfold bytesToHex
    simp [byteToHex, ih]
    omega

/-- Reversing preserves length. -/
theorem bytesInDisplayOrder_length (bs : List Nat) :
    (bytesInDisplayOrder bs).length = bs.length := by
  unfold bytesInDisplayOrder
  exact List.length_reverse

/-- **T1 (length is exactly 64).** On a valid 32-byte tip, `getbestblockhash`
returns a hex string of length exactly 64. This is the consensus-relevant
shape contract the RPC clients depend on (e.g. lightwalletd).

The contract follows directly from the per-byte encoding (2 chars/byte) and
the fixed `[u8; 32]` hash width. -/
theorem getBestBlockHash_length (h : List Nat) (hH : IsHash h) :
    (getBestBlockHash (some h)).map List.length = some HEX_LEN := by
  unfold getBestBlockHash IsHash at *
  simp [bytesToHex_length, bytesInDisplayOrder_length, hH, HASH_BYTES, HEX_LEN]

/-! ## Lowercase-hex character class -/

/-- A nibble (`< 16`) maps to a valid lowercase hex char code. -/
theorem nibbleToHex_isHexChar (n : Nat) (h : n < 16) :
    IsLowerHexChar (nibbleToHex n) := by
  unfold nibbleToHex IsLowerHexChar ASCII_ZERO ASCII_NINE ASCII_A ASCII_F
  by_cases h9 : n ≤ 9
  · left
    simp [h9]
    omega
  · right
    have h15 : n ≤ 15 := by omega
    simp [h9, h15]
    omega

/-- For a byte (`< 256`), the high nibble is `< 16`. -/
theorem byte_high_nibble (b : Nat) (h : IsByte b) : b / 16 < 16 := by
  unfold IsByte at h
  omega

/-- Every char of `byteToHex b` for a valid byte is a lowercase hex char. -/
theorem byteToHex_chars_hex (b : Nat) (hB : IsByte b)
    (c : Nat) (hc : c ∈ byteToHex b) : IsLowerHexChar c := by
  unfold byteToHex at hc
  -- Both chars come from `nibbleToHex` on a value < 16.
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h
  · rw [h]
    exact nibbleToHex_isHexChar _ (byte_high_nibble b hB)
  · rw [h]
    have : b % 16 < 16 := Nat.mod_lt _ (by decide)
    exact nibbleToHex_isHexChar _ this

/-- Helper: every char of `bytesToHex bs` is a hex char, when every byte is
in range. -/
theorem bytesToHex_chars_hex (bs : List Nat) (hbs : ∀ b ∈ bs, IsByte b)
    (c : Nat) (hc : c ∈ bytesToHex bs) : IsLowerHexChar c := by
  induction bs with
  | nil =>
    unfold bytesToHex at hc
    simp at hc
  | cons b rest ih =>
    unfold bytesToHex at hc
    simp only [List.mem_append] at hc
    rcases hc with hc1 | hc1
    · have hb : IsByte b := hbs b (List.mem_cons_self ..)
      exact byteToHex_chars_hex b hb c hc1
    · apply ih _ hc1
      intro x hx
      exact hbs x (List.mem_cons_of_mem _ hx)

/-- Reversing preserves the byte-range hypothesis. -/
theorem bytesInDisplayOrder_bytes (h : List Nat) (hbs : ∀ b ∈ h, IsByte b) :
    ∀ b ∈ bytesInDisplayOrder h, IsByte b := by
  unfold bytesInDisplayOrder
  intro b hb
  rw [List.mem_reverse] at hb
  exact hbs b hb

/-- **T2 (every output char is lowercase hex 0-9/a-f).** Every character of
the `getbestblockhash` response is a lowercase ASCII hex digit. This is the
character-class half of the "64 lowercase hex chars" claim. -/
theorem getBestBlockHash_chars_hex (h : List Nat) (_ : IsHash h)
    (hbs : ∀ b ∈ h, IsByte b)
    (s : List Nat) (hs : getBestBlockHash (some h) = some s)
    (c : Nat) (hc : c ∈ s) : IsLowerHexChar c := by
  unfold getBestBlockHash at hs
  simp only [Option.map_some, Option.some.injEq] at hs
  rw [← hs] at hc
  exact bytesToHex_chars_hex _ (bytesInDisplayOrder_bytes h hbs) c hc

/-! ## Concrete vector: the zero hash -/

/-- The zero hash: 32 zero bytes (the `Default` derive on `block::Hash`). -/
def zeroHash : List Nat := List.replicate HASH_BYTES 0

/-- The zero hash is well-formed. -/
theorem zeroHash_isHash : IsHash zeroHash := by
  unfold zeroHash IsHash
  exact List.length_replicate

/-- Reversing a list of zeros gives a list of zeros. -/
theorem bytesInDisplayOrder_zeroHash :
    bytesInDisplayOrder zeroHash = zeroHash := by
  unfold bytesInDisplayOrder zeroHash
  exact List.reverse_replicate

/-- `byteToHex 0 = ['0','0']` (ASCII `48, 48`). -/
theorem byteToHex_zero : byteToHex 0 = [ASCII_ZERO, ASCII_ZERO] := by
  unfold byteToHex nibbleToHex
  decide

/-- `bytesToHex` of `replicate n 0` is `replicate (2*n) '0'` (in ASCII). -/
theorem bytesToHex_replicate_zero (n : Nat) :
    bytesToHex (List.replicate n 0) = List.replicate (2 * n) ASCII_ZERO := by
  induction n with
  | zero =>
    change bytesToHex [] = List.replicate 0 ASCII_ZERO
    rfl
  | succ k ih =>
    rw [List.replicate_succ]
    unfold bytesToHex
    rw [byteToHex_zero, ih]
    -- ASCII_ZERO :: ASCII_ZERO :: replicate (2*k) ASCII_ZERO = replicate (2*(k+1)) ASCII_ZERO
    have h_eq : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [h_eq, List.replicate_succ, List.replicate_succ]
    simp

/-- **T3 (concrete vector: zero hash).** The all-zero `block::Hash` encodes to
64 ASCII `'0'` characters. This is the smallest test vector for the RPC and
matches what zcashd / Bitcoin's `getbestblockhash` would emit for a zero hash. -/
theorem getBestBlockHash_zeroHash :
    getBestBlockHash (some zeroHash) = some (List.replicate HEX_LEN ASCII_ZERO) := by
  change some (bytesToHex (bytesInDisplayOrder zeroHash))
       = some (List.replicate HEX_LEN ASCII_ZERO)
  rw [bytesInDisplayOrder_zeroHash]
  change some (bytesToHex (List.replicate HASH_BYTES 0))
       = some (List.replicate HEX_LEN ASCII_ZERO)
  rw [bytesToHex_replicate_zero]
  have h_eq : 2 * HASH_BYTES = HEX_LEN := by unfold HASH_BYTES HEX_LEN; decide
  rw [h_eq]

/-! ## "No blocks in state" branch -/

/-- **T4 (empty state).** When the chain tip is empty, `getbestblockhash`
returns `none` — mirroring the `ok_or_misc_error("No blocks in state")` arm
in the Rust handler. -/
theorem getBestBlockHash_emptyState : getBestBlockHash none = none := by
  unfold getBestBlockHash
  rfl

/-! ## Byte-swap: the wire-format ordering relative to display order -/

/-- The first emitted byte-pair in the hex output corresponds to the
*last* byte of the serialised-order hash. This is the byte-swap that makes
`getbestblockhash` print hashes in u256 / big-endian display order, the
convention zcashd inherited from Bitcoin. -/
theorem first_byte_in_hex_is_last_in_serialised (h : List Nat) (_ : IsHash h) :
    (bytesInDisplayOrder h).head? = h.getLast? := by
  unfold bytesInDisplayOrder
  exact List.head?_reverse

/-- The last emitted byte-pair in the hex output corresponds to the
*first* byte of the serialised-order hash. -/
theorem last_byte_in_hex_is_first_in_serialised (h : List Nat) (_ : IsHash h) :
    (bytesInDisplayOrder h).getLast? = h.head? := by
  unfold bytesInDisplayOrder
  rw [List.getLast?_reverse]

/-- **T5 (byte-swap on the wire).** The display-order bytes Zcash hex-encodes
are exactly the **reverse** of the serialised-order bytes that `ZcashSerialize`
writes. This is the consensus-relevant claim that the RPC emits a
byte-swapped hash — without the swap, the hex output would not match
zcashd / Bitcoin. -/
theorem display_is_reverse_of_serialised (h : List Nat) :
    bytesInDisplayOrder h = h.reverse := rfl

/-! ## A small non-zero vector -/

/-- A test vector: a hash whose internal serialised bytes are
`[0x01, 0x00, ..., 0x00]` (one nonzero byte at index 0, rest zero). The display
hex should be `"0...001"` — i.e. the `01` ends up at the *end* of the hex
string, not the start. This is the most direct test of the byte-swap. -/
def testHash01 : List Nat := 1 :: List.replicate (HASH_BYTES - 1) 0

theorem testHash01_isHash : IsHash testHash01 := by
  unfold testHash01 IsHash
  rw [List.length_cons, List.length_replicate]
  decide

/-- `byteToHex 1 = ['0','1']` in ASCII. -/
theorem byteToHex_one : byteToHex 1 = [ASCII_ZERO, ASCII_ZERO + 1] := by
  unfold byteToHex nibbleToHex
  decide

/-- Reversing `1 :: replicate 31 0` gives `replicate 31 0 ++ [1]`. -/
theorem testHash01_reversed :
    bytesInDisplayOrder testHash01 = List.replicate (HASH_BYTES - 1) 0 ++ [1] := by
  unfold bytesInDisplayOrder testHash01
  rw [List.reverse_cons, List.reverse_replicate]

/-- `bytesToHex (replicate n 0 ++ [1]) = replicate (2*n) '0' ++ ['0', '1']`. -/
theorem bytesToHex_zeros_then_one (n : Nat) :
    bytesToHex (List.replicate n 0 ++ [1])
      = List.replicate (2 * n) ASCII_ZERO ++ [ASCII_ZERO, ASCII_ZERO + 1] := by
  induction n with
  | zero =>
    change bytesToHex [1] = List.replicate 0 ASCII_ZERO ++ [ASCII_ZERO, ASCII_ZERO + 1]
    unfold bytesToHex
    rw [byteToHex_one]
    rfl
  | succ k ih =>
    rw [List.replicate_succ]
    change bytesToHex (0 :: (List.replicate k 0 ++ [1]))
         = List.replicate (2 * (k + 1)) ASCII_ZERO ++ [ASCII_ZERO, ASCII_ZERO + 1]
    unfold bytesToHex
    rw [byteToHex_zero]
    rw [ih]
    have h_eq : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [h_eq, List.replicate_succ, List.replicate_succ]
    simp

/-- **T6 (byte-swap concrete vector).** A hash whose internal serialised-order
bytes are `[01, 00, ..., 00]` encodes to the 64-char hex string
`"0000...0001"` — the `01` appears at the **end**, not the start. This is the
direct concrete witness of the byte-swap: without `bytesInDisplayOrder`, the
hex would start with `01` instead of ending with it. -/
theorem getBestBlockHash_testHash01 :
    getBestBlockHash (some testHash01)
      = some (List.replicate (HEX_LEN - 2) ASCII_ZERO ++ [ASCII_ZERO, ASCII_ZERO + 1]) := by
  change some (bytesToHex (bytesInDisplayOrder testHash01))
       = some (List.replicate (HEX_LEN - 2) ASCII_ZERO ++ [ASCII_ZERO, ASCII_ZERO + 1])
  rw [testHash01_reversed]
  rw [bytesToHex_zeros_then_one]
  have h_eq : 2 * (HASH_BYTES - 1) = HEX_LEN - 2 := by
    unfold HASH_BYTES HEX_LEN; decide
  rw [h_eq]

/-! ## Round-trip via reversing the display-order bytes -/

/-- Reversing twice is the identity (i.e. `bytesInDisplayOrder` is an
involution). This is the operation a client performs to recover the
serialised-order hash from the RPC's hex output, after hex-decoding. -/
theorem bytesInDisplayOrder_involutive (bs : List Nat) :
    bytesInDisplayOrder (bytesInDisplayOrder bs) = bs := by
  unfold bytesInDisplayOrder
  exact List.reverse_reverse bs

/-! ## Determinism and structural properties -/

/-- **T7 (determinism).** `getbestblockhash` is a pure function of the tip:
two calls with the same tip return the same result. -/
theorem getBestBlockHash_deterministic (t : Tip) :
    getBestBlockHash t = getBestBlockHash t := rfl

/-- **T8 (success iff tip exists).** `getbestblockhash` returns `some _` iff
the chain-tip oracle returns `some _`. This pins the failure mode: the only
way to get an `Err` from the Rust handler is the empty-state branch. -/
theorem getBestBlockHash_isSome_iff (t : Tip) :
    (getBestBlockHash t).isSome ↔ t.isSome := by
  unfold getBestBlockHash
  cases t with
  | none => simp
  | some _ => simp

/-- **T9 (length pin).** Spell out `HEX_LEN = 2 * HASH_BYTES`. This makes the
"two hex chars per byte" relation visible at the constant level so any future
change to one of the constants will surface a build failure here. -/
theorem hex_len_eq_twice_hash_bytes : HEX_LEN = 2 * HASH_BYTES := by
  unfold HEX_LEN HASH_BYTES
  decide

/-- **T10 (concrete byte-pair vector).** A standalone witness for the
"high nibble first" per-byte encoding: `byteToHex 0xAB` is `['a', 'b']`
(ASCII `97, 98`). This pins the bigendian-per-byte convention. -/
theorem byteToHex_AB : byteToHex 0xAB = [ASCII_A, ASCII_A + 1] := by
  unfold byteToHex nibbleToHex ASCII_A
  decide

end Zebra.RpcGetbestblockhash
