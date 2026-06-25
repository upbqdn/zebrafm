import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Hash round-trip from `zebra-chain/src/block/hash.rs` and
`zebra-chain/src/transaction/hash.rs`

`block::Hash` and `transaction::Hash` are both 32-byte newtypes over `[u8; 32]`:

```rust
pub struct Hash(pub [u8; 32]);
```

Their `From<[u8; 32]>` / `Into<[u8; 32]>` conversions and the Zcash
`zcash_serialize` / `zcash_deserialize` impls forward the 32 raw bytes verbatim,
so on the wire and through the newtype both round-trip as the identity on the
inner array.

The interesting consensus-relevant byte-level reorientation is `BytesInDisplayOrder`,
which Zebra uses to map between

  * **serialised order** — little-endian, the order written to disk / wire, and
  * **display order** — big-endian, the order shown to users (and used by RPCs,
    `hex` debug output, and `FromHex`).

Both `block::Hash` and `transaction::Hash` implement
`BytesInDisplayOrder<true>` — i.e. they reverse the bytes when going between
serialised and display order. This is consensus-critical: a hash printed/parsed
in the wrong endianness fails to match. We model the `REVERSED` parameter
explicitly and prove the reversal is an involution on both sides.

We model:
  * a `Hash` as a `List Nat` of length 32 (each byte is implicitly `< 256`),
  * the byte-array constructor (`From<[u8; 32]>`) as `fromBytes`,
  * the byte-array extractor (`From<Hash> for [u8; 32]`) as `toBytes`,
  * the wire format (`ZcashSerialize` / `ZcashDeserialize`) as
    `zcashSerialize` / `zcashDeserialize` (the deserializer length-checks),
  * the display-order reorientation as
    `bytesInDisplayOrder` / `fromBytesInDisplayOrder`, parameterised over a
    `REVERSED : Bool` flag matching the Rust trait's const generic.
  * the all-zero hash (the `Default` derive) as `zero`.

The basic newtype round-trip is `rfl` (it is the identity on a `List Nat`,
mirroring the fact that the Rust wrapper is a transparent newtype). The
display-order round-trip is **not** `rfl` when `REVERSED = true`: it relies on
`List.reverse` being an involution. We surface this asymmetry explicitly so the
"round-trip" claim is honest about which transformation is being tracked.
-/

namespace Zebra.HashRoundTrip

/-- The fixed hash width in bytes (the `32` in `[u8; 32]`).
Source: `zebra-chain/src/block/hash.rs:26` and
`zebra-chain/src/transaction/hash.rs:63`. -/
def HASH_BYTES : Nat := 32

/-- A 32-byte hash, modelled as a `List Nat` of length 32. The `IsHash`
predicate carries the length invariant that the Rust `[u8; 32]` type enforces
statically. -/
def IsHash (bs : List Nat) : Prop := bs.length = HASH_BYTES

/-! ## Newtype-level wrapping (transparent)

`block::Hash` and `transaction::Hash` are `pub struct Hash(pub [u8; 32])`, so
`From<[u8; 32]>` and `From<Hash> for [u8; 32]` are the obvious wrap/unwrap.
Mirroring this in Lean, the constructor and extractor are the identity on a
`List Nat`. The corresponding round-trip theorems are honestly `rfl` because
both sides definitionally reduce to the same list — the same way the Rust
newtype is a zero-cost wrapper. We name them `*_id` rather than `*_roundtrip`
to avoid overselling them as semantic results. -/

/-- `impl From<[u8; 32]> for Hash`: wraps the byte array.
Source: `block/hash.rs:82-86`, `transaction/hash.rs:93-97`. -/
def fromBytes (bs : List Nat) : List Nat := bs

/-- `impl From<Hash> for [u8; 32]`: unwraps the inner byte array.
Source: `block/hash.rs:29-31` (via `BytesInDisplayOrder::bytes_in_serialized_order`)
and `transaction/hash.rs:105-109` (`From<Hash> for [u8; 32]`). -/
def toBytes (h : List Nat) : List Nat := h

/-- The zero hash (the `Default` derive on `block::Hash`): 32 zero bytes.
Source: `block/hash.rs:25` (`#[cfg_attr(..., derive(Arbitrary, Default))]`). -/
def zero : List Nat := List.replicate HASH_BYTES 0

/-! ## Wire format (`ZcashSerialize` / `ZcashDeserialize`)

The `ZcashSerialize` impl for `Hash` writes the 32 raw bytes (`writer.write_all`
on `&self.0`); the `ZcashDeserialize` impl reads 32 raw bytes back into a fresh
`Hash`. Both directions are byte-identity at the buffer level. The deserializer
*does* fail on a short reader (it reads exactly 32 bytes), so the Lean model
length-checks the input. -/

/-- `impl ZcashSerialize for Hash`: write the 32 raw bytes verbatim.
Source: `block/hash.rs:122-127`, `transaction/hash.rs:186-190`. -/
def zcashSerialize (h : List Nat) : List Nat := toBytes h

/-- `impl ZcashDeserialize for Hash`: read 32 raw bytes; reject any other
length. Source: `block/hash.rs:129-133`, `transaction/hash.rs:192-196`. -/
def zcashDeserialize (bs : List Nat) : Option (List Nat) :=
  if bs.length = HASH_BYTES then some bs else none

/-! ## `BytesInDisplayOrder`

The Rust trait is `BytesInDisplayOrder<const SHOULD_REVERSE_BYTES_IN_DISPLAY_ORDER: bool,
const BYTE_LEN: usize = 32>`. Its default `bytes_in_display_order` /
`from_bytes_in_display_order` methods conditionally reverse the byte array
based on the `SHOULD_REVERSE_BYTES_IN_DISPLAY_ORDER` const generic.

  * `impl BytesInDisplayOrder<true> for block::Hash` (block/hash.rs:28)
  * `impl BytesInDisplayOrder<true> for transaction::Hash` (transaction/hash.rs:117)

Both hash types use `REVERSED = true`. We expose the boolean parameter
explicitly so the model can also describe a hypothetical `<false>` instance,
and so the no-op-vs-reverse cases are visible in the theorems.
Source: `zebra-chain/src/serialization/display_order.rs:9-37`. -/

/-- `bytes_in_display_order`: starting from serialised-order bytes, optionally
reverse them to obtain display-order bytes. Mirrors the trait's default impl.
Source: `serialization/display_order.rs:21-27`. -/
def bytesInDisplayOrder (REVERSED : Bool) (bs : List Nat) : List Nat :=
  if REVERSED then bs.reverse else bs

/-- `from_bytes_in_display_order`: starting from display-order bytes, optionally
reverse them back to serialised order, then build the hash from the wrapped
serialised-order bytes. Mirrors the trait's default impl.
Source: `serialization/display_order.rs:30-36`. -/
def fromBytesInDisplayOrder (REVERSED : Bool) (bs : List Nat) : List Nat :=
  if REVERSED then bs.reverse else bs

/-! ## Newtype-level theorems (honestly `rfl`)

These hold definitionally because `fromBytes` / `toBytes` are the identity on
the underlying `List Nat`. The Rust newtype is also a transparent wrapper, so
the claim "the wrapper round-trips on the inner array" is itself a statement
about identity. They are named to reflect that fact (`*_id`, `*_eq`) rather
than overselling them as non-trivial round-trips. -/

/-- **T1.** Newtype unwrap of a wrap is the identity:
`toBytes (fromBytes bs) = bs`. Holds by `rfl` because `Hash` is a transparent
newtype over `[u8; 32]`. -/
theorem toBytes_fromBytes_id (bs : List Nat) : toBytes (fromBytes bs) = bs := rfl

/-- **T2.** Newtype wrap of an unwrap is the identity:
`fromBytes (toBytes h) = h`. Holds by `rfl` because `Hash` is a transparent
newtype over `[u8; 32]`. -/
theorem fromBytes_toBytes_id (h : List Nat) : fromBytes (toBytes h) = h := rfl

/-- **T3.** `fromBytes` preserves length, so it preserves the `IsHash`
invariant. -/
theorem fromBytes_isHash (bs : List Nat) (h : IsHash bs) : IsHash (fromBytes bs) := h

/-- **T4.** `toBytes` preserves length: its output always has the same byte
count as the input hash. -/
theorem toBytes_length (h : List Nat) : (toBytes h).length = h.length := rfl

/-- **T5.** The newtype wrapper reflects byte-array equality:
`fromBytes bs₁ = fromBytes bs₂ → bs₁ = bs₂`. Holds by `rfl` because the wrapper
is the identity. Named to make clear it is a definitional fact about the
identity model, not a non-trivial injectivity result. -/
theorem fromBytes_eq_iff (bs₁ bs₂ : List Nat) (h : fromBytes bs₁ = fromBytes bs₂) :
    bs₁ = bs₂ := h

/-! ## The zero hash -/

/-- **T6.** The zero hash is well-defined: it has length 32. -/
theorem zero_length : zero.length = HASH_BYTES := by
  unfold zero
  exact List.length_replicate

/-- **T7.** The zero hash is a valid hash (satisfies `IsHash`). -/
theorem zero_isHash : IsHash zero := zero_length

/-- **T8.** Every byte of the zero hash is `0`. -/
theorem zero_bytes_all_zero (i : Nat) (h : i < HASH_BYTES) :
    zero[i]? = some 0 := by
  unfold zero
  rw [List.getElem?_replicate]
  simp [h]

/-! ## Wire-format theorems -/

/-- **T9.** `zcashSerialize` produces 32 bytes for a valid hash. -/
theorem zcashSerialize_length (h : List Nat) (hH : IsHash h) :
    (zcashSerialize h).length = HASH_BYTES := hH

/-- **T10.** Wire round-trip: `zcashDeserialize (zcashSerialize h) = some h`
for any valid hash. -/
theorem zcashSerialize_deserialize (h : List Nat) (hH : IsHash h) :
    zcashDeserialize (zcashSerialize h) = some h := by
  unfold zcashDeserialize zcashSerialize toBytes IsHash at *
  simp [hH]

/-- **T11.** The deserializer rejects any byte sequence whose length is not 32.
Models the Rust `read_32_bytes` failure on a short reader. -/
theorem zcashDeserialize_rejects_wrong_length (bs : List Nat)
    (h : bs.length ≠ HASH_BYTES) : zcashDeserialize bs = none := by
  unfold zcashDeserialize
  simp [h]

/-- **T12.** The deserializer's output, when it succeeds, is a valid hash. -/
theorem zcashDeserialize_isHash (bs : List Nat) (h : List Nat)
    (heq : zcashDeserialize bs = some h) : IsHash h := by
  unfold zcashDeserialize at heq
  split_ifs at heq with hcond
  simp only [Option.some.injEq] at heq
  unfold IsHash
  rw [← heq]
  exact hcond

/-! ## `BytesInDisplayOrder` theorems

These are the non-trivial round-trip results. With `REVERSED = false` they
reduce to `rfl`; with `REVERSED = true` they rely on `List.reverse_reverse`. -/

/-- **T13.** Display-order is a self-inverse: applying
`from_bytes_in_display_order` to the result of `bytes_in_display_order`
recovers the original bytes, for either value of the `REVERSED` flag.
For `REVERSED = true` this is `List.reverse_reverse`. -/
theorem fromBytesInDisplayOrder_bytesInDisplayOrder (REVERSED : Bool) (bs : List Nat) :
    fromBytesInDisplayOrder REVERSED (bytesInDisplayOrder REVERSED bs) = bs := by
  unfold fromBytesInDisplayOrder bytesInDisplayOrder
  cases REVERSED with
  | false => rfl
  | true => simp [List.reverse_reverse]

/-- **T14.** The dual direction: `bytes_in_display_order` of
`from_bytes_in_display_order` is also the identity. -/
theorem bytesInDisplayOrder_fromBytesInDisplayOrder (REVERSED : Bool) (bs : List Nat) :
    bytesInDisplayOrder REVERSED (fromBytesInDisplayOrder REVERSED bs) = bs := by
  unfold bytesInDisplayOrder fromBytesInDisplayOrder
  cases REVERSED with
  | false => rfl
  | true => simp [List.reverse_reverse]

/-- **T15.** Display-order conversion preserves the 32-byte length, regardless
of the `REVERSED` flag. -/
theorem bytesInDisplayOrder_length (REVERSED : Bool) (bs : List Nat) :
    (bytesInDisplayOrder REVERSED bs).length = bs.length := by
  unfold bytesInDisplayOrder
  cases REVERSED with
  | false => rfl
  | true => exact List.length_reverse

/-- **T16.** Display-order conversion preserves the `IsHash` invariant. -/
theorem bytesInDisplayOrder_isHash (REVERSED : Bool) (bs : List Nat) (h : IsHash bs) :
    IsHash (bytesInDisplayOrder REVERSED bs) := by
  unfold IsHash at *
  rw [bytesInDisplayOrder_length]
  exact h

/-- **T17.** The inverse direction also preserves length. -/
theorem fromBytesInDisplayOrder_length (REVERSED : Bool) (bs : List Nat) :
    (fromBytesInDisplayOrder REVERSED bs).length = bs.length := by
  unfold fromBytesInDisplayOrder
  cases REVERSED with
  | false => rfl
  | true => exact List.length_reverse

/-- **T18.** With `REVERSED = false`, `bytesInDisplayOrder` is the identity
(matches the trait's default behaviour when the flag is off). -/
theorem bytesInDisplayOrder_false (bs : List Nat) :
    bytesInDisplayOrder false bs = bs := rfl

/-- **T19.** With `REVERSED = true`, `bytesInDisplayOrder` is exactly
`List.reverse`. This is the case for both `block::Hash` and `transaction::Hash`.
-/
theorem bytesInDisplayOrder_true (bs : List Nat) :
    bytesInDisplayOrder true bs = bs.reverse := rfl

/-- **T20.** The zero hash is a fixed point of `bytesInDisplayOrder` for any
`REVERSED` flag — reversing 32 zero bytes still gives 32 zero bytes. -/
theorem bytesInDisplayOrder_zero (REVERSED : Bool) :
    bytesInDisplayOrder REVERSED zero = zero := by
  unfold bytesInDisplayOrder zero
  cases REVERSED with
  | false => rfl
  | true => exact List.reverse_replicate

/-! ## Specialisations for `block::Hash` and `transaction::Hash`

Both hash types are `impl BytesInDisplayOrder<true>`, so the relevant
display-order transforms reverse the bytes. We surface this as named
specialisations so the `REVERSED = true` semantics are explicit at the call
site, matching what consumers like `Display`, `Debug` and `FromHex` rely on.
Source: `block/hash.rs:28`, `transaction/hash.rs:117`. -/

namespace Block

/-- `block::Hash` reverses bytes when going to display order.
Source: `block/hash.rs:28`. -/
def bytesInDisplayOrder (h : List Nat) : List Nat :=
  Zebra.HashRoundTrip.bytesInDisplayOrder true h

/-- `block::Hash` reverses bytes when going from display order.
Source: `block/hash.rs:28`. -/
def fromBytesInDisplayOrder (bs : List Nat) : List Nat :=
  Zebra.HashRoundTrip.fromBytesInDisplayOrder true bs

/-- **T21.** Display-order round-trip for `block::Hash` is `List.reverse`
composed with itself — non-trivially `bs.reverse.reverse = bs`. -/
theorem displayOrder_roundtrip (bs : List Nat) :
    fromBytesInDisplayOrder (bytesInDisplayOrder bs) = bs := by
  unfold fromBytesInDisplayOrder bytesInDisplayOrder
  exact Zebra.HashRoundTrip.fromBytesInDisplayOrder_bytesInDisplayOrder true bs

/-- **T22.** `block::Hash`'s display-order conversion preserves length. -/
theorem displayOrder_length (bs : List Nat) :
    (bytesInDisplayOrder bs).length = bs.length := by
  unfold bytesInDisplayOrder
  exact Zebra.HashRoundTrip.bytesInDisplayOrder_length true bs

end Block

namespace Transaction

/-- `transaction::Hash` reverses bytes when going to display order.
Source: `transaction/hash.rs:117`. -/
def bytesInDisplayOrder (h : List Nat) : List Nat :=
  Zebra.HashRoundTrip.bytesInDisplayOrder true h

/-- `transaction::Hash` reverses bytes when going from display order.
Source: `transaction/hash.rs:117`. -/
def fromBytesInDisplayOrder (bs : List Nat) : List Nat :=
  Zebra.HashRoundTrip.fromBytesInDisplayOrder true bs

/-- **T23.** Display-order round-trip for `transaction::Hash` is
`List.reverse` composed with itself. -/
theorem displayOrder_roundtrip (bs : List Nat) :
    fromBytesInDisplayOrder (bytesInDisplayOrder bs) = bs := by
  unfold fromBytesInDisplayOrder bytesInDisplayOrder
  exact Zebra.HashRoundTrip.fromBytesInDisplayOrder_bytesInDisplayOrder true bs

/-- **T24.** `transaction::Hash`'s display-order conversion preserves length. -/
theorem displayOrder_length (bs : List Nat) :
    (bytesInDisplayOrder bs).length = bs.length := by
  unfold bytesInDisplayOrder
  exact Zebra.HashRoundTrip.bytesInDisplayOrder_length true bs

/-- **T25.** `block::Hash` and `transaction::Hash` use the same
display-order reorientation: both `<true>`, both reverse. This makes the
parity explicit at the Lean level. -/
theorem agrees_with_block_displayOrder (bs : List Nat) :
    bytesInDisplayOrder bs = Block.bytesInDisplayOrder bs := rfl

end Transaction

/-! ## Pipeline: wire ↔ display order

`FromHex for block::Hash` is `Self::from_bytes_in_display_order(&hash)` after
hex-decoding; `transaction::Hash::from_str` does
`bytes.reverse(); Hash(bytes)`. Composing the display-order conversion with
the wire format gives the user-facing parse/print pipeline. -/

/-- **T26.** Wire→display→wire round-trip: serialising a valid hash, taking
its display-order bytes, parsing them back from display order, and
deserialising recovers the original hash. This is the consensus-relevant
pipeline that `FromHex`/`Display` exposes. -/
theorem display_wire_roundtrip (REVERSED : Bool) (h : List Nat) (hH : IsHash h) :
    zcashDeserialize
        (fromBytesInDisplayOrder REVERSED (bytesInDisplayOrder REVERSED (zcashSerialize h)))
      = some h := by
  rw [fromBytesInDisplayOrder_bytesInDisplayOrder]
  exact zcashSerialize_deserialize h hH

end Zebra.HashRoundTrip
