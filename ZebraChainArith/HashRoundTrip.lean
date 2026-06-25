import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Hash round-trip from `zebra-chain/src/block/hash.rs` and
`zebra-chain/src/transaction/hash.rs`

`block::Hash` and `transaction::Hash` are both 32-byte newtypes over `[u8; 32]`:

```rust
pub struct Hash(pub [u8; 32]);
```

Their `From<[u8; 32]>` / `Into<[u8; 32]>` conversions, as well as the
`bytes_in_serialized_order` / `from_bytes_in_serialized_order` pair from the
`BytesInDisplayOrder` impl, simply forward to the wrapped array. The Zcash
`zcash_serialize` / `zcash_deserialize` impls likewise write/read 32 raw bytes.

We model:
  * a `Hash` as a `List Nat` of length 32 (each byte is implicitly `< 256`),
  * the byte-array constructor as `fromBytes`,
  * the byte-array extractor as `toBytes`,
  * the all-zero hash (the `Default` impl) as `zero`.

We prove byte-array round-trip in both directions, length preservation, and
that the zero hash is well-defined.
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

/-- `Hash::from(bytes)` and `from_bytes_in_serialized_order`: the constructor
simply wraps the `[u8; 32]`.
Source: `zebra-chain/src/block/hash.rs:33` and
`zebra-chain/src/transaction/hash.rs:93,122`. -/
def fromBytes (bs : List Nat) : List Nat := bs

/-- `<[u8; 32]>::from(hash)` and `bytes_in_serialized_order`: the extractor
unwraps the inner `[u8; 32]`.
Source: `zebra-chain/src/block/hash.rs:29` and
`zebra-chain/src/transaction/hash.rs:105,118`. -/
def toBytes (h : List Nat) : List Nat := h

/-- The zero hash (the `Default` derive on `block::Hash`): 32 zero bytes.
Source: `zebra-chain/src/block/hash.rs:25` (the `Default` derive). -/
def zero : List Nat := List.replicate HASH_BYTES 0

/-- `ZcashSerialize for Hash` writes the 32 raw bytes; `ZcashDeserialize`
reads 32 raw bytes back into a fresh `Hash`. Together they are the identity
on the underlying byte array.
Source: `zebra-chain/src/block/hash.rs:122,129` and
`zebra-chain/src/transaction/hash.rs:186,192`. -/
def zcashSerialize (h : List Nat) : List Nat := h

def zcashDeserialize (bs : List Nat) : Option (List Nat) :=
  if bs.length = HASH_BYTES then some bs else none

/-! ## Theorems -/

/-- **T1.** Constructor round-trip: `toBytes (fromBytes bs) = bs`. This is
the byte-array round-trip claim for any input. -/
theorem toBytes_fromBytes (bs : List Nat) : toBytes (fromBytes bs) = bs := rfl

/-- **T2.** Extractor round-trip: `fromBytes (toBytes h) = h`. The "from
bytes of to bytes" direction the prompt asks for. -/
theorem fromBytes_toBytes (h : List Nat) : fromBytes (toBytes h) = h := rfl

/-- **T3.** `fromBytes` preserves length, so it preserves the `IsHash`
invariant. -/
theorem fromBytes_isHash (bs : List Nat) (h : IsHash bs) : IsHash (fromBytes bs) := by
  unfold IsHash fromBytes at *
  exact h

/-- **T4.** `toBytes` preserves length: its output always has the same byte
count as the input hash. -/
theorem toBytes_length (h : List Nat) : (toBytes h).length = h.length := rfl

/-- **T5.** Constructor is injective: distinct byte arrays give distinct
hashes. (Equivalently, `fromBytes` reflects equality.) -/
theorem fromBytes_injective (bs₁ bs₂ : List Nat) (h : fromBytes bs₁ = fromBytes bs₂) :
    bs₁ = bs₂ := h

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

/-- **T9.** `zcashSerialize` produces 32 bytes for a valid hash. -/
theorem zcashSerialize_length (h : List Nat) (hH : IsHash h) :
    (zcashSerialize h).length = HASH_BYTES := by
  unfold zcashSerialize IsHash at *
  exact hH

/-- **T10.** Wire round-trip: `zcashDeserialize (zcashSerialize h) = some h`
for any valid hash. This is the on-the-wire counterpart of T2. -/
theorem zcashSerialize_deserialize (h : List Nat) (hH : IsHash h) :
    zcashDeserialize (zcashSerialize h) = some h := by
  unfold zcashDeserialize zcashSerialize IsHash at *
  simp [hH]

/-- **T11.** The deserializer rejects any byte sequence whose length is not 32. -/
theorem zcashDeserialize_rejects_wrong_length (bs : List Nat) (h : bs.length ≠ HASH_BYTES) :
    zcashDeserialize bs = none := by
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

end Zebra.HashRoundTrip
