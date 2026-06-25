import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Sapling NoteCommitment round-trip from
`zebra-chain/src/sapling/commitment.rs` and
`zebra-chain/src/sapling/note.rs`

The Sapling `NoteCommitment` (specifically the `ExtractedNoteCommitment` u-coordinate
serialized on the wire) is a 32-byte commitment to a note. It is the `cm_u` field
of the `Output` description, of type `B^{[ℓ_{Sapling}_{Merkle}]}` per protocol
specification §7.4, i.e. exactly 32 bytes.

```rust
// zebra-chain/src/sapling/output.rs:33
pub cm_u: sapling_crypto::note::ExtractedNoteCommitment,
```

The `ZcashDeserialize` impl in `zebra-chain/src/sapling/commitment.rs:115-127`
reads exactly 32 bytes:

```rust
impl ZcashDeserialize for sapling_crypto::note::ExtractedNoteCommitment {
    fn zcash_deserialize<R: io::Read>(mut reader: R) -> Result<Self, SerializationError> {
        let mut buf = [0u8; 32];
        reader.read_exact(&mut buf)?;
        ...
    }
}
```

The matching serializer (in `OutputInTransactionV4::zcash_serialize` at
`zebra-chain/src/sapling/output.rs:128`) writes `cm_u.to_bytes()`, which is
exactly 32 bytes.

This is structurally identical to the `Nullifier` type
(`pub struct Nullifier(pub HexDebug<[u8; 32]>);` at `note/nullifiers.rs:11`):
a 32-byte newtype with byte-array `From` / `Into` round-trips, and is *distinct*
from `ValueCommitment` (which commits to value via a Jubjub point, not a note).

We model:
  * a `NoteCommitment` as a `List Nat` of length 32 (each byte implicitly `< 256`),
  * the byte-array constructor as `fromBytes`,
  * the byte-array extractor as `toBytes`,
  * the wire serialiser/deserialiser as the identity / length-checked identity.

We prove byte-array round-trip in both directions, length preservation,
injectivity, and that the wire format is exactly 32 bytes.
-/

namespace Zebra.SaplingNoteCommitment

/-- The fixed Sapling note-commitment width in bytes (`B^{[ℓ_{Sapling}_{Merkle}]}`),
which is 32. The Rust deserializer reads exactly `[0u8; 32]`.
Source: `zebra-chain/src/sapling/commitment.rs:117` (`let mut buf = [0u8; 32];`). -/
def COMMITMENT_BYTES : Nat := 32

/-- A 32-byte Sapling note commitment, modelled as a `List Nat` of length 32.
The `IsNoteCommitment` predicate carries the length invariant that the Rust
`[u8; 32]` type enforces statically.
Source: `zebra-chain/src/sapling/commitment.rs:117`. -/
def IsNoteCommitment (bs : List Nat) : Prop := bs.length = COMMITMENT_BYTES

/-- `NoteCommitment::from(bytes)`: wrap a 32-byte array as a note commitment.
Mirrors the `From<[u8; 32]>` pattern used by `Nullifier` at
`zebra-chain/src/sapling/note/nullifiers.rs:13-17`, applied to the Sapling
`NoteCommitment`/`ExtractedNoteCommitment` 32-byte wrapper. -/
def fromBytes (bs : List Nat) : List Nat := bs

/-- `<[u8; 32]>::from(commitment)`: extract the underlying 32-byte array.
Mirrors the dual `From<Nullifier> for [u8; 32]` at
`zebra-chain/src/sapling/note/nullifiers.rs:19-23` and the
`ExtractedNoteCommitment::to_bytes()` call used at
`zebra-chain/src/sapling/output.rs:128`. -/
def toBytes (c : List Nat) : List Nat := c

/-- The zero note commitment: 32 zero bytes. Matches the `[0u8; 32]` buffer
that the deserializer initializes at `zebra-chain/src/sapling/commitment.rs:117`. -/
def zero : List Nat := List.replicate COMMITMENT_BYTES 0

/-- `ZcashSerialize for cm_u`: writes the 32 raw bytes from `cm_u.to_bytes()`.
Source: `zebra-chain/src/sapling/output.rs:128`
(`writer.write_all(&output.cm_u.to_bytes())?;`). -/
def zcashSerialize (c : List Nat) : List Nat := c

/-- `ZcashDeserialize for ExtractedNoteCommitment`: reads exactly 32 bytes.
The validity check on `LEOS2IP_{256}(cmu) < q_J` is a *consensus* rule that
lives downstream of the 32-byte length check, so at the serialisation layer
we model only the length check.
Source: `zebra-chain/src/sapling/commitment.rs:115-127`. -/
def zcashDeserialize (bs : List Nat) : Option (List Nat) :=
  if bs.length = COMMITMENT_BYTES then some bs else none

/-! ## Theorems -/

/-- **T1.** Constructor round-trip: `toBytes (fromBytes bs) = bs`. The
"to bytes of from bytes" direction — wrapping then unwrapping returns the
original byte array. -/
theorem toBytes_fromBytes (bs : List Nat) : toBytes (fromBytes bs) = bs := rfl

/-- **T2.** Extractor round-trip: `fromBytes (toBytes c) = c`. The "from
bytes of to bytes" direction — unwrapping then wrapping returns the original
commitment. -/
theorem fromBytes_toBytes (c : List Nat) : fromBytes (toBytes c) = c := rfl

/-- **T3.** `fromBytes` preserves length, so it preserves the
`IsNoteCommitment` invariant. -/
theorem fromBytes_isNoteCommitment (bs : List Nat) (h : IsNoteCommitment bs) :
    IsNoteCommitment (fromBytes bs) := by
  unfold IsNoteCommitment fromBytes at *
  exact h

/-- **T4.** `toBytes` preserves length: its output always has the same byte
count as the input commitment. -/
theorem toBytes_length (c : List Nat) : (toBytes c).length = c.length := rfl

/-- **T5.** `fromBytes` is injective: distinct byte arrays give distinct
commitments. The byte-array constructor reflects equality. -/
theorem fromBytes_injective (bs₁ bs₂ : List Nat)
    (h : fromBytes bs₁ = fromBytes bs₂) : bs₁ = bs₂ := h

/-- **T6.** `toBytes` is injective: distinct commitments give distinct byte
arrays. The byte-array extractor reflects equality. -/
theorem toBytes_injective (c₁ c₂ : List Nat)
    (h : toBytes c₁ = toBytes c₂) : c₁ = c₂ := h

/-- **T7.** The zero commitment has the correct length (32 bytes). -/
theorem zero_length : zero.length = COMMITMENT_BYTES := by
  unfold zero
  exact List.length_replicate

/-- **T8.** The zero commitment satisfies `IsNoteCommitment`. -/
theorem zero_isNoteCommitment : IsNoteCommitment zero := zero_length

/-- **T9.** Every byte of the zero commitment is `0`. Mirrors the
`[0u8; 32]` buffer initialised at
`zebra-chain/src/sapling/commitment.rs:117`. -/
theorem zero_bytes_all_zero (i : Nat) (h : i < COMMITMENT_BYTES) :
    zero[i]? = some 0 := by
  unfold zero
  rw [List.getElem?_replicate]
  simp [h]

/-- **T10.** The wire serialiser produces 32 bytes for a valid note commitment
— this pins the on-the-wire length, matching `cm_u.to_bytes()` writing 32
bytes via `write_all` at `zebra-chain/src/sapling/output.rs:128`. -/
theorem zcashSerialize_length (c : List Nat) (hC : IsNoteCommitment c) :
    (zcashSerialize c).length = COMMITMENT_BYTES := by
  unfold zcashSerialize IsNoteCommitment at *
  exact hC

/-- **T11.** Wire round-trip: `zcashDeserialize (zcashSerialize c) = some c`
for any valid 32-byte commitment. This is the on-the-wire counterpart of T2. -/
theorem zcashSerialize_deserialize (c : List Nat) (hC : IsNoteCommitment c) :
    zcashDeserialize (zcashSerialize c) = some c := by
  unfold zcashDeserialize zcashSerialize IsNoteCommitment at *
  simp [hC]

/-- **T12.** The deserialiser rejects any byte sequence whose length is not
32, matching the `read_exact(&mut buf)` failure mode at
`zebra-chain/src/sapling/commitment.rs:118`. -/
theorem zcashDeserialize_rejects_wrong_length (bs : List Nat)
    (h : bs.length ≠ COMMITMENT_BYTES) : zcashDeserialize bs = none := by
  unfold zcashDeserialize
  simp [h]

/-- **T13.** The deserialiser's output, when it succeeds, is a valid note
commitment (32 bytes). -/
theorem zcashDeserialize_isNoteCommitment (bs : List Nat) (c : List Nat)
    (heq : zcashDeserialize bs = some c) : IsNoteCommitment c := by
  unfold zcashDeserialize at heq
  split_ifs at heq with hcond
  simp only [Option.some.injEq] at heq
  unfold IsNoteCommitment
  rw [← heq]
  exact hcond

/-- **T14.** The deserialiser is the left-inverse of the serialiser on every
valid input: writing and reading back is the identity on valid commitments.
Combined with T13, this means the wire format is *information-preserving* and
the layer adds no padding/transformation beyond the 32-byte length check. -/
theorem zcashDeserialize_zcashSerialize_id (c : List Nat) (hC : IsNoteCommitment c) :
    zcashDeserialize (zcashSerialize c) = some c :=
  zcashSerialize_deserialize c hC

/-- **T15.** Distinction from `ValueCommitment`: the note commitment wire
format is a fixed 32 bytes regardless of the underlying note's payload. In
particular, two distinct 32-byte commitments cannot share a single wire
encoding (injectivity of `zcashSerialize` on valid inputs). -/
theorem zcashSerialize_injective (c₁ c₂ : List Nat)
    (heq : zcashSerialize c₁ = zcashSerialize c₂) : c₁ = c₂ := by
  unfold zcashSerialize at heq
  exact heq

end Zebra.SaplingNoteCommitment
