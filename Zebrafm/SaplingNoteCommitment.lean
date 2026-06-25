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
reads 32 bytes and then **rejects non-canonical encodings** via
`ExtractedNoteCommitment::from_bytes(&buf).into_option()`:

```rust
impl ZcashDeserialize for sapling_crypto::note::ExtractedNoteCommitment {
    fn zcash_deserialize<R: io::Read>(mut reader: R) -> Result<Self, SerializationError> {
        let mut buf = [0u8; 32];
        reader.read_exact(&mut buf)?;

        let extracted_note_commitment: Option<sapling_crypto::note::ExtractedNoteCommitment> =
            sapling_crypto::note::ExtractedNoteCommitment::from_bytes(&buf).into_option();

        extracted_note_commitment.ok_or(SerializationError::Parse(
            "invalid ExtractedNoteCommitment bytes",
        ))
    }
}
```

Inside `sapling_crypto`, `ExtractedNoteCommitment(pub(super) bls12_381::Scalar)`
and `ExtractedNoteCommitment::from_bytes` calls `bls12_381::Scalar::from_repr`,
which in turn calls `bls12_381::Scalar::from_bytes`. That function:
  * reads the 32-byte input as a **little-endian** unsigned integer, and
  * returns `CtOption::none` unless the integer is **strictly less than
    the BLS12-381 scalar-field modulus** (= Jubjub base-field order
    `q_J = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001`,
    since `jubjub::Base = jubjub::Fq = bls12_381::Scalar`).

So the wire-format predicate is a **canonical-encoding** check on `[u8; 32]`,
not just a length check. The matching serializer (in
`OutputInTransactionV4::zcash_serialize` at `zebra-chain/src/sapling/output.rs:128`)
writes `cm_u.to_bytes()`, the canonical 32-byte LE field repr.

This module is the wire-format mirror of the Sapling **anchor** in
`OrchardAnchorBytes` (both wrap `jubjub::Base`); the difference is that
the anchor lives at the tree-root surface and this lives at the per-output
`cm_u` surface. The canonical-encoding predicate is the same.

We model:
  * a `NoteCommitment` as a `List Nat` of length 32 (each byte implicitly `< 256`),
  * the byte-array constructor as `fromBytes`,
  * the byte-array extractor as `toBytes`,
  * the on-the-wire deserialiser as a partial function `zcashDeserialize`
    that returns `none` on any non-canonical 32-byte input.

The previous version of this module modelled `zcashDeserialize` as a pure
length check and proved 15 theorems that were all `rfl`-trivial because
`fromBytes` and `toBytes` were both the identity. That overstated the
guarantees the chain layer actually provides: a 32-byte sequence whose
LE value is `≥ q_J` would have been "accepted" by the model but is
**rejected** by Rust. The current version fixes that by adding
`isCanonicalJubjubBase` and proving the round-trip / rejection behaviour
strictly under that predicate.
-/

namespace Zebra.SaplingNoteCommitment

/-! ## Constants -/

/-- The fixed Sapling note-commitment width in bytes
(`B^{[ℓ_{Sapling}_{Merkle}]}`), which is 32. The Rust deserializer reads
exactly `[0u8; 32]`.
Source: `zebra-chain/src/sapling/commitment.rs:117`
(`let mut buf = [0u8; 32];`). -/
def COMMITMENT_BYTES : Nat := 32

/-- The per-byte upper bound: every `u8` is `< 256`. Used inside the
canonical-encoding predicate so that the bytes-to-integer interpretation
is well-defined. -/
def BYTE_MAX : Nat := 256

/-- The Jubjub base-field order
`q_J = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001`.
Inside `sapling_crypto`, `ExtractedNoteCommitment(bls12_381::Scalar)` and
`bls12_381::Scalar::from_bytes` rejects 32 LE bytes whose unsigned value
is `≥ q_J`. Since `jubjub::Base = jubjub::Fq = bls12_381::Scalar`, this
is the same field-order constant used elsewhere in this crate for the
Sapling anchor (`OrchardAnchorBytes.JUBJUB_FIELD_ORDER`).
Source: `bls12_381` crate `src/scalar.rs` `MODULUS` constant; also
documented in the Zcash protocol spec §5.4.9.3 ("Encoding of Sapling
Notes"). -/
def JUBJUB_FIELD_ORDER : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-! ## Byte-list interpretation -/

/-- Little-endian interpretation of a byte list as a `Nat`: the head byte
is the least significant. For a `[u8; 32]` array `bs`, this equals
`bs[0] + bs[1] * 256 + bs[2] * 256^2 + ... + bs[31] * 256^31`. This
mirrors the way `bls12_381::Scalar::from_bytes` (`bls12_381` crate
`src/scalar.rs`) reads the four 8-byte little-endian limbs from
`bytes[0..8]`, `[8..16]`, `[16..24]`, `[24..32]` before checking
membership against the modulus. -/
def leValue : List Nat → Nat
  | []      => 0
  | b :: bs => b + BYTE_MAX * leValue bs

/-- The per-byte well-formedness predicate: every byte fits in 8 bits.
Stated as `Bool` so the canonical-encoding predicate stays decidable.
Bytes of an `[u8; 32]` array always satisfy this; this list-level
predicate just lifts that into the Lean model. -/
def AllBytes (bs : List Nat) : Bool := bs.all (· < BYTE_MAX)

/-- The length-32 predicate, stated as a `Bool` for use inside the
canonical-encoding tests. -/
def IsCommitmentBool (bs : List Nat) : Bool := bs.length = COMMITMENT_BYTES

/-! ## Note-commitment byte invariants -/

/-- A 32-byte Sapling note commitment, modelled as a `List Nat` of length 32.
The `IsNoteCommitment` predicate carries the length invariant that the Rust
`[u8; 32]` type enforces statically. It does **not** include the canonical-
encoding check — values produced by `cmu.to_bytes()` always satisfy it
trivially, but a raw 32-byte input from the wire need not.
Source: `zebra-chain/src/sapling/commitment.rs:117`. -/
def IsNoteCommitment (bs : List Nat) : Prop := bs.length = COMMITMENT_BYTES

/-- The canonical-encoding predicate: a 32-byte sequence canonically
encodes an `ExtractedNoteCommitment` iff it has length 32, every byte
fits in 8 bits, and its little-endian value is **strictly less than**
the Jubjub base-field order `q_J`. This is the consensus-critical check
the Rust deserializer performs via
`sapling_crypto::note::ExtractedNoteCommitment::from_bytes(&buf).into_option()`
at `zebra-chain/src/sapling/commitment.rs:120-126`. -/
def isCanonicalJubjubBase (bs : List Nat) : Bool :=
  IsCommitmentBool bs && AllBytes bs && (leValue bs < JUBJUB_FIELD_ORDER)

/-- `Prop`-valued canonical-encoding predicate, for use in theorem
statements that need a `Prop` hypothesis. Definitionally equal to
`isCanonicalJubjubBase bs = true`. -/
def IsCanonicalJubjubBase (bs : List Nat) : Prop :=
  isCanonicalJubjubBase bs = true

/-! ## Encoder / decoder -/

/-- `NoteCommitment::from(bytes)`: wrap a 32-byte array as a note
commitment. Mirrors the `From<[u8; 32]>` pattern used by `Nullifier` at
`zebra-chain/src/sapling/note/nullifiers.rs:13-17`, applied to the
Sapling `NoteCommitment`/`ExtractedNoteCommitment` 32-byte wrapper. This
constructor does **not** perform a canonical-encoding check at the model
level — the byte-level data is preserved verbatim. -/
def fromBytes (bs : List Nat) : List Nat := bs

/-- `<[u8; 32]>::from(commitment)`: extract the underlying 32-byte
canonical LE field repr. Mirrors `ExtractedNoteCommitment::to_bytes()`
(which calls `bls12_381::Scalar::to_repr()`, i.e. the canonical LE form)
as used at `zebra-chain/src/sapling/output.rs:128`. -/
def toBytes (c : List Nat) : List Nat := c

/-- The zero note commitment: 32 zero bytes. Matches the `[0u8; 32]`
buffer that the deserializer initializes at
`zebra-chain/src/sapling/commitment.rs:117`. It is also the canonical
encoding of the field element zero (`bls12_381::Scalar::zero().to_repr()`). -/
def zero : List Nat := List.replicate COMMITMENT_BYTES 0

/-- `ZcashSerialize for cm_u`: writes the 32 raw bytes from
`cm_u.to_bytes()`. The bytes returned by `to_bytes()` are by construction
the canonical 32-byte LE repr of a field element, so the serialiser's
output always satisfies `isCanonicalJubjubBase`.
Source: `zebra-chain/src/sapling/output.rs:128`
(`writer.write_all(&output.cm_u.to_bytes())?;`). -/
def zcashSerialize (c : List Nat) : List Nat := c

/-- `ZcashDeserialize for ExtractedNoteCommitment`: reads exactly 32
bytes and rejects any encoding that is not the canonical LE repr of a
field element. This **is** the wire-format check performed by Rust:

```rust
let extracted_note_commitment: Option<sapling_crypto::note::ExtractedNoteCommitment> =
    sapling_crypto::note::ExtractedNoteCommitment::from_bytes(&buf).into_option();
extracted_note_commitment.ok_or(SerializationError::Parse(
    "invalid ExtractedNoteCommitment bytes",
))
```

The previous version of this module accepted any 32-byte input, which
overstated the chain layer's contract.
Source: `zebra-chain/src/sapling/commitment.rs:115-127`. -/
def zcashDeserialize (bs : List Nat) : Option (List Nat) :=
  if isCanonicalJubjubBase bs then some bs else none

/-! ## Helper lemmas on `leValue` -/

/-- `leValue` of the empty list is `0`. -/
theorem leValue_nil : leValue [] = 0 := rfl

/-- `leValue` is recursive in the obvious little-endian way. -/
theorem leValue_cons (b : Nat) (bs : List Nat) :
    leValue (b :: bs) = b + BYTE_MAX * leValue bs := rfl

/-- `leValue` of any replicated-zero list is `0`. The all-zeros 32-byte
sequence is the canonical encoding of the field-zero element. -/
theorem leValue_replicate_zero (n : Nat) :
    leValue (List.replicate n 0) = 0 := by
  induction n with
  | zero => simp [leValue]
  | succ k ih =>
    rw [List.replicate_succ, leValue_cons, ih]
    simp

/-! ## Theorems on constants -/

/-- The 32-byte wire width is concretely 32. The Rust consensus code reads
`[u8; 32]` directly, so any future change to this constant is a
hard-fork-level event we want flagged at proof-check time. -/
theorem commitment_bytes_eq : COMMITMENT_BYTES = 32 := rfl

/-- The Jubjub base-field order is strictly less than `2^256`, so a
32-byte little-endian encoding can — concretely does, see
`all_ones_not_canonical` below — produce values that land outside the
field. This is exactly why the canonical-encoding check exists. -/
theorem jubjub_field_order_lt_wide_bound :
    JUBJUB_FIELD_ORDER < 2 ^ 256 := by decide

/-! ## Theorems: round-trip and length under `IsNoteCommitment` -/

/-- **Constructor round-trip.** `toBytes (fromBytes bs) = bs`. At the
byte level, the `From<[u8; 32]>` / `From<NoteCommitment> for [u8; 32]`
impls compose to the identity, since the inner state is just the bytes.
This holds unconditionally, including for non-canonical inputs — Rust
does *not* check canonicality on the `From<[u8; 32]>` constructor either
(only `from_bytes` / `zcash_deserialize` does). -/
theorem toBytes_fromBytes (bs : List Nat) : toBytes (fromBytes bs) = bs := rfl

/-- **Extractor round-trip.** `fromBytes (toBytes c) = c`. The dual to
the constructor round-trip; together they witness that the byte-level
state of the commitment is preserved through the byte-array conversions. -/
theorem fromBytes_toBytes (c : List Nat) : fromBytes (toBytes c) = c := rfl

/-- `fromBytes` preserves length, so it preserves the `IsNoteCommitment`
invariant. -/
theorem fromBytes_isNoteCommitment (bs : List Nat) (h : IsNoteCommitment bs) :
    IsNoteCommitment (fromBytes bs) := by
  unfold IsNoteCommitment fromBytes at *
  exact h

/-- `toBytes` preserves length: its output always has the same byte count
as the input commitment. -/
theorem toBytes_length (c : List Nat) : (toBytes c).length = c.length := rfl

/-! ## Theorems: zero / sentinel -/

/-- The zero commitment has the correct length (32 bytes). -/
theorem zero_length : zero.length = COMMITMENT_BYTES := by
  unfold zero
  exact List.length_replicate

/-- The zero commitment satisfies `IsNoteCommitment`. -/
theorem zero_isNoteCommitment : IsNoteCommitment zero := zero_length

/-- Every byte of the zero commitment is `0`. Mirrors the `[0u8; 32]`
buffer initialised at `zebra-chain/src/sapling/commitment.rs:117`, and
also matches the LE canonical repr of the field-zero element returned by
`bls12_381::Scalar::zero().to_repr()`. -/
theorem zero_bytes_all_zero (i : Nat) (h : i < COMMITMENT_BYTES) :
    zero[i]? = some 0 := by
  unfold zero
  rw [List.getElem?_replicate]
  simp [h]

/-! ## Theorems: canonical-encoding behaviour

These are the load-bearing claims that the previous version of this
module was missing. They mirror the structure of the Sapling anchor
proofs in `OrchardAnchorBytes`, which uses the *same* field-order. -/

/-- **Canonical-zero sentinel.** The 32-byte all-zeros sequence is
canonical: it has length 32, all bytes fit in `u8`, and its LE value is
`0 < q_J`. This is the encoding of `bls12_381::Scalar::zero()` and is
therefore accepted by the Rust deserializer. -/
theorem zero_isCanonical : IsCanonicalJubjubBase zero := by
  unfold IsCanonicalJubjubBase isCanonicalJubjubBase
  decide

/-- **Non-canonical witness (all-`0xff`).** The 32-byte all-`0xff`
sequence has LE value `2^256 - 1`, which exceeds `q_J`, so it fails the
canonical-encoding check. The Rust deserializer rejects it with
`SerializationError::Parse("invalid ExtractedNoteCommitment bytes")`.
This is a concrete witness that the predicate carves out a *strict*
subset of length-32 byte sequences. -/
theorem all_ones_not_canonical :
    ¬ IsCanonicalJubjubBase (List.replicate COMMITMENT_BYTES 255) := by
  unfold IsCanonicalJubjubBase isCanonicalJubjubBase
  decide

/-- **Length-32 non-canonical witness.** A 32-byte input that satisfies
`IsNoteCommitment` (length 32) but **fails** the canonical-encoding
check: 32 bytes whose first byte is `0` and last byte is `0xff`, encoding
the value `0xff * 2^248`, which exceeds `q_J`. This concretely shows
that `IsNoteCommitment` and `IsCanonicalJubjubBase` are not the same:
the old length-only model accepted bytes the real Rust code rejects. -/
theorem isNoteCommitment_strictly_weaker_than_canonical :
    ∃ bs : List Nat, IsNoteCommitment bs ∧ ¬ IsCanonicalJubjubBase bs := by
  refine ⟨List.replicate COMMITMENT_BYTES 255, ?_, ?_⟩
  · unfold IsNoteCommitment
    rw [List.length_replicate]
  · unfold IsCanonicalJubjubBase isCanonicalJubjubBase
    decide

/-- A canonical 32-byte input also satisfies the length invariant. The
canonical predicate strictly refines `IsNoteCommitment`. -/
theorem isCanonical_implies_isNoteCommitment (bs : List Nat)
    (h : IsCanonicalJubjubBase bs) : IsNoteCommitment bs := by
  unfold IsCanonicalJubjubBase isCanonicalJubjubBase at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold IsNoteCommitment IsCommitmentBool at *
  simpa using h.1.1

/-! ## Theorems: `zcashDeserialize` partiality -/

/-- **Acceptance on canonical input.** On a canonical 32-byte input,
`zcashDeserialize` returns `some bs`. This corresponds to the
`extracted_note_commitment.ok_or(...)` success branch in Rust:
`from_bytes(&buf).into_option()` returns `Some(_)` exactly when the
bytes are canonical. -/
theorem zcashDeserialize_canonical (bs : List Nat)
    (h : IsCanonicalJubjubBase bs) :
    zcashDeserialize bs = some bs := by
  unfold zcashDeserialize
  simp [show isCanonicalJubjubBase bs = true from h]

/-- **Rejection on non-canonical input.** Even for a length-32 input,
if the canonical-encoding check fails, `zcashDeserialize` returns
`none`. Mirrors the Rust `SerializationError::Parse("invalid
ExtractedNoteCommitment bytes")` error path at
`zebra-chain/src/sapling/commitment.rs:123-125`. -/
theorem zcashDeserialize_noncanonical (bs : List Nat)
    (h : ¬ IsCanonicalJubjubBase bs) :
    zcashDeserialize bs = none := by
  unfold zcashDeserialize
  have : isCanonicalJubjubBase bs = false := by
    cases hc : isCanonicalJubjubBase bs
    · rfl
    · exfalso; exact h hc
  simp [this]

/-- **Rejection on wrong length.** The deserialiser rejects any byte
sequence whose length is not 32, matching the `read_exact(&mut buf)`
failure mode at `zebra-chain/src/sapling/commitment.rs:118` (which
returns `Err(io::Error::UnexpectedEof)` before even attempting the
canonical-encoding check). -/
theorem zcashDeserialize_rejects_wrong_length (bs : List Nat)
    (h : bs.length ≠ COMMITMENT_BYTES) : zcashDeserialize bs = none := by
  apply zcashDeserialize_noncanonical
  intro hc
  unfold IsCanonicalJubjubBase isCanonicalJubjubBase IsCommitmentBool at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact h hc.1.1

/-- A successful deserialise result satisfies `IsNoteCommitment` (length
32). Combines the canonical-encoding check with the length component of
the predicate. -/
theorem zcashDeserialize_isNoteCommitment (bs : List Nat) (c : List Nat)
    (heq : zcashDeserialize bs = some c) : IsNoteCommitment c := by
  unfold zcashDeserialize at heq
  by_cases hC : isCanonicalJubjubBase bs
  · rw [if_pos hC] at heq
    simp only [Option.some.injEq] at heq
    subst heq
    unfold isCanonicalJubjubBase IsCommitmentBool at hC
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hC
    unfold IsNoteCommitment
    exact hC.1.1
  · rw [if_neg hC] at heq
    cases heq

/-- A successful deserialise result is canonical: if Rust accepts the
bytes, they pass the field-membership check. This is the dual to
`zcashDeserialize_canonical`. -/
theorem zcashDeserialize_some_canonical (bs : List Nat) (c : List Nat)
    (heq : zcashDeserialize bs = some c) : IsCanonicalJubjubBase c := by
  unfold zcashDeserialize at heq
  by_cases hC : isCanonicalJubjubBase bs
  · rw [if_pos hC] at heq
    simp only [Option.some.injEq] at heq
    subst heq
    exact hC
  · rw [if_neg hC] at heq
    cases heq

/-! ## Theorems: wire-format round-trip under canonicality -/

/-- **Wire serialiser length on canonical commitments.** The serialiser
produces exactly 32 bytes for any canonical commitment — pinning the
on-the-wire length, matching `cm_u.to_bytes()` writing 32 bytes via
`write_all` at `zebra-chain/src/sapling/output.rs:128`. The length pin
comes from canonicality (which subsumes length), not from a separate
hypothesis. -/
theorem zcashSerialize_length_of_canonical (c : List Nat)
    (hC : IsCanonicalJubjubBase c) :
    (zcashSerialize c).length = COMMITMENT_BYTES := by
  unfold zcashSerialize
  exact isCanonical_implies_isNoteCommitment c hC

/-- **Wire round-trip under canonicality.** A canonical commitment can
be serialised and parsed back to itself. This is the load-bearing
on-the-wire correctness claim: a value Rust would accept survives the
write/read cycle. -/
theorem zcashSerialize_deserialize (c : List Nat)
    (hC : IsCanonicalJubjubBase c) :
    zcashDeserialize (zcashSerialize c) = some c := by
  unfold zcashSerialize
  exact zcashDeserialize_canonical c hC

/-- The deserialiser is the left-inverse of the serialiser on every
canonical input. Combined with `zcashDeserialize_some_canonical`, this
means the wire format is *information-preserving* on its accepted
domain. -/
theorem zcashDeserialize_zcashSerialize_id (c : List Nat)
    (hC : IsCanonicalJubjubBase c) :
    zcashDeserialize (zcashSerialize c) = some c :=
  zcashSerialize_deserialize c hC

/-! ## Theorems: injectivity

These mirror the wire-level injectivity claims in `OrchardAnchorBytes`.
They are stated honestly: at the byte level the encoders are the
identity, and equality of bytes implies equality of (canonical)
commitments. These are *not* fictional — they reflect the consensus
property that distinct canonical 32-byte encodings denote distinct
field elements (canonical encoding is injective by construction). -/

/-- `fromBytes` is injective at the byte level: identical underlying
bytes denote the same commitment. This is consensus-relevant for the
`cm_u` field's role in the Sapling note commitment tree, where two
distinct `cmu` byte sequences must denote distinct leaves. -/
theorem fromBytes_injective (bs₁ bs₂ : List Nat)
    (h : fromBytes bs₁ = fromBytes bs₂) : bs₁ = bs₂ := h

/-- `toBytes` is injective at the byte level: distinct commitments yield
distinct LE field reprs. (`bls12_381::Scalar::to_repr` is a bijection
onto its image; we mirror that here at the byte-list level.) -/
theorem toBytes_injective (c₁ c₂ : List Nat)
    (h : toBytes c₁ = toBytes c₂) : c₁ = c₂ := h

/-- The wire serialiser is injective: distinct commitments yield
distinct wire encodings. This is just `toBytes_injective` lifted to
the wire surface. -/
theorem zcashSerialize_injective (c₁ c₂ : List Nat)
    (heq : zcashSerialize c₁ = zcashSerialize c₂) : c₁ = c₂ := by
  unfold zcashSerialize at heq
  exact heq

end Zebra.SaplingNoteCommitment
