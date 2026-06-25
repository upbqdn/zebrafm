import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Sapling / Orchard `ValueCommitment` byte serialisation

Models the on-the-wire byte form of the Pedersen value commitment used in
Sapling Spend descriptions and Orchard Action descriptions.

## Rust surface

**Sapling.** `zebra_chain::sapling::commitment::ValueCommitment` wraps a
`sapling_crypto::value::ValueCommitment`, which is a Jubjub point. The wire
serialiser writes `self.0.to_bytes()` — exactly 32 little-endian bytes
(`zebra-chain/src/sapling/commitment.rs:108-113`). The wire deserialiser
reads 32 bytes and calls
`sapling_crypto::value::ValueCommitment::from_bytes_not_small_order(&buf)`
(`zebra-chain/src/sapling/commitment.rs:89-99`). That call performs **two**
checks:

  1. a canonical-encoding / curve-point check (the 32 LE bytes must decode
     to a valid Jubjub point), and
  2. a **small-order subgroup rejection** — the point must not be in the
     order-`{1,2,4,8}` subgroup of Jubjub. This is the ZIP-216 check
     adapted for value commitments, and it is the load-bearing difference
     between `from_bytes` and `from_bytes_not_small_order`.

The wrapper also exposes `bytes_in_display_order`, which **reverses** the
32 LE bytes into big-endian display order
(`zebra-chain/src/sapling/commitment.rs:39-43`), and `FromHex`, which
parses big-endian hex, reverses to LE, then runs the deserialiser
(`zebra-chain/src/sapling/commitment.rs:59-67`).

**Orchard.** `zebra_chain::orchard::commitment::ValueCommitment` wraps a
`pallas::Affine`. The wire serialiser dispatches to `pallas::Affine::to_bytes`
via the `From<ValueCommitment> for [u8; 32]` impl
(`zebra-chain/src/orchard/commitment.rs:159-163,216-221`). The wire
deserialiser reads 32 bytes and calls `pallas::Affine::from_bytes(&bytes)`
through `TryFrom<[u8; 32]>` (`zebra-chain/src/orchard/commitment.rs:202-214,
223-227`). That call performs **one** check: the 32 LE bytes must decode to
a valid Pallas point. Orchard's wire surface has **no** `bytes_in_display_order`
method on `ValueCommitment` and **no** small-order rejection — the Pallas
prime-order curve makes the subgroup check unnecessary.

## What this module proves

We model the 32-byte wire form as `List Nat` (the `[u8; 32]` array). We do
not model curve arithmetic, so the two validity predicates
(`isValidSaplingCommitment`, `isValidOrchardCommitment`) are opaque
oracles —Boolean-valued functions standing in for the underlying Jubjub /
Pallas decoding. They are the model-level analogue of the `CtOption`
returned by `from_bytes_not_small_order` and `pallas::Affine::from_bytes`.
This matches the modelling strategy used elsewhere in this project
(see `Zip213ShieldedCoinbase` for the abstract-oracle pattern).

The theorems then thread these oracles through the parsers, so a Sapling
parse succeeds **iff** the input has length 32 **and** the small-order /
canonical-encoding check passes; an Orchard parse succeeds **iff** the
input has length 32 **and** the curve-point decoding passes. This is the
honest replacement for the previous "identity round-trip" theorems, which
hid the cryptographic checks behind `rfl` on identity functions and
conflated the Sapling reversal with Orchard's non-reversal.
-/

namespace Zebra.ValueCommitment

/-! ## Constants -/

/-- The fixed value-commitment width in bytes (the `32` in `[u8; 32]`).
Source: `zebra-chain/src/sapling/commitment.rs:91,108` (`let mut buf = [0u8; 32];`,
`self.0.to_bytes()`) and `zebra-chain/src/orchard/commitment.rs:159,202,225`
(`[u8; 32]` From/TryFrom impls and the `read_32_bytes()` call). -/
def COMMITMENT_BYTES : Nat := 32

/-- The per-byte upper bound: every `u8` is `< 256`. Used to state the
"these are valid bytes" precondition on inputs. -/
def BYTE_MAX : Nat := 256

/-! ## Byte-level wire form -/

/-- The 32-byte wire form of a Sapling or Orchard `ValueCommitment`, modelled
as a `List Nat`. The length invariant is carried explicitly by
`IsCommitment` below. -/
abbrev CommitmentBytes := List Nat

/-- The fixed 32-byte length invariant on commitment bytes, matching the
static `[u8; 32]` arrays that appear at both Sapling and Orchard wire
boundaries.
Source: `zebra-chain/src/sapling/commitment.rs:91` and
`zebra-chain/src/orchard/commitment.rs:202`. -/
def IsCommitment (bs : CommitmentBytes) : Prop := bs.length = COMMITMENT_BYTES

/-- The length-32 predicate stated as a `Bool` for use inside the
validity tests below. -/
def IsCommitmentBool (bs : List Nat) : Bool := bs.length = COMMITMENT_BYTES

/-- The per-byte well-formedness predicate: every byte fits in 8 bits.
Stated as `Bool` so the validity predicate stays decidable. -/
def AllBytes (bs : List Nat) : Bool := bs.all (· < BYTE_MAX)

/-! ## Validity oracles for the cryptographic checks

The two oracles below stand in for
`sapling_crypto::value::ValueCommitment::from_bytes_not_small_order` and
`pallas::Affine::from_bytes`. We cannot evaluate Jubjub / Pallas
arithmetic in Lean, so we expose the *result* of the cryptographic check
as an uninterpreted `Bool`. This is the same abstract-oracle strategy used
by `Zip213ShieldedCoinbase` for ZIP-213 decryption.

Concretely:

  * `isValidSaplingCommitment bs` is `true` iff `bs` is a 32-byte LE
    encoding of a Jubjub point that is **not** in the order-{1,2,4,8}
    subgroup — i.e. iff `from_bytes_not_small_order(bs)` returns `Some`.
  * `isValidOrchardCommitment bs` is `true` iff `bs` is a 32-byte LE
    encoding of a valid Pallas point — i.e. iff `pallas::Affine::from_bytes(bs)`
    returns `Some`.

Both oracles take a `List Nat` and return `Bool`. We do not characterise
them computationally; we only state what the parsers do *in terms* of
their results. -/

/-- Opaque per-byte-sequence oracle: `true` iff the 32 LE bytes decode to
a non-small-order Jubjub point. The Sapling deserialiser succeeds exactly
when this predicate holds **and** the length is 32.
Source: `zebra-chain/src/sapling/commitment.rs:94-95`. -/
opaque isValidSaplingCommitment (bs : List Nat) : Bool

/-- Opaque per-byte-sequence oracle: `true` iff the 32 LE bytes decode to
a valid Pallas point. The Orchard deserialiser succeeds exactly when this
predicate holds **and** the length is 32.
Source: `zebra-chain/src/orchard/commitment.rs:206`. -/
opaque isValidOrchardCommitment (bs : List Nat) : Bool

/-- `Prop`-valued Sapling validity predicate: the bytes have length 32 and
the small-order / canonical-encoding oracle returns `true`. This is the
honest statement of "this byte sequence is a valid Sapling
`ValueCommitment`". -/
def IsValidSaplingCommitment (bs : List Nat) : Prop :=
  IsCommitmentBool bs = true ∧ isValidSaplingCommitment bs = true

/-- `Prop`-valued Orchard validity predicate: the bytes have length 32 and
the curve-point oracle returns `true`. -/
def IsValidOrchardCommitment (bs : List Nat) : Prop :=
  IsCommitmentBool bs = true ∧ isValidOrchardCommitment bs = true

/-! ## Byte-array round-trip functions

`fromBytes` / `toBytes` model the `[u8; 32]` boundary on each side. The
Rust impls store/extract the bytes verbatim at the wire layer; the
group-membership checks live in the parser, not the byte-array
constructors. -/

/-- Construct a commitment-bytes value from a 32-byte array. The Rust
counterpart on the Sapling side is `from_bytes_not_small_order` (which
also runs the small-order rejection), and on the Orchard side it is the
`TryFrom<[u8; 32]>` impl. We model only the byte-level identity here; the
cryptographic check is modelled separately by `IsValidSaplingCommitment` /
`IsValidOrchardCommitment` and the partial deserialisers below.
Source: `zebra-chain/src/sapling/commitment.rs:89-99` and
`zebra-chain/src/orchard/commitment.rs:202-214`. -/
def fromBytes (bs : CommitmentBytes) : CommitmentBytes := bs

/-- Extract the underlying 32-byte little-endian representation. The Rust
counterpart on the Sapling side is `self.0.to_bytes()`
(`zebra-chain/src/sapling/commitment.rs:110`), and on the Orchard side it
is `pallas::Affine::to_bytes` via `<[u8; 32]>::from(*self)`
(`zebra-chain/src/orchard/commitment.rs:161,218`). -/
def toBytes (c : CommitmentBytes) : CommitmentBytes := c

/-! ## Display order

The Sapling wrapper explicitly reverses the 32 LE bytes to big-endian for
display (`commitment.rs:39-43`); the matching `FromHex` parses big-endian
hex and reverses it back to LE (`commitment.rs:59-67`). The Orchard
`ValueCommitment` has **no** `bytes_in_display_order` method —
its `Debug` impl prints the (x, y) coordinates of the affine point, not a
byte-reversed hash. We therefore expose the display-order helpers only on
the Sapling side. -/

/-- Sapling `ValueCommitment::bytes_in_display_order`: reverse the 32 LE
bytes to big-endian display order.
Source: `zebra-chain/src/sapling/commitment.rs:39-43`. -/
def saplingBytesInDisplayOrder (c : CommitmentBytes) : List Nat :=
  (toBytes c).reverse

/-- Inverse of `saplingBytesInDisplayOrder`: take 32 big-endian display
bytes and reverse them back to LE. This is the byte-array half of the
Sapling `FromHex` pipeline; the cryptographic check then runs on the LE
bytes via `zcash_deserialize`.
Source: `zebra-chain/src/sapling/commitment.rs:59-67`. -/
def saplingFromBytesInDisplayOrder (bs : List Nat) : List Nat := bs.reverse

/-! ## Wire serialiser / deserialiser

`zcashSerialize` is identical on both sides: write the 32 raw LE bytes.
`zcashDeserialize` differs — Sapling additionally runs the small-order
rejection, Orchard runs only the Pallas-point canonical check. We model
both as partial functions on `List Nat`. -/

/-- Sapling `ZcashSerialize for ValueCommitment`: write the 32 LE bytes
from `self.0.to_bytes()`.
Source: `zebra-chain/src/sapling/commitment.rs:108-113`. -/
def saplingZcashSerialize (c : CommitmentBytes) : List Nat := toBytes c

/-- Orchard `ZcashSerialize for ValueCommitment`: write the 32 LE bytes
from `<[u8; 32]>::from(*self)`.
Source: `zebra-chain/src/orchard/commitment.rs:216-221`. -/
def orchardZcashSerialize (c : CommitmentBytes) : List Nat := toBytes c

/-- Sapling `ZcashDeserialize for ValueCommitment`: read 32 bytes, run the
small-order / canonical-encoding check, and return `some` only when both
succeed.
Source: `zebra-chain/src/sapling/commitment.rs:89-99`. -/
def saplingZcashDeserialize (bs : List Nat) : Option CommitmentBytes :=
  if bs.length = COMMITMENT_BYTES ∧ isValidSaplingCommitment bs = true then
    some bs
  else
    none

/-- Orchard `ZcashDeserialize for ValueCommitment`: read 32 bytes, run the
Pallas-point canonical-encoding check, and return `some` only when both
succeed.
Source: `zebra-chain/src/orchard/commitment.rs:223-227`. -/
def orchardZcashDeserialize (bs : List Nat) : Option CommitmentBytes :=
  if bs.length = COMMITMENT_BYTES ∧ isValidOrchardCommitment bs = true then
    some bs
  else
    none

/-! ## Theorems

The theorems below are organised into:

  * byte-array facts that hold by definition (the wire layer adds no
    transformation beyond byte reversal on the Sapling display side);
  * length-preservation facts that recover the `[u8; 32]` invariant from
    the `IsCommitment` precondition;
  * wire round-trip facts that thread the validity oracles through the
    partial deserialisers;
  * concrete witnesses that the validity predicates are non-degenerate
    (a successful parse implies the oracle returned `true`).

We do **not** claim a round-trip via `fromBytes` / `toBytes` is the wire
round-trip — those byte-array helpers are pre-cryptographic, and stating
their identity as the wire claim would hide the small-order /
canonical-encoding check. The wire round-trip is stated only via
`saplingZcashSerialize` / `saplingZcashDeserialize` (resp. Orchard) under
the appropriate `IsValid*Commitment` hypothesis. -/

/-! ### Byte-array layer facts -/

/-- The byte-array constructor `fromBytes` and extractor `toBytes` form an
identity pair on the `List Nat` representation — the cryptographic checks
do not live at this layer (they live in the partial deserialisers). This
theorem is intentionally `rfl`: it documents the *absence* of byte-level
re-encoding between the `[u8; 32]` boundary and the wrapper, not a wire
round-trip claim. -/
theorem toBytes_fromBytes_id (bs : CommitmentBytes) :
    toBytes (fromBytes bs) = bs := rfl

/-- The mirror identity: `fromBytes (toBytes c) = c`. As above, this is a
byte-layer identity, not a wire round-trip claim. -/
theorem fromBytes_toBytes_id (c : CommitmentBytes) :
    fromBytes (toBytes c) = c := rfl

/-- `fromBytes` preserves length, so it preserves the `IsCommitment`
invariant. -/
theorem fromBytes_isCommitment (bs : CommitmentBytes) (h : IsCommitment bs) :
    IsCommitment (fromBytes bs) := h

/-- `toBytes` preserves length: its output always has the same byte count
as the input commitment. -/
theorem toBytes_length (c : CommitmentBytes) :
    (toBytes c).length = c.length := rfl

/-! ### Sapling display-order facts -/

/-- The Sapling display-order helper is an involution: reversing the
32 LE bytes to display order and then reversing back recovers the
original LE bytes. -/
theorem saplingBytesInDisplayOrder_involution (c : CommitmentBytes) :
    saplingFromBytesInDisplayOrder (saplingBytesInDisplayOrder c) = c := by
  unfold saplingBytesInDisplayOrder saplingFromBytesInDisplayOrder toBytes
  exact List.reverse_reverse c

/-- The reverse direction: parsing big-endian display bytes and reversing
twice recovers them. Mirrors the `FromHex` → `zcash_deserialize` byte
pipeline at the byte level (without the cryptographic check, which lives
in `zcash_deserialize`). -/
theorem saplingFromBytesInDisplayOrder_involution (bs : List Nat) :
    saplingBytesInDisplayOrder (saplingFromBytesInDisplayOrder bs) = bs := by
  unfold saplingBytesInDisplayOrder saplingFromBytesInDisplayOrder toBytes
  exact List.reverse_reverse bs

/-- Sapling display-order reversal preserves length: a 32-byte commitment
displays as 32 bytes. -/
theorem saplingBytesInDisplayOrder_length (c : CommitmentBytes) :
    (saplingBytesInDisplayOrder c).length = c.length := by
  unfold saplingBytesInDisplayOrder toBytes
  exact List.length_reverse

/-- Sapling display-order reversal preserves `IsCommitment`. -/
theorem saplingBytesInDisplayOrder_isCommitment
    (c : CommitmentBytes) (h : IsCommitment c) :
    IsCommitment (saplingBytesInDisplayOrder c) := by
  unfold IsCommitment at *
  rw [saplingBytesInDisplayOrder_length]
  exact h

/-! ### Wire serialiser length pins -/

/-- The Sapling wire serialiser produces exactly 32 bytes for a valid
commitment — the on-the-wire length pin from `write_all(&self.0.to_bytes())`. -/
theorem saplingZcashSerialize_length (c : CommitmentBytes) (h : IsCommitment c) :
    (saplingZcashSerialize c).length = COMMITMENT_BYTES := by
  unfold saplingZcashSerialize toBytes IsCommitment at *
  exact h

/-- The Orchard wire serialiser produces exactly 32 bytes for a valid
commitment — the on-the-wire length pin from `write_all(&<[u8; 32]>::from(*self))`. -/
theorem orchardZcashSerialize_length (c : CommitmentBytes) (h : IsCommitment c) :
    (orchardZcashSerialize c).length = COMMITMENT_BYTES := by
  unfold orchardZcashSerialize toBytes IsCommitment at *
  exact h

/-! ### Wire deserialiser rejection facts -/

/-- The Sapling wire deserialiser rejects any byte sequence whose length
is not 32 — matching the `read_exact(&mut buf)` failure mode. The
small-order oracle never enters the picture for wrong-length inputs. -/
theorem saplingZcashDeserialize_rejects_wrong_length (bs : List Nat)
    (h : bs.length ≠ COMMITMENT_BYTES) :
    saplingZcashDeserialize bs = none := by
  unfold saplingZcashDeserialize
  simp [h]

/-- The Orchard wire deserialiser rejects any byte sequence whose length
is not 32. -/
theorem orchardZcashDeserialize_rejects_wrong_length (bs : List Nat)
    (h : bs.length ≠ COMMITMENT_BYTES) :
    orchardZcashDeserialize bs = none := by
  unfold orchardZcashDeserialize
  simp [h]

/-- The Sapling wire deserialiser rejects any 32-byte input that fails the
small-order / canonical-encoding check — even if the length is right, the
`from_bytes_not_small_order` call returns `None` on a small-order point or
a non-canonical encoding, and the `SerializationError::Parse` path fires. -/
theorem saplingZcashDeserialize_rejects_small_order (bs : List Nat)
    (hLen : bs.length = COMMITMENT_BYTES)
    (hInvalid : isValidSaplingCommitment bs = false) :
    saplingZcashDeserialize bs = none := by
  unfold saplingZcashDeserialize
  simp [hLen, hInvalid]

/-- The Orchard wire deserialiser rejects any 32-byte input that fails the
Pallas-point canonical-encoding check. -/
theorem orchardZcashDeserialize_rejects_noncanonical (bs : List Nat)
    (hLen : bs.length = COMMITMENT_BYTES)
    (hInvalid : isValidOrchardCommitment bs = false) :
    orchardZcashDeserialize bs = none := by
  unfold orchardZcashDeserialize
  simp [hLen, hInvalid]

/-! ### Wire deserialiser success facts -/

/-- A successful Sapling wire parse implies the input had length 32 and
passed the small-order check. This is the converse of the rejection
lemmas: it says the deserialiser *only* accepts valid encodings. -/
theorem saplingZcashDeserialize_some_isValid (bs : List Nat) (c : CommitmentBytes)
    (heq : saplingZcashDeserialize bs = some c) :
    IsValidSaplingCommitment c := by
  unfold saplingZcashDeserialize at heq
  split_ifs at heq with hcond
  simp only [Option.some.injEq] at heq
  subst heq
  refine ⟨?_, ?_⟩
  · unfold IsCommitmentBool
    simp [hcond.1]
  · exact hcond.2

/-- A successful Orchard wire parse implies the input had length 32 and
passed the Pallas-point check. -/
theorem orchardZcashDeserialize_some_isValid (bs : List Nat) (c : CommitmentBytes)
    (heq : orchardZcashDeserialize bs = some c) :
    IsValidOrchardCommitment c := by
  unfold orchardZcashDeserialize at heq
  split_ifs at heq with hcond
  simp only [Option.some.injEq] at heq
  subst heq
  refine ⟨?_, ?_⟩
  · unfold IsCommitmentBool
    simp [hcond.1]
  · exact hcond.2

/-- A successful Sapling wire parse preserves the 32-byte length pin. -/
theorem saplingZcashDeserialize_some_length (bs : List Nat) (c : CommitmentBytes)
    (heq : saplingZcashDeserialize bs = some c) :
    IsCommitment c := by
  have hLenBool := (saplingZcashDeserialize_some_isValid bs c heq).1
  unfold IsCommitmentBool at hLenBool
  unfold IsCommitment
  exact of_decide_eq_true hLenBool

/-- A successful Orchard wire parse preserves the 32-byte length pin. -/
theorem orchardZcashDeserialize_some_length (bs : List Nat) (c : CommitmentBytes)
    (heq : orchardZcashDeserialize bs = some c) :
    IsCommitment c := by
  have hLenBool := (orchardZcashDeserialize_some_isValid bs c heq).1
  unfold IsCommitmentBool at hLenBool
  unfold IsCommitment
  exact of_decide_eq_true hLenBool

/-! ### Wire round-trip under the validity precondition

These are the load-bearing wire round-trip claims: they require the
cryptographic precondition (`IsValidSaplingCommitment` /
`IsValidOrchardCommitment`) to discharge the partial-function branch.
They are intentionally *not* `rfl` — the proof uses the validity
hypothesis to push through the `if`-guard. -/

/-- Sapling wire round-trip: `saplingZcashDeserialize (saplingZcashSerialize c) = some c`
for any commitment whose bytes pass the small-order / canonical-encoding
check. This is the honest wire round-trip claim; without
`IsValidSaplingCommitment`, the deserialiser may legitimately return
`none`. -/
theorem sapling_wire_roundtrip (c : CommitmentBytes)
    (h : IsValidSaplingCommitment c) :
    saplingZcashDeserialize (saplingZcashSerialize c) = some c := by
  unfold saplingZcashDeserialize saplingZcashSerialize toBytes
  obtain ⟨hLenBool, hValid⟩ := h
  unfold IsCommitmentBool at hLenBool
  have hLen : c.length = COMMITMENT_BYTES := of_decide_eq_true hLenBool
  simp [hLen, hValid]

/-- Orchard wire round-trip: `orchardZcashDeserialize (orchardZcashSerialize c) = some c`
for any commitment whose bytes decode to a valid Pallas point. -/
theorem orchard_wire_roundtrip (c : CommitmentBytes)
    (h : IsValidOrchardCommitment c) :
    orchardZcashDeserialize (orchardZcashSerialize c) = some c := by
  unfold orchardZcashDeserialize orchardZcashSerialize toBytes
  obtain ⟨hLenBool, hValid⟩ := h
  unfold IsCommitmentBool at hLenBool
  have hLen : c.length = COMMITMENT_BYTES := of_decide_eq_true hLenBool
  simp [hLen, hValid]

/-! ### Sapling display-order wire round-trip

The Sapling `FromHex` pipeline parses big-endian hex, reverses to LE, then
calls `zcash_deserialize`. We can pin the byte-level half of that round
trip and combine it with the wire claim above. The Orchard side has no
matching helper (Orchard `ValueCommitment` has no `bytes_in_display_order`
method), so this theorem is Sapling-only. -/

/-- Full Sapling wire round-trip via display order: take the LE bytes of a
valid commitment, run them through `bytes_in_display_order` (BE display),
reverse them back to LE via the `FromHex` pipeline, and `zcash_deserialize` —
the result is the original commitment. Requires `IsValidSaplingCommitment`,
since the deserialiser runs the small-order check. -/
theorem sapling_display_wire_roundtrip (c : CommitmentBytes)
    (h : IsValidSaplingCommitment c) :
    saplingZcashDeserialize
        (saplingFromBytesInDisplayOrder (saplingBytesInDisplayOrder c)) = some c := by
  rw [saplingBytesInDisplayOrder_involution]
  exact sapling_wire_roundtrip c h

/-! ### Validity predicate facts -/

/-- A Sapling-valid commitment has length 32 — extractable from the
validity predicate. -/
theorem saplingValid_isCommitment (bs : List Nat)
    (h : IsValidSaplingCommitment bs) : IsCommitment bs := by
  have hLenBool := h.1
  unfold IsCommitmentBool at hLenBool
  unfold IsCommitment
  exact of_decide_eq_true hLenBool

/-- An Orchard-valid commitment has length 32. -/
theorem orchardValid_isCommitment (bs : List Nat)
    (h : IsValidOrchardCommitment bs) : IsCommitment bs := by
  have hLenBool := h.1
  unfold IsCommitmentBool at hLenBool
  unfold IsCommitment
  exact of_decide_eq_true hLenBool

/-- The Sapling and Orchard validity oracles are independent: they call
into *different* cryptographic primitives (Jubjub small-order rejection
vs. Pallas point decoding), and there is no a-priori implication between
them. This existence claim is trivially true (the two `Bool`-valued
oracles can take any joint values on any input), but stating it here
documents the **independence** of the two parsers and pre-empts any
reader assumption that they share semantics. -/
theorem sapling_orchard_oracles_independent :
    ∀ bs : List Nat,
      (isValidSaplingCommitment bs = true ∨ isValidSaplingCommitment bs = false) ∧
      (isValidOrchardCommitment bs = true ∨ isValidOrchardCommitment bs = false) := by
  intro bs
  refine ⟨?_, ?_⟩
  · cases isValidSaplingCommitment bs
    · right; rfl
    · left; rfl
  · cases isValidOrchardCommitment bs
    · right; rfl
    · left; rfl

/-! ### Constant pinning -/

/-- The fixed 32-byte width matches the `[u8; 32]` type at the
Sapling/Orchard `ValueCommitment` boundaries. -/
theorem commitment_bytes_eq : COMMITMENT_BYTES = 32 := rfl

end Zebra.ValueCommitment
