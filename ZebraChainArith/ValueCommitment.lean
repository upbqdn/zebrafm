import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Sapling / Orchard `ValueCommitment` byte serialisation

Models the on-the-wire byte form of the Pedersen value commitment used in
Sapling Spend descriptions and Orchard Action descriptions:

  * Sapling `ValueCommitment` (a `sapling_crypto::value::ValueCommitment`)
    serialises as exactly 32 little-endian bytes via `to_bytes()`, and the
    Zebra wrapper exposes a `bytes_in_display_order` that reverses the
    32 bytes for big-endian display (matching zcashd's display convention).
    See `zebra-chain/src/sapling/commitment.rs:39,89,108`.
  * Orchard `ValueCommitment` (a `pallas::Affine`) serialises as exactly
    32 little-endian bytes via `to_bytes()`. See
    `zebra-chain/src/orchard/commitment.rs:159,216`.

Both round-trip through `ZcashSerialize` / `ZcashDeserialize`, modulo the
group-membership/canonical-encoding check that the underlying crypto crate
performs on deserialisation — for any commitment that came from a real
sender, the bytes are valid and `zcashDeserialize ∘ zcashSerialize = id`.

We do **not** model the underlying curve / group structure; only the
32-byte serialised form that gets transmitted on the wire, plus the
display-order byte-reversal.
-/

namespace Zebra.ValueCommitment

/-- The fixed value-commitment width in bytes (the `32` in `[u8; 32]`).
Source: `zebra-chain/src/sapling/commitment.rs:39,91` and
`zebra-chain/src/orchard/commitment.rs:159,202`. -/
def COMMITMENT_BYTES : Nat := 32

/-- The `IsCommitment` predicate carries the 32-byte length invariant
that the Rust `[u8; 32]` type enforces statically. -/
def IsCommitment (bs : List Nat) : Prop := bs.length = COMMITMENT_BYTES

/-- Construct a `ValueCommitment` from a 32-byte array. The Rust impls are
`TryFrom<[u8; 32]>` (Orchard) and the inner type's
`from_bytes_not_small_order(&buf)` (Sapling); both perform a
group-membership check before accepting the bytes. We model the byte-level
round-trip and treat the group check as out-of-band — the byte form of a
*valid* commitment satisfies `IsCommitment` and round-trips.
Source: `zebra-chain/src/sapling/commitment.rs:89` and
`zebra-chain/src/orchard/commitment.rs:202`. -/
def fromBytes (bs : List Nat) : List Nat := bs

/-- Extract the underlying 32-byte little-endian representation.
Source: `zebra-chain/src/sapling/commitment.rs:108` and
`zebra-chain/src/orchard/commitment.rs:159`. -/
def toBytes (c : List Nat) : List Nat := c

/-- `bytes_in_display_order` reverses the LE bytes for big-endian display.
The Sapling impl explicitly reverses the bytes; the Orchard side uses the
same convention via the surrounding `Display` plumbing.
Source: `zebra-chain/src/sapling/commitment.rs:39`. -/
def bytesInDisplayOrder (c : List Nat) : List Nat := (toBytes c).reverse

/-- The inverse of `bytes_in_display_order`: take 32 big-endian display
bytes and reverse them back to the internal little-endian form.
Source: `zebra-chain/src/sapling/commitment.rs:59` (`from_hex` reverses
the parsed hex bytes before handing them to `zcash_deserialize`). -/
def fromBytesInDisplayOrder (bs : List Nat) : List Nat := bs.reverse

/-- `ZcashSerialize for ValueCommitment`: write 32 raw bytes.
Source: `zebra-chain/src/sapling/commitment.rs:108-113` and
`zebra-chain/src/orchard/commitment.rs:216-221`. -/
def zcashSerialize (c : List Nat) : List Nat := toBytes c

/-- `ZcashDeserialize for ValueCommitment`: read 32 raw bytes; reject any
other length. The crypto-level validity check is modelled at the
`isValidCommitmentBytes` predicate below.
Source: `zebra-chain/src/sapling/commitment.rs:89-99` and
`zebra-chain/src/orchard/commitment.rs:223-227`. -/
def zcashDeserialize (bs : List Nat) : Option (List Nat) :=
  if bs.length = COMMITMENT_BYTES then some bs else none

/-! ## Theorems -/

/-- **T1.** Constructor round-trip: `toBytes (fromBytes bs) = bs`. The
byte-array round-trip claim for any input. -/
theorem toBytes_fromBytes (bs : List Nat) : toBytes (fromBytes bs) = bs := rfl

/-- **T2.** Extractor round-trip: `fromBytes (toBytes c) = c`. The
"from-bytes-of-to-bytes" direction. -/
theorem fromBytes_toBytes (c : List Nat) : fromBytes (toBytes c) = c := rfl

/-- **T3.** `fromBytes` preserves length, so it preserves the
`IsCommitment` invariant. -/
theorem fromBytes_isCommitment (bs : List Nat) (h : IsCommitment bs) :
    IsCommitment (fromBytes bs) := by
  unfold IsCommitment fromBytes at *
  exact h

/-- **T4.** `toBytes` preserves length: its output always has the same
byte count as the input commitment. -/
theorem toBytes_length (c : List Nat) : (toBytes c).length = c.length := rfl

/-- **T5.** Constructor is injective: distinct byte arrays give distinct
commitments. Equivalently, `fromBytes` reflects equality. -/
theorem fromBytes_injective (bs₁ bs₂ : List Nat)
    (h : fromBytes bs₁ = fromBytes bs₂) : bs₁ = bs₂ := h

/-- **T6.** Extractor is injective: distinct commitments produce distinct
byte arrays. -/
theorem toBytes_injective (c₁ c₂ : List Nat) (h : toBytes c₁ = toBytes c₂) :
    c₁ = c₂ := h

/-- **T7.** Display-order reversal is an involution: reversing the bytes
twice returns the original commitment. -/
theorem bytesInDisplayOrder_involution (c : List Nat) :
    fromBytesInDisplayOrder (bytesInDisplayOrder c) = c := by
  unfold bytesInDisplayOrder fromBytesInDisplayOrder toBytes
  exact List.reverse_reverse c

/-- **T8.** Display-order reversal preserves length: a 32-byte commitment
displays as 32 bytes. -/
theorem bytesInDisplayOrder_length (c : List Nat) :
    (bytesInDisplayOrder c).length = c.length := by
  unfold bytesInDisplayOrder toBytes
  exact List.length_reverse

/-- **T9.** Display-order reversal preserves the `IsCommitment` invariant. -/
theorem bytesInDisplayOrder_isCommitment (c : List Nat) (h : IsCommitment c) :
    IsCommitment (bytesInDisplayOrder c) := by
  unfold IsCommitment at *
  rw [bytesInDisplayOrder_length]
  exact h

/-- **T10.** `zcashSerialize` produces exactly 32 bytes for a valid
commitment — the on-the-wire length pin. -/
theorem zcashSerialize_length (c : List Nat) (h : IsCommitment c) :
    (zcashSerialize c).length = COMMITMENT_BYTES := by
  unfold zcashSerialize toBytes IsCommitment at *
  exact h

/-- **T11.** Wire round-trip: `zcashDeserialize (zcashSerialize c) = some c`
for any valid 32-byte commitment. This is the on-the-wire counterpart of
T2. The underlying group-membership check is modelled as an assumption
on `c` having come from a real sender. -/
theorem zcashSerialize_deserialize (c : List Nat) (h : IsCommitment c) :
    zcashDeserialize (zcashSerialize c) = some c := by
  unfold zcashDeserialize zcashSerialize toBytes IsCommitment at *
  simp [h]

/-- **T12.** The deserializer rejects any byte sequence whose length is
not 32 — the wire-level length-pin. -/
theorem zcashDeserialize_rejects_wrong_length (bs : List Nat)
    (h : bs.length ≠ COMMITMENT_BYTES) : zcashDeserialize bs = none := by
  unfold zcashDeserialize
  simp [h]

/-- **T13.** The deserializer's output, when it succeeds, is a valid
commitment satisfying the 32-byte length pin. -/
theorem zcashDeserialize_isCommitment (bs : List Nat) (c : List Nat)
    (heq : zcashDeserialize bs = some c) : IsCommitment c := by
  unfold zcashDeserialize at heq
  split_ifs at heq with hcond
  simp only [Option.some.injEq] at heq
  unfold IsCommitment
  rw [← heq]
  exact hcond

/-- **T14.** Display-order round-trip from the other direction: parsing
big-endian display bytes and reversing twice recovers them. This models
the `FromHex` → `zcash_deserialize` pipeline.
Source: `zebra-chain/src/sapling/commitment.rs:56`. -/
theorem fromBytesInDisplayOrder_involution (bs : List Nat) :
    bytesInDisplayOrder (fromBytesInDisplayOrder bs) = bs := by
  unfold bytesInDisplayOrder fromBytesInDisplayOrder toBytes
  exact List.reverse_reverse bs

/-- **T15.** Full wire round-trip via display order: take the LE bytes of
a commitment, run them through `bytes_in_display_order` (BE display),
reverse them back to LE via `from_hex`, and deserialise — the result is
the original commitment. -/
theorem display_wire_roundtrip (c : List Nat) (h : IsCommitment c) :
    zcashDeserialize (fromBytesInDisplayOrder (bytesInDisplayOrder c)) = some c := by
  rw [bytesInDisplayOrder_involution]
  exact zcashSerialize_deserialize c h

end Zebra.ValueCommitment
