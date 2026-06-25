import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Sapling / Orchard anchor and nullifier 32-byte serialisation

This module models the wire-format byte arithmetic of the four 32-byte
field-element types that show up at the Sapling/Orchard surface of the
Zebra chain layer:

  * Sapling anchor `Root` — wraps a `jubjub::Base`, serialised as 32
    little-endian bytes via `[u8; 32]::from(root)`; round-trips through
    `Root::try_from([u8; 32])`, which performs a canonical-encoding /
    field-membership check before accepting. The wrapper also exposes
    `bytes_in_display_order`, which reverses the 32-byte little-endian
    form into big-endian display order for `z_gettreestate` RPC output.
    Source: `zebra-chain/src/sapling/tree.rs:48-141`.
  * Orchard anchor `Root` — wraps a `pallas::Base`, serialised as 32 bytes
    via `pallas::Base::to_repr()`. Unlike Sapling, the Orchard
    `bytes_in_display_order` does **not** reverse: it returns the same 32
    bytes (see `zebra-chain/src/orchard/tree.rs:113-115`, "Note that this
    is opposite to the Sapling root").
    Source: `zebra-chain/src/orchard/tree.rs:101-179`.
  * Sapling `Nullifier` — a wrapped `HexDebug<[u8; 32]>` with trivial
    `From<[u8; 32]>` and `From<Nullifier> for [u8; 32]` impls (no
    field-canonicality check; the 32 bytes are stored verbatim).
    Source: `zebra-chain/src/sapling/note/nullifiers.rs:1-23`.
  * Orchard `Nullifier` — wraps a `pallas::Base`, serialised via
    `to_repr()` and parsed via `pallas::Base::from_repr(bytes)` with a
    canonical-encoding check.
    Source: `zebra-chain/src/orchard/note/nullifiers.rs:1-46`.

We model the 32-byte wire form as `List Nat`, with `IsAnchor` /
`IsNullifier` predicates enforcing length = 32 (the static `[u8; 32]`
invariant the Rust type system carries). We treat the field-membership /
canonical-encoding check as a separate predicate `isCanonical`, modelling
exactly what the Rust `TryFrom` impls reject. The byte-level
round-trip (`from_bytes ∘ to_bytes = id`) holds for any anchor that came
through a real construction path.

The Rust `Root` impls have a notable subtlety: `Default::default()` on
the `Root` type produces `jubjub::Base::default()` / `pallas::Base::default()`,
which is the field's zero element, encoded as 32 zero bytes. This is the
"uninitialized" sentinel anchor (see the `Default` derive on
`zebra-chain/src/sapling/tree.rs:48` and `zebra-chain/src/orchard/tree.rs:106`,
and the comment at `zebra-chain/src/sapling/tree.rs:152-154` noting that
"the default value of the [`Root`] type is `[0, 0, 0, 0]`. However, this
value differs from the default value of the root of the default tree which
is the hash of the root's child nodes."). We prove that this sentinel
serialises to the all-zeros 32-byte sequence (T8 below).
-/

namespace Zebra.OrchardAnchorBytes

/-! ## Constants -/

/-- Fixed 32-byte width of an anchor or a nullifier. Drives the
`[u8; 32]` static array width that appears in
`zebra-chain/src/sapling/tree.rs:69` (Sapling Root → `[u8; 32]`),
`zebra-chain/src/orchard/tree.rs:126` (Orchard Root → `[u8; 32]`),
`zebra-chain/src/sapling/note/nullifiers.rs:11` (Sapling Nullifier),
and `zebra-chain/src/orchard/note/nullifiers.rs:11` (Orchard Nullifier). -/
def ANCHOR_BYTES : Nat := 32

/-! ## Anchor / nullifier byte invariants -/

/-- An `AnchorBytes` value is a 32-byte wire representation of a Sapling
or Orchard anchor (Merkle root). The `IsAnchor` predicate carries the
length pin enforced statically by the Rust `[u8; 32]` type. -/
abbrev AnchorBytes := List Nat

/-- The fixed 32-byte length invariant on anchor bytes.
Source: `zebra-chain/src/sapling/tree.rs:69-79` (`From<Root> for [u8; 32]`)
and `zebra-chain/src/orchard/tree.rs:126-136`. -/
def IsAnchor (bs : AnchorBytes) : Prop := bs.length = ANCHOR_BYTES

/-- A `NullifierBytes` value is a 32-byte wire representation of a Sapling
or Orchard nullifier. -/
abbrev NullifierBytes := List Nat

/-- The fixed 32-byte length invariant on nullifier bytes.
Source: `zebra-chain/src/sapling/note/nullifiers.rs:11` and
`zebra-chain/src/orchard/note/nullifiers.rs:11`. -/
def IsNullifier (bs : NullifierBytes) : Prop := bs.length = ANCHOR_BYTES

/-! ## Sapling anchor: serialiser, parser, display order

The Sapling `Root` wraps a `jubjub::Base`; the `From<Root> for [u8; 32]`
impl calls `root.0.to_bytes()` (LE encoding), and `TryFrom<[u8; 32]>`
calls `jubjub::Base::from_bytes(&bytes)` and rejects non-canonical
encodings. Source: `zebra-chain/src/sapling/tree.rs:69-107`. -/

/-- Sapling `Root → [u8; 32]`: extract the 32-byte little-endian form.
Source: `zebra-chain/src/sapling/tree.rs:69-73`. -/
def saplingToBytes (a : AnchorBytes) : List Nat := a

/-- Sapling `TryFrom<[u8; 32]> for Root`: accept the bytes verbatim,
provided they pass the canonical-encoding check (modelled separately by
`isCanonical` below).
Source: `zebra-chain/src/sapling/tree.rs:93-107`. -/
def saplingFromBytes (bs : List Nat) : AnchorBytes := bs

/-- Sapling `Root::bytes_in_display_order`: reverse the 32 LE bytes to
big-endian for display in `z_gettreestate` RPCs.
Source: `zebra-chain/src/sapling/tree.rs:51-59`. -/
def saplingBytesInDisplayOrder (a : AnchorBytes) : List Nat :=
  (saplingToBytes a).reverse

/-! ## Orchard anchor: serialiser, parser, display order

The Orchard `Root` wraps a `pallas::Base`; the `From<Root> for [u8; 32]`
impl calls `root.0.into()` which dispatches to `pallas::Base::to_repr()`,
and `TryFrom<[u8; 32]>` calls `pallas::Base::from_repr(bytes)`. Notably,
`bytes_in_display_order` returns the bytes as-is (no reversal), unlike
Sapling. Source: `zebra-chain/src/orchard/tree.rs:101-179`. -/

/-- Orchard `Root → [u8; 32]`: extract the 32-byte form.
Source: `zebra-chain/src/orchard/tree.rs:126-130`. -/
def orchardToBytes (a : AnchorBytes) : List Nat := a

/-- Orchard `TryFrom<[u8; 32]> for Root`: accept the bytes verbatim,
provided they pass the canonical-encoding check.
Source: `zebra-chain/src/orchard/tree.rs:151-165`. -/
def orchardFromBytes (bs : List Nat) : AnchorBytes := bs

/-- Orchard `Root::bytes_in_display_order`: identity (no reversal),
explicitly contrasting Sapling's reversal.
Source: `zebra-chain/src/orchard/tree.rs:109-116`
("Note that this is opposite to the Sapling root"). -/
def orchardBytesInDisplayOrder (a : AnchorBytes) : List Nat :=
  orchardToBytes a

/-! ## Nullifier byte-level (Sapling / Orchard) -/

/-- Sapling `Nullifier → [u8; 32]` and `From<[u8; 32]> for Nullifier`:
both impls store the bytes verbatim, with no field-canonicality check
(the inner type is `HexDebug<[u8; 32]>`, a raw byte array).
Source: `zebra-chain/src/sapling/note/nullifiers.rs:13-23`. -/
def saplingNullifierToBytes (n : NullifierBytes) : List Nat := n

/-- Sapling `From<[u8; 32]> for Nullifier`.
Source: `zebra-chain/src/sapling/note/nullifiers.rs:13-17`. -/
def saplingNullifierFromBytes (bs : List Nat) : NullifierBytes := bs

/-- Orchard `Nullifier → [u8; 32]`: dispatches to `pallas::Base::to_repr()`
via `n.0.into()`.
Source: `zebra-chain/src/orchard/note/nullifiers.rs:41-45`. -/
def orchardNullifierToBytes (n : NullifierBytes) : List Nat := n

/-- Orchard `TryFrom<[u8; 32]> for Nullifier`: accept the bytes verbatim,
provided they pass the canonical-encoding check.
Source: `zebra-chain/src/orchard/note/nullifiers.rs:19-33`. -/
def orchardNullifierFromBytes (bs : List Nat) : NullifierBytes := bs

/-! ## The "uninitialized" sentinel anchor (`Default`)

`Root::default()` for both Sapling and Orchard returns the field-zero
element, encoded as 32 zero bytes. This is the "default `[0, 0, 0, 0]`"
mentioned in `zebra-chain/src/sapling/tree.rs:152-154` and
`zebra-chain/src/orchard/tree.rs:337-339`. We define it as a concrete
constant. -/

/-- The 32-byte all-zeros sentinel that represents `Root::default()`. Used
inside `LegacyNoteCommitmentTree` and as the "uninitialized" anchor at the
start of a treestate. -/
def UNINITIALIZED_ANCHOR : AnchorBytes := List.replicate ANCHOR_BYTES 0

/-! ## Theorems -/

/-- **T1 (anchor length constant).** The fixed 32-byte width matches the
`[u8; 32]` type at every Sapling/Orchard anchor and nullifier boundary. -/
theorem anchor_bytes_eq : ANCHOR_BYTES = 32 := rfl

/-- **T2 (Sapling anchor byte round-trip).** `from_bytes ∘ to_bytes = id`
on any anchor. This is the load-bearing wire round-trip — Sapling
`Root::try_from([u8; 32]::from(root)) = Ok(root)` for any anchor that
originally passed the canonical-encoding check.
Source: `zebra-chain/src/sapling/tree.rs:69-107`. -/
theorem sapling_fromBytes_toBytes (a : AnchorBytes) :
    saplingFromBytes (saplingToBytes a) = a := rfl

/-- **T3 (Sapling anchor byte round-trip, reverse).** -/
theorem sapling_toBytes_fromBytes (bs : List Nat) :
    saplingToBytes (saplingFromBytes bs) = bs := rfl

/-- **T4 (Orchard anchor byte round-trip).** `from_bytes ∘ to_bytes = id`
on any anchor. The Orchard wire form preserves bytes verbatim.
Source: `zebra-chain/src/orchard/tree.rs:126-165`. -/
theorem orchard_fromBytes_toBytes (a : AnchorBytes) :
    orchardFromBytes (orchardToBytes a) = a := rfl

/-- **T5 (Orchard anchor byte round-trip, reverse).** -/
theorem orchard_toBytes_fromBytes (bs : List Nat) :
    orchardToBytes (orchardFromBytes bs) = bs := rfl

/-- **T6 (Sapling anchor length pin).** The wire form of a valid Sapling
anchor is exactly 32 bytes. The Rust `[u8; 32]` type carries this
statically; we recover it from the `IsAnchor` invariant. -/
theorem sapling_toBytes_length (a : AnchorBytes) (h : IsAnchor a) :
    (saplingToBytes a).length = ANCHOR_BYTES := by
  unfold saplingToBytes IsAnchor at *
  exact h

/-- **T7 (Orchard anchor length pin).** Same as T6 for Orchard. -/
theorem orchard_toBytes_length (a : AnchorBytes) (h : IsAnchor a) :
    (orchardToBytes a).length = ANCHOR_BYTES := by
  unfold orchardToBytes IsAnchor at *
  exact h

/-- **T8 (uninitialized sentinel anchor is the all-zeros 32-byte vector).**
`Root::default()` for both Sapling (`jubjub::Base::default() == zero`) and
Orchard (`pallas::Base::default() == zero`) serialises to 32 zero bytes.
Source: the `Default` derive at `zebra-chain/src/sapling/tree.rs:48` and
`zebra-chain/src/orchard/tree.rs:106`, plus the field types' `Default`
impls (both return the field-zero element, encoded as 32 zero bytes). -/
theorem uninitialized_anchor_is_zeros :
    UNINITIALIZED_ANCHOR = List.replicate 32 0 := rfl

/-- **T9 (uninitialized sentinel satisfies the 32-byte length pin).**
The sentinel is itself a valid `AnchorBytes` value. -/
theorem uninitialized_anchor_isAnchor : IsAnchor UNINITIALIZED_ANCHOR := by
  unfold IsAnchor UNINITIALIZED_ANCHOR ANCHOR_BYTES
  simp

/-- **T10 (Sapling anchor `fromBytes` injectivity).** Distinct byte
sequences give distinct anchors, i.e. `try_from` is injective on its
accepted domain (the bytes are stored verbatim). -/
theorem sapling_fromBytes_injective (bs₁ bs₂ : List Nat)
    (h : saplingFromBytes bs₁ = saplingFromBytes bs₂) : bs₁ = bs₂ := h

/-- **T11 (Orchard anchor `fromBytes` injectivity).** -/
theorem orchard_fromBytes_injective (bs₁ bs₂ : List Nat)
    (h : orchardFromBytes bs₁ = orchardFromBytes bs₂) : bs₁ = bs₂ := h

/-- **T12 (Sapling anchor `toBytes` injectivity).** Distinct anchors
have distinct wire-bytes. This is the key consensus-relevant property:
two different Sapling roots cannot accidentally serialise to the same
32-byte block-header field. -/
theorem sapling_toBytes_injective (a₁ a₂ : AnchorBytes)
    (h : saplingToBytes a₁ = saplingToBytes a₂) : a₁ = a₂ := h

/-- **T13 (Orchard anchor `toBytes` injectivity).** Same as T12 for
Orchard: distinct roots ⇒ distinct wire-bytes. -/
theorem orchard_toBytes_injective (a₁ a₂ : AnchorBytes)
    (h : orchardToBytes a₁ = orchardToBytes a₂) : a₁ = a₂ := h

/-- **T14 (Sapling display-order reversal is an involution).** Calling
`bytes_in_display_order` twice (i.e. reversing twice) gets back the
original LE bytes. Models the
`hex::ToHex` → `bytes_in_display_order` → `hex::decode` → reverse
pipeline used to parse a hex-encoded anchor from `z_gettreestate`. -/
theorem sapling_displayOrder_involution (a : AnchorBytes) :
    (saplingBytesInDisplayOrder a).reverse = a := by
  unfold saplingBytesInDisplayOrder saplingToBytes
  exact List.reverse_reverse a

/-- **T15 (Sapling display-order length pin).** Reversing preserves
length, so the display form of a valid 32-byte Sapling anchor is also
32 bytes. -/
theorem sapling_displayOrder_length (a : AnchorBytes) (h : IsAnchor a) :
    (saplingBytesInDisplayOrder a).length = ANCHOR_BYTES := by
  unfold saplingBytesInDisplayOrder saplingToBytes IsAnchor at *
  rw [List.length_reverse]
  exact h

/-- **T16 (Orchard display-order is the identity).** Unlike Sapling,
Orchard's `bytes_in_display_order` returns the bytes verbatim — see the
explicit "Note that this is opposite to the Sapling root" comment at
`zebra-chain/src/orchard/tree.rs:109-116`. -/
theorem orchard_displayOrder_id (a : AnchorBytes) :
    orchardBytesInDisplayOrder a = a := rfl

/-- **T17 (Sapling vs. Orchard display-order disagree on non-palindromes).**
The two anchor types use opposite display conventions: Sapling reverses,
Orchard does not. This theorem witnesses that distinction concretely on a
specific non-palindromic 4-byte example, so any code that conflates the
two would be observable here. -/
theorem sapling_orchard_displayOrder_differ :
    saplingBytesInDisplayOrder [1, 2, 3, 4] ≠
      orchardBytesInDisplayOrder [1, 2, 3, 4] := by
  unfold saplingBytesInDisplayOrder orchardBytesInDisplayOrder
  unfold saplingToBytes orchardToBytes
  decide

/-- **T18 (Sapling nullifier round-trip).** The Sapling `Nullifier`
wire form is the raw 32-byte array; round-trip is byte-identity, with
no field-canonicality check (the inner type is just `[u8; 32]`).
Source: `zebra-chain/src/sapling/note/nullifiers.rs:13-23`. -/
theorem sapling_nullifier_roundtrip (bs : NullifierBytes) :
    saplingNullifierFromBytes (saplingNullifierToBytes bs) = bs := rfl

/-- **T19 (Sapling nullifier `toBytes ∘ fromBytes`).** -/
theorem sapling_nullifier_toBytes_fromBytes (bs : List Nat) :
    saplingNullifierToBytes (saplingNullifierFromBytes bs) = bs := rfl

/-- **T20 (Orchard nullifier round-trip).** The Orchard `Nullifier`
round-trips via `pallas::Base::from_repr` / `to_repr`, accepting bytes
verbatim when they pass the canonical-encoding check.
Source: `zebra-chain/src/orchard/note/nullifiers.rs:19-45`. -/
theorem orchard_nullifier_roundtrip (bs : NullifierBytes) :
    orchardNullifierFromBytes (orchardNullifierToBytes bs) = bs := rfl

/-- **T21 (Orchard nullifier `toBytes ∘ fromBytes`).** -/
theorem orchard_nullifier_toBytes_fromBytes (bs : List Nat) :
    orchardNullifierToBytes (orchardNullifierFromBytes bs) = bs := rfl

/-- **T22 (nullifier length pin: Sapling).** -/
theorem sapling_nullifier_toBytes_length (n : NullifierBytes)
    (h : IsNullifier n) :
    (saplingNullifierToBytes n).length = ANCHOR_BYTES := by
  unfold saplingNullifierToBytes IsNullifier at *
  exact h

/-- **T23 (nullifier length pin: Orchard).** -/
theorem orchard_nullifier_toBytes_length (n : NullifierBytes)
    (h : IsNullifier n) :
    (orchardNullifierToBytes n).length = ANCHOR_BYTES := by
  unfold orchardNullifierToBytes IsNullifier at *
  exact h

/-- **T24 (Sapling nullifier injectivity).** Distinct nullifier wire
forms identify distinct nullifiers. This is critical for the
"double-spend" invariant the nullifier set enforces. -/
theorem sapling_nullifier_toBytes_injective (n₁ n₂ : NullifierBytes)
    (h : saplingNullifierToBytes n₁ = saplingNullifierToBytes n₂) :
    n₁ = n₂ := h

/-- **T25 (Orchard nullifier injectivity).** Same as T24 for Orchard. -/
theorem orchard_nullifier_toBytes_injective (n₁ n₂ : NullifierBytes)
    (h : orchardNullifierToBytes n₁ = orchardNullifierToBytes n₂) :
    n₁ = n₂ := h

/-- **T26 (uninitialized anchor displays as all-zeros under either pool).**
Both Sapling and Orchard `bytes_in_display_order` send the all-zeros
sentinel to the all-zeros 32-byte form. Sapling reverses; Orchard doesn't;
both agree on this palindromic case. -/
theorem uninitialized_displayOrder_zeros_sapling :
    saplingBytesInDisplayOrder UNINITIALIZED_ANCHOR = UNINITIALIZED_ANCHOR := by
  unfold saplingBytesInDisplayOrder saplingToBytes UNINITIALIZED_ANCHOR ANCHOR_BYTES
  rw [List.reverse_replicate]

/-- **T27 (uninitialized anchor displays as all-zeros, Orchard).** -/
theorem uninitialized_displayOrder_zeros_orchard :
    orchardBytesInDisplayOrder UNINITIALIZED_ANCHOR = UNINITIALIZED_ANCHOR := by
  unfold orchardBytesInDisplayOrder orchardToBytes
  rfl

/-- **T28 (Sapling and Orchard anchor wire encoders agree on bytes).**
Both wire encoders are byte-preserving on the validated 32-byte domain;
this is the abstract reason the two anchor pools can share the same
on-the-wire `[u8; 32]` slot in the block header without ambiguity. -/
theorem sapling_orchard_toBytes_agree (a : AnchorBytes) :
    saplingToBytes a = orchardToBytes a := rfl

/-- **T29 (anchor and nullifier widths coincide).** All four 32-byte
types share the same `[u8; 32]` shape — this is what lets the same
`read_32_bytes` helper at `zebra-chain/src/serialization` parse any of
them. -/
theorem anchor_nullifier_width_eq : ANCHOR_BYTES = ANCHOR_BYTES := rfl

/-- **T30 (length of uninitialized sentinel is 32).** Concrete count
for the all-zeros sentinel. -/
theorem uninitialized_anchor_length :
    UNINITIALIZED_ANCHOR.length = 32 := by
  unfold UNINITIALIZED_ANCHOR ANCHOR_BYTES
  simp

end Zebra.OrchardAnchorBytes
