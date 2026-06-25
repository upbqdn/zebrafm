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
invariant the Rust type system carries). The `TryFrom<[u8; 32]>` impls
for the field-backed types (Sapling anchor, Orchard anchor, Orchard
nullifier) further enforce a **field-membership / canonical-encoding**
check: the 32 LE bytes must decode to a value strictly less than the
field order. We model that check explicitly via `isSaplingCanonical` /
`isOrchardCanonical`, and model the parsers as **partial** functions
returning `Option`. The Sapling `Nullifier` parser has no such check
(its inner type is `HexDebug<[u8; 32]>`), so its parser is total.

The Rust `Root` impls have a notable subtlety: `Default::default()` on
the `Root` type produces `jubjub::Base::default()` / `pallas::Base::default()`,
which is the field's zero element, encoded as 32 zero bytes. This is the
"uninitialized" sentinel anchor (see the `Default` derive on
`zebra-chain/src/sapling/tree.rs:48` and `zebra-chain/src/orchard/tree.rs:106`,
and the comment at `zebra-chain/src/sapling/tree.rs:152-154` noting that
"the default value of the [`Root`] type is `[0, 0, 0, 0]`. However, this
value differs from the default value of the root of the default tree which
is the hash of the root's child nodes."). The sentinel is canonical: zero
is less than any field order, so it decodes successfully (T-canonical-zero
below).
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

/-- The per-byte upper bound: every `u8` is `< 256`. -/
def BYTE_MAX : Nat := 256

/-- Jubjub base-field order `q_J`. The Sapling `Root` and `Nullifier`
internal fields are `jubjub::Base`; the `from_bytes` check rejects 32 LE
bytes whose value is `≥ q_J`.
Source: jubjub crate `src/fq.rs` `MODULUS` constant. Also documented at
<https://zips.z.cash/zip-0216>. -/
def JUBJUB_FIELD_ORDER : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- Pallas base-field order `p_P`. The Orchard `Root` and `Nullifier`
internal fields are `pallas::Base`; the `from_repr` check rejects 32 LE
bytes whose value is `≥ p_P`.
Source: pasta_curves crate, "Pallas Base field prime". -/
def PALLAS_FIELD_ORDER : Nat :=
  0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001

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

/-! ## Little-endian byte interpretation

Both the Sapling (`jubjub::Base`) and Orchard (`pallas::Base`) parsers
read the 32-byte input as a *little-endian* unsigned integer and compare
it against the field order. We model that with `leValue`. -/

/-- Little-endian interpretation of a byte list as a `Nat`: the head byte
is the least significant. For a `[u8; 32]` array `bs`, this equals
`bs[0] + bs[1] * 256 + bs[2] * 256^2 + ... + bs[31] * 256^31`. -/
def leValue : List Nat → Nat
  | []      => 0
  | b :: bs => b + BYTE_MAX * leValue bs

/-- The per-byte well-formedness predicate: every byte fits in 8 bits.
Stated as `Bool` so the canonical-encoding predicate stays decidable. -/
def AllBytes (bs : List Nat) : Bool := bs.all (· < BYTE_MAX)

/-- The length-32 predicate, stated as a `Bool` for use inside the
canonical-encoding tests. -/
def IsAnchorBool (bs : List Nat) : Bool := bs.length = ANCHOR_BYTES

/-! ## Canonical-encoding predicates

The Rust `TryFrom<[u8; 32]>` impls for `Sapling::Root`, `Orchard::Root`
and `Orchard::Nullifier` all enforce that the 32 LE bytes decode to a
field element, i.e. their LE value is strictly below the corresponding
field order. (The `from_bytes` / `from_repr` returns `CtOption::none`
otherwise, and the impls translate that into a `SerializationError`.) -/

/-- A 32-byte sequence is the **canonical** Sapling encoding iff it has
length 32, every byte fits in 8 bits, and its LE value is `< q_J`
(the Jubjub base-field order).
Source: `zebra-chain/src/sapling/tree.rs:93-107` (calls
`jubjub::Base::from_bytes`). -/
def isSaplingCanonical (bs : List Nat) : Bool :=
  IsAnchorBool bs && AllBytes bs && (leValue bs < JUBJUB_FIELD_ORDER)

/-- `Prop`-valued Sapling canonical-encoding predicate. -/
def IsSaplingCanonical (bs : List Nat) : Prop := isSaplingCanonical bs = true

/-- A 32-byte sequence is the **canonical** Orchard encoding iff it has
length 32, every byte fits in 8 bits, and its LE value is `< p_P`
(the Pallas base-field order).
Source: `zebra-chain/src/orchard/tree.rs:151-165` (calls
`pallas::Base::from_repr`). -/
def isOrchardCanonical (bs : List Nat) : Bool :=
  IsAnchorBool bs && AllBytes bs && (leValue bs < PALLAS_FIELD_ORDER)

/-- `Prop`-valued Orchard canonical-encoding predicate. -/
def IsOrchardCanonical (bs : List Nat) : Prop := isOrchardCanonical bs = true

/-! ## Sapling anchor: serialiser, parser, display order

The Sapling `Root` wraps a `jubjub::Base`; the `From<Root> for [u8; 32]`
impl calls `root.0.to_bytes()` (LE encoding), and `TryFrom<[u8; 32]>`
calls `jubjub::Base::from_bytes(&bytes)` and rejects non-canonical
encodings. Source: `zebra-chain/src/sapling/tree.rs:69-107`. -/

/-- Sapling `Root → [u8; 32]`: extract the 32-byte little-endian form.
The Rust impl reads the canonical repr out of the underlying field
element; on the wire we model the serialised form by the `List Nat`
itself, since we don't model the field arithmetic.
Source: `zebra-chain/src/sapling/tree.rs:69-73`. -/
def saplingToBytes (a : AnchorBytes) : List Nat := a

/-- Sapling `TryFrom<[u8; 32]> for Root`: returns `some` only when the
canonical-encoding check passes, mirroring the `CtOption` returned by
`jubjub::Base::from_bytes` and the `SerializationError` translation in
`tree.rs:101-104`.
Source: `zebra-chain/src/sapling/tree.rs:93-107`. -/
def saplingTryFromBytes (bs : List Nat) : Option AnchorBytes :=
  if isSaplingCanonical bs then some bs else none

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

/-- Orchard `TryFrom<[u8; 32]> for Root`: returns `some` only when the
canonical-encoding check passes, mirroring the `CtOption` returned by
`pallas::Base::from_repr` and the `SerializationError` translation in
`tree.rs:159-163`.
Source: `zebra-chain/src/orchard/tree.rs:151-165`. -/
def orchardTryFromBytes (bs : List Nat) : Option AnchorBytes :=
  if isOrchardCanonical bs then some bs else none

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

/-- Sapling `From<[u8; 32]> for Nullifier`: total, since the inner type
is just a raw byte array (no canonical-encoding check).
Source: `zebra-chain/src/sapling/note/nullifiers.rs:13-17`. -/
def saplingNullifierFromBytes (bs : List Nat) : NullifierBytes := bs

/-- Orchard `Nullifier → [u8; 32]`: dispatches to `pallas::Base::to_repr()`
via `n.0.into()`.
Source: `zebra-chain/src/orchard/note/nullifiers.rs:41-45`. -/
def orchardNullifierToBytes (n : NullifierBytes) : List Nat := n

/-- Orchard `TryFrom<[u8; 32]> for Nullifier`: returns `some` only when
the canonical-encoding check passes, mirroring the `CtOption` returned by
`pallas::Base::from_repr`.
Source: `zebra-chain/src/orchard/note/nullifiers.rs:19-33`. -/
def orchardNullifierTryFromBytes (bs : List Nat) : Option NullifierBytes :=
  if isOrchardCanonical bs then some bs else none

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

/-! ## Helper lemmas on `leValue`

`leValue` of the empty list is 0; the all-zeros sequence has `leValue` 0,
which is what makes the uninitialized sentinel canonical under both
fields. -/

theorem leValue_nil : leValue [] = 0 := rfl

theorem leValue_cons (b : Nat) (bs : List Nat) :
    leValue (b :: bs) = b + BYTE_MAX * leValue bs := rfl

/-- `leValue` of any replicated-zero list is `0`. -/
theorem leValue_replicate_zero (n : Nat) : leValue (List.replicate n 0) = 0 := by
  induction n with
  | zero => simp [leValue]
  | succ k ih =>
    rw [List.replicate_succ, leValue_cons, ih]
    simp

/-! ## Theorems -/

/-- The fixed 32-byte width matches the `[u8; 32]` type at every
Sapling/Orchard anchor and nullifier boundary. -/
theorem anchor_bytes_eq : ANCHOR_BYTES = 32 := rfl

/-! ### Field-order facts -/

/-- The Jubjub base-field order is strictly less than `2^256` (so 32-byte
encodings can land outside the field). -/
theorem jubjub_field_order_lt_wide_bound : JUBJUB_FIELD_ORDER < 2 ^ 256 := by
  decide

/-- The Pallas base-field order is strictly less than `2^256` (so 32-byte
encodings can land outside the field). -/
theorem pallas_field_order_lt_wide_bound : PALLAS_FIELD_ORDER < 2 ^ 256 := by
  decide

/-- The Pallas base-field order is strictly smaller than the Jubjub
base-field order: `p_P < q_J`. (The Sapling and Orchard parsers therefore
accept different subsets of the 32-byte cube.) -/
theorem pallas_lt_jubjub : PALLAS_FIELD_ORDER < JUBJUB_FIELD_ORDER := by
  decide

/-! ### Canonical-encoding witnesses

We need at least one concrete canonical encoding (the all-zeros sentinel)
and one concrete non-canonical encoding (32 `0xff` bytes) to show the
`TryFrom` impls aren't degenerate. -/

/-- The 32-byte all-zeros sentinel is a canonical Sapling encoding: it
has length 32, all bytes fit in `u8`, and its LE value is `0 < q_J`. -/
theorem uninitialized_isSaplingCanonical :
    IsSaplingCanonical UNINITIALIZED_ANCHOR := by
  unfold IsSaplingCanonical isSaplingCanonical
  decide

/-- The 32-byte all-zeros sentinel is a canonical Orchard encoding: same
reasoning under `p_P`. -/
theorem uninitialized_isOrchardCanonical :
    IsOrchardCanonical UNINITIALIZED_ANCHOR := by
  unfold IsOrchardCanonical isOrchardCanonical
  decide

/-- The 32-byte all-`0xff` sequence has LE value `2^256 - 1`, which is
strictly greater than both `q_J` and `p_P`, so it fails *both* canonical
checks. This is a concrete witness that the parsers really reject some
32-byte sequences. -/
theorem all_ones_not_sapling_canonical :
    ¬ IsSaplingCanonical (List.replicate ANCHOR_BYTES 255) := by
  unfold IsSaplingCanonical isSaplingCanonical
  decide

theorem all_ones_not_orchard_canonical :
    ¬ IsOrchardCanonical (List.replicate ANCHOR_BYTES 255) := by
  unfold IsOrchardCanonical isOrchardCanonical
  decide

/-- A 32-byte sequence whose LE value sits between `p_P` and `q_J` is
canonical under Sapling but not Orchard. We use `p_P` itself: encoded as
32 LE bytes it equals `p_P`, which satisfies `p_P < q_J` (Sapling check
passes) but fails `p_P < p_P` (Orchard check fails). This witnesses that
the two canonical-encoding predicates are *distinct*. -/
theorem sapling_orchard_canonical_predicates_differ :
    ∃ bs : List Nat, IsSaplingCanonical bs ∧ ¬ IsOrchardCanonical bs := by
  -- Use 32 LE bytes encoding the value `p_P`. The bytes are constructed
  -- by reading off the low byte of `p_P` and recursively shifting.
  refine ⟨[0x01, 0x00, 0x00, 0x00, 0xed, 0x30, 0x2d, 0x99,
           0x1b, 0xf9, 0x4c, 0x09, 0xfc, 0x98, 0x46, 0x22,
           0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
           0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40],
          ?_, ?_⟩
  · -- Sapling canonical: length=32, bytes<256, leValue = p_P < q_J.
    unfold IsSaplingCanonical isSaplingCanonical
    decide
  · -- Orchard non-canonical: leValue = p_P, but check requires < p_P.
    unfold IsOrchardCanonical isOrchardCanonical
    decide

/-! ### Decoder behaviour: round-trip is partial -/

/-- Sapling `TryFrom<[u8; 32]> for Root` accepts canonical encodings:
on a canonical input it returns `some bs` (the parser then wraps it as
`Root` — at the byte level that's the same data). -/
theorem saplingTryFromBytes_canonical (bs : List Nat)
    (h : IsSaplingCanonical bs) :
    saplingTryFromBytes bs = some bs := by
  unfold saplingTryFromBytes
  simp [show isSaplingCanonical bs = true from h]

/-- Sapling `TryFrom<[u8; 32]> for Root` rejects non-canonical encodings:
on a non-canonical input it returns `none`, mirroring the Rust
`SerializationError::Parse(...)` return path. -/
theorem saplingTryFromBytes_noncanonical (bs : List Nat)
    (h : ¬ IsSaplingCanonical bs) :
    saplingTryFromBytes bs = none := by
  unfold saplingTryFromBytes
  have : isSaplingCanonical bs = false := by
    cases hc : isSaplingCanonical bs
    · rfl
    · exfalso; exact h hc
  simp [this]

/-- Orchard `TryFrom<[u8; 32]> for Root` accepts canonical encodings. -/
theorem orchardTryFromBytes_canonical (bs : List Nat)
    (h : IsOrchardCanonical bs) :
    orchardTryFromBytes bs = some bs := by
  unfold orchardTryFromBytes
  simp [show isOrchardCanonical bs = true from h]

/-- Orchard `TryFrom<[u8; 32]> for Root` rejects non-canonical encodings. -/
theorem orchardTryFromBytes_noncanonical (bs : List Nat)
    (h : ¬ IsOrchardCanonical bs) :
    orchardTryFromBytes bs = none := by
  unfold orchardTryFromBytes
  have : isOrchardCanonical bs = false := by
    cases hc : isOrchardCanonical bs
    · rfl
    · exfalso; exact h hc
  simp [this]

/-- Orchard `TryFrom<[u8; 32]> for Nullifier` accepts canonical encodings.
The nullifier parser is the same `pallas::Base::from_repr` call as the
Orchard anchor parser, so it shares the predicate. -/
theorem orchardNullifierTryFromBytes_canonical (bs : List Nat)
    (h : IsOrchardCanonical bs) :
    orchardNullifierTryFromBytes bs = some bs := by
  unfold orchardNullifierTryFromBytes
  simp [show isOrchardCanonical bs = true from h]

/-- Orchard `TryFrom<[u8; 32]> for Nullifier` rejects non-canonical
encodings. -/
theorem orchardNullifierTryFromBytes_noncanonical (bs : List Nat)
    (h : ¬ IsOrchardCanonical bs) :
    orchardNullifierTryFromBytes bs = none := by
  unfold orchardNullifierTryFromBytes
  have : isOrchardCanonical bs = false := by
    cases hc : isOrchardCanonical bs
    · rfl
    · exfalso; exact h hc
  simp [this]

/-! ### Anchor round-trip under the canonical-encoding pre-condition

These are the load-bearing wire round-trip claims for the field-backed
parsers. They are *not* `rfl` — they unfold the partial-function
`if`-on-`Bool` and use the canonical-encoding hypothesis to discharge
the branch. -/

/-- Sapling anchor round-trip under canonical-encoding: a canonical 32-byte
input parses to `some a` whose serialisation is the input again. -/
theorem sapling_anchor_roundtrip (bs : List Nat) (h : IsSaplingCanonical bs) :
    Option.map saplingToBytes (saplingTryFromBytes bs) = some bs := by
  rw [saplingTryFromBytes_canonical bs h]
  rfl

/-- Orchard anchor round-trip under canonical-encoding. -/
theorem orchard_anchor_roundtrip (bs : List Nat) (h : IsOrchardCanonical bs) :
    Option.map orchardToBytes (orchardTryFromBytes bs) = some bs := by
  rw [orchardTryFromBytes_canonical bs h]
  rfl

/-- Orchard nullifier round-trip under canonical-encoding. -/
theorem orchard_nullifier_roundtrip (bs : List Nat) (h : IsOrchardCanonical bs) :
    Option.map orchardNullifierToBytes (orchardNullifierTryFromBytes bs) = some bs := by
  rw [orchardNullifierTryFromBytes_canonical bs h]
  rfl

/-- Sapling nullifier round-trip: `fromBytes (toBytes bs) = bs`. Total,
since the Sapling nullifier parser performs no canonical check (the
inner type is `HexDebug<[u8; 32]>`, a raw byte array). This *is*
intentionally `rfl` over identity — it captures the fact that the Sapling
nullifier surface has *no* extra check, in contrast to the other three
parsers in this module.
Source: `zebra-chain/src/sapling/note/nullifiers.rs:13-23`. -/
theorem sapling_nullifier_roundtrip (bs : NullifierBytes) :
    saplingNullifierFromBytes (saplingNullifierToBytes bs) = bs := rfl

/-! ### Length pins -/

/-- The wire form of a valid Sapling anchor is exactly 32 bytes. The Rust
`[u8; 32]` type carries this statically; we recover it from `IsAnchor`. -/
theorem sapling_toBytes_length (a : AnchorBytes) (h : IsAnchor a) :
    (saplingToBytes a).length = ANCHOR_BYTES := h

/-- The wire form of a valid Orchard anchor is exactly 32 bytes. -/
theorem orchard_toBytes_length (a : AnchorBytes) (h : IsAnchor a) :
    (orchardToBytes a).length = ANCHOR_BYTES := h

/-- A successful Sapling parse yields a length-32 byte string. -/
theorem saplingTryFromBytes_some_length (bs : List Nat) (a : AnchorBytes)
    (h : saplingTryFromBytes bs = some a) : a.length = ANCHOR_BYTES := by
  unfold saplingTryFromBytes at h
  by_cases hC : isSaplingCanonical bs
  · rw [if_pos hC] at h
    simp only [Option.some.injEq] at h
    subst h
    -- The `isSaplingCanonical` hypothesis carries `IsAnchorBool bs = true`.
    unfold isSaplingCanonical IsAnchorBool at hC
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hC
    exact hC.1.1
  · rw [if_neg hC] at h
    cases h

/-- A successful Orchard parse yields a length-32 byte string. -/
theorem orchardTryFromBytes_some_length (bs : List Nat) (a : AnchorBytes)
    (h : orchardTryFromBytes bs = some a) : a.length = ANCHOR_BYTES := by
  unfold orchardTryFromBytes at h
  by_cases hC : isOrchardCanonical bs
  · rw [if_pos hC] at h
    simp only [Option.some.injEq] at h
    subst h
    unfold isOrchardCanonical IsAnchorBool at hC
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hC
    exact hC.1.1
  · rw [if_neg hC] at h
    cases h

/-- A successful Orchard nullifier parse yields a length-32 byte string. -/
theorem orchardNullifierTryFromBytes_some_length (bs : List Nat)
    (a : NullifierBytes) (h : orchardNullifierTryFromBytes bs = some a) :
    a.length = ANCHOR_BYTES := by
  unfold orchardNullifierTryFromBytes at h
  by_cases hC : isOrchardCanonical bs
  · rw [if_pos hC] at h
    simp only [Option.some.injEq] at h
    subst h
    unfold isOrchardCanonical IsAnchorBool at hC
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hC
    exact hC.1.1
  · rw [if_neg hC] at h
    cases h

/-! ### Canonical-encoding strict-subset facts

The Rust `TryFrom<[u8; 32]>` impls reject some 32-byte sequences. The
following theorems witness, concretely, that the canonical predicates
carve out *strict* subsets of the length-32 byte cube. -/

/-- A canonical Sapling encoding is in particular a length-32 byte string
with bytes in `u8`. -/
theorem sapling_canonical_isAnchor (bs : List Nat) (h : IsSaplingCanonical bs) :
    bs.length = ANCHOR_BYTES := by
  unfold IsSaplingCanonical isSaplingCanonical IsAnchorBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- A canonical Orchard encoding is in particular a length-32 byte string. -/
theorem orchard_canonical_isAnchor (bs : List Nat) (h : IsOrchardCanonical bs) :
    bs.length = ANCHOR_BYTES := by
  unfold IsOrchardCanonical isOrchardCanonical IsAnchorBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- A canonical encoding's LE value is in the field: `leValue bs < q_J`
under Sapling. This is the field-membership statement the Rust
`from_bytes` guarantees on success. -/
theorem sapling_canonical_le_value_bound (bs : List Nat)
    (h : IsSaplingCanonical bs) : leValue bs < JUBJUB_FIELD_ORDER := by
  unfold IsSaplingCanonical isSaplingCanonical at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- A canonical encoding's LE value is in the field: `leValue bs < p_P`
under Orchard. -/
theorem orchard_canonical_le_value_bound (bs : List Nat)
    (h : IsOrchardCanonical bs) : leValue bs < PALLAS_FIELD_ORDER := by
  unfold IsOrchardCanonical isOrchardCanonical at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- An Orchard-canonical encoding is also Sapling-canonical: `p_P < q_J`,
so any `leValue bs < p_P` automatically satisfies `leValue bs < q_J`. The
converse fails (see `sapling_orchard_canonical_predicates_differ`).

In Zcash terms: every byte string the Orchard parser accepts is also
accepted by the Sapling parser, but not vice versa. The Orchard
parser is *stricter*. -/
theorem orchard_canonical_implies_sapling_canonical (bs : List Nat)
    (h : IsOrchardCanonical bs) : IsSaplingCanonical bs := by
  unfold IsOrchardCanonical isOrchardCanonical at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold IsSaplingCanonical isSaplingCanonical
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h.1, lt_of_lt_of_le h.2 (Nat.le_of_lt pallas_lt_jubjub)⟩

/-! ### The uninitialized sentinel -/

/-- The uninitialized sentinel is the all-zeros 32-byte vector. -/
theorem uninitialized_anchor_is_zeros :
    UNINITIALIZED_ANCHOR = List.replicate 32 0 := rfl

/-- The sentinel satisfies the length pin. -/
theorem uninitialized_anchor_isAnchor : IsAnchor UNINITIALIZED_ANCHOR := by
  unfold IsAnchor UNINITIALIZED_ANCHOR ANCHOR_BYTES
  simp

/-- The Sapling parser accepts the uninitialized sentinel. -/
theorem saplingTryFromBytes_uninitialized :
    saplingTryFromBytes UNINITIALIZED_ANCHOR = some UNINITIALIZED_ANCHOR :=
  saplingTryFromBytes_canonical _ uninitialized_isSaplingCanonical

/-- The Orchard parser accepts the uninitialized sentinel. -/
theorem orchardTryFromBytes_uninitialized :
    orchardTryFromBytes UNINITIALIZED_ANCHOR = some UNINITIALIZED_ANCHOR :=
  orchardTryFromBytes_canonical _ uninitialized_isOrchardCanonical

/-- Sanity: the sentinel has length 32. -/
theorem uninitialized_anchor_length :
    UNINITIALIZED_ANCHOR.length = 32 := by
  unfold UNINITIALIZED_ANCHOR ANCHOR_BYTES
  simp

/-! ### Display-order behaviour: Sapling vs Orchard

This is the visible Rust-level difference between the two anchor types,
captured at the source by the comment "Note that this is opposite to the
Sapling root" in `zebra-chain/src/orchard/tree.rs:111-112`. -/

/-- Calling `bytes_in_display_order` twice on the Sapling anchor gets back
the original LE bytes (the Sapling impl reverses; reversing twice is
the identity). Models the `hex::ToHex` → `bytes_in_display_order` →
`hex::decode` → reverse pipeline used to parse a hex-encoded anchor from
`z_gettreestate`. -/
theorem sapling_displayOrder_involution (a : AnchorBytes) :
    (saplingBytesInDisplayOrder a).reverse = a := by
  unfold saplingBytesInDisplayOrder saplingToBytes
  exact List.reverse_reverse a

/-- Reversing preserves length, so the Sapling display form of a valid
32-byte anchor is also 32 bytes. -/
theorem sapling_displayOrder_length (a : AnchorBytes) (h : IsAnchor a) :
    (saplingBytesInDisplayOrder a).length = ANCHOR_BYTES := by
  unfold saplingBytesInDisplayOrder saplingToBytes IsAnchor at *
  rw [List.length_reverse]
  exact h

/-- Unlike Sapling, Orchard's `bytes_in_display_order` returns the bytes
verbatim — see the explicit "Note that this is opposite to the Sapling
root" comment at `zebra-chain/src/orchard/tree.rs:109-116`. -/
theorem orchard_displayOrder_id (a : AnchorBytes) :
    orchardBytesInDisplayOrder a = a := rfl

/-- The two anchor types use opposite display conventions on
non-palindromic inputs: Sapling reverses, Orchard does not. Any code that
conflates the two would be observable here. -/
theorem sapling_orchard_displayOrder_differ :
    saplingBytesInDisplayOrder [1, 2, 3, 4] ≠
      orchardBytesInDisplayOrder [1, 2, 3, 4] := by
  unfold saplingBytesInDisplayOrder orchardBytesInDisplayOrder
  unfold saplingToBytes orchardToBytes
  decide

/-- Both `bytes_in_display_order` impls send the all-zeros sentinel to
itself: the Sapling reversal preserves a palindrome, and the Orchard
impl is the identity. So the displayed form of the uninitialized anchor
is the same string of 32 zero bytes for both pools. -/
theorem uninitialized_displayOrder_zeros_sapling :
    saplingBytesInDisplayOrder UNINITIALIZED_ANCHOR = UNINITIALIZED_ANCHOR := by
  unfold saplingBytesInDisplayOrder saplingToBytes UNINITIALIZED_ANCHOR ANCHOR_BYTES
  rw [List.reverse_replicate]

theorem uninitialized_displayOrder_zeros_orchard :
    orchardBytesInDisplayOrder UNINITIALIZED_ANCHOR = UNINITIALIZED_ANCHOR := rfl

end Zebra.OrchardAnchorBytes
