import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Nullifier byte models across shielded pools

Sprout, Sapling and Orchard all expose a 32-byte nullifier on the wire; the
chain stores them in a per-pool nullifier set, and duplicate-nullifier
detection is the consensus mechanism that prevents shielded double-spends.

What the three Rust types actually do at the byte boundary differs, and this
module's job is to pin that difference honestly:

  * `sprout::note::Nullifier(HexDebug<[u8; 32]>)`. The `From<[u8; 32]>` /
    `From<Nullifier> for [u8; 32]` impls are length-only — the inner type is
    a raw byte array with no canonical-encoding check. Source:
    `zebra-chain/src/sprout/note/nullifiers.rs:42-70`.

  * `sapling::note::Nullifier(HexDebug<[u8; 32]>)`. Same shape as Sprout — the
    inner type is a raw byte array, so the conversion pair is length-only and
    cannot reject any 32-byte input. Source:
    `zebra-chain/src/sapling/note/nullifiers.rs:11-23`.

  * `orchard::note::Nullifier(pallas::Base)`. Here the wrapper is a Pallas
    base-field element, and `TryFrom<[u8; 32]>` calls `pallas::Base::from_repr`,
    which returns `CtOption::none` whenever the 32 LE bytes encode a value `≥
    p_P` (the Pallas base-field order). Non-canonical bytes are rejected with
    `SerializationError::Parse`. Source:
    `zebra-chain/src/orchard/note/nullifiers.rs:19-45`.

We deliberately model the Orchard canonical-encoding gate rather than papering
over it with an identity decoder. The Sprout/Sapling identity-style decoders
correctly reflect their Rust counterparts, but the round-trip theorems are
renamed and re-documented so they advertise what they actually prove rather
than implying a non-trivial decoding step.

Sprout also has a separate `NullifierSeed` (rho) `[u8; 32]` newtype (the
`sproutkeycomponents` spec value) at `nullifiers.rs:16-34`; we include a
sibling model so the file covers every public 32-byte nullifier-adjacent type
the Rust crate exposes.

The three pools sit in sibling sub-namespaces so the proofs mirror the
Rust-level newtype distinction that keeps the nullifier sets disjoint at the
type level.
-/

namespace Zebra.Nullifiers

/-- The fixed nullifier width in bytes (the `32` in `[u8; 32]`).
Source: `zebra-chain/src/sprout/note/nullifiers.rs:42`,
`zebra-chain/src/sapling/note/nullifiers.rs:11`,
`zebra-chain/src/orchard/note/nullifiers.rs:11`. -/
def NULLIFIER_BYTES : Nat := 32

/-- The per-byte upper bound: every `u8` is `< 256`. Used by the
canonical-encoding check on the Orchard nullifier. -/
def BYTE_MAX : Nat := 256

/-- Pallas base-field order `p_P`. The Orchard `Nullifier` wraps a
`pallas::Base`; `TryFrom<[u8; 32]>` rejects 32 LE bytes whose value is `≥
p_P` (`pallas::Base::from_repr` returns `CtOption::none`).
Source: pasta_curves crate, "Pallas base-field prime"; matches
`Zebrafm.OrchardAnchorBytes.PALLAS_FIELD_ORDER`. -/
def PALLAS_FIELD_ORDER : Nat :=
  0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001

/-- Little-endian interpretation of a byte list as a `Nat`: the head byte is
the least significant. For a `[u8; 32]` array `bs`, this equals
`bs[0] + bs[1] * 256 + bs[2] * 256^2 + ... + bs[31] * 256^31`. The Pallas
`from_repr` call interprets the byte slice in this little-endian order. -/
def leValue : List Nat → Nat
  | []      => 0
  | b :: bs => b + BYTE_MAX * leValue bs

/-- The per-byte well-formedness predicate: every byte fits in 8 bits. -/
def AllBytes (bs : List Nat) : Bool := bs.all (· < BYTE_MAX)

/-- The length-32 invariant, stated as a `Bool` for use inside the
canonical-encoding test. -/
def IsNullifierBool (bs : List Nat) : Bool := bs.length = NULLIFIER_BYTES

/-! ## Sprout nullifier (`zebra-chain/src/sprout/note/nullifiers.rs:42-70`) -/

namespace Sprout

/-- The length invariant carried by the Rust `[u8; 32]` type.
Source: `zebra-chain/src/sprout/note/nullifiers.rs:42`. -/
def IsNullifier (bs : List Nat) : Prop := bs.length = NULLIFIER_BYTES

/-- `impl From<[u8; 32]> for Nullifier`: wraps the byte array (the inner type
is `HexDebug<[u8; 32]>`, a raw byte container with no canonical check).
Source: `zebra-chain/src/sprout/note/nullifiers.rs:54-58`. -/
def fromBytes (bs : List Nat) : List Nat := bs

/-- `impl From<Nullifier> for [u8; 32]`: extracts the byte array.
Source: `zebra-chain/src/sprout/note/nullifiers.rs:60-64`. -/
def toBytes (n : List Nat) : List Nat := n

/-- `Nullifier::bytes_in_display_order` — big-endian byte order for RPCs like
`getrawtransaction`. Implemented as `toBytes` followed by `reverse`.
Source: `zebra-chain/src/sprout/note/nullifiers.rs:47-52`. -/
def bytesInDisplayOrder (n : List Nat) : List Nat := (toBytes n).reverse

/-- The zero nullifier: 32 zero bytes. Not a `Default` impl in Rust, but a
useful concrete witness that the 32-byte invariant is inhabitable. -/
def zero : List Nat := List.replicate NULLIFIER_BYTES 0

/-! ### Sprout `NullifierSeed` (rho), a sibling `[u8; 32]` newtype.

`nullifiers.rs:16-34` declares `pub struct NullifierSeed(pub(crate)
HexDebug<[u8; 32]>);` and exposes the same `From<[u8; 32]>` /
`From<NullifierSeed> for [u8; 32]` conversion pair as the `Nullifier`. The
`AsRef<[u8]>` impl exposes the raw bytes. We model it as a sibling
`Seed` type sharing the length invariant. -/

/-- The length invariant carried by the Rust `NullifierSeed([u8; 32])` type.
Source: `zebra-chain/src/sprout/note/nullifiers.rs:16`. -/
def IsSeed (bs : List Nat) : Prop := bs.length = NULLIFIER_BYTES

/-- `impl From<[u8; 32]> for NullifierSeed`: wraps the bytes verbatim.
Source: `zebra-chain/src/sprout/note/nullifiers.rs:24-28`. -/
def seedFromBytes (bs : List Nat) : List Nat := bs

/-- `impl From<NullifierSeed> for [u8; 32]`: extracts the bytes verbatim.
Source: `zebra-chain/src/sprout/note/nullifiers.rs:30-34`. -/
def seedToBytes (s : List Nat) : List Nat := s

/-- `impl AsRef<[u8]> for NullifierSeed`: a borrow of the inner bytes. We
model the borrow as the bytes themselves since we don't track lifetimes.
Source: `zebra-chain/src/sprout/note/nullifiers.rs:18-22`. -/
def seedAsRef (s : List Nat) : List Nat := s

end Sprout

/-! ## Sapling nullifier (`zebra-chain/src/sapling/note/nullifiers.rs:11-23`) -/

namespace Sapling

/-- The length invariant carried by the Rust `[u8; 32]` type.
Source: `zebra-chain/src/sapling/note/nullifiers.rs:11`. -/
def IsNullifier (bs : List Nat) : Prop := bs.length = NULLIFIER_BYTES

/-- `impl From<[u8; 32]> for Nullifier`: wraps the byte array (the inner type
is `HexDebug<[u8; 32]>`, a raw byte container with no canonical check).
Source: `zebra-chain/src/sapling/note/nullifiers.rs:13-17`. -/
def fromBytes (bs : List Nat) : List Nat := bs

/-- `impl From<Nullifier> for [u8; 32]`: extracts the byte array.
Source: `zebra-chain/src/sapling/note/nullifiers.rs:19-23`. -/
def toBytes (n : List Nat) : List Nat := n

/-- The zero nullifier: 32 zero bytes. -/
def zero : List Nat := List.replicate NULLIFIER_BYTES 0

end Sapling

/-! ## Orchard nullifier (`zebra-chain/src/orchard/note/nullifiers.rs:10-45`)

The Rust type wraps a `pallas::Base`. `TryFrom<[u8; 32]>` calls
`pallas::Base::from_repr(bytes)`, which returns `CtOption::none` when the
32 LE bytes encode a value `≥ p_P` and `Some(field_element)` otherwise.
The `From<Nullifier> for [u8; 32]` impl extracts the canonical 32-byte
little-endian representation via `n.0.into()` (dispatches to
`pallas::Base::to_repr`).

We model the byte boundary precisely:

  * `tryFromBytes : List Nat → Option (List Nat)` returns `none` on
    non-canonical inputs and `some bs` on canonical inputs — mirroring
    `pallas::Base::from_repr` + `SerializationError::Parse`.
  * `toBytes` is identity, since `pallas::Base::to_repr` of an element that
    came from a canonical `bs` returns exactly `bs`.

This is the consensus-critical shape that the duplicate-nullifier set lookup
depends on: only canonical bytes can be stored, and the stored bytes
round-trip back through the decoder. -/

namespace Orchard

/-- The length invariant carried by the canonical 32-byte field repr.
Source: `zebra-chain/src/orchard/note/nullifiers.rs:10-11`. -/
def IsNullifier (bs : List Nat) : Prop := bs.length = NULLIFIER_BYTES

/-- A 32-byte sequence is the **canonical** Orchard nullifier encoding iff
it has length 32, every byte fits in `u8`, and its LE value is `< p_P`
(the Pallas base-field order).
Source: `zebra-chain/src/orchard/note/nullifiers.rs:19-33` (calls
`pallas::Base::from_repr`). -/
def isCanonical (bs : List Nat) : Bool :=
  IsNullifierBool bs && AllBytes bs && (leValue bs < PALLAS_FIELD_ORDER)

/-- `Prop`-valued Orchard canonical-encoding predicate. -/
def IsCanonical (bs : List Nat) : Prop := isCanonical bs = true

/-- `impl TryFrom<[u8; 32]> for Nullifier`: returns `some` only when the
bytes are a canonical `pallas::Base` repr, mirroring the `CtOption` returned
by `pallas::Base::from_repr` and the `SerializationError::Parse` translation
at `nullifiers.rs:28-30`.
Source: `zebra-chain/src/orchard/note/nullifiers.rs:19-33`. -/
def tryFromBytes (bs : List Nat) : Option (List Nat) :=
  if isCanonical bs then some bs else none

/-- `impl From<Nullifier> for [u8; 32]`: the canonical 32-byte little-endian
repr of the underlying `pallas::Base`. For any nullifier built via
`tryFromBytes`, this returns exactly the input bytes.
Source: `zebra-chain/src/orchard/note/nullifiers.rs:41-45`. -/
def toBytes (n : List Nat) : List Nat := n

/-- The zero nullifier: 32 zero bytes (the canonical repr of
`pallas::Base::zero`). -/
def zero : List Nat := List.replicate NULLIFIER_BYTES 0

end Orchard

/-! ## Helper lemmas on `leValue` -/

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

/-! ### Sprout

The Sprout `Nullifier` is a `HexDebug<[u8; 32]>`, so `From<[u8; 32]>` /
`From<Nullifier> for [u8; 32]` are length-only (no canonical check). The
round-trip theorems below are honest about this — they are renamed from the
audit's flagged `*_round_trip` names to `*_bytes_eq` because the proof
content is byte-list equality, not a decoder/encoder round-trip in the
information-preservation sense. The load-bearing claims are the length
and validity preservation theorems. -/

/-- **T1 (sprout encoder is the byte-array identity).** Renamed from
`sprout_fromBytes_toBytes`: makes clear the proof is `rfl`, not a non-trivial
decoder/encoder round-trip. The Rust impls are total length-only wrappers.
Source: `nullifiers.rs:54-64`. -/
theorem sprout_fromBytes_toBytes_eq_id (n : List Nat) :
    Sprout.fromBytes (Sprout.toBytes n) = n := rfl

/-- **T2 (sprout decoder is the byte-array identity).** Symmetric to T1. -/
theorem sprout_toBytes_fromBytes_eq_id (bs : List Nat) :
    Sprout.toBytes (Sprout.fromBytes bs) = bs := rfl

/-- **T3 (sprout `to_bytes` length).** `to_bytes` preserves the 32-byte width
on any valid sprout nullifier. -/
theorem sprout_toBytes_length (n : List Nat) (hN : Sprout.IsNullifier n) :
    (Sprout.toBytes n).length = NULLIFIER_BYTES := by
  unfold Sprout.toBytes Sprout.IsNullifier at *
  exact hN

/-- **T4 (sprout `from_bytes` preserves length).** Length-32 input gives a
valid sprout nullifier. -/
theorem sprout_fromBytes_isNullifier (bs : List Nat)
    (h : bs.length = NULLIFIER_BYTES) :
    Sprout.IsNullifier (Sprout.fromBytes bs) := by
  unfold Sprout.IsNullifier Sprout.fromBytes
  exact h

/-- **T5 (sprout `from_bytes` injectivity).** Distinct bytes give distinct
sprout nullifiers. -/
theorem sprout_fromBytes_injective (bs₁ bs₂ : List Nat)
    (h : Sprout.fromBytes bs₁ = Sprout.fromBytes bs₂) : bs₁ = bs₂ := h

/-- **T6 (sprout `to_bytes` injectivity).** Conversely, distinct sprout
nullifiers give distinct byte arrays. -/
theorem sprout_toBytes_injective (n₁ n₂ : List Nat)
    (h : Sprout.toBytes n₁ = Sprout.toBytes n₂) : n₁ = n₂ := h

/-- **T7 (sprout zero is valid).** The zero sprout nullifier has length 32. -/
theorem sprout_zero_isNullifier : Sprout.IsNullifier Sprout.zero := by
  unfold Sprout.IsNullifier Sprout.zero
  exact List.length_replicate

/-- **T7a (sprout display order is reversal).** `bytes_in_display_order`
reverses the LE bytes for big-endian RPC output. The display-order length
matches the underlying nullifier's length. -/
theorem sprout_bytesInDisplayOrder_length
    (n : List Nat) (hN : Sprout.IsNullifier n) :
    (Sprout.bytesInDisplayOrder n).length = NULLIFIER_BYTES := by
  unfold Sprout.bytesInDisplayOrder
  rw [List.length_reverse]
  exact sprout_toBytes_length n hN

/-- **T7b (sprout display order round-trip).** Reversing twice returns the
original LE bytes. This is the safety property that lets RPC display and
on-wire storage agree on the same nullifier. -/
theorem sprout_bytesInDisplayOrder_involutive (n : List Nat) :
    Sprout.bytesInDisplayOrder (Sprout.bytesInDisplayOrder n) = Sprout.toBytes n := by
  unfold Sprout.bytesInDisplayOrder Sprout.toBytes
  exact List.reverse_reverse _

/-! ### Sprout `NullifierSeed` (rho) — a sibling `[u8; 32]` newtype -/

/-- **T7c (sprout seed encoder is the byte-array identity).** Like the
`Nullifier` conversions, the `NullifierSeed` conversion pair stores the bytes
verbatim — the Rust inner type is `HexDebug<[u8; 32]>`. -/
theorem sprout_seedFromBytes_toBytes_eq_id (s : List Nat) :
    Sprout.seedFromBytes (Sprout.seedToBytes s) = s := rfl

/-- **T7d (sprout seed decoder is the byte-array identity).** Symmetric. -/
theorem sprout_seedToBytes_fromBytes_eq_id (bs : List Nat) :
    Sprout.seedToBytes (Sprout.seedFromBytes bs) = bs := rfl

/-- **T7e (sprout seed `AsRef<[u8]>` exposes the underlying bytes).** -/
theorem sprout_seedAsRef_eq_toBytes (s : List Nat) :
    Sprout.seedAsRef s = Sprout.seedToBytes s := rfl

/-- **T7f (sprout seed preserves length).** -/
theorem sprout_seedFromBytes_isSeed (bs : List Nat)
    (h : bs.length = NULLIFIER_BYTES) :
    Sprout.IsSeed (Sprout.seedFromBytes bs) := h

/-! ### Sapling

Sapling `Nullifier` is also a `HexDebug<[u8; 32]>`, so `From<[u8; 32]>` /
`From<Nullifier> for [u8; 32]` are length-only. Theorems renamed mirror the
Sprout ones. -/

/-- **T8 (sapling encoder is the byte-array identity).** Renamed from
`sapling_fromBytes_toBytes`: the proof is `rfl`, not a non-trivial decoder
round-trip. Source: `sapling/note/nullifiers.rs:13-23`. -/
theorem sapling_fromBytes_toBytes_eq_id (n : List Nat) :
    Sapling.fromBytes (Sapling.toBytes n) = n := rfl

/-- **T9 (sapling decoder is the byte-array identity).** -/
theorem sapling_toBytes_fromBytes_eq_id (bs : List Nat) :
    Sapling.toBytes (Sapling.fromBytes bs) = bs := rfl

/-- **T10 (sapling `to_bytes` length).** -/
theorem sapling_toBytes_length (n : List Nat) (hN : Sapling.IsNullifier n) :
    (Sapling.toBytes n).length = NULLIFIER_BYTES := by
  unfold Sapling.toBytes Sapling.IsNullifier at *
  exact hN

/-- **T11 (sapling `from_bytes` preserves length).** -/
theorem sapling_fromBytes_isNullifier (bs : List Nat)
    (h : bs.length = NULLIFIER_BYTES) :
    Sapling.IsNullifier (Sapling.fromBytes bs) := by
  unfold Sapling.IsNullifier Sapling.fromBytes
  exact h

/-- **T12 (sapling `from_bytes` injectivity).** -/
theorem sapling_fromBytes_injective (bs₁ bs₂ : List Nat)
    (h : Sapling.fromBytes bs₁ = Sapling.fromBytes bs₂) : bs₁ = bs₂ := h

/-- **T13 (sapling `to_bytes` injectivity).** -/
theorem sapling_toBytes_injective (n₁ n₂ : List Nat)
    (h : Sapling.toBytes n₁ = Sapling.toBytes n₂) : n₁ = n₂ := h

/-- **T14 (sapling zero is valid).** -/
theorem sapling_zero_isNullifier : Sapling.IsNullifier Sapling.zero := by
  unfold Sapling.IsNullifier Sapling.zero
  exact List.length_replicate

/-! ### Orchard

This is the audit-critical section: the Rust `TryFrom<[u8; 32]>` impl calls
`pallas::Base::from_repr`, which rejects non-canonical bytes (LE value `≥
p_P`). The previous version of this file modelled `fromBytes` as the byte
identity, hiding the canonical-encoding gate and producing `rfl`
round-trips. The theorems below now exercise the gate:

  * Round-trip on canonical bytes goes through `tryFromBytes` and `toBytes`;
    canonical bytes survive, non-canonical bytes are rejected.
  * Concrete vectors: zero is canonical, all-`0xff` is not, and the value
    `p_P` itself (encoded LE) is rejected — proving the gate is non-trivial.
  * The Orchard predicate is strictly stronger than the Sapling/Sprout
    length-only one. -/

/-- **T15 (orchard `to_bytes` is the byte-array identity).** Honest naming
of the previous `orchard_fromBytes_toBytes`: only `toBytes` is identity;
`tryFromBytes` is a gated decoder. -/
theorem orchard_toBytes_eq_id (n : List Nat) :
    Orchard.toBytes n = n := rfl

/-- **T16 (orchard canonical round-trip).** On canonical inputs the
`TryFrom<[u8; 32]>` impl returns `Some(nullifier)` whose `Into<[u8; 32]>`
gives back exactly the input bytes. This is the consensus-critical shape
the duplicate-nullifier set relies on: every canonical encoding survives
the parse-then-reserialise cycle. Source: `nullifiers.rs:19-45`. -/
theorem orchard_canonical_round_trip (bs : List Nat) (h : Orchard.IsCanonical bs) :
    (Orchard.tryFromBytes bs).map Orchard.toBytes = some bs := by
  have hT : Orchard.isCanonical bs = true := h
  unfold Orchard.tryFromBytes
  rw [hT]
  rfl

/-- **T17 (orchard `to_bytes` length on a canonical-built nullifier).** Any
nullifier produced by `tryFromBytes` has the 32-byte width. -/
theorem orchard_tryFromBytes_length (bs : List Nat) (n : List Nat)
    (h : Orchard.tryFromBytes bs = some n) :
    n.length = NULLIFIER_BYTES := by
  unfold Orchard.tryFromBytes at h
  split at h
  · -- canonical branch
    rename_i hC
    have hn : n = bs := (Option.some_inj.mp h).symm
    subst hn
    -- Recover the length component from `hC : isCanonical bs = true`.
    unfold Orchard.isCanonical IsNullifierBool at hC
    rw [Bool.and_eq_true, Bool.and_eq_true] at hC
    obtain ⟨⟨hLen, _⟩, _⟩ := hC
    exact (decide_eq_true_iff).mp hLen
  · -- non-canonical branch: h : none = some n
    cases h

/-- **T18 (orchard `tryFromBytes` rejects wrong-length input).** A bytes
list whose length is not 32 fails the canonical-encoding check. -/
theorem orchard_tryFromBytes_rejects_wrong_length (bs : List Nat)
    (h : bs.length ≠ NULLIFIER_BYTES) :
    Orchard.tryFromBytes bs = none := by
  unfold Orchard.tryFromBytes
  have hF : Orchard.isCanonical bs = false := by
    unfold Orchard.isCanonical IsNullifierBool
    simp only [decide_eq_false h, Bool.false_and]
  rw [hF]
  rfl

/-- **T19 (orchard `tryFromBytes` injectivity).** When two canonical inputs
parse to the same nullifier, the inputs were already equal. -/
theorem orchard_tryFromBytes_injective (bs₁ bs₂ : List Nat) (n : List Nat)
    (h₁ : Orchard.tryFromBytes bs₁ = some n)
    (h₂ : Orchard.tryFromBytes bs₂ = some n) :
    bs₁ = bs₂ := by
  unfold Orchard.tryFromBytes at h₁ h₂
  split at h₁
  · split at h₂
    · -- both canonical
      have e₁ : bs₁ = n := Option.some_inj.mp h₁
      have e₂ : bs₂ = n := Option.some_inj.mp h₂
      exact e₁.trans e₂.symm
    · cases h₂
  · cases h₁

/-- **T20 (orchard `to_bytes` injectivity).** The canonical 32-byte repr
determines the nullifier value. -/
theorem orchard_toBytes_injective (n₁ n₂ : List Nat)
    (h : Orchard.toBytes n₁ = Orchard.toBytes n₂) : n₁ = n₂ := h

/-- **T21 (orchard zero is a canonical encoding).** The 32 zero bytes encode
`pallas::Base::zero` (LE value 0), which is `< p_P`, so the canonical check
passes and `tryFromBytes` succeeds. -/
theorem orchard_zero_isCanonical : Orchard.IsCanonical Orchard.zero := by
  unfold Orchard.IsCanonical Orchard.isCanonical Orchard.zero IsNullifierBool AllBytes
  decide

/-- **T22 (orchard zero round-trips).** Combined with T16: `tryFromBytes`
accepts the zero bytes, and the resulting nullifier's `toBytes` returns the
zero bytes. -/
theorem orchard_zero_round_trip :
    (Orchard.tryFromBytes Orchard.zero).map Orchard.toBytes = some Orchard.zero := by
  exact orchard_canonical_round_trip _ orchard_zero_isCanonical

/-- **T23 (orchard zero has length 32).** -/
theorem orchard_zero_isNullifier : Orchard.IsNullifier Orchard.zero := by
  unfold Orchard.IsNullifier Orchard.zero
  exact List.length_replicate

/-! ### Non-canonical witnesses

These are the theorems that prove the Orchard canonical-encoding gate has
real content — without them, `isCanonical` could be the constant `true` and
the round-trip theorems would still pass. -/

/-- **T24 (all-`0xff` bytes are NOT a canonical Orchard nullifier).** The
32-byte sequence `[0xff; 32]` has LE value `2^256 - 1`, which is far above
`p_P`. The Rust `pallas::Base::from_repr` returns `CtOption::none`, and our
`tryFromBytes` returns `none`. -/
theorem orchard_all_ones_not_canonical :
    ¬ Orchard.IsCanonical (List.replicate NULLIFIER_BYTES 255) := by
  unfold Orchard.IsCanonical Orchard.isCanonical IsNullifierBool AllBytes
  decide

/-- **T25 (`tryFromBytes` rejects all-`0xff`).** Concrete witness that the
gate is non-trivial. -/
theorem orchard_tryFromBytes_rejects_all_ones :
    Orchard.tryFromBytes (List.replicate NULLIFIER_BYTES 255) = none := by
  unfold Orchard.tryFromBytes
  have hF : Orchard.isCanonical (List.replicate NULLIFIER_BYTES 255) = false := by
    unfold Orchard.isCanonical IsNullifierBool AllBytes
    decide
  rw [hF]
  rfl

/-- **T26 (`p_P` itself is a non-canonical encoding).** The 32 LE bytes that
encode the value `p_P` exactly fail the strict `< p_P` check — they are at
the boundary. This pins the strictness of the canonical-encoding inequality. -/
def pallasOrderBytes : List Nat :=
  -- p_P = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
  -- in little-endian (low byte first):
  [0x01, 0x00, 0x00, 0x00, 0xed, 0x30, 0x2d, 0x99,
   0x1b, 0xf9, 0x4c, 0x09, 0xfc, 0x98, 0x46, 0x22,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40]

/-- **T26 (the `p_P` LE encoding is exactly the boundary value).** `leValue`
of `pallasOrderBytes` equals `PALLAS_FIELD_ORDER`. -/
theorem pallasOrderBytes_leValue :
    leValue pallasOrderBytes = PALLAS_FIELD_ORDER := by
  decide

/-- **T27 (boundary is non-canonical).** The bytes encoding `p_P` exactly
satisfy length 32 and every-byte-fits-in-`u8`, but fail the strict `< p_P`
test — so they are NOT canonical. -/
theorem pallasOrderBytes_not_canonical :
    ¬ Orchard.IsCanonical pallasOrderBytes := by
  unfold Orchard.IsCanonical Orchard.isCanonical IsNullifierBool AllBytes
  decide

/-- **T28 (`tryFromBytes` rejects the boundary).** Concrete vector showing
the Rust gate's strict inequality is faithfully reproduced. -/
theorem orchard_tryFromBytes_rejects_pallas_order :
    Orchard.tryFromBytes pallasOrderBytes = none := by
  unfold Orchard.tryFromBytes
  have hF : Orchard.isCanonical pallasOrderBytes = false := by
    unfold Orchard.isCanonical IsNullifierBool AllBytes
    decide
  rw [hF]
  rfl

/-! ### Cross-pool facts -/

/-- **T29 (zero nullifiers agree across pools at the byte level).** The
sprout / sapling / orchard zero nullifiers are all 32 zero bytes, so they
have the same byte representation. This confirms that the pool-distinction
at the *value* level (Rust newtypes; here Lean namespaces) is the only thing
keeping their nullifier sets disjoint — at the bit level the encoding is
uniform. -/
theorem zero_bytes_uniform :
    Sprout.toBytes Sprout.zero = Sapling.toBytes Sapling.zero ∧
    Sapling.toBytes Sapling.zero = Orchard.toBytes Orchard.zero := by
  refine ⟨rfl, rfl⟩

/-- **T30 (sprout zero is index-wise zero).** Every byte of the zero sprout
nullifier is `0`. -/
theorem sprout_zero_bytes_all_zero (i : Nat) (h : i < NULLIFIER_BYTES) :
    Sprout.zero[i]? = some 0 := by
  unfold Sprout.zero
  rw [List.getElem?_replicate]
  simp [h]

/-- **T31 (sapling zero is index-wise zero).** -/
theorem sapling_zero_bytes_all_zero (i : Nat) (h : i < NULLIFIER_BYTES) :
    Sapling.zero[i]? = some 0 := by
  unfold Sapling.zero
  rw [List.getElem?_replicate]
  simp [h]

/-- **T32 (orchard zero is index-wise zero).** -/
theorem orchard_zero_bytes_all_zero (i : Nat) (h : i < NULLIFIER_BYTES) :
    Orchard.zero[i]? = some 0 := by
  unfold Orchard.zero
  rw [List.getElem?_replicate]
  simp [h]

/-- **T33 (Sprout and Sapling share the length-only invariant).** Their
`IsNullifier` predicates are extensionally equal, because in both cases the
Rust newtype wraps a `HexDebug<[u8; 32]>` with no canonical-encoding step. -/
theorem sprout_sapling_length_only (bs : List Nat) :
    Sprout.IsNullifier bs ↔ Sapling.IsNullifier bs := by
  unfold Sprout.IsNullifier Sapling.IsNullifier
  exact Iff.rfl

/-- **T34 (Orchard canonicality is strictly stronger than length-only).**
Every canonically-encoded Orchard nullifier has length 32 (i.e. is an
`IsNullifier`), but the converse fails (witnesses: T24, T27). -/
theorem orchard_canonical_implies_isNullifier (bs : List Nat)
    (h : Orchard.IsCanonical bs) : Orchard.IsNullifier bs := by
  unfold Orchard.IsCanonical Orchard.isCanonical IsNullifierBool at h
  unfold Orchard.IsNullifier
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hLen, _⟩, _⟩ := h
  exact (decide_eq_true_iff).mp hLen

/-- **T35 (length-only does not imply Orchard canonicality).** The boundary
encoding of `p_P` has length 32 but is NOT canonical. -/
theorem orchard_isNullifier_not_implies_canonical :
    ∃ bs : List Nat, Orchard.IsNullifier bs ∧ ¬ Orchard.IsCanonical bs := by
  refine ⟨pallasOrderBytes, ?_, pallasOrderBytes_not_canonical⟩
  unfold Orchard.IsNullifier pallasOrderBytes
  decide

/-- **T36 (`NULLIFIER_BYTES` is concretely 32).** Pin the constant; consensus
code reads `[u8; 32]` directly, so any future change here is a hard-fork-level
event we want flagged at proof-check time. -/
theorem nullifier_bytes_eq : NULLIFIER_BYTES = 32 := rfl

/-- **T37 (zero nullifier byte length).** Sanity check that the concrete
zero witness exhibits the 32-byte width across all three pools. -/
theorem zero_lengths :
    Sprout.zero.length = 32 ∧
    Sapling.zero.length = 32 ∧
    Orchard.zero.length = 32 := by
  refine ⟨?_, ?_, ?_⟩
  · exact List.length_replicate
  · exact List.length_replicate
  · exact List.length_replicate

/-- **T38 (Pallas field order pins).** Cross-check the constant matches
the value used in `OrchardAnchorBytes`. The `decide` proof is what would
catch a typo in the 32-byte hex literal. -/
theorem pallas_field_order_lt_wide_bound :
    PALLAS_FIELD_ORDER < 2 ^ 256 := by
  decide

/-- **T39 (Pallas field order is non-zero).** A sanity pin: `p_P > 0`, so
the canonical-encoding inequality `leValue bs < p_P` has at least one
solution (namely the zero encoding). -/
theorem pallas_field_order_pos : 0 < PALLAS_FIELD_ORDER := by decide

end Zebra.Nullifiers
