import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# 32-byte nullifier round-trip across shielded pools

Sprout, Sapling and Orchard all encode a nullifier as a 32-byte value that the
chain stores in a per-pool nullifier set; duplicate-nullifier detection is the
consensus mechanism that prevents shielded double-spends.

Concretely:

  * `sprout::note::Nullifier` is `pub struct Nullifier(pub HexDebug<[u8; 32]>);`
    with bidirectional `From<[u8; 32]>` / `From<Nullifier> for [u8; 32]` impls.
    Source: `zebra-chain/src/sprout/note/nullifiers.rs:42-70`.
  * `sapling::note::Nullifier` is `pub struct Nullifier(pub HexDebug<[u8; 32]>);`
    with the same conversion pair.
    Source: `zebra-chain/src/sapling/note/nullifiers.rs:11-23`.
  * `orchard::note::Nullifier(pallas::Base)` is a 32-byte serialised
    `pallas::Base`. `From<Nullifier> for [u8; 32]` returns the canonical
    little-endian byte repr; `TryFrom<[u8; 32]>` succeeds when the bytes are a
    canonical `pallas::Base` repr. Round-trip on the *bytes* (canonical
    encoding) is what the consensus-critical nullifier-set lookup relies on.
    Source: `zebra-chain/src/orchard/note/nullifiers.rs:10-46`.

We do **not** model the underlying `pallas::Base` field arithmetic — round-trip
on the bytes is what is consensus-critical for the nullifier-set lookup that
prevents double-spends. We model each pool's nullifier as a `List Nat` of
length 32 (each byte implicitly `< 256`), with the length invariant tracked
via the `IsNullifier` predicate.

The three pools are kept in sibling sub-namespaces so the proofs mirror the
Rust-level newtype distinction that keeps the nullifier sets disjoint at the
type level.
-/

namespace Zebra.Nullifiers

/-- The fixed nullifier width in bytes (the `32` in `[u8; 32]`).
Source: `zebra-chain/src/sprout/note/nullifiers.rs:42`,
`zebra-chain/src/sapling/note/nullifiers.rs:11`,
`zebra-chain/src/orchard/note/nullifiers.rs:10`. -/
def NULLIFIER_BYTES : Nat := 32

/-! ## Sprout nullifier (`zebra-chain/src/sprout/note/nullifiers.rs`) -/

namespace Sprout

/-- The length invariant carried by the Rust `[u8; 32]` type.
Source: `zebra-chain/src/sprout/note/nullifiers.rs:42`. -/
def IsNullifier (bs : List Nat) : Prop := bs.length = NULLIFIER_BYTES

/-- `impl From<[u8; 32]> for Nullifier`: wraps the byte array.
Source: `zebra-chain/src/sprout/note/nullifiers.rs:54-58`. -/
def fromBytes (bs : List Nat) : List Nat := bs

/-- `impl From<Nullifier> for [u8; 32]`: extracts the byte array.
Source: `zebra-chain/src/sprout/note/nullifiers.rs:60-64`. -/
def toBytes (n : List Nat) : List Nat := n

/-- The zero nullifier: 32 zero bytes. Not a `Default` impl in Rust, but a
useful concrete witness that the 32-byte invariant is inhabitable. -/
def zero : List Nat := List.replicate NULLIFIER_BYTES 0

end Sprout

/-! ## Sapling nullifier (`zebra-chain/src/sapling/note/nullifiers.rs`) -/

namespace Sapling

/-- The length invariant carried by the Rust `[u8; 32]` type.
Source: `zebra-chain/src/sapling/note/nullifiers.rs:11`. -/
def IsNullifier (bs : List Nat) : Prop := bs.length = NULLIFIER_BYTES

/-- `impl From<[u8; 32]> for Nullifier`: wraps the byte array.
Source: `zebra-chain/src/sapling/note/nullifiers.rs:13-17`. -/
def fromBytes (bs : List Nat) : List Nat := bs

/-- `impl From<Nullifier> for [u8; 32]`: extracts the byte array.
Source: `zebra-chain/src/sapling/note/nullifiers.rs:19-23`. -/
def toBytes (n : List Nat) : List Nat := n

/-- The zero nullifier: 32 zero bytes. -/
def zero : List Nat := List.replicate NULLIFIER_BYTES 0

end Sapling

/-! ## Orchard nullifier (`zebra-chain/src/orchard/note/nullifiers.rs`)

The Rust type wraps a `pallas::Base`, but the `From<Nullifier> for [u8; 32]`
extracts the canonical 32-byte little-endian field repr, and the
`TryFrom<[u8; 32]> for Nullifier` parses the bytes back through
`pallas::Base::from_repr`. Round-trip on the bytes is what the nullifier-set
lookup uses — we don't model the underlying field. -/

namespace Orchard

/-- The length invariant carried by the canonical 32-byte field repr.
Source: `zebra-chain/src/orchard/note/nullifiers.rs:10-11`. -/
def IsNullifier (bs : List Nat) : Prop := bs.length = NULLIFIER_BYTES

/-- `impl TryFrom<[u8; 32]> for Nullifier`: at the byte level we treat the
canonical repr as valid (round-trip witnesses the part of the API that the
nullifier-set lookup depends on).
Source: `zebra-chain/src/orchard/note/nullifiers.rs:19-33`. -/
def fromBytes (bs : List Nat) : List Nat := bs

/-- `impl From<Nullifier> for [u8; 32]`: canonical 32-byte little-endian repr.
Source: `zebra-chain/src/orchard/note/nullifiers.rs:41-45`. -/
def toBytes (n : List Nat) : List Nat := n

/-- The zero nullifier: 32 zero bytes (the canonical repr of
`pallas::Base::zero`). -/
def zero : List Nat := List.replicate NULLIFIER_BYTES 0

end Orchard

/-! ## Theorems -/

/-! ### Sprout -/

/-- **T1 (sprout round-trip).** `fromBytes (toBytes n) = n` for any nullifier;
the bytes-to-nullifier and nullifier-to-bytes Rust impls compose to the
identity. -/
theorem sprout_fromBytes_toBytes (n : List Nat) :
    Sprout.fromBytes (Sprout.toBytes n) = n := rfl

/-- **T2 (sprout constructor round-trip).** `toBytes (fromBytes bs) = bs`. -/
theorem sprout_toBytes_fromBytes (bs : List Nat) :
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

/-! ### Sapling -/

/-- **T8 (sapling round-trip).** `fromBytes (toBytes n) = n`. -/
theorem sapling_fromBytes_toBytes (n : List Nat) :
    Sapling.fromBytes (Sapling.toBytes n) = n := rfl

/-- **T9 (sapling constructor round-trip).** `toBytes (fromBytes bs) = bs`. -/
theorem sapling_toBytes_fromBytes (bs : List Nat) :
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

/-! ### Orchard -/

/-- **T15 (orchard round-trip).** `fromBytes (toBytes n) = n`. -/
theorem orchard_fromBytes_toBytes (n : List Nat) :
    Orchard.fromBytes (Orchard.toBytes n) = n := rfl

/-- **T16 (orchard constructor round-trip).** `toBytes (fromBytes bs) = bs`. -/
theorem orchard_toBytes_fromBytes (bs : List Nat) :
    Orchard.toBytes (Orchard.fromBytes bs) = bs := rfl

/-- **T17 (orchard `to_bytes` length).** -/
theorem orchard_toBytes_length (n : List Nat) (hN : Orchard.IsNullifier n) :
    (Orchard.toBytes n).length = NULLIFIER_BYTES := by
  unfold Orchard.toBytes Orchard.IsNullifier at *
  exact hN

/-- **T18 (orchard `from_bytes` preserves length).** -/
theorem orchard_fromBytes_isNullifier (bs : List Nat)
    (h : bs.length = NULLIFIER_BYTES) :
    Orchard.IsNullifier (Orchard.fromBytes bs) := by
  unfold Orchard.IsNullifier Orchard.fromBytes
  exact h

/-- **T19 (orchard `from_bytes` injectivity).** -/
theorem orchard_fromBytes_injective (bs₁ bs₂ : List Nat)
    (h : Orchard.fromBytes bs₁ = Orchard.fromBytes bs₂) : bs₁ = bs₂ := h

/-- **T20 (orchard `to_bytes` injectivity).** -/
theorem orchard_toBytes_injective (n₁ n₂ : List Nat)
    (h : Orchard.toBytes n₁ = Orchard.toBytes n₂) : n₁ = n₂ := h

/-- **T21 (orchard zero is valid).** -/
theorem orchard_zero_isNullifier : Orchard.IsNullifier Orchard.zero := by
  unfold Orchard.IsNullifier Orchard.zero
  exact List.length_replicate

/-! ### Cross-pool facts -/

/-- **T22 (zero nullifiers agree across pools at the byte level).** The
sprout / sapling / orchard zero nullifiers are all 32 zero bytes, so they have
the same byte representation. This confirms that the pool-distinction at the
*value* level (Rust newtypes; here Lean namespaces) is the only thing keeping
their nullifier sets disjoint — at the bit level the encoding is uniform. -/
theorem zero_bytes_uniform :
    Sprout.toBytes Sprout.zero = Sapling.toBytes Sapling.zero ∧
    Sapling.toBytes Sapling.zero = Orchard.toBytes Orchard.zero := by
  refine ⟨rfl, rfl⟩

/-- **T23 (sprout zero is index-wise zero).** Every byte of the zero sprout
nullifier is `0`. -/
theorem sprout_zero_bytes_all_zero (i : Nat) (h : i < NULLIFIER_BYTES) :
    Sprout.zero[i]? = some 0 := by
  unfold Sprout.zero
  rw [List.getElem?_replicate]
  simp [h]

/-- **T24 (sapling zero is index-wise zero).** -/
theorem sapling_zero_bytes_all_zero (i : Nat) (h : i < NULLIFIER_BYTES) :
    Sapling.zero[i]? = some 0 := by
  unfold Sapling.zero
  rw [List.getElem?_replicate]
  simp [h]

/-- **T25 (orchard zero is index-wise zero).** -/
theorem orchard_zero_bytes_all_zero (i : Nat) (h : i < NULLIFIER_BYTES) :
    Orchard.zero[i]? = some 0 := by
  unfold Orchard.zero
  rw [List.getElem?_replicate]
  simp [h]

/-- **T26 (all pools agree on the 32-byte width invariant).** This is what
makes `[u8; 32]` representable in Rust uniformly across the three nullifier
pools. -/
theorem all_pools_width_eq (bs : List Nat) :
    (Sprout.IsNullifier bs ↔ bs.length = NULLIFIER_BYTES) ∧
    (Sapling.IsNullifier bs ↔ bs.length = NULLIFIER_BYTES) ∧
    (Orchard.IsNullifier bs ↔ bs.length = NULLIFIER_BYTES) := by
  refine ⟨?_, ?_, ?_⟩ <;> exact Iff.rfl

/-- **T27 (`NULLIFIER_BYTES` is concretely 32).** Pin the constant; consensus
code reads `[u8; 32]` directly, so any future change here is a hard-fork-level
event we want flagged at proof-check time. -/
theorem nullifier_bytes_eq : NULLIFIER_BYTES = 32 := rfl

/-- **T28 (zero nullifier byte length).** Sanity check that the concrete zero
witness exhibits the 32-byte width across all three pools. -/
theorem zero_lengths :
    Sprout.zero.length = 32 ∧
    Sapling.zero.length = 32 ∧
    Orchard.zero.length = 32 := by
  refine ⟨?_, ?_, ?_⟩
  · exact List.length_replicate
  · exact List.length_replicate
  · exact List.length_replicate

end Zebra.Nullifiers
