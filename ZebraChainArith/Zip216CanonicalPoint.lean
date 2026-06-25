import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# ZIP-216: canonical encoding of compressed Jubjub points

ZIP-216 requires that nodes accept only the **canonical** 32-byte encoding of
a compressed Jubjub point. A 32-byte sequence `bs` encodes a Jubjub point by
interpreting the low 255 bits as the affine `v` coordinate (a field element of
the Jubjub base field `F_q`, where
`q = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001`) and
the top bit as the sign of `u`. The encoding is *canonical* iff the encoded
field-element value is strictly less than `q`; otherwise the value modulo `q`
collides with a *different* 32-byte sequence that already represents the same
field element, and ZIP-216 forces the node to reject the duplicate.

In Zebra this canonical-point check is what the `jubjub::AffinePoint::from_bytes`
constructor enforces internally on the
`TransmissionKey::try_from([u8; 32])` and `EphemeralPublicKey::try_from([u8; 32])`
paths:

```rust
/// Attempts to interpret a byte representation of an affine Jubjub point,
/// failing if the element is not on the curve, non-canonical, or not in the
/// prime-order subgroup.
///
/// <https://github.com/zkcrypto/jubjub/blob/master/src/lib.rs#L411>
/// <https://zips.z.cash/zip-0216>
fn try_from(bytes: [u8; 32]) -> Result<Self, Self::Error> {
    let affine_point = jubjub::AffinePoint::from_bytes(bytes).unwrap();
    ...
}
```

Source: `zebra-chain/src/sapling/keys.rs:213-226` (TransmissionKey) and
`zebra-chain/src/sapling/keys.rs:288-310` (EphemeralPublicKey).
Source: <https://zips.z.cash/zip-0216>.

We model the byte-level canonical-encoding check, deliberately abstracting
away the curve/subgroup structure (which lives in the `jubjub` crate and is
not arithmetic in the sense this verification project covers). The model:

  * a 32-byte sequence is a `List Nat` of length `POINT_BYTES = 32`;
  * the underlying field-element value is the little-endian interpretation of
    those 32 bytes as a `Nat`;
  * the encoding is *canonical* iff that value is `< FIELD_ORDER`;
  * canonical encodings form a strict subset of all 32-byte sequences;
  * decoding a non-canonical sequence yields `none`;
  * decoding a canonical sequence round-trips.

The load-bearing claims are:

  1. Canonical encodings are a strict subset of all 32-byte encodings.
  2. The decoder rejects non-canonical sequences.
  3. Canonical encodings survive the decode/encode round-trip.
-/

namespace Zebra.Zip216CanonicalPoint

/-! ## Constants and primitive operations -/

/-- The fixed compressed-Jubjub-point width in bytes (the `[u8; 32]` in the
`jubjub::AffinePoint::from_bytes` argument).
Source: `zebra-chain/src/sapling/keys.rs:219`. -/
def POINT_BYTES : Nat := 32

/-- The Jubjub base-field order `q`, i.e. the modulus of `F_q`. Numerically:

```
0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
```

A 32-byte little-endian value is the canonical encoding of an `F_q` element
iff it is strictly less than this constant.
Source: <https://zips.z.cash/zip-0216>.
Source: jubjub crate `src/fq.rs` `MODULUS` constant. -/
def FIELD_ORDER : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- Maximum encodable 32-byte value plus one: `2^256`. We use this constant
in the strict-subset / range arguments below. By definition this is what
the 32-byte LE encoding can represent. -/
def WIDE_BOUND : Nat := 2 ^ 256

/-- The per-byte upper bound: every `u8` is `< 256`. -/
def BYTE_MAX : Nat := 256

/-- Little-endian interpretation of a byte list as a `Nat`: the head byte is
the least significant. We use this to read out the underlying field-element
value the 32 bytes represent.

For a `[u8; 32]` array `bs`, this equals
`bs[0] + bs[1] * 256 + bs[2] * 256^2 + ... + bs[31] * 256^31`. -/
def leValue : List Nat → Nat
  | []      => 0
  | b :: bs => b + BYTE_MAX * leValue bs

/-- The 32-byte length invariant the Rust `[u8; 32]` type enforces statically. -/
def IsPointBytes (bs : List Nat) : Bool := bs.length = POINT_BYTES

/-- The per-byte well-formedness predicate: every byte fits in 8 bits. We
state it as a `Bool`-valued list-level test so that the canonical-encoding
predicate is decidable by construction. -/
def AllBytes (bs : List Nat) : Bool := bs.all (· < BYTE_MAX)

/-! ## Canonical encoding -/

/-- A 32-byte sequence is the **canonical** ZIP-216 encoding of a Jubjub
field element iff:

  * it has the fixed `POINT_BYTES = 32` length,
  * each byte is `< 256` (i.e. fits in `u8`),
  * its little-endian value is `< FIELD_ORDER`.

Defined as a `Bool` so that `decode` below can use plain `if`-on-bool.
Source: <https://zips.z.cash/zip-0216>. -/
def isCanonical (bs : List Nat) : Bool :=
  IsPointBytes bs && AllBytes bs && (leValue bs < FIELD_ORDER)

/-- `Prop`-valued canonical-encoding predicate, derived from the `Bool` one
for use in theorem statements. -/
def IsCanonical (bs : List Nat) : Prop := isCanonical bs = true

/-- The set-theoretic predicate "is a 32-byte sequence whose bytes fit in
8 bits". This is the ambient set the ZIP-216 canonical encodings are a
*subset* of. -/
def IsAnyPointEncoding (bs : List Nat) : Prop :=
  IsPointBytes bs = true ∧ AllBytes bs = true

/-! ## Decoder model

We model `jubjub::AffinePoint::from_bytes` as a partial function that:

  * rejects wrong-length sequences;
  * rejects non-canonical sequences (this is the ZIP-216 check);
  * returns the underlying field-element value on success.

The on-curve and prime-subgroup checks are out of scope for this module —
they live above the canonical-encoding gate the ZIP enforces. -/

/-- Decode a 32-byte sequence into a field-element value, enforcing the
ZIP-216 canonical-encoding check. Returns `some v` on success and `none`
on any failure (wrong length, byte out of `u8` range, non-canonical).
Source: `zebra-chain/src/sapling/keys.rs:218-219`. -/
def decode (bs : List Nat) : Option Nat :=
  if isCanonical bs then some (leValue bs) else none

/-- Encode a field-element value `v` (assumed already reduced, i.e.
`v < FIELD_ORDER`) into its canonical 32-byte little-endian form. We model
this abstractly by accepting an explicit byte-list witness whose `leValue`
equals `v` and whose canonical-encoding predicate holds; the `jubjub`
crate's `to_bytes` is implemented exactly as "write 32 little-endian bytes
of the canonical representative", so any canonical `bs` with `leValue bs = v`
is what `to_bytes(v)` would produce. -/
def encode (v : Nat) (bs : List Nat) : Option (List Nat) :=
  if isCanonical bs && (leValue bs = v) then some bs else none

/-! ## Helper lemmas on `leValue` -/

/-- `leValue` of the empty list is `0`. -/
theorem leValue_nil : leValue [] = 0 := rfl

/-- `leValue` on a cons is the head plus 256 times the tail's value. -/
theorem leValue_cons (b : Nat) (bs : List Nat) :
    leValue (b :: bs) = b + BYTE_MAX * leValue bs := rfl

/-! ## Theorems

The load-bearing claims of this module: canonical encodings are a strict
subset of all 32-byte sequences; the decoder rejects non-canonical inputs;
canonical encodings round-trip through `decode`/`encode`. -/

/-- **T1.** The Jubjub field order is strictly less than the 32-byte
encoding's upper bound `2^256`.

This is what makes non-canonical encodings *possible*: the codomain of `[u8;
32]` is larger than `F_q`, so there exist 32-byte sequences whose LE value
is `≥ FIELD_ORDER`. -/
theorem field_order_lt_wide_bound : FIELD_ORDER < WIDE_BOUND := by
  decide

/-- **T2.** The Jubjub field order is strictly positive. -/
theorem field_order_pos : 0 < FIELD_ORDER := by decide

/-- **T3.** Every canonical encoding is a valid 32-byte encoding. The
inclusion `Canonical ⊆ AnyPointEncoding` is by definition. -/
theorem canonical_is_point_encoding (bs : List Nat) (h : IsCanonical bs) :
    IsAnyPointEncoding bs := by
  unfold IsCanonical isCanonical at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

/-- **T4 (strict-subset witness).** There exists a 32-byte sequence whose
bytes all fit in `u8` but which is *not* a canonical ZIP-216 encoding. The
witness is `[0xff, 0xff, ..., 0xff]` (thirty-two `0xff` bytes), whose LE
value is `2^256 - 1`, much larger than `FIELD_ORDER`. -/
theorem exists_noncanonical : ∃ bs : List Nat,
    IsAnyPointEncoding bs ∧ ¬ IsCanonical bs := by
  refine ⟨List.replicate POINT_BYTES 255, ?_, ?_⟩
  · -- it's a valid 32-byte encoding
    constructor
    · -- length is 32
      unfold IsPointBytes POINT_BYTES
      simp
    · -- every byte is < 256
      unfold AllBytes BYTE_MAX
      simp
  · -- but it's NOT canonical: its LE value is ≥ FIELD_ORDER
    unfold IsCanonical isCanonical
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
    intro _
    -- compute the LE value of 32 0xff bytes and compare to FIELD_ORDER
    decide

/-- **T5 (strict-subset proof).** Canonical encodings are a *strict* subset
of valid 32-byte encodings: every canonical encoding is valid, but not every
valid 32-byte encoding is canonical.

This is the load-bearing "ZIP-216 makes some encodings illegal" claim. -/
theorem canonical_strict_subset :
    (∀ bs, IsCanonical bs → IsAnyPointEncoding bs) ∧
    (∃ bs, IsAnyPointEncoding bs ∧ ¬ IsCanonical bs) :=
  ⟨canonical_is_point_encoding, exists_noncanonical⟩

/-- **T6.** The decoder accepts canonical encodings: on a canonical input
`bs`, `decode bs` returns the LE field-element value. -/
theorem decode_canonical (bs : List Nat) (h : IsCanonical bs) :
    decode bs = some (leValue bs) := by
  unfold decode
  simp [show isCanonical bs = true from h]

/-- **T7.** The decoder rejects non-canonical encodings: if `bs` is not
canonical, `decode bs = none`. This is the ZIP-216 enforcement statement
at the byte level. -/
theorem decode_noncanonical (bs : List Nat) (h : ¬ IsCanonical bs) :
    decode bs = none := by
  unfold decode
  have : isCanonical bs = false := by
    cases hc : isCanonical bs
    · rfl
    · exfalso; exact h hc
  simp [this]

/-- **T8.** A successful decode yields a value that fits in `F_q`. This is
the post-condition the `jubjub::AffinePoint::from_bytes`-callers downstream
in `TransmissionKey::try_from` rely on. -/
theorem decode_value_lt_field_order (bs : List Nat) (v : Nat)
    (h : decode bs = some v) : v < FIELD_ORDER := by
  unfold decode at h
  by_cases hC : isCanonical bs
  · -- canonical case
    rw [if_pos hC] at h
    simp only [Option.some.injEq] at h
    -- `IsCanonical bs` ↔ `isCanonical bs = true`; extract `leValue bs < FIELD_ORDER`
    have hCan : IsCanonical bs := hC
    unfold IsCanonical isCanonical at hCan
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hCan
    rw [← h]
    exact hCan.2
  · rw [if_neg hC] at h
    cases h

/-- **T9.** A successful decode implies the input was a canonical encoding.
The decoder is "tight": there is no `some` output without canonical input. -/
theorem decode_some_implies_canonical (bs : List Nat) (v : Nat)
    (h : decode bs = some v) : IsCanonical bs := by
  unfold decode at h
  by_cases hC : isCanonical bs
  · exact hC
  · rw [if_neg hC] at h
    cases h

/-- **T10.** Concrete rejection: the all-`0xff` 32-byte sequence — a valid
`[u8; 32]` — is rejected by `decode` because it is non-canonical. This is
the ZIP-216 rejection in action.

Note that for non-`[u8; 32]` Rust callers this would never happen, but the
`from_bytes` constructor still has to reject it; that's the ZIP. -/
theorem decode_rejects_all_ff :
    decode (List.replicate POINT_BYTES 255) = none := by
  unfold decode
  have h : isCanonical (List.replicate POINT_BYTES 255) = false := by decide
  simp [h]

/-- **T11.** Canonical encoding round-trips through `encode ∘ decode`: any
canonical 32-byte sequence is recovered by re-encoding the value the
decoder extracted. -/
theorem encode_decode_roundtrip (bs : List Nat) (h : IsCanonical bs) :
    encode (leValue bs) bs = some bs := by
  unfold encode
  have hC : isCanonical bs = true := h
  simp [hC]

/-- **T12.** Decoder round-trip for canonical inputs: starting from a
canonical byte sequence, decoding yields its LE value, and re-encoding
returns the original bytes. -/
theorem decode_then_encode (bs : List Nat) (h : IsCanonical bs) :
    (decode bs).bind (fun v => encode v bs) = some bs := by
  rw [decode_canonical bs h, Option.bind_some]
  exact encode_decode_roundtrip bs h

/-- **T13.** The decoder is wrong-length-rejecting: any sequence whose
length is not 32 is rejected (because `isCanonical` requires the length
invariant). -/
theorem decode_rejects_wrong_length (bs : List Nat) (h : bs.length ≠ POINT_BYTES) :
    decode bs = none := by
  apply decode_noncanonical
  intro hCan
  unfold IsCanonical isCanonical at hCan
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hCan
  apply h
  have hLen : IsPointBytes bs = true := hCan.1.1
  unfold IsPointBytes at hLen
  simpa using hLen

/-- **T14.** A 32-byte sequence whose LE value is `≥ FIELD_ORDER` is
guaranteed non-canonical. This is exactly the ZIP-216 non-canonical
condition. -/
theorem noncanonical_of_value_ge_field_order (bs : List Nat)
    (hVal : FIELD_ORDER ≤ leValue bs) :
    ¬ IsCanonical bs := by
  intro hCan
  unfold IsCanonical isCanonical at hCan
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hCan
  have : leValue bs < FIELD_ORDER := hCan.2
  omega

/-- **T15.** Canonical encoding is decidable on concrete byte lists (length,
byte ranges, and an inequality of `Nat` are all decidable). -/
instance instDecidableIsCanonical (bs : List Nat) : Decidable (IsCanonical bs) := by
  unfold IsCanonical
  exact instDecidableEqBool _ _

/-- **T16 (range tightness).** Every value the decoder returns is in
`{0, 1, …, FIELD_ORDER - 1}` — the residue range of `F_q`. -/
theorem decode_range (bs : List Nat) (v : Nat) (h : decode bs = some v) :
    v < FIELD_ORDER := decode_value_lt_field_order bs v h

/-- **T17 (round-trip on the inner value).** For any canonical encoding `bs`,
the field-element value the decoder returns is uniquely determined by `bs`,
and re-encoding via `encode v bs` recovers the original bytes. This is the
combined round-trip statement. -/
theorem decode_value_unique_and_roundtrip (bs : List Nat) (h : IsCanonical bs) :
    ∃ v, decode bs = some v ∧ v < FIELD_ORDER ∧ encode v bs = some bs := by
  have hLE : leValue bs < FIELD_ORDER := by
    unfold IsCanonical isCanonical at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  exact ⟨leValue bs, decode_canonical bs h, hLE, encode_decode_roundtrip bs h⟩

/-- **T18 (encode rejects non-matching values).** The `encode` model only
accepts a `(v, bs)` pair when `bs` is canonical *and* its LE value really
is `v`. Mismatched pairs return `none`. -/
theorem encode_rejects_mismatch (v : Nat) (bs : List Nat)
    (h : leValue bs ≠ v) : encode v bs = none := by
  unfold encode
  have : (isCanonical bs && (leValue bs = v)) = false := by
    by_cases hC : isCanonical bs = true
    · simp [hC, h]
    · simp [Bool.eq_false_iff.mpr hC]
  simp [this]

end Zebra.Zip216CanonicalPoint
