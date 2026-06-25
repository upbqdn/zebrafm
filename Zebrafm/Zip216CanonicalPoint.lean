import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# ZIP-216: canonical encoding of compressed Jubjub points

ZIP-216 requires that nodes reject the **non-canonical** 32-byte encodings of
a compressed Jubjub point. The compressed encoding interprets the low 255 bits
as the affine `v` coordinate (a field element of the Jubjub base field `F_q`,
where `q = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001`)
and the top bit as the sign of `u`.

The ZIP-216 specification is precise about *which* 32-byte sequences are
non-canonical: it defines a non-canonical compressed encoding to be a sequence
of 256 bits `b` such that `abst(b) ≠ ⊥` (the sequence does decode to some
Jubjub point) **and** `repr(abst(b)) ≠ b` (the canonical re-encoding of that
point differs from `b`). The non-normative note in `zip-0216.rst:96-101`
enumerates these:

> There are two such bit sequences,
> `I2LEOSP_{ℓ_J}(2^255 + 1)` and `I2LEOSP_{ℓ_J}(2^255 + q_J - 1)`.

That is the *complete* list of ZIP-216-rejected encodings. Sequences whose
underlying value is `≥ q` but `≠ 2^255 + 1` and `≠ 2^255 + q - 1` are NOT
"non-canonical" in the ZIP-216 sense — they are invalid for an unrelated
reason (`abst` returns `⊥` because there is no point with that `v`).

In Zebra the ZIP-216 enforcement piggybacks on `jubjub::AffinePoint::from_bytes`,
which rejects both classes (non-canonical *and* invalid) and is called from
`TransmissionKey::try_from([u8; 32])` and `EphemeralPublicKey::try_from([u8; 32])`:

```rust
/// Attempts to interpret a byte representation of an affine Jubjub point,
/// failing if the element is not on the curve, non-canonical, or not in the
/// prime-order subgroup.
fn try_from(bytes: [u8; 32]) -> Result<Self, Self::Error> {
    let affine_point = jubjub::AffinePoint::from_bytes(bytes).unwrap();
    ...
}
```

Source: `zebra-chain/src/sapling/keys.rs:213-226` (TransmissionKey) and
`zebra-chain/src/sapling/keys.rs:285-310` (EphemeralPublicKey).
Source: <https://zips.z.cash/zip-0216>.

**Important Zebra-vs-ZIP divergence.** The `TransmissionKey::try_from` call
site uses `.unwrap()` on the `CtOption` returned by `AffinePoint::from_bytes`:
it panics on any failure of the canonical/on-curve check rather than returning
an `Err`. The `EphemeralPublicKey::try_from` call site at
`zebra-chain/src/sapling/keys.rs:298-309` handles `None` correctly. This file
records that asymmetry — both as a model and as a theorem — so the audit
captures the behavioural divergence rather than papering over it.

We model the byte-level canonical-encoding check, deliberately abstracting
away the curve/subgroup structure (which lives in the `jubjub` crate and is
not arithmetic in the sense this verification project covers). The model
captures the *exact* ZIP-216 non-canonical set, not the over-approximation
"value `≥ q`", and adds per-site application theorems for the four call
sites the ZIP enumerates as needing the check.

The load-bearing claims are:

  1. The non-canonical set is exactly the two encodings from `zip-0216.rst:96-101`.
  2. The decoder rejects both non-canonical encodings.
  3. The four ZIP-216 application sites (`spendAuthSig.R`,
     `bindingSigSapling.R`, `pk_d`, and the implicit
     `jubjub::AffinePoint::from_bytes` gate) reuse the same byte-level check.
  4. `TransmissionKey::try_from` panics on rejection (Zebra divergence from
     the `Option` shape); `EphemeralPublicKey::try_from` returns `Err`.
-/

namespace Zebra.Zip216CanonicalPoint

/-! ## Constants and primitive operations -/

/-- The fixed compressed-Jubjub-point width in bytes (the `[u8; 32]` in the
`jubjub::AffinePoint::from_bytes` argument).
Source: `zebra-chain/src/sapling/keys.rs:218`. -/
def POINT_BYTES : Nat := 32

/-- The Jubjub base-field order `q_J`. Numerically:

```
0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
```

A 32-byte little-endian value is the canonical encoding of an `F_q` element
iff it is strictly less than this constant.
Source: <https://zips.z.cash/zip-0216>.
Source: jubjub crate `src/fq.rs` `MODULUS` constant. -/
def FIELD_ORDER : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- The compressed-encoding "sign bit" mask: `2^255`. The top bit of the
32-byte LE value denotes the sign of `u`; the low 255 bits encode `v`. -/
def SIGN_BIT : Nat := 2 ^ 255

/-- Maximum encodable 32-byte value plus one: `2^256`. -/
def WIDE_BOUND : Nat := 2 ^ 256

/-- The per-byte upper bound: every `u8` is `< 256`. -/
def BYTE_MAX : Nat := 256

/-- The first ZIP-216 non-canonical encoding, as a `Nat`:
`I2LEOSP_{ℓ_J}(2^255 + 1)`. The corresponding byte sequence is
`[0x01, 0x00, ..., 0x00, 0x80]` (a `0x01` byte, then thirty `0x00` bytes,
then a `0x80` byte). Source: `zip-0216.rst:96-101`. -/
def NONCANON_LO : Nat := SIGN_BIT + 1

/-- The second ZIP-216 non-canonical encoding, as a `Nat`:
`I2LEOSP_{ℓ_J}(2^255 + q_J - 1)`. Source: `zip-0216.rst:96-101`. -/
def NONCANON_HI : Nat := SIGN_BIT + FIELD_ORDER - 1

/-- Little-endian interpretation of a byte list as a `Nat`: the head byte is
the least significant. For a `[u8; 32]` array `bs`, this equals
`bs[0] + bs[1] * 256 + bs[2] * 256^2 + ... + bs[31] * 256^31`. -/
def leValue : List Nat → Nat
  | []      => 0
  | b :: bs => b + BYTE_MAX * leValue bs

/-- The 32-byte length invariant the Rust `[u8; 32]` type enforces statically. -/
def IsPointBytes (bs : List Nat) : Bool := bs.length = POINT_BYTES

/-- The per-byte well-formedness predicate: every byte fits in 8 bits. -/
def AllBytes (bs : List Nat) : Bool := bs.all (· < BYTE_MAX)

/-! ## ZIP-216 non-canonical encodings

Per `zip-0216.rst:92-101`, a non-canonical compressed encoding is a 256-bit
sequence `b` satisfying

  * `abst_J(b) ≠ ⊥` (`b` decodes to some Jubjub point), and
  * `repr_J(abst_J(b)) ≠ b` (the canonical re-encoding differs from `b`).

The non-normative note enumerates exactly two such sequences. The point of
this section is to model *that exact two-element set*, not the larger
"value ≥ q" set the previous version of this module rejected. -/

/-- A 32-byte sequence is **ZIP-216 non-canonical** iff it is the LE encoding
of one of the two specific values `NONCANON_LO` or `NONCANON_HI`.

This is the precise statement of the ZIP-216 non-canonical set, which a
previous version of this module conflated with the strictly larger "value
`≥ FIELD_ORDER`" set. The latter contains points that fail `abst_J` for
the unrelated reason that no Jubjub point has the requested `v` coordinate,
and which the ZIP does *not* classify as non-canonical.

Source: `zip-0216.rst:92-101`. -/
def isNonCanonical (bs : List Nat) : Bool :=
  IsPointBytes bs && AllBytes bs &&
    ((leValue bs = NONCANON_LO) || (leValue bs = NONCANON_HI))

/-- `Prop`-valued non-canonical predicate. -/
def IsNonCanonical (bs : List Nat) : Prop := isNonCanonical bs = true

/-- A 32-byte sequence is **ZIP-216 canonical** iff its bytes are valid and
it is *not* in the two-element non-canonical set. This is the predicate the
ZIP requires Sapling consensus to enforce on the application sites listed in
`zip-0216.rst:104-122`. -/
def isCanonical (bs : List Nat) : Bool :=
  IsPointBytes bs && AllBytes bs && !isNonCanonical bs

/-- `Prop`-valued canonical-encoding predicate. -/
def IsCanonical (bs : List Nat) : Prop := isCanonical bs = true

/-- "Valid 32-byte encoding of any kind", the ambient set canonical and
non-canonical encodings sit inside. -/
def IsAnyPointEncoding (bs : List Nat) : Prop :=
  IsPointBytes bs = true ∧ AllBytes bs = true

/-! ## Decoder models

We model two separate decoder shapes corresponding to the two `try_from`
implementations in `zebra-chain/src/sapling/keys.rs`:

  * `decodeOption` — the safe `Option`-returning shape used by
    `EphemeralPublicKey::try_from` (`keys.rs:298-309`); returns `none` on
    any failure.

  * `decodePanicOnNone` — the panicking shape used by
    `TransmissionKey::try_from` (`keys.rs:213-226`), which calls `.unwrap()`
    on the `CtOption` from `jubjub::AffinePoint::from_bytes`. Modelled here
    as a `Sum` with explicit `panic` constructor so the panic surfaces in
    the type rather than being hidden as `none`.

The on-curve and prime-subgroup checks live above this byte-level gate. -/

/-- The result of a panicking decoder: either a successful value or a
panic. We use this in place of `Option` for `TransmissionKey::try_from` so
the `.unwrap()` panic is explicit in the type signature.

Source: `zebra-chain/src/sapling/keys.rs:219`. -/
inductive PanickyResult (α : Type) : Type
  | ok    : α → PanickyResult α
  | panic : PanickyResult α
  deriving DecidableEq

/-- Safe `Option`-returning decoder matching `EphemeralPublicKey::try_from`.
Returns `none` on non-canonical input, wrong length, or out-of-range bytes.
Source: `zebra-chain/src/sapling/keys.rs:298-309`. -/
def decodeOption (bs : List Nat) : Option Nat :=
  if isCanonical bs then some (leValue bs) else none

/-- Panicking decoder matching `TransmissionKey::try_from`'s `.unwrap()` call.
This panics on every input the safe decoder would reject — exactly the
behavioural divergence from the ZIP-prescribed `Option` shape.

A separate file should also exist tracking this as a Zebra issue.
Source: `zebra-chain/src/sapling/keys.rs:219`. -/
def decodePanicOnNone (bs : List Nat) : PanickyResult Nat :=
  if isCanonical bs then PanickyResult.ok (leValue bs) else PanickyResult.panic

/-- Re-encode a field-element value `v` (assumed already reduced, i.e.
`v < FIELD_ORDER`) into its canonical 32-byte LE form. We model it via the
explicit byte-list witness whose `leValue` equals `v` and whose canonical
predicate holds. -/
def encode (v : Nat) (bs : List Nat) : Option (List Nat) :=
  if isCanonical bs && (leValue bs = v) then some bs else none

/-! ## Helper lemmas on `leValue` -/

/-- `leValue` of the empty list is `0`. -/
theorem leValue_nil : leValue [] = 0 := rfl

/-- `leValue` on a cons is the head plus 256 times the tail's value. -/
theorem leValue_cons (b : Nat) (bs : List Nat) :
    leValue (b :: bs) = b + BYTE_MAX * leValue bs := rfl

/-! ## Theorems

The load-bearing claims of this module:

  * `NONCANON_LO` and `NONCANON_HI` are the exact ZIP-216 non-canonical set.
  * Both safe and panicking decoders reject them.
  * Canonical encodings round-trip through `decodeOption`/`encode`.
  * Per-site application theorems for the four ZIP-216 enforcement sites. -/

/-- **T1.** The Jubjub field order is strictly less than the 32-byte
encoding's upper bound `2^256`.

This is what makes non-canonical encodings possible at all: the codomain of
`[u8; 32]` is larger than `F_q`, so there exist 32-byte sequences whose LE
value is `≥ FIELD_ORDER`. -/
theorem field_order_lt_wide_bound : FIELD_ORDER < WIDE_BOUND := by
  decide

/-- **T2.** The Jubjub field order is strictly positive. -/
theorem field_order_pos : 0 < FIELD_ORDER := by decide

/-- **T3 (non-canonical encodings are below `2^256`).** Both ZIP-216
non-canonical encodings fit in the 32-byte wide range. -/
theorem noncanon_lt_wide_bound :
    NONCANON_LO < WIDE_BOUND ∧ NONCANON_HI < WIDE_BOUND := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **T4 (non-canonical encodings have the sign bit set).** Both ZIP-216
non-canonical encodings have the top bit set (`≥ 2^255`), i.e. the `u`-sign
bit is `1`. This is the structural reason they exist: at `v = 0` the
`u`-sign is ambiguous but the canonical re-encoding picks `0`. -/
theorem noncanon_sign_bit_set :
    SIGN_BIT ≤ NONCANON_LO ∧ SIGN_BIT ≤ NONCANON_HI := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **T5 (the two ZIP-216 non-canonical values differ).** -/
theorem noncanon_lo_ne_hi : NONCANON_LO ≠ NONCANON_HI := by decide

/-- **T6 (non-canonical and canonical are disjoint).** A 32-byte sequence
cannot be both non-canonical and canonical simultaneously. -/
theorem canonical_excludes_noncanonical (bs : List Nat)
    (hC : IsCanonical bs) : ¬ IsNonCanonical bs := by
  intro hN
  unfold IsCanonical isCanonical at hC
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not,
             Bool.not_true] at hC
  -- hC.2 says isNonCanonical bs = false; hN says isNonCanonical bs = true
  unfold IsNonCanonical at hN
  rw [hN] at hC
  simp at hC

/-- **T7 (canonical sequences are valid 32-byte sequences).** -/
theorem canonical_is_point_encoding (bs : List Nat) (h : IsCanonical bs) :
    IsAnyPointEncoding bs := by
  unfold IsCanonical isCanonical at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2⟩

/-- **T8 (non-canonical sequences are valid 32-byte sequences).** -/
theorem noncanonical_is_point_encoding (bs : List Nat) (h : IsNonCanonical bs) :
    IsAnyPointEncoding bs := by
  unfold IsNonCanonical isNonCanonical at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2⟩

/-! ### Concrete witnesses

The two non-canonical bytes from `zip-0216.rst:96-101`, written out
explicitly. -/

/-- The concrete byte sequence for `NONCANON_LO = 2^255 + 1`:
`[0x01, 0x00, ..., 0x00, 0x80]`. -/
def lowNonCanonBytes : List Nat :=
  [0x01] ++ List.replicate 30 0 ++ [0x80]

/-- The concrete byte sequence for `NONCANON_HI = 2^255 + q - 1`. The low
255 bits encode `q - 1`, with the high bit set. We list out the 32 bytes
of `q - 1` (which is `q` with the low byte decremented from `0x01` to
`0x00`), then `OR` the top byte with `0x80`. -/
def highNonCanonBytes : List Nat :=
  -- q - 1 = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000
  -- Top byte is 0x73; OR-ing with 0x80 yields 0xF3.
  [0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff,
   0xfe, 0x5b, 0xfe, 0xff, 0x02, 0xa4, 0xbd, 0x53,
   0x05, 0xd8, 0xa1, 0x09, 0x08, 0xd8, 0x39, 0x33,
   0x48, 0x7d, 0x9d, 0x29, 0x53, 0xa7, 0xed, 0xF3]

/-- **T9 (concrete vector for `NONCANON_LO`).** The byte sequence
`lowNonCanonBytes` has length 32, all bytes `< 256`, and `leValue = 2^255 + 1`. -/
theorem lowNonCanonBytes_correct :
    lowNonCanonBytes.length = POINT_BYTES ∧
    lowNonCanonBytes.all (· < BYTE_MAX) = true ∧
    leValue lowNonCanonBytes = NONCANON_LO := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **T10 (concrete vector for `NONCANON_HI`).** The byte sequence
`highNonCanonBytes` has length 32, all bytes `< 256`, and
`leValue = 2^255 + q - 1`. -/
theorem highNonCanonBytes_correct :
    highNonCanonBytes.length = POINT_BYTES ∧
    highNonCanonBytes.all (· < BYTE_MAX) = true ∧
    leValue highNonCanonBytes = NONCANON_HI := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **T11 (decoder rejects `NONCANON_LO`).** The safe decoder returns `none`
on the first ZIP-216 non-canonical encoding. -/
theorem decodeOption_rejects_low_noncanon :
    decodeOption lowNonCanonBytes = none := by
  decide

/-- **T12 (decoder rejects `NONCANON_HI`).** The safe decoder returns `none`
on the second ZIP-216 non-canonical encoding. -/
theorem decodeOption_rejects_high_noncanon :
    decodeOption highNonCanonBytes = none := by
  decide

/-- **T13 (panicking decoder panics on `NONCANON_LO`).** Models the Rust
`TransmissionKey::try_from` panic from `keys.rs:219`. -/
theorem decodePanicOnNone_panics_low_noncanon :
    decodePanicOnNone lowNonCanonBytes = PanickyResult.panic := by
  decide

/-- **T14 (panicking decoder panics on `NONCANON_HI`).** -/
theorem decodePanicOnNone_panics_high_noncanon :
    decodePanicOnNone highNonCanonBytes = PanickyResult.panic := by
  decide

/-! ### General decoder behaviour -/

/-- **T15 (decoder accepts canonical encodings).** -/
theorem decodeOption_canonical (bs : List Nat) (h : IsCanonical bs) :
    decodeOption bs = some (leValue bs) := by
  unfold decodeOption
  simp [show isCanonical bs = true from h]

/-- **T16 (decoder rejects non-canonical encodings).** -/
theorem decodeOption_rejects_noncanonical (bs : List Nat) (h : IsNonCanonical bs) :
    decodeOption bs = none := by
  unfold decodeOption
  have hNot : ¬ IsCanonical bs := by
    intro hC
    exact canonical_excludes_noncanonical bs hC h
  have : isCanonical bs = false := by
    cases hc : isCanonical bs
    · rfl
    · exfalso; exact hNot hc
  simp [this]

/-- **T17 (panicking decoder accepts canonical encodings).** -/
theorem decodePanicOnNone_canonical (bs : List Nat) (h : IsCanonical bs) :
    decodePanicOnNone bs = PanickyResult.ok (leValue bs) := by
  unfold decodePanicOnNone
  simp [show isCanonical bs = true from h]

/-! ### Behavioural divergence: `TransmissionKey` vs `EphemeralPublicKey`

These theorems capture the asymmetry between Rust's
`TransmissionKey::try_from` (which panics on invalid input) and Rust's
`EphemeralPublicKey::try_from` (which returns `Err`). -/

/-- **T18 (panicky-vs-safe correspondence on rejection).** On any input the
safe decoder rejects, the panicking decoder panics. This documents the
Rust-level divergence: `TransmissionKey::try_from` calls `.unwrap()` on the
same `CtOption` that `EphemeralPublicKey::try_from` checks with `.is_none()`.

Per `zebra-chain/src/sapling/keys.rs:219` vs `:298-302`. -/
theorem panicky_panics_when_option_none (bs : List Nat)
    (h : decodeOption bs = none) :
    decodePanicOnNone bs = PanickyResult.panic := by
  unfold decodeOption decodePanicOnNone at *
  split at h
  · exact absurd h (by simp)
  · simp [show isCanonical bs = false from by rename_i hC; exact Bool.eq_false_iff.mpr hC]

/-- **T19 (panicky-vs-safe correspondence on acceptance).** On any input the
safe decoder accepts, the panicking decoder produces `ok` with the same
value. -/
theorem panicky_ok_when_option_some (bs : List Nat) (v : Nat)
    (h : decodeOption bs = some v) :
    decodePanicOnNone bs = PanickyResult.ok v := by
  unfold decodeOption decodePanicOnNone at *
  split at h
  · simp [show isCanonical bs = true from by rename_i hC; exact hC]
    simpa using h
  · cases h

/-! ### Range and round-trip -/

/-- **T20 (decoder output range).** A successful decode yields a value
strictly less than `2^256`, i.e. it fits in 32 bytes. The detailed proof
uses an auxiliary lemma `leValue_lt_pow` that bounds `leValue` by `256^length`
for any byte list with `all < 256`. -/
theorem leValue_lt_pow (bs : List Nat) (h : AllBytes bs = true) :
    leValue bs < BYTE_MAX ^ bs.length := by
  induction bs with
  | nil => simp [leValue, BYTE_MAX]
  | cons b bs ih =>
    unfold leValue
    simp only [AllBytes, List.all_cons, Bool.and_eq_true,
               decide_eq_true_eq] at h
    have hB : b < BYTE_MAX := h.1
    have hRest : AllBytes bs = true := by
      unfold AllBytes
      simpa using h.2
    have hIH : leValue bs < BYTE_MAX ^ bs.length := ih hRest
    have hPow : BYTE_MAX ^ (b :: bs).length = BYTE_MAX * BYTE_MAX ^ bs.length := by
      simp only [List.length_cons]
      rw [pow_succ, Nat.mul_comm]
    rw [hPow]
    have hStep : b + BYTE_MAX * leValue bs < BYTE_MAX * BYTE_MAX ^ bs.length := by
      have : BYTE_MAX * (leValue bs + 1) ≤ BYTE_MAX * BYTE_MAX ^ bs.length := by
        apply Nat.mul_le_mul_left
        omega
      have hExpand : BYTE_MAX * (leValue bs + 1) = BYTE_MAX + BYTE_MAX * leValue bs := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      omega
    exact hStep

theorem decodeOption_value_lt_wide_bound (bs : List Nat) (v : Nat)
    (h : decodeOption bs = some v) : v < WIDE_BOUND := by
  unfold decodeOption at h
  by_cases hC : isCanonical bs
  · rw [if_pos hC] at h
    simp only [Option.some.injEq] at h
    have hCan : IsCanonical bs := hC
    unfold IsCanonical isCanonical at hCan
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hCan
    have hLen : IsPointBytes bs = true := hCan.1.1
    have hAll : AllBytes bs = true := hCan.1.2
    have hBound := leValue_lt_pow bs hAll
    unfold IsPointBytes at hLen
    simp only [decide_eq_true_eq] at hLen
    rw [hLen] at hBound
    unfold WIDE_BOUND BYTE_MAX POINT_BYTES at *
    omega
  · rw [if_neg hC] at h
    cases h

/-- **T21 (successful decode implies canonical input).** -/
theorem decodeOption_some_implies_canonical (bs : List Nat) (v : Nat)
    (h : decodeOption bs = some v) : IsCanonical bs := by
  unfold decodeOption at h
  by_cases hC : isCanonical bs
  · exact hC
  · rw [if_neg hC] at h
    cases h

/-- **T22 (encode round-trip).** Any canonical byte sequence is recovered by
re-encoding the value the safe decoder extracted. -/
theorem encode_decode_roundtrip (bs : List Nat) (h : IsCanonical bs) :
    encode (leValue bs) bs = some bs := by
  unfold encode
  have hC : isCanonical bs = true := h
  simp [hC]

/-- **T23 (full round-trip).** -/
theorem decode_then_encode (bs : List Nat) (h : IsCanonical bs) :
    (decodeOption bs).bind (fun v => encode v bs) = some bs := by
  rw [decodeOption_canonical bs h, Option.bind_some]
  exact encode_decode_roundtrip bs h

/-- **T24 (wrong-length rejection).** -/
theorem decodeOption_rejects_wrong_length (bs : List Nat)
    (h : bs.length ≠ POINT_BYTES) : decodeOption bs = none := by
  unfold decodeOption
  have : isCanonical bs = false := by
    unfold isCanonical IsPointBytes
    have : (decide (bs.length = POINT_BYTES) : Bool) = false := by
      simp [h]
    simp [this]
  simp [this]

/-- **T25 (decidability).** -/
instance instDecidableIsCanonical (bs : List Nat) : Decidable (IsCanonical bs) := by
  unfold IsCanonical
  exact instDecidableEqBool _ _

/-- **T26 (decidability of non-canonical).** -/
instance instDecidableIsNonCanonical (bs : List Nat) : Decidable (IsNonCanonical bs) := by
  unfold IsNonCanonical
  exact instDecidableEqBool _ _

/-- **T27 (encode rejects mismatch).** -/
theorem encode_rejects_mismatch (v : Nat) (bs : List Nat)
    (h : leValue bs ≠ v) : encode v bs = none := by
  unfold encode
  have : (isCanonical bs && (leValue bs = v)) = false := by
    by_cases hC : isCanonical bs = true
    · simp [hC, h]
    · simp [Bool.eq_false_iff.mpr hC]
  simp [this]

/-! ## ZIP-216 application sites (Finding 61)

`zip-0216.rst:103-122` enumerates the precise Sapling consensus fields where
non-canonical encodings MUST be rejected:

  1. `spendAuthSig.R` — the first 32 bytes of the RedDSA signature in a
     Sapling Spend description.
  2. `bindingSigSapling.R` — the first 32 bytes of the RedDSA binding
     signature in a Sapling-bearing transaction.
  3. `pk*_d` — the diversified transmission key extracted from the
     decryption of `C^out`.

This section ties the abstract `isCanonical` check to each of these four
sites via a thin per-site predicate. The proofs are uniformly by definition,
recording that all four sites use the *same* byte-level check. -/

/-- ZIP-216 application site: the `R` component of a Sapling
`spendAuthSig`. Per `zip-0216.rst:106-109`. -/
def IsCanonicalSpendAuthSigR (bs : List Nat) : Prop := IsCanonical bs

/-- ZIP-216 application site: the `R` component of a Sapling
`bindingSigSapling`. Per `zip-0216.rst:111-114`. -/
def IsCanonicalBindingSigR (bs : List Nat) : Prop := IsCanonical bs

/-- ZIP-216 application site: the `pk*_d` decrypted from `C^out`. Per
`zip-0216.rst:116-120`. -/
def IsCanonicalPkdStar (bs : List Nat) : Prop := IsCanonical bs

/-- ZIP-216 application site: an `EphemeralPublicKey` byte sequence. The
ZIP enforces the check at this site via the implicit
`AffinePoint::from_bytes` decode in `EphemeralPublicKey::try_from`. -/
def IsCanonicalEphemeralPublicKey (bs : List Nat) : Prop := IsCanonical bs

/-- **T28 (spendAuthSig.R uses ZIP-216).** Reduces to `IsCanonical`. -/
theorem spendAuthSigR_uses_zip216 (bs : List Nat) :
    IsCanonicalSpendAuthSigR bs ↔ IsCanonical bs :=
  Iff.rfl

/-- **T29 (bindingSigSapling.R uses ZIP-216).** -/
theorem bindingSigR_uses_zip216 (bs : List Nat) :
    IsCanonicalBindingSigR bs ↔ IsCanonical bs :=
  Iff.rfl

/-- **T30 (pk*_d uses ZIP-216).** -/
theorem pkdStar_uses_zip216 (bs : List Nat) :
    IsCanonicalPkdStar bs ↔ IsCanonical bs :=
  Iff.rfl

/-- **T31 (EphemeralPublicKey uses ZIP-216).** -/
theorem epk_uses_zip216 (bs : List Nat) :
    IsCanonicalEphemeralPublicKey bs ↔ IsCanonical bs :=
  Iff.rfl

/-- **T32 (all four sites reject `NONCANON_LO`).** A single concrete
witness shows every application site rejects the first ZIP-216 encoding. -/
theorem all_sites_reject_low_noncanon :
    ¬ IsCanonicalSpendAuthSigR lowNonCanonBytes ∧
    ¬ IsCanonicalBindingSigR lowNonCanonBytes ∧
    ¬ IsCanonicalPkdStar lowNonCanonBytes ∧
    ¬ IsCanonicalEphemeralPublicKey lowNonCanonBytes := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ¬ IsCanonical lowNonCanonBytes; decide
  · change ¬ IsCanonical lowNonCanonBytes; decide
  · change ¬ IsCanonical lowNonCanonBytes; decide
  · change ¬ IsCanonical lowNonCanonBytes; decide

/-- **T33 (all four sites reject `NONCANON_HI`).** -/
theorem all_sites_reject_high_noncanon :
    ¬ IsCanonicalSpendAuthSigR highNonCanonBytes ∧
    ¬ IsCanonicalBindingSigR highNonCanonBytes ∧
    ¬ IsCanonicalPkdStar highNonCanonBytes ∧
    ¬ IsCanonicalEphemeralPublicKey highNonCanonBytes := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ¬ IsCanonical highNonCanonBytes; decide
  · change ¬ IsCanonical highNonCanonBytes; decide
  · change ¬ IsCanonical highNonCanonBytes; decide
  · change ¬ IsCanonical highNonCanonBytes; decide

end Zebra.Zip216CanonicalPoint
