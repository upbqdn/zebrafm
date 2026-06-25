import Zebrafm.Height
import Zebrafm.Amount
import Zebrafm.CompactSize

/-!
# `Zebrafm` Specification

Per-property specification surface for the verification. Each property is
exposed as a `def`-valued `Prop` so that downstream consumers can refer to a
named specification rather than inlining the theorem statement. The
corresponding proofs live in [`ZebrafmProofs.lean`](ZebrafmProofs.lean).

The specification mirrors the inline theorem statements in
[`Zebrafm/Height.lean`](Zebrafm/Height.lean),
[`Zebrafm/Amount.lean`](Zebrafm/Amount.lean), and
[`Zebrafm/CompactSize.lean`](Zebrafm/CompactSize.lean) — this
file is a re-statement to satisfy the proposal's file-layout convention,
not an independent specification.
-/

namespace Zebrafm.Spec

open Zebra

/-! ## Height specifications -/

/-- `try_from` succeeds exactly on the valid range. -/
def Height.TryFromCheck : Prop :=
  ∀ n, (Zebra.Height.tryFromU32 n).isSome ↔ n ≤ Zebra.Height.MAX_AS_U32

/-- `subH` is the integer difference. -/
def Height.SubHEqInt : Prop :=
  ∀ a b, Zebra.Height.subH a b = (a : Int) - (b : Int)

/-- `add` and `sub` results, when present, lie in `[0, MAX_AS_U32]`. -/
def Height.AddSubResultBounded : Prop :=
  (∀ h d r, Zebra.Height.add h d = some r → r ≤ Zebra.Height.MAX_AS_U32) ∧
    (∀ h d r, Zebra.Height.sub h d = some r → r ≤ Zebra.Height.MAX_AS_U32)

/-- Round-trip: `add` then `sub` recovers the input for valid heights. -/
def Height.RoundTrip : Prop :=
  ∀ h d r, h ≤ Zebra.Height.MAX_AS_U32 → Zebra.Height.add h d = some r →
    Zebra.Height.sub r d = some h

/-- `add` is monotone in the diff argument. -/
def Height.AddMonotone : Prop :=
  ∀ h d₁ d₂ r₁ r₂,
    Zebra.Height.add h d₁ = some r₁ → Zebra.Height.add h d₂ = some r₂ →
    d₁ ≤ d₂ → r₁ ≤ r₂

/-! ## Amount specifications -/

/-- `validate` succeeds exactly on the constraint's range. -/
def Amount.ValidateInRange : Prop :=
  ∀ c v, (Zebra.Amount.Constraint.validate c v).isSome ↔ c.lo ≤ v ∧ v ≤ c.hi

/-- `checkedAdd` succeeds iff the integer sum is in range. -/
def Amount.CheckedAddInRange : Prop :=
  ∀ c a b, (Zebra.Amount.checkedAdd c a b).isSome ↔ c.lo ≤ a + b ∧ a + b ≤ c.hi

/-- `checkedSub` succeeds iff the integer difference is in range. -/
def Amount.CheckedSubInRange : Prop :=
  ∀ c a b, (Zebra.Amount.checkedSub c a b).isSome ↔ c.lo ≤ a - b ∧ a - b ≤ c.hi

/-- `Mul<u64>` succeeds iff the product is in range. -/
def Amount.MulU64InRange : Prop :=
  ∀ c a b, (Zebra.Amount.mulU64 c a b).isSome ↔
    c.lo ≤ a * (b : Int) ∧ a * (b : Int) ≤ c.hi

/-- `Neg`'s inverse property: `a + neg a = 0`. -/
def Amount.NegInverse : Prop := ∀ a, a + Zebra.Amount.neg a = 0

/-- Division by zero returns `none`. -/
def Amount.DivByZero : Prop :=
  ∀ c a, Zebra.Amount.divU64 c a 0 = none

/-- `Sum`'s result, when present, equals the natural integer sum. -/
def Amount.SumValue : Prop :=
  ∀ c xs r, Zebra.Amount.sumFold c xs = some r → r = xs.foldr (· + ·) 0

/-! ## CompactSize specifications -/

/-- Encoder/decoder round-trip universally (for `n ≤ U64_MAX`). -/
def CompactSize.RoundTrip : Prop :=
  ∀ n, n ≤ Zebra.CompactSize.U64_MAX →
    Zebra.CompactSize.decode (Zebra.CompactSize.encode n) = some (n, [])

/-- The encoder produces output of length 1, 3, 5, or 9. -/
def CompactSize.EncodeLength : Prop :=
  ∀ n, (Zebra.CompactSize.encode n).length = 1
        ∨ (Zebra.CompactSize.encode n).length = 3
        ∨ (Zebra.CompactSize.encode n).length = 5
        ∨ (Zebra.CompactSize.encode n).length = 9

/-- The decoder is total. -/
def CompactSize.DecodeTotal : Prop :=
  ∀ bytes, (Zebra.CompactSize.decode bytes).isSome ∨
    Zebra.CompactSize.decode bytes = none

/-- The decoder rejects non-minimal 3-byte encodings (canonicity). -/
def CompactSize.CanonicityBand2 : Prop :=
  ∀ b0 b1 rest, Zebra.CompactSize.fromLE2 b0 b1 < 0xfd →
    Zebra.CompactSize.decode (0xfd :: b0 :: b1 :: rest) = none

/-- The `CompactSizeMessage` DoS cap rejects oversized values. -/
def CompactSize.MessageCap : Prop :=
  ∀ n, Zebra.CompactSize.MAX_PROTOCOL_MESSAGE_LEN < n →
    Zebra.CompactSize.messageTryFrom n = none

end Zebrafm.Spec
