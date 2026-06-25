import ZebrafmSpec

/-!
# `Zebrafm` Proofs

This file discharges every specification declared in
[`ZebrafmSpec.lean`](ZebrafmSpec.lean) by reducing it to the
inline theorems proved in
[`Zebrafm/Height.lean`](Zebrafm/Height.lean),
[`Zebrafm/Amount.lean`](Zebrafm/Amount.lean), and
[`Zebrafm/CompactSize.lean`](Zebrafm/CompactSize.lean).

The split between this file and the inline theorems is a file-layout
convention from the original verification proposal; the actual kernel
checking is performed when the underlying inline theorems are elaborated.
-/

namespace Zebrafm.Proofs

open Zebra
open Zebrafm.Spec

/-! ## Height -/

theorem height_tryFromCheck : Height.TryFromCheck :=
  fun n => Zebra.Height.tryFromU32_iff n

theorem height_subHEqInt : Height.SubHEqInt :=
  fun a b => Zebra.Height.subH_eq a b

theorem height_addSubResultBounded : Height.AddSubResultBounded :=
  ⟨fun h d r => Zebra.Height.add_result_bounded h d r,
   fun h d r => Zebra.Height.sub_result_bounded h d r⟩

theorem height_roundTrip : Height.RoundTrip :=
  fun h d r hH heq => Zebra.Height.add_sub_eq h d r hH heq

theorem height_addMonotone : Height.AddMonotone :=
  fun h d₁ d₂ r₁ r₂ heq₁ heq₂ hle =>
    Zebra.Height.add_monotone h d₁ d₂ r₁ r₂ heq₁ heq₂ hle

/-! ## Amount -/

theorem amount_validateInRange : Amount.ValidateInRange := by
  intro c v
  rcases c with _ | _ | _ <;>
    simp [Zebra.Amount.Constraint.validate, Zebra.Amount.Constraint.lo,
          Zebra.Amount.Constraint.hi, Option.isSome]
  all_goals
    constructor
    · intro h; split_ifs at h with hcond; exact hcond
    · intro h; split_ifs <;> simp_all

theorem amount_checkedAddInRange : Amount.CheckedAddInRange := by
  intro c a b
  exact Zebra.Amount.checkedAdd_iff c a b

theorem amount_checkedSubInRange : Amount.CheckedSubInRange := by
  intro c a b
  exact Zebra.Amount.checkedSub_iff c a b

theorem amount_mulU64InRange : Amount.MulU64InRange := by
  intro c a b
  exact Zebra.Amount.mulU64_iff c a b

theorem amount_negInverse : Amount.NegInverse :=
  fun a => Zebra.Amount.neg_inverse a

theorem amount_divByZero : Amount.DivByZero :=
  fun c a => Zebra.Amount.divU64_zero c a

theorem amount_sumValue : Amount.SumValue :=
  fun c xs r => Zebra.Amount.sum_value c xs r

/-! ## CompactSize -/

theorem compactSize_roundTrip : CompactSize.RoundTrip :=
  fun n h => Zebra.CompactSize.roundtrip_universal n h

theorem compactSize_encodeLength : CompactSize.EncodeLength :=
  fun n => Zebra.CompactSize.encode_length n

theorem compactSize_decodeTotal : CompactSize.DecodeTotal :=
  fun bytes => Zebra.CompactSize.decode_total bytes

theorem compactSize_canonicityBand2 : CompactSize.CanonicityBand2 :=
  fun b0 b1 rest h => Zebra.CompactSize.canonicity_band2 b0 b1 rest h

theorem compactSize_messageCap : CompactSize.MessageCap :=
  fun n h => Zebra.CompactSize.messageTryFrom_rejects_overlimit n h

end Zebrafm.Proofs
