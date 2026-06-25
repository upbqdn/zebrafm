import ZebraChainArith.Height
import ZebraChainArith.Amount
import ZebraChainArith.CompactSize
import ZebraChainArith.NetworkUpgrade
import ZebraChainArith.LockTime
import ZebraChainArith.Subsidy

open Zebra

-- Height
#print axioms Height.tryFromU32_iff
#print axioms Height.subH_eq
#print axioms Height.add_result_bounded
#print axioms Height.sub_result_bounded
#print axioms Height.add_sub_eq
#print axioms Height.add_monotone
#print axioms Height.subH_antisymm
#print axioms Height.subH_self
#print axioms Height.tryFromU32_valid
#print axioms Height.add_zero_identity
#print axioms Height.sub_zero_identity

-- Amount
#print axioms Amount.validate_negativeAllowed_iff
#print axioms Amount.validate_nonNegative_iff
#print axioms Amount.checkedAdd_iff
#print axioms Amount.checkedAdd_in_range
#print axioms Amount.checkedSub_iff
#print axioms Amount.checkedSub_in_range
#print axioms Amount.mulU64_iff
#print axioms Amount.neg_inverse
#print axioms Amount.neg_negativeAllowed_closed
#print axioms Amount.validate_negativeOrZero_iff
#print axioms Amount.divU64_zero
#print axioms Amount.divU64_nonNegative_closed
#print axioms Amount.sum_empty
#print axioms Amount.sum_singleton_nonNegative
#print axioms Amount.checkedAdd_comm
#print axioms Amount.neg_zero
#print axioms Amount.neg_neg_eq
#print axioms Amount.checkedSub_as_add
#print axioms Amount.checkedAdd_zero

-- CompactSize
#print axioms CompactSize.roundtrip_band1
#print axioms CompactSize.roundtrip_band2
#print axioms CompactSize.roundtrip_band3
#print axioms CompactSize.roundtrip_band4
#print axioms CompactSize.encode_length
#print axioms CompactSize.decode_total
#print axioms CompactSize.canonicity_band2
#print axioms CompactSize.canonicity_band3
#print axioms CompactSize.canonicity_band4
#print axioms CompactSize.messageTryFrom_iff
#print axioms CompactSize.messageTryFrom_rejects_overlimit
#print axioms CompactSize.decode_empty
#print axioms CompactSize.encode_first_byte_canonical
#print axioms CompactSize.encode_nonempty
#print axioms CompactSize.roundtrip_universal

-- NetworkUpgrade
#print axioms NetworkUpgrade.current_zero
#print axioms NetworkUpgrade.current_at_activation_height
#print axioms NetworkUpgrade.current_on_nu5_band
#print axioms NetworkUpgrade.current_on_nu6_band
#print axioms NetworkUpgrade.current_monotone_at_nu6
#print axioms NetworkUpgrade.current_below_nu6
#print axioms NetworkUpgrade.current_surjective
#print axioms NetworkUpgrade.current_total
#print axioms NetworkUpgrade.activation_heights_strictly_increasing
#print axioms NetworkUpgrade.currentOrd_monotone

-- LockTime
#print axioms LockTime.encode_length
#print axioms LockTime.roundtrip_height
#print axioms LockTime.roundtrip_time
#print axioms LockTime.roundtrip_universal
#print axioms LockTime.decode_total
#print axioms LockTime.decode_empty
#print axioms LockTime.decode_one
#print axioms LockTime.decode_two
#print axioms LockTime.decode_three

-- Subsidy
#print axioms Subsidy.halving_monotone
#print axioms Subsidy.halving_pre_blossom
#print axioms Subsidy.halving_at_blossom
#print axioms Subsidy.halving_one_interval_post_blossom
#print axioms Subsidy.halvingDivisor_in_range
#print axioms Subsidy.halvingDivisor_overflow
#print axioms Subsidy.blockSubsidy_zero_when_overflow
#print axioms Subsidy.blockSubsidy_at_blossom
#print axioms Subsidy.blockSubsidy_first_halving
#print axioms Subsidy.blockSubsidy_nonincreasing
