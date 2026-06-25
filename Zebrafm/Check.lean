import Zebrafm.Height
import Zebrafm.Amount
import Zebrafm.CompactSize
import Zebrafm.NetworkUpgrade
import Zebrafm.LockTime
import Zebrafm.Subsidy
import Zebrafm.BlockSizeLimits
import Zebrafm.CoinbaseMaturity
import Zebrafm.BlockMaxTime
import Zebrafm.ReorgWindow
import Zebrafm.FoundersReward
import Zebrafm.AddrMessageCap
import Zebrafm.MempoolAdmission
import Zebrafm.Bech32
import Zebrafm.MinNetworkVersion
import Zebrafm.TestnetMinDifficulty
import Zebrafm.PowAveragingWindow
import Zebrafm.Bip34CoinbaseHeight
import Zebrafm.BlockHeader
import Zebrafm.HashRoundTrip
import Zebrafm.PoolValueBalance

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

-- BlockSizeLimits
#print axioms BlockSizeLimits.sizeCheck_iff
#print axioms BlockSizeLimits.sizeCheck_reject_above
#print axioms BlockSizeLimits.sizeCheck_monotone_bound
#print axioms BlockSizeLimits.sizeCheck_antitone_size
#print axioms BlockSizeLimits.block_le_protocol
#print axioms BlockSizeLimits.blockOk_implies_protocolOk
#print axioms BlockSizeLimits.sizeCheck_at_bound
#print axioms BlockSizeLimits.sizeCheck_just_above
#print axioms BlockSizeLimits.MAX_BLOCK_BYTES_value
#print axioms BlockSizeLimits.MAX_PROTOCOL_MESSAGE_LEN_value
#print axioms BlockSizeLimits.protocol_minus_block
#print axioms BlockSizeLimits.sizeCheck_zero
#print axioms BlockSizeLimits.blockSizeOk_at_max
#print axioms BlockSizeLimits.protocolMessageSizeOk_just_above

-- CoinbaseMaturity
#print axioms CoinbaseMaturity.canSpend_iff
#print axioms CoinbaseMaturity.cannot_spend_before_maturity
#print axioms CoinbaseMaturity.can_spend_at_maturity
#print axioms CoinbaseMaturity.canSpend_mono_spend
#print axioms CoinbaseMaturity.canSpend_antitone_created
#print axioms CoinbaseMaturity.canSpend_iff_min
#print axioms CoinbaseMaturity.maturity_value
#print axioms CoinbaseMaturity.genesis_maturity
#print axioms CoinbaseMaturity.canSpend_diff_ge
#print axioms CoinbaseMaturity.diff_ge_canSpend

-- BlockMaxTime
#print axioms BlockMaxTime.tolerance_value
#print axioms BlockMaxTime.isAcceptable_iff
#print axioms BlockMaxTime.now_is_acceptable
#print axioms BlockMaxTime.past_is_acceptable
#print axioms BlockMaxTime.boundary_is_acceptable
#print axioms BlockMaxTime.just_past_boundary_rejected
#print axioms BlockMaxTime.acceptable_mono_now
#print axioms BlockMaxTime.acceptable_antimono_blockTime
#print axioms BlockMaxTime.maxAcceptable_acceptable
#print axioms BlockMaxTime.maxAcceptable_is_upper_bound
#print axioms BlockMaxTime.above_maxAcceptable_rejected
#print axioms BlockMaxTime.maxAcceptable_mono

-- ReorgWindow
#print axioms ReorgWindow.isFinalized_iff
#print axioms ReorgWindow.inReorgWindow_iff
#print axioms ReorgWindow.isFinalized_mono_tip
#print axioms ReorgWindow.isFinalized_antimono_block
#print axioms ReorgWindow.isFinalized_at_boundary
#print axioms ReorgWindow.inReorgWindow_below_threshold
#print axioms ReorgWindow.finalized_or_in_window
#print axioms ReorgWindow.not_both_finalized_and_in_window
#print axioms ReorgWindow.tip_in_window
#print axioms ReorgWindow.above_tip_in_window
#print axioms ReorgWindow.genesis_finalized_iff

-- FoundersReward
#print axioms FoundersReward.founders_divisor_eq_five
#print axioms FoundersReward.founders_ratio_one_fifth
#print axioms FoundersReward.foundersReward_post_canopy
#print axioms FoundersReward.minerReward_post_canopy
#print axioms FoundersReward.foundersReward_pre_canopy
#print axioms FoundersReward.foundersReward_le_fifth
#print axioms FoundersReward.foundersReward_le_subsidy
#print axioms FoundersReward.sum_conservation_pre_canopy
#print axioms FoundersReward.sum_conservation_post_canopy
#print axioms FoundersReward.foundersReward_monotone_subsidy
#print axioms FoundersReward.minerReward_monotone_pre_canopy
#print axioms FoundersReward.minerReward_pre_canopy_div5
#print axioms FoundersReward.foundersReward_at_genesis_subsidy
#print axioms FoundersReward.minerReward_at_genesis_subsidy

-- AddrMessageCap
#print axioms AddrMessageCap.addrTryFrom_iff
#print axioms AddrMessageCap.invTryFrom_iff
#print axioms AddrMessageCap.txInvSentTryFrom_iff
#print axioms AddrMessageCap.addrTryFrom_rejects_overlimit
#print axioms AddrMessageCap.invTryFrom_rejects_overlimit
#print axioms AddrMessageCap.txInvSentTryFrom_rejects_overlimit
#print axioms AddrMessageCap.addrTryFrom_valid
#print axioms AddrMessageCap.invTryFrom_valid
#print axioms AddrMessageCap.tx_inv_sent_le_inv_received
#print axioms AddrMessageCap.addr_le_inv
#print axioms AddrMessageCap.addrTryFrom_at_cap
#print axioms AddrMessageCap.invTryFrom_at_cap
#print axioms AddrMessageCap.addrTryFrom_cap_plus_one
#print axioms AddrMessageCap.invTryFrom_cap_plus_one

-- MempoolAdmission
#print axioms MempoolAdmission.admitted_iff
#print axioms MempoolAdmission.unpaidActions_le_conventional
#print axioms MempoolAdmission.unpaidActions_zero_of_fee_ge
#print axioms MempoolAdmission.admitted_monotone_fee
#print axioms MempoolAdmission.admitted_antitone_actions
#print axioms MempoolAdmission.admitted_of_fee_ge
#print axioms MempoolAdmission.admitted_zero_actions
#print axioms MempoolAdmission.admitted_insufficient_concrete
#print axioms MempoolAdmission.admitted_boundary_concrete

-- Bech32
#print axioms Bech32.polymod_deterministic
#print axioms Bech32.polymod_nil
#print axioms Bech32.polymod_lt_2pow30
#print axioms Bech32.polymod_snoc
#print axioms Bech32.polymod_append
#print axioms Bech32.hrpExpand_length
#print axioms Bech32.encode_length
#print axioms Bech32.encode_separator_after_hrp
#print axioms Bech32.encode_checksum_suffix
#print axioms Bech32.encode_injective_data
#print axioms Bech32.separator_is_one
#print axioms Bech32.checksum_length_is_six
#print axioms Bech32.charset_size_is_32
#print axioms Bech32.polymodStep_lt
#print axioms Bech32.hrpExpand_nonempty
#print axioms Bech32.encode_nonempty

-- MinNetworkVersion
#print axioms MinNetworkVersion.minSpecifiedMainnet_monotone
#print axioms MinNetworkVersion.minSpecifiedTestnet_monotone
#print axioms MinNetworkVersion.minSpecified_monotone
#print axioms MinNetworkVersion.mainnet_ge_testnet
#print axioms MinNetworkVersion.minSpecified_lt_u32
#print axioms MinNetworkVersion.initial_mainnet_value
#print axioms MinNetworkVersion.initial_testnet_value
#print axioms MinNetworkVersion.initial_ge_genesis_floor
#print axioms MinNetworkVersion.mainnet_strict_consecutive

-- TestnetMinDifficulty
#print axioms TestnetMinDifficulty.postBlossomMinDifficultyGap_eq_450
#print axioms TestnetMinDifficulty.preBlossomMinDifficultyGap_eq_900
#print axioms TestnetMinDifficulty.minimumDifficultySpacingForHeight_isSome_iff
#print axioms TestnetMinDifficulty.minimumDifficultySpacingForHeight_mainnet
#print axioms TestnetMinDifficulty.minimumDifficultySpacingForHeight_below_start
#print axioms TestnetMinDifficulty.minimumDifficultySpacingForHeight_testnet_active
#print axioms TestnetMinDifficulty.isTestnetMinDifficultyBlock_mainnet
#print axioms TestnetMinDifficulty.isTestnetMinDifficultyBlock_below_start
#print axioms TestnetMinDifficulty.isTestnetMinDifficultyBlock_active_iff
#print axioms TestnetMinDifficulty.isTestnetMinDifficultyBlock_boundary_strict
#print axioms TestnetMinDifficulty.isTestnetMinDifficultyBlock_above_boundary
#print axioms TestnetMinDifficulty.isTestnetMinDifficultyBlock_mono_gap

-- PowAveragingWindow
#print axioms PowAveragingWindow.averaging_window_gt_median_span
#print axioms PowAveragingWindow.pow_averaging_window_value
#print axioms PowAveragingWindow.pow_median_block_span_value
#print axioms PowAveragingWindow.averaging_window_timespan_eq
#print axioms PowAveragingWindow.pre_blossom_averaging_window_timespan_value
#print axioms PowAveragingWindow.post_blossom_averaging_window_timespan_value
#print axioms PowAveragingWindow.blossom_halves_target_spacing
#print axioms PowAveragingWindow.blossom_halves_averaging_window
#print axioms PowAveragingWindow.averaging_window_timespan_monotone
#print axioms PowAveragingWindow.averaging_window_timespan_zero_iff
#print axioms PowAveragingWindow.pow_constants_positive

-- Bip34CoinbaseHeight
#print axioms Bip34CoinbaseHeight.encode_length
#print axioms Bip34CoinbaseHeight.encode_length_bounds
#print axioms Bip34CoinbaseHeight.roundtrip_op_n
#print axioms Bip34CoinbaseHeight.roundtrip_one_byte
#print axioms Bip34CoinbaseHeight.roundtrip_two_byte
#print axioms Bip34CoinbaseHeight.roundtrip_three_byte
#print axioms Bip34CoinbaseHeight.roundtrip_four_byte
#print axioms Bip34CoinbaseHeight.encode_length_op_n
#print axioms Bip34CoinbaseHeight.encode_length_one_byte
#print axioms Bip34CoinbaseHeight.decode_empty
#print axioms Bip34CoinbaseHeight.decode_op_0
#print axioms Bip34CoinbaseHeight.decode_one_byte_noncanonical
#print axioms Bip34CoinbaseHeight.decode_unknown_prefix

-- BlockHeader
#print axioms BlockHeader.toLE4_length
#print axioms BlockHeader.encodeFixed_length
#print axioms BlockHeader.version_roundtrip
#print axioms BlockHeader.time_roundtrip
#print axioms BlockHeader.bits_roundtrip
#print axioms BlockHeader.encode_version_prefix
#print axioms BlockHeader.header_size_decomposition
#print axioms BlockHeader.encode_injective_version

-- HashRoundTrip
#print axioms HashRoundTrip.toBytes_fromBytes
#print axioms HashRoundTrip.fromBytes_toBytes
#print axioms HashRoundTrip.fromBytes_isHash
#print axioms HashRoundTrip.toBytes_length
#print axioms HashRoundTrip.fromBytes_injective
#print axioms HashRoundTrip.zero_length
#print axioms HashRoundTrip.zero_isHash
#print axioms HashRoundTrip.zero_bytes_all_zero
#print axioms HashRoundTrip.zcashSerialize_length
#print axioms HashRoundTrip.zcashSerialize_deserialize
#print axioms HashRoundTrip.zcashDeserialize_rejects_wrong_length
#print axioms HashRoundTrip.zcashDeserialize_isHash

-- PoolValueBalance
#print axioms PoolValueBalance.max_money_value
#print axioms PoolValueBalance.toBytes_length
#print axioms PoolValueBalance.toBytes_length_40
#print axioms PoolValueBalance.toLE8_length
#print axioms PoolValueBalance.total_bounded
#print axioms PoolValueBalance.total_bounded_concrete
#print axioms PoolValueBalance.zero_valid
#print axioms PoolValueBalance.total_zero
#print axioms PoolValueBalance.total_monotone_transparent
#print axioms PoolValueBalance.pool_count_layout
#print axioms PoolValueBalance.toLE8_bytes_lt_256
#print axioms PoolValueBalance.toBytes_bytes_lt_256
