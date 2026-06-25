//! Property-based tests that mirror the Lean theorems.
//!
//! Each test exercises a property proved in the parent Lean project against
//! the live Rust code in this crate. If the Rust code drifts away from what
//! Lean has proved — e.g. a hand-edit introduces a bug Aeneas's extraction
//! would catch — these tests fail.

use proptest::prelude::*;
use zebra_chain_arith::{amount, compact_size, height};

// ---------- Height ----------

proptest! {
    /// Lean: `Zebra.Height.tryFromU32_iff`
    #[test]
    fn height_try_from_iff(n in any::<u32>()) {
        let result = height::try_from_u32(n);
        prop_assert_eq!(result.is_some(), n <= height::MAX_AS_U32);
    }

    /// Lean: `Zebra.Height.add_result_bounded` (combined with success-implies-in-range)
    #[test]
    fn height_add_in_range(h in 0u32..=height::MAX_AS_U32, d in i64::MIN..i64::MAX) {
        if let Some(r) = height::add(h, d) {
            prop_assert!(r <= height::MAX_AS_U32);
        }
    }

    /// Lean: `Zebra.Height.add_sub_eq` (round-trip)
    #[test]
    fn height_round_trip(h in 0u32..=height::MAX_AS_U32, d in -1_000_000_000i64..1_000_000_000) {
        if let Some(r) = height::add(h, d) {
            prop_assert_eq!(height::sub(r, d), Some(h));
        }
    }

    /// Lean: `Zebra.Height.subH_antisymm`
    #[test]
    fn height_sub_antisym(a in 0u32..=height::MAX_AS_U32, b in 0u32..=height::MAX_AS_U32) {
        prop_assert_eq!(height::sub_h(a, b), -height::sub_h(b, a));
    }
}

// ---------- Amount ----------

const NN: amount::Constraint = amount::Constraint::NonNegative;
const NA: amount::Constraint = amount::Constraint::NegativeAllowed;

proptest! {
    /// Lean: `Zebra.Amount.validate_nonNegative_iff`
    #[test]
    fn amount_validate_nonneg_iff(v in -3_000_000_000_000_000i64..3_000_000_000_000_000) {
        let result = amount::validate(NN, v);
        prop_assert_eq!(result.is_some(), 0 <= v && v <= amount::MAX_MONEY);
    }

    /// Lean: `Zebra.Amount.checkedAdd_in_range`
    #[test]
    fn amount_checked_add_in_range(
        a in -amount::MAX_MONEY..=amount::MAX_MONEY,
        b in -amount::MAX_MONEY..=amount::MAX_MONEY,
    ) {
        if let Some(r) = amount::checked_add(NA, a, b) {
            prop_assert!(-amount::MAX_MONEY <= r && r <= amount::MAX_MONEY);
        }
    }

    /// Lean: `Zebra.Amount.neg_inverse` (`a + neg a = 0`)
    #[test]
    fn amount_neg_inverse(a in i64::MIN/2..i64::MAX/2) {
        prop_assert_eq!(a.wrapping_add(amount::neg(a)), 0);
    }

    /// Lean: `Zebra.Amount.checkedAdd_comm`
    #[test]
    fn amount_checked_add_comm(
        a in -amount::MAX_MONEY..=amount::MAX_MONEY,
        b in -amount::MAX_MONEY..=amount::MAX_MONEY,
    ) {
        prop_assert_eq!(amount::checked_add(NA, a, b), amount::checked_add(NA, b, a));
    }

    /// Lean: `Zebra.Amount.divU64_zero`
    #[test]
    fn amount_div_zero_rejected(a in any::<i64>()) {
        prop_assert!(amount::div_u64(NN, a, 0).is_none());
    }
}

// ---------- CompactSize ----------

proptest! {
    /// Lean: `Zebra.CompactSize.roundtrip_universal`
    #[test]
    fn compact_size_round_trip(n in 0u64..u64::MAX) {
        let encoded = compact_size::encode(n);
        let (decoded, rest) = compact_size::decode(&encoded)
            .expect("canonical encoding always decodes");
        prop_assert_eq!(decoded, n);
        prop_assert!(rest.is_empty());
    }

    /// Lean: `Zebra.CompactSize.encode_length` — length is in {1, 3, 5, 9}.
    #[test]
    fn compact_size_length(n in 0u64..u64::MAX) {
        let len = compact_size::encode(n).len();
        prop_assert!(matches!(len, 1 | 3 | 5 | 9));
    }

    /// Lean: `Zebra.CompactSize.canonicity_band2` — `0xfd` with payload < 0xfd is rejected.
    #[test]
    fn compact_size_canonicity_band2(payload in 0u16..0xfd) {
        let mut bytes = vec![0xfd];
        bytes.extend_from_slice(&payload.to_le_bytes());
        prop_assert!(compact_size::decode(&bytes).is_none());
    }

    /// Lean: `Zebra.CompactSize.messageTryFrom_iff`.
    #[test]
    fn compact_size_message_cap(n in any::<u32>()) {
        let result = compact_size::message_try_from(n);
        prop_assert_eq!(result.is_some(), n <= compact_size::MAX_PROTOCOL_MESSAGE_LEN);
    }
}
