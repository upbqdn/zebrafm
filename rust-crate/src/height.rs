//! Block height arithmetic, mirroring `zebra-chain/src/block/height.rs`.

/// The maximum height: `u32::MAX / 2 = 2^31 - 1`.
pub const MAX_AS_U32: u32 = u32::MAX / 2;

/// `Height::try_from<u32>`: returns `Some(h)` iff `h <= MAX_AS_U32`.
pub fn try_from_u32(n: u32) -> Option<u32> {
    if n <= MAX_AS_U32 {
        Some(n)
    } else {
        None
    }
}

/// `impl Add<HeightDiff> for Height`. Widens to `i64`, adds, and accepts iff
/// the result is in `[0, MAX_AS_U32]`.
pub fn add(h: u32, d: i64) -> Option<u32> {
    let lhs = h as i64;
    let res = lhs.checked_add(d)?;
    if res < 0 || res > (MAX_AS_U32 as i64) {
        None
    } else {
        Some(res as u32)
    }
}

/// `impl Sub<HeightDiff> for Height`.
pub fn sub(h: u32, d: i64) -> Option<u32> {
    let lhs = h as i64;
    let res = lhs.checked_sub(d)?;
    if res < 0 || res > (MAX_AS_U32 as i64) {
        None
    } else {
        Some(res as u32)
    }
}

/// `impl Sub<Height> for Height`: signed difference of two height values.
pub fn sub_h(lhs: u32, rhs: u32) -> i64 {
    (lhs as i64) - (rhs as i64)
}
