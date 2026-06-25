//! Amount arithmetic, mirroring `zebra-chain/src/amount.rs`.

/// Number of zatoshis in 1 ZEC.
pub const COIN: i64 = 100_000_000;

/// The maximum zatoshi amount: `21_000_000 * COIN`.
pub const MAX_MONEY: i64 = 21_000_000 * COIN;

/// The three `Constraint` markers from the Rust source.
#[derive(Clone, Copy)]
pub enum Constraint {
    NegativeAllowed,
    NonNegative,
    NegativeOrZero,
}

/// Lower bound of a constraint's valid range.
pub fn lo(c: Constraint) -> i64 {
    match c {
        Constraint::NegativeAllowed => -MAX_MONEY,
        Constraint::NonNegative => 0,
        Constraint::NegativeOrZero => -MAX_MONEY,
    }
}

/// Upper bound of a constraint's valid range.
pub fn hi(c: Constraint) -> i64 {
    match c {
        Constraint::NegativeAllowed => MAX_MONEY,
        Constraint::NonNegative => MAX_MONEY,
        Constraint::NegativeOrZero => 0,
    }
}

/// `Constraint::validate`: returns `Some(v)` iff `v` is in `[lo, hi]`.
pub fn validate(c: Constraint, v: i64) -> Option<i64> {
    if lo(c) <= v && v <= hi(c) {
        Some(v)
    } else {
        None
    }
}

/// `impl Add<Amount<C>> for Amount<C>`: checked addition under the constraint.
pub fn checked_add(c: Constraint, a: i64, b: i64) -> Option<i64> {
    let sum = a.checked_add(b)?;
    validate(c, sum)
}

/// `impl Sub<Amount<C>> for Amount<C>`: checked subtraction.
pub fn checked_sub(c: Constraint, a: i64, b: i64) -> Option<i64> {
    let diff = a.checked_sub(b)?;
    validate(c, diff)
}

/// `impl Mul<u64> for Amount<C>`: i128-widened multiplication, validated.
pub fn mul_u64(c: Constraint, a: i64, b: u64) -> Option<i64> {
    let prod = (a as i128).checked_mul(b as i128)?;
    if prod < (i64::MIN as i128) || prod > (i64::MAX as i128) {
        return None;
    }
    validate(c, prod as i64)
}

/// `impl Div<u64> for Amount<C>`: i128-widened division.
pub fn div_u64(c: Constraint, a: i64, b: u64) -> Option<i64> {
    if b == 0 {
        return None;
    }
    let q = (a as i128) / (b as i128);
    validate(c, q as i64)
}

/// `impl Neg for Amount<C>`: returns `-a`.
pub fn neg(a: i64) -> i64 {
    -a
}
