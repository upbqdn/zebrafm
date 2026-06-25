import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# PoolValueBalance from `zebra-chain/src/value_balance.rs`

`ValueBalance<C>` is a 5-pool record:

```text
pub struct ValueBalance<C> {
    transparent: Amount<C>,
    sprout:      Amount<C>,
    sapling:     Amount<C>,
    orchard:     Amount<C>,
    deferred:    Amount<C>,
}
```

with `C : Constraint` selecting the per-pool range:

* `NonNegative`     ⇒ each pool in `[0, MAX_MONEY]`
* `NegativeAllowed` ⇒ each pool in `[-MAX_MONEY, MAX_MONEY]`

where `MAX_MONEY = 21_000_000 * COIN = 21_000_000 * 100_000_000 = 2.1e15`
zatoshis.

We model `ValueBalance<NonNegative>` with `Nat` pools and
`ValueBalance<NegativeAllowed>` with `Int` pools. The Rust serialised form is
the concatenation of each pool's `Amount::to_bytes` — `i64` little-endian
two's complement, 8 bytes each, total 40 bytes. For non-negative amounts (the
only kind for which Rust calls `ValueBalance::to_bytes`), the top bits are
always zero, so the encoding reduces to a plain LE encoding of the `Nat`
value.

## Findings addressed

* **Finding 50.** The Rust `remaining_transaction_value` sums the four
  transaction pools (`transparent + sprout + sapling + orchard`) — it
  excludes `deferred`. We split the model into `total4` (matching Rust) and
  `total5` (which corresponds to no Rust function; deferred goes to the
  protocol's lockbox stream). The old `total` name retains the 5-pool sum
  but its docstring now reflects that it has no direct Rust analogue, and we
  add `total4` with a faithful semantics theorem.
* **Finding 51.** Sapling/Orchard balances can be negative
  (`NegativeAllowed`). Encoding `-1: i64` produces `[0xff; 8]`, which the
  `Nat`-based `toLE8` cannot model. We add `toI64LE`, a two's-complement
  little-endian encoder for `Int` values in `[-2^63, 2^63)`, and a signed
  value-balance type `ValueBalanceSigned` with its own `toBytesSigned`.
-/

namespace Zebra.PoolValueBalance

/-! ## Constants -/

/-- Number of zatoshis in 1 ZEC.
Source: `zebra-chain/src/amount.rs:607` (`pub const COIN: i64 = 100_000_000`). -/
def COIN : Nat := 100_000_000

/-- The supply cap on every pool balance: `21_000_000 * COIN`.
Source: `zebra-chain/src/amount.rs:610`
(`pub const MAX_MONEY: i64 = 21_000_000 * COIN`). -/
def MAX_MONEY : Nat := 21_000_000 * COIN

/-- Number of bytes used to serialise an `Amount<C>`.
Source: `zebra-chain/src/amount.rs:109` (`pub fn to_bytes(&self) -> [u8; 8]`). -/
def AMOUNT_BYTES : Nat := 8

/-- Number of pools in a `ValueBalance`: transparent, sprout, sapling,
orchard, deferred.
Source: `zebra-chain/src/value_balance.rs:23` (`pub struct ValueBalance<C>`). -/
def POOL_COUNT : Nat := 5

/-- Number of pools summed by `ValueBalance::remaining_transaction_value`:
transparent, sprout, sapling, orchard. The deferred pool is excluded.
Source: `zebra-chain/src/value_balance.rs:170-177`. -/
def TX_POOL_COUNT : Nat := 4

/-- Total serialised length of a `ValueBalance`: `5 * 8 = 40` bytes.
Source: `zebra-chain/src/value_balance.rs:322` (`pub fn to_bytes(self) -> [u8; 40]`). -/
def VALUE_BALANCE_BYTES : Nat := POOL_COUNT * AMOUNT_BYTES

/-- Legacy serialised length accepted by `ValueBalance::from_bytes` for
backward compatibility (pre-deferred-pool blocks): `4 * 8 = 32` bytes.
Source: `zebra-chain/src/value_balance.rs:346-348,379-388`. -/
def VALUE_BALANCE_LEGACY_BYTES : Nat := TX_POOL_COUNT * AMOUNT_BYTES

/-! ## `ValueBalance<NonNegative>` -/

/-- A `ValueBalance<NonNegative>`: each pool is a `Nat`. The `NonNegative`
constraint requires `0 ≤ x ≤ MAX_MONEY`; we model `0 ≤ x` structurally and
the upper bound via the `valid` predicate.
Source: `zebra-chain/src/value_balance.rs:23`, `amount.rs:578-584`. -/
structure ValueBalance where
  transparent : Nat
  sprout      : Nat
  sapling     : Nat
  orchard     : Nat
  deferred    : Nat
  deriving Repr, DecidableEq

/-- The all-zero value balance.
Source: `zebra-chain/src/value_balance.rs` (`ValueBalance::zero`). -/
def zero : ValueBalance :=
  { transparent := 0, sprout := 0, sapling := 0, orchard := 0, deferred := 0 }

/-- Each pool is within `[0, MAX_MONEY]` (the `NonNegative` constraint).
Source: `zebra-chain/src/amount.rs:582` (range `0..=MAX_MONEY`). -/
def valid (vb : ValueBalance) : Prop :=
  vb.transparent ≤ MAX_MONEY ∧
  vb.sprout      ≤ MAX_MONEY ∧
  vb.sapling     ≤ MAX_MONEY ∧
  vb.orchard     ≤ MAX_MONEY ∧
  vb.deferred    ≤ MAX_MONEY

/-- Sum of the four transaction pools — the value computed by Rust's
`ValueBalance::remaining_transaction_value` before its non-negativity check.
The deferred pool is intentionally excluded.
Source: `zebra-chain/src/value_balance.rs:170-177`. -/
def total4 (vb : ValueBalance) : Nat :=
  vb.transparent + vb.sprout + vb.sapling + vb.orchard

/-- Sum of all five pool balances. **Has no direct Rust analogue.** Rust
never computes this aggregate (the deferred pool is fed by a separate
lockbox stream rather than mixed with transaction pools). We keep this
definition because lemmas downstream parameterise over it; the meaningful
sum is `total4`.
Source: structural sum of `zebra-chain/src/value_balance.rs:23-29`. -/
def total (vb : ValueBalance) : Nat :=
  vb.transparent + vb.sprout + vb.sapling + vb.orchard + vb.deferred

/-! ## Byte encoding -/

/-- Little-endian 8-byte encoding (low byte first) of a `Nat` truncated to
the low 64 bits. For non-negative amounts in `[0, MAX_MONEY]` this matches
`LittleEndian::write_i64` exactly because `MAX_MONEY < 2^51`, so the high
13 bits of the `i64` are zero.
Source: `zebra-chain/src/amount.rs:109-113`. -/
def toLE8 (n : Nat) : List Nat :=
  [ n % 256
  , (n / 256) % 256
  , (n / 65536) % 256
  , (n / 16777216) % 256
  , (n / 4294967296) % 256
  , (n / 1099511627776) % 256
  , (n / 281474976710656) % 256
  , (n / 72057594037927936) % 256 ]

/-- `ValueBalance::to_bytes`: concat the 8-byte encoding of each pool, in
the order `transparent, sprout, sapling, orchard, deferred`.
Source: `zebra-chain/src/value_balance.rs:322-338`. -/
def toBytes (vb : ValueBalance) : List Nat :=
  toLE8 vb.transparent ++
  toLE8 vb.sprout      ++
  toLE8 vb.sapling     ++
  toLE8 vb.orchard     ++
  toLE8 vb.deferred

/-! ## `ValueBalance<NegativeAllowed>` (Finding 51)

Models the signed variant used by `remaining_transaction_value` and other
in-transaction computations. Values are in `[-MAX_MONEY, MAX_MONEY]`. -/

/-- The signed value-balance type: each pool is an `Int`. Models
`ValueBalance<NegativeAllowed>`.
Source: `zebra-chain/src/value_balance.rs:23`, `amount.rs:556-562`. -/
structure ValueBalanceSigned where
  transparent : Int
  sprout      : Int
  sapling     : Int
  orchard     : Int
  deferred    : Int
  deriving Repr, DecidableEq

/-- Each pool is within `[-MAX_MONEY, MAX_MONEY]` (the `NegativeAllowed`
constraint).
Source: `zebra-chain/src/amount.rs:558-561`. -/
def validSigned (vb : ValueBalanceSigned) : Prop :=
  -(MAX_MONEY : Int) ≤ vb.transparent ∧ vb.transparent ≤ (MAX_MONEY : Int) ∧
  -(MAX_MONEY : Int) ≤ vb.sprout      ∧ vb.sprout      ≤ (MAX_MONEY : Int) ∧
  -(MAX_MONEY : Int) ≤ vb.sapling     ∧ vb.sapling     ≤ (MAX_MONEY : Int) ∧
  -(MAX_MONEY : Int) ≤ vb.orchard     ∧ vb.orchard     ≤ (MAX_MONEY : Int) ∧
  -(MAX_MONEY : Int) ≤ vb.deferred    ∧ vb.deferred    ≤ (MAX_MONEY : Int)

/-- Two's-complement encoding into the canonical `[0, 2^64)` representative.
For `0 ≤ v < 2^63` returns `v`; for `-2^63 ≤ v < 0` returns `v + 2^64`. -/
def i64Repr (v : Int) : Int :=
  if 0 ≤ v then v else v + 18446744073709551616

/-- Little-endian two's-complement 8-byte encoding of an `Int` value
intended to fit in an `i64`. Mirrors `LittleEndian::write_i64`.
Source: `zebra-chain/src/amount.rs:109-113`. -/
def toI64LE (v : Int) : List Nat :=
  let r := (i64Repr v).toNat
  [ r % 256
  , (r / 256) % 256
  , (r / 65536) % 256
  , (r / 16777216) % 256
  , (r / 4294967296) % 256
  , (r / 1099511627776) % 256
  , (r / 281474976710656) % 256
  , (r / 72057594037927936) % 256 ]

/-- Signed `ValueBalance::to_bytes`: concat the 8-byte encoding of each
pool in the order `transparent, sprout, sapling, orchard, deferred`. The
underlying per-pool encoder is now the signed two's-complement encoder. -/
def toBytesSigned (vb : ValueBalanceSigned) : List Nat :=
  toI64LE vb.transparent ++
  toI64LE vb.sprout      ++
  toI64LE vb.sapling     ++
  toI64LE vb.orchard     ++
  toI64LE vb.deferred

/-- Sum of the four transaction pools, signed.
Source: `zebra-chain/src/value_balance.rs:170-177`. -/
def total4Signed (vb : ValueBalanceSigned) : Int :=
  vb.transparent + vb.sprout + vb.sapling + vb.orchard

/-! ## Theorems -/

/-- **T1.** `MAX_MONEY` matches the documented constant `2.1e15` zatoshis. -/
theorem max_money_value : MAX_MONEY = 2_100_000_000_000_000 := by
  unfold MAX_MONEY COIN; rfl

/-- **T2.** The serialised value balance is exactly `5 * 8 = 40` bytes. -/
theorem toBytes_length (vb : ValueBalance) :
    (toBytes vb).length = VALUE_BALANCE_BYTES := by
  unfold toBytes toLE8 VALUE_BALANCE_BYTES POOL_COUNT AMOUNT_BYTES
  simp

/-- **T3.** Concrete: the serialised value balance is exactly 40 bytes. -/
theorem toBytes_length_40 (vb : ValueBalance) :
    (toBytes vb).length = 40 := by
  rw [toBytes_length]; rfl

/-- **T4.** Each per-pool encoding is exactly 8 bytes. -/
theorem toLE8_length (n : Nat) : (toLE8 n).length = AMOUNT_BYTES := by
  unfold toLE8 AMOUNT_BYTES; rfl

/-- **T5.** A valid value balance has 5-pool aggregate at most
`5 * MAX_MONEY`. This is purely a structural bound on `total`; it does not
correspond to any Rust-level invariant since Rust never computes the 5-pool
sum. The meaningful bound is `total4_bounded` below. -/
theorem total_bounded (vb : ValueBalance) (hv : valid vb) :
    total vb ≤ POOL_COUNT * MAX_MONEY := by
  unfold valid at hv
  unfold total POOL_COUNT
  obtain ⟨h1, h2, h3, h4, h5⟩ := hv
  omega

/-- **T6.** Concrete: a valid value balance has 5-pool aggregate at most
`5 * 2.1e15 = 1.05e16` zatoshis. Caveat as in T5: this is a structural
bound, not a consensus invariant. -/
theorem total_bounded_concrete (vb : ValueBalance) (hv : valid vb) :
    total vb ≤ 10_500_000_000_000_000 := by
  have h := total_bounded vb hv
  unfold POOL_COUNT MAX_MONEY COIN at h
  omega

/-- **T7.** The `zero` value balance is valid. -/
theorem zero_valid : valid zero := by
  unfold valid zero MAX_MONEY COIN
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **T8.** The `zero` value balance has 5-pool sum 0. -/
theorem total_zero : total zero = 0 := by
  unfold total zero; rfl

/-- **T9.** `total` is monotone in the transparent pool: increasing it can
only increase the 5-pool sum. -/
theorem total_monotone_transparent (vb : ValueBalance) (x : Nat)
    (hx : vb.transparent ≤ x) :
    total vb ≤ total { vb with transparent := x } := by
  unfold total
  simp
  omega

/-- **T10.** Pool count is exactly 5 and matches the byte layout. -/
theorem pool_count_layout :
    POOL_COUNT * AMOUNT_BYTES = VALUE_BALANCE_BYTES := by
  unfold VALUE_BALANCE_BYTES; rfl

/-- **T11.** `valid` is decidable. -/
instance : DecidablePred valid := by
  intro vb
  unfold valid
  exact inferInstance

set_option linter.flexible false in
/-- **T12.** Every byte produced by `toLE8` is `< 256`. -/
theorem toLE8_bytes_lt_256 (n : Nat) :
    ∀ b ∈ toLE8 n, b < 256 := by
  intro b hb
  unfold toLE8 at hb
  simp at hb
  rcases hb with h | h | h | h | h | h | h | h
  all_goals (rw [h]; exact Nat.mod_lt _ (by decide))

set_option linter.flexible false in
/-- **T13.** Every byte produced by `toBytes` is `< 256`. -/
theorem toBytes_bytes_lt_256 (vb : ValueBalance) :
    ∀ b ∈ toBytes vb, b < 256 := by
  intro b hb
  unfold toBytes at hb
  simp [List.mem_append] at hb
  rcases hb with h | h | h | h | h
  all_goals exact toLE8_bytes_lt_256 _ b h

/-! ### Theorems for `total4` (Finding 50)

These match the Rust `remaining_transaction_value` semantics, which sums
transparent + sprout + sapling + orchard and excludes the deferred pool. -/

/-- **T14 (Finding 50).** `total4` literally equals the Rust formula
`transparent + sprout + sapling + orchard`. -/
theorem total4_definition (vb : ValueBalance) :
    total4 vb = vb.transparent + vb.sprout + vb.sapling + vb.orchard := rfl

/-- **T15 (Finding 50).** `total4` excludes `deferred`: changing `deferred`
does not affect `total4`. This is the property that broke for the original
`total`. -/
theorem total4_independent_of_deferred (vb : ValueBalance) (d : Nat) :
    total4 { vb with deferred := d } = total4 vb := by
  unfold total4; rfl

/-- **T16 (Finding 50).** A valid value balance has `total4` at most
`4 * MAX_MONEY = 8.4e15` zatoshis. This is the bound on
`remaining_transaction_value`'s pre-check sum. -/
theorem total4_bounded (vb : ValueBalance) (hv : valid vb) :
    total4 vb ≤ TX_POOL_COUNT * MAX_MONEY := by
  unfold valid at hv
  unfold total4 TX_POOL_COUNT
  obtain ⟨h1, h2, h3, h4, _⟩ := hv
  omega

/-- **T17 (Finding 50).** Concrete: a valid value balance has `total4` at
most `8.4e15` zatoshis. -/
theorem total4_bounded_concrete (vb : ValueBalance) (hv : valid vb) :
    total4 vb ≤ 8_400_000_000_000_000 := by
  have h := total4_bounded vb hv
  unfold TX_POOL_COUNT MAX_MONEY COIN at h
  omega

/-- **T18 (Finding 50).** `total = total4 + deferred`. The 5-pool aggregate
is exactly the transaction-pool aggregate plus deferred. -/
theorem total_eq_total4_plus_deferred (vb : ValueBalance) :
    total vb = total4 vb + vb.deferred := by
  unfold total total4; rfl

/-- **T19 (Finding 50).** The 5-pool sum and 4-pool sum agree exactly when
the deferred pool is zero. -/
theorem total_eq_total4_iff_deferred_zero (vb : ValueBalance) :
    total vb = total4 vb ↔ vb.deferred = 0 := by
  rw [total_eq_total4_plus_deferred]
  omega

/-! ### Theorems for `total4Signed` and the signed encoder (Finding 51) -/

/-- **T20 (Finding 51).** The signed serialised value balance is exactly 40
bytes. -/
theorem toBytesSigned_length (vb : ValueBalanceSigned) :
    (toBytesSigned vb).length = VALUE_BALANCE_BYTES := by
  unfold toBytesSigned toI64LE VALUE_BALANCE_BYTES POOL_COUNT AMOUNT_BYTES
  simp

/-- **T21 (Finding 51).** Each per-pool signed encoding is 8 bytes. -/
theorem toI64LE_length (v : Int) : (toI64LE v).length = AMOUNT_BYTES := by
  unfold toI64LE AMOUNT_BYTES
  simp

/-- **T22 (Finding 51).** Encoding `-1: i64` produces `[0xff; 8]` — the
canonical two's-complement representation of `-1`. This is the concrete
case that the pure-`Nat` `toLE8` *cannot* produce, demonstrating that the
signed encoder is strictly more expressive. -/
theorem toI64LE_neg_one : toI64LE (-1) = [255, 255, 255, 255, 255, 255, 255, 255] := by
  unfold toI64LE i64Repr
  decide

/-- **T23 (Finding 51).** For non-negative `v` in the `i64` range, the
signed encoder agrees with the unsigned `toLE8` applied to `v.toNat`. So
the `NonNegative` and `NegativeAllowed` encoders coincide on the overlap
of their domains. -/
theorem toI64LE_eq_toLE8_of_nonneg (v : Int) (hv : 0 ≤ v) :
    toI64LE v = toLE8 v.toNat := by
  unfold toI64LE toLE8 i64Repr
  simp [hv]

/-- **T24 (Finding 51).** Encoding `0` yields all zero bytes (the obvious
sanity check). -/
theorem toI64LE_zero : toI64LE 0 = [0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold toI64LE i64Repr
  decide

set_option linter.flexible false in
/-- **T25 (Finding 51).** Every byte produced by `toI64LE` is `< 256`. -/
theorem toI64LE_bytes_lt_256 (v : Int) :
    ∀ b ∈ toI64LE v, b < 256 := by
  intro b hb
  unfold toI64LE at hb
  simp at hb
  rcases hb with h | h | h | h | h | h | h | h
  all_goals (rw [h]; exact Nat.mod_lt _ (by decide))

set_option linter.flexible false in
/-- **T26 (Finding 51).** Every byte produced by `toBytesSigned` is `< 256`. -/
theorem toBytesSigned_bytes_lt_256 (vb : ValueBalanceSigned) :
    ∀ b ∈ toBytesSigned vb, b < 256 := by
  intro b hb
  unfold toBytesSigned at hb
  simp [List.mem_append] at hb
  rcases hb with h | h | h | h | h
  all_goals exact toI64LE_bytes_lt_256 _ b h

/-- **T27 (Finding 51).** `total4Signed` literally matches the Rust formula. -/
theorem total4Signed_definition (vb : ValueBalanceSigned) :
    total4Signed vb = vb.transparent + vb.sprout + vb.sapling + vb.orchard := rfl

/-- **T28 (Finding 51).** A signed-valid value balance has
`|total4Signed|` at most `4 * MAX_MONEY`. This is the analogue of T16 for
the signed case: a sum of four `[-MAX_MONEY, MAX_MONEY]` integers lies in
`[-4 * MAX_MONEY, 4 * MAX_MONEY]`. -/
theorem total4Signed_bounded (vb : ValueBalanceSigned) (hv : validSigned vb) :
    -((TX_POOL_COUNT : Int) * MAX_MONEY) ≤ total4Signed vb ∧
    total4Signed vb ≤ (TX_POOL_COUNT : Int) * MAX_MONEY := by
  unfold validSigned at hv
  unfold total4Signed TX_POOL_COUNT
  obtain ⟨h1a, h1b, h2a, h2b, h3a, h3b, h4a, h4b, _, _⟩ := hv
  refine ⟨?_, ?_⟩ <;> push_cast <;> linarith

/-- **T29 (Finding 51).** A signed-valid value balance can be genuinely
negative: the all-`-1` value balance is valid and has `total4Signed = -4`.
This documents that the signed model admits values the `Nat` model cannot. -/
theorem total4Signed_can_be_negative :
    let vb : ValueBalanceSigned :=
      { transparent := -1, sprout := -1, sapling := -1, orchard := -1, deferred := -1 }
    validSigned vb ∧ total4Signed vb = -4 := by
  refine ⟨?_, ?_⟩
  · unfold validSigned
    unfold MAX_MONEY COIN
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · unfold total4Signed; decide

/-! ### Backward-compatible deserialisation length (mentioned in
FINDINGS low/medium list)

Rust's `ValueBalance::from_bytes` accepts both 32-byte (pre-deferred) and
40-byte inputs, treating the deferred pool as zero in the 32-byte case. We
do not model the parsing function fully here, but we expose the two valid
input lengths as constants and prove their relationship. -/

/-- **T30.** The legacy and current serialised lengths are 32 and 40 bytes. -/
theorem legacy_and_current_lengths :
    VALUE_BALANCE_LEGACY_BYTES = 32 ∧ VALUE_BALANCE_BYTES = 40 := by
  refine ⟨?_, ?_⟩
  · unfold VALUE_BALANCE_LEGACY_BYTES TX_POOL_COUNT AMOUNT_BYTES; rfl
  · unfold VALUE_BALANCE_BYTES POOL_COUNT AMOUNT_BYTES; rfl

/-- **T31.** The legacy form omits exactly the deferred pool (one
8-byte amount). -/
theorem legacy_omits_one_amount :
    VALUE_BALANCE_BYTES = VALUE_BALANCE_LEGACY_BYTES + AMOUNT_BYTES := by
  unfold VALUE_BALANCE_BYTES VALUE_BALANCE_LEGACY_BYTES
    POOL_COUNT TX_POOL_COUNT AMOUNT_BYTES
  rfl

end Zebra.PoolValueBalance
