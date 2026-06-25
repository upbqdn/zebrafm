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

with `NonNegative` constraint bounding each pool to `0 ≤ x ≤ MAX_MONEY`, and
`MAX_MONEY = 21_000_000 * COIN = 21_000_000 * 100_000_000 = 2.1e15` zatoshis.

Each `Amount<C>` is serialised as 8 little-endian bytes; the value balance is
the concatenation of the five amounts → exactly 40 bytes.

We model each pool as `Nat` (since `NonNegative`), the value balance as a
plain record, and the wire bytes as `List Nat`.
-/

namespace Zebra.PoolValueBalance

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

/-- Total serialised length of a `ValueBalance`: 5 * 8 = 40 bytes.
Source: `zebra-chain/src/value_balance.rs:322` (`pub fn to_bytes(self) -> [u8; 40]`). -/
def VALUE_BALANCE_BYTES : Nat := POOL_COUNT * AMOUNT_BYTES

/-- A `ValueBalance<NonNegative>`: each pool is a `Nat` (the non-negative
constraint forces `0 ≤ x`; we additionally model the upper bound `x ≤
MAX_MONEY` as a hypothesis on the `valid` predicate below).
Source: `zebra-chain/src/value_balance.rs:23`. -/
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

/-- Sum of all five pool balances.
Source: `zebra-chain/src/value_balance.rs:176`
(`(self.transparent + self.sprout + self.sapling + self.orchard)?...`). -/
def total (vb : ValueBalance) : Nat :=
  vb.transparent + vb.sprout + vb.sapling + vb.orchard + vb.deferred

/-- Little-endian 8-byte encoding (low byte first) of a `Nat` truncated to
the low 64 bits. Models `Amount::to_bytes`.
Source: `zebra-chain/src/amount.rs:109`. -/
def toLE8 (n : Nat) : List Nat :=
  [ n % 256
  , (n / 256) % 256
  , (n / 65536) % 256
  , (n / 16777216) % 256
  , (n / 4294967296) % 256
  , (n / 1099511627776) % 256
  , (n / 281474976710656) % 256
  , (n / 72057594037927936) % 256 ]

/-- `ValueBalance::to_bytes`: concat the 8-byte encoding of each pool, in the
order `transparent, sprout, sapling, orchard, deferred`.
Source: `zebra-chain/src/value_balance.rs:322`. -/
def toBytes (vb : ValueBalance) : List Nat :=
  toLE8 vb.transparent ++
  toLE8 vb.sprout      ++
  toLE8 vb.sapling     ++
  toLE8 vb.orchard     ++
  toLE8 vb.deferred

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

/-- **T5.** A valid value balance has total at most `5 * MAX_MONEY`. -/
theorem total_bounded (vb : ValueBalance) (hv : valid vb) :
    total vb ≤ POOL_COUNT * MAX_MONEY := by
  unfold valid at hv
  unfold total POOL_COUNT
  obtain ⟨h1, h2, h3, h4, h5⟩ := hv
  omega

/-- **T6.** Concrete: a valid value balance has total at most
`5 * 2.1e15 = 1.05e16` zatoshis. -/
theorem total_bounded_concrete (vb : ValueBalance) (hv : valid vb) :
    total vb ≤ 10_500_000_000_000_000 := by
  have h := total_bounded vb hv
  unfold POOL_COUNT MAX_MONEY COIN at h
  omega

/-- **T7.** The `zero` value balance is valid. -/
theorem zero_valid : valid zero := by
  unfold valid zero MAX_MONEY COIN
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **T8.** The `zero` value balance has total 0. -/
theorem total_zero : total zero = 0 := by
  unfold total zero; rfl

/-- **T9.** Total is monotone in the transparent pool: increasing it can
only increase the total. -/
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

/-- **T11.** `valid` is decidable (constants and `≤` on `Nat`). -/
instance : DecidablePred valid := by
  intro vb
  unfold valid
  exact inferInstance

set_option linter.flexible false in
/-- **T12.** Every byte produced by `toLE8` is < 256 (well-formed bytes). -/
theorem toLE8_bytes_lt_256 (n : Nat) :
    ∀ b ∈ toLE8 n, b < 256 := by
  intro b hb
  unfold toLE8 at hb
  simp at hb
  rcases hb with h | h | h | h | h | h | h | h
  all_goals (rw [h]; exact Nat.mod_lt _ (by decide))

set_option linter.flexible false in
/-- **T13.** Every byte produced by `toBytes` is < 256. -/
theorem toBytes_bytes_lt_256 (vb : ValueBalance) :
    ∀ b ∈ toBytes vb, b < 256 := by
  intro b hb
  unfold toBytes at hb
  simp [List.mem_append] at hb
  rcases hb with h | h | h | h | h
  all_goals exact toLE8_bytes_lt_256 _ b h

end Zebra.PoolValueBalance
