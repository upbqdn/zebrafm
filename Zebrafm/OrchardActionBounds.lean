import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Orchard action-count and value-balance bounds

Models the consensus-relevant arithmetic bounds on the Orchard shielded data
from `zebra-chain/src/orchard/shielded_data.rs`:

  * `ACTION_SIZE = 5 * 32 + 580 + 80 = 820` bytes (one `Action`).
  * `SPEND_AUTH_SIG_SIZE = 64` bytes.
  * `AUTHORIZED_ACTION_SIZE = ACTION_SIZE + SPEND_AUTH_SIG_SIZE = 884` bytes.
  * `MAX_ACTION_ALLOCATION = (MAX_BLOCK_BYTES - 1) / AUTHORIZED_ACTION_SIZE`,
    the bound asserted statically in
    `impl TrustedPreallocate for Action` to be `< 2^16` (and trivially
    `< 2^32`, so the action count fits in a `u32`).

For value balance, each Orchard action's value commitment contributes to a
running net `valueBalanceOrchard` which is an `Amount<NegativeAllowed>`
ranging over `[-MAX_MONEY, MAX_MONEY]` (see
`zebra-chain/src/amount.rs:556` and `:610`). The binding signature ties this
balancing value to the action value commitments
(`shielded_data.rs:123 binding_verification_key`). We prove that a left fold
of per-action `value_balance` contributions stays in
`[-MAX_MONEY, MAX_MONEY]` when each running partial sum (the value the Rust
`Sum` impl would `checked_add` into) stays in range — i.e. the running sum
never overflows the `NegativeAllowed` constraint.

Modelling choices: action counts are `Nat` (Rust `u32`); per-action value
balance contributions and partial sums are `Int` (the Rust `i64` widening
inside `Amount` arithmetic is exact at the bounds we use).
-/

namespace Zebra.OrchardActionBounds

/-! ## Block / action size constants -/

/-- The maximum size of a Zcash block, in bytes.
Source: `zebra-chain/src/block/serialize.rs:24`
(`pub const MAX_BLOCK_BYTES: u64 = 2_000_000`). -/
def MAX_BLOCK_BYTES : Nat := 2_000_000

/-- Size of a single Orchard `Action` in bytes: `5 * 32 + 580 + 80 = 820`.
Source: `zebra-chain/src/orchard/shielded_data.rs:194`
(`pub const ACTION_SIZE: u64 = 5 * 32 + 580 + 80`). -/
def ACTION_SIZE : Nat := 5 * 32 + 580 + 80

/-- Size of a `Signature<SpendAuth>` in bytes.
Source: `zebra-chain/src/orchard/shielded_data.rs:202`
(`pub const SPEND_AUTH_SIG_SIZE: u64 = 64`). -/
def SPEND_AUTH_SIG_SIZE : Nat := 64

/-- Size of an `AuthorizedAction` in bytes: `ACTION_SIZE + SPEND_AUTH_SIG_SIZE`.
Source: `zebra-chain/src/orchard/shielded_data.rs:207`
(`pub const AUTHORIZED_ACTION_SIZE: u64 = ACTION_SIZE + SPEND_AUTH_SIG_SIZE`). -/
def AUTHORIZED_ACTION_SIZE : Nat := ACTION_SIZE + SPEND_AUTH_SIG_SIZE

/-- The minimum action footprint inside a `Vec<AuthorizedAction>`. Used as
`MIN_ACTION_BYTES` in the bound `MAX_BLOCK_BYTES / MIN_ACTION_BYTES`,
matching the Rust `max_allocation` formula
`(MAX_BLOCK_BYTES - 1) / AUTHORIZED_ACTION_SIZE`. -/
def MIN_ACTION_BYTES : Nat := AUTHORIZED_ACTION_SIZE

/-- `u32::MAX = 2^32 - 1`. -/
def U32_MAX : Nat := 2 ^ 32 - 1

/-- `u16::MAX + 1 = 2^16`. Used by the static assertion in the Rust source
that the maximum action count is `< 2^16`. -/
def U16_LIMIT : Nat := 2 ^ 16

/-! ## Maximum action count -/

/-- The maximum number of actions that can fit into a maximally large block.
Source: `zebra-chain/src/orchard/shielded_data.rs:219`
(`const MAX: u64 = (MAX_BLOCK_BYTES - 1) / AUTHORIZED_ACTION_SIZE`). -/
def MAX_ACTION_ALLOCATION : Nat := (MAX_BLOCK_BYTES - 1) / AUTHORIZED_ACTION_SIZE

/-- Predicate: the action count `n` fits in the on-chain action allocation. -/
def actionCountValid (n : Nat) : Prop := n ≤ MAX_ACTION_ALLOCATION

/-! ## Value-balance bounds (NegativeAllowed) -/

/-- Number of zatoshis in 1 ZEC.
Source: `zebra-chain/src/amount.rs:607`. -/
def COIN : Int := 100_000_000

/-- The maximum zatoshi amount: `21_000_000 * COIN`.
Source: `zebra-chain/src/amount.rs:610`. -/
def MAX_MONEY : Int := 21_000_000 * COIN

/-- `NegativeAllowed::valid_range` = `[-MAX_MONEY, MAX_MONEY]`, the range of
the `valueBalanceOrchard` field as well as each action's per-pool value
balance contribution.
Source: `zebra-chain/src/amount.rs:558` (`impl Constraint for NegativeAllowed`). -/
def inRange (v : Int) : Prop := -MAX_MONEY ≤ v ∧ v ≤ MAX_MONEY

/-- Left fold of per-action value balance contributions starting from `acc`.
This models accumulating the running sum left-to-right, the way the binding
verification key is constructed in
`zebra-chain/src/orchard/shielded_data.rs:123`. -/
def sumFrom (acc : Int) : List Int → Int
  | []      => acc
  | x :: xs => sumFrom (acc + x) xs

/-- The empty-action sum starting from `acc` is just `acc`. -/
@[simp] theorem sumFrom_nil (acc : Int) : sumFrom acc [] = acc := rfl

/-- Sum of a list of per-action `value_balance` contributions, with running
sum starting at zero. The "net value balance" of an Orchard transaction. -/
def netValueBalance (contribs : List Int) : Int := sumFrom 0 contribs

/-- The running-sum invariant relative to a starting accumulator: stepping
the fold by one action keeps the partial sum in `[-MAX_MONEY, MAX_MONEY]` at
every intermediate stage. This is exactly the condition the Rust
`Sum<Amount<C>> for Result<Amount<C>>` impl checks (per-step `checked_add`
never overflows the constraint). -/
def runningSumInRange (acc : Int) : List Int → Prop
  | []      => inRange acc
  | x :: xs => inRange acc ∧ runningSumInRange (acc + x) xs

/-! ## Theorems -/

/-- **T1 (concrete: `MAX_BLOCK_BYTES = 2_000_000`).** -/
theorem max_block_bytes_value : MAX_BLOCK_BYTES = 2_000_000 := rfl

/-- **T2 (concrete: `AUTHORIZED_ACTION_SIZE = 884`).** -/
theorem authorized_action_size_value : AUTHORIZED_ACTION_SIZE = 884 := rfl

/-- **T3 (concrete: `MAX_ACTION_ALLOCATION = 2262`).** This is the value the
Rust source pins via `(MAX_BLOCK_BYTES - 1) / AUTHORIZED_ACTION_SIZE`. -/
theorem max_action_allocation_value : MAX_ACTION_ALLOCATION = 2262 := by
  unfold MAX_ACTION_ALLOCATION MAX_BLOCK_BYTES AUTHORIZED_ACTION_SIZE
        ACTION_SIZE SPEND_AUTH_SIG_SIZE
  decide

/-- **T4 (action count fits in `u32`).** Any valid action count is bounded by
`MAX_ACTION_ALLOCATION`, hence by `u32::MAX`. -/
theorem actionCountValid_fits_u32 (n : Nat) (h : actionCountValid n) :
    n ≤ U32_MAX := by
  unfold actionCountValid at h
  have := max_action_allocation_value
  unfold U32_MAX
  omega

/-- **T5 (action count fits in `u16`).** The Rust source asserts statically that
`MAX < (1 << 16)`. This is the same static assertion, in Lean. -/
theorem actionCountValid_fits_u16 (n : Nat) (h : actionCountValid n) :
    n < U16_LIMIT := by
  unfold actionCountValid at h
  have := max_action_allocation_value
  unfold U16_LIMIT
  omega

/-- **T6 (block-size bound: action count ≤ `MAX_BLOCK_BYTES / MIN_ACTION_BYTES`).**
The Rust formula uses `(MAX_BLOCK_BYTES - 1) / AUTHORIZED_ACTION_SIZE`, which
is `≤` the simpler `MAX_BLOCK_BYTES / MIN_ACTION_BYTES` (here
`MIN_ACTION_BYTES = AUTHORIZED_ACTION_SIZE`). -/
theorem actionCount_le_max_block_div_min_action (n : Nat) (h : actionCountValid n) :
    n ≤ MAX_BLOCK_BYTES / MIN_ACTION_BYTES := by
  unfold actionCountValid MAX_ACTION_ALLOCATION at h
  unfold MIN_ACTION_BYTES
  have hb : MAX_BLOCK_BYTES - 1 ≤ MAX_BLOCK_BYTES := Nat.sub_le _ _
  have hdiv : (MAX_BLOCK_BYTES - 1) / AUTHORIZED_ACTION_SIZE
              ≤ MAX_BLOCK_BYTES / AUTHORIZED_ACTION_SIZE :=
    Nat.div_le_div_right hb
  omega

/-- **T7 (zero net value balance for zero actions).** A transaction with no
actions has a net value balance of `0`. -/
theorem netValueBalance_empty : netValueBalance [] = 0 := rfl

/-- **T8 (zero is in `NegativeAllowed`'s range).** The base case for sum
closure: `0` lies in `[-MAX_MONEY, MAX_MONEY]`. -/
theorem zero_inRange : inRange 0 := by
  unfold inRange MAX_MONEY COIN
  exact ⟨by decide, by decide⟩

/-- **T9 (`sumFrom` accumulator semantics).** The fold's result equals the
starting accumulator plus the list sum. -/
theorem sumFrom_eq_acc_add_foldr (acc : Int) (xs : List Int) :
    sumFrom acc xs = acc + xs.foldr (· + ·) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    change sumFrom (acc + x) xs = acc + (x :: xs).foldr (· + ·) 0
    rw [ih (acc + x)]
    have hf : (x :: xs).foldr (· + ·) 0 = x + xs.foldr (· + ·) 0 := rfl
    rw [hf]; ring

/-- **T10 (`netValueBalance` equals the right-fold sum).** Useful for
turning fold facts about value balance into arithmetic facts. -/
theorem netValueBalance_eq_foldr (xs : List Int) :
    netValueBalance xs = xs.foldr (· + ·) 0 := by
  unfold netValueBalance
  rw [sumFrom_eq_acc_add_foldr]
  ring

/-- **T11 (running-sum closure: final fold value in range).** Under the
`runningSumInRange` invariant — every per-step partial sum is in
`[-MAX_MONEY, MAX_MONEY]` — the final fold value is also in range. -/
theorem sumFrom_inRange (acc : Int) (xs : List Int)
    (h : runningSumInRange acc xs) : inRange (sumFrom acc xs) := by
  induction xs generalizing acc with
  | nil => exact h
  | cons x xs ih =>
    obtain ⟨_, hRest⟩ := h
    change inRange (sumFrom (acc + x) xs)
    exact ih (acc + x) hRest

/-- **T12 (net-value-balance closure).** The load-bearing closure result the
prompt asks for: for an Orchard transaction whose list of per-action value
balance contributions satisfies the running-sum invariant (starting from
`0`), the net value balance lies in `[-MAX_MONEY, MAX_MONEY]`. -/
theorem netValueBalance_inRange (xs : List Int)
    (h : runningSumInRange 0 xs) :
    inRange (netValueBalance xs) :=
  sumFrom_inRange 0 xs h

/-- **T13 (zero actions starts in range).** The base case of the running-sum
invariant for an empty action list starting from `0`. -/
theorem runningSumInRange_empty : runningSumInRange 0 [] := zero_inRange

/-- **T14 (zero-action tx has 0 net value balance).** A transaction with no
actions has zero net value balance — and that zero is in range. -/
theorem netValueBalance_zero_actions :
    netValueBalance [] = 0 ∧ inRange (netValueBalance []) :=
  ⟨rfl, zero_inRange⟩

/-- **T15 (singleton net-value-balance).** A single-action transaction has
net value balance equal to that action's contribution. -/
theorem netValueBalance_singleton (x : Int) : netValueBalance [x] = x := by
  rw [netValueBalance_eq_foldr]
  simp

/-- **T16 (singleton range closure).** If an action's value balance is in
range, the singleton's net value balance is in range. -/
theorem netValueBalance_singleton_inRange (x : Int) (h : inRange x) :
    inRange (netValueBalance [x]) := by
  rw [netValueBalance_singleton]
  exact h

/-- **T17 (`MAX_MONEY` matches the documented constant).** -/
theorem max_money_value : MAX_MONEY = 2_100_000_000_000_000 := by
  unfold MAX_MONEY COIN; rfl

/-- **T18 (action allocation is positive).** Sanity check: a maximally large
block can carry at least one Orchard action. -/
theorem max_action_allocation_pos : 0 < MAX_ACTION_ALLOCATION := by
  rw [max_action_allocation_value]; decide

/-- **T19 (`actionCountValid` is decidable).** -/
instance : DecidablePred actionCountValid := by
  intro n
  unfold actionCountValid
  exact inferInstance

/-- **T20 (zero actions are valid).** -/
theorem actionCountValid_zero : actionCountValid 0 := by
  unfold actionCountValid; exact Nat.zero_le _

/-- **T21 (the action allocation is itself a valid count).** -/
theorem actionCountValid_max : actionCountValid MAX_ACTION_ALLOCATION := by
  unfold actionCountValid; exact le_refl _

/-- **T22 (`actionCountValid` is monotone-closed-downward).** If `n ≤ m` and
`m` is a valid action count, so is `n`. -/
theorem actionCountValid_mono (n m : Nat) (hle : n ≤ m) (h : actionCountValid m) :
    actionCountValid n := by
  unfold actionCountValid at *
  omega

end Zebra.OrchardActionBounds
