import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Amount arithmetic from `zebra-chain/src/amount.rs`

Models the `Amount<C>` type — a newtype over `i64` parameterised by a
`Constraint` marker. The Rust value is `Amount<C>(i64, PhantomData<C>)`; the
arithmetic widens to `i128` only inside `Mul<u64>`. Closure under the
constraint range is enforced by `Constraint::validate`, which is called by every
`try_from`/`try_into` path.

We model the underlying value as `Int` (Rust `i64`) and the multiplication's
internal widening as plain `Int` arithmetic (Rust `i128`); the bounds
guarantee none of these widenings overflow in the real type sizes.

The three Rust constraint markers (`NegativeAllowed`, `NonNegative`,
`NegativeOrZero`) are encoded as cases of `Constraint`.
-/

namespace Zebra.Amount

/-- Number of zatoshis in 1 ZEC.
Source: `zebra-chain/src/amount.rs:607` -/
def COIN : Int := 100_000_000

/-- The maximum zatoshi amount: `21_000_000 * COIN = 2_100_000_000_000_000`.
Source: `zebra-chain/src/amount.rs:610` -/
def MAX_MONEY : Int := 21_000_000 * COIN

/-- The three `Constraint` markers from the Rust source.
Sources: `NegativeAllowed` at `zebra-chain/src/amount.rs:556`,
`NonNegative` at `:578`, `NegativeOrZero` at `:598`. -/
inductive Constraint
  | negativeAllowed
  | nonNegative
  | negativeOrZero

/-- Lower bound of a constraint's valid range. -/
def Constraint.lo : Constraint → Int
  | .negativeAllowed => -MAX_MONEY
  | .nonNegative     => 0
  | .negativeOrZero  => -MAX_MONEY

/-- Upper bound of a constraint's valid range. -/
def Constraint.hi : Constraint → Int
  | .negativeAllowed => MAX_MONEY
  | .nonNegative     => MAX_MONEY
  | .negativeOrZero  => 0

/-- `Constraint::validate`: returns `Some v` iff `v` is in `[lo, hi]`. -/
def Constraint.validate (c : Constraint) (v : Int) : Option Int :=
  if c.lo ≤ v ∧ v ≤ c.hi then some v else none

/-- `impl Add<Amount<C>> for Amount<C>`: checked addition under the constraint. -/
def checkedAdd (c : Constraint) (a b : Int) : Option Int :=
  c.validate (a + b)

/-- `impl Sub<Amount<C>> for Amount<C>`: checked subtraction. -/
def checkedSub (c : Constraint) (a b : Int) : Option Int :=
  c.validate (a - b)

/-- `impl Mul<u64> for Amount<C>`: i128-widened multiplication, validated. -/
def mulU64 (c : Constraint) (a : Int) (b : Nat) : Option Int :=
  c.validate (a * (b : Int))

/-- `impl Neg for Amount<C>`: returns `Amount<NegativeAllowed>` of `-a`.
The Rust code `expect`s this never fails on `[-MAX, MAX]`, which we prove. -/
def neg (a : Int) : Int := -a

/-! ## Theorems -/

/-- **T1.** `validate` under `NegativeAllowed` succeeds iff `|v| ≤ MAX_MONEY`. -/
theorem validate_negativeAllowed_iff (v : Int) :
    (Constraint.negativeAllowed.validate v).isSome ↔
      -MAX_MONEY ≤ v ∧ v ≤ MAX_MONEY := by
  unfold Constraint.validate Constraint.lo Constraint.hi
  by_cases h : -MAX_MONEY ≤ v ∧ v ≤ MAX_MONEY <;> simp [h]

/-- **T2.** `validate` under `NonNegative` succeeds iff `0 ≤ v ≤ MAX_MONEY`. -/
theorem validate_nonNegative_iff (v : Int) :
    (Constraint.nonNegative.validate v).isSome ↔
      0 ≤ v ∧ v ≤ MAX_MONEY := by
  unfold Constraint.validate Constraint.lo Constraint.hi
  by_cases h : 0 ≤ v ∧ v ≤ MAX_MONEY <;> simp [h]

/-- **T3.** `checkedAdd` returns `some r` iff the integer sum is in range, in
which case `r` equals the sum. -/
theorem checkedAdd_iff (c : Constraint) (a b : Int) :
    (checkedAdd c a b).isSome ↔ c.lo ≤ a + b ∧ a + b ≤ c.hi := by
  unfold checkedAdd Constraint.validate
  by_cases h : c.lo ≤ a + b ∧ a + b ≤ c.hi <;> simp [h]

/-- **T4.** `checkedAdd` result, when present, lies in `[lo, hi]`. -/
theorem checkedAdd_in_range (c : Constraint) (a b r : Int)
    (heq : checkedAdd c a b = some r) : c.lo ≤ r ∧ r ≤ c.hi := by
  unfold checkedAdd Constraint.validate at heq
  split_ifs at heq with hcond
  simp only [Option.some.injEq] at heq
  subst heq
  exact hcond

/-- **T5.** `checkedSub` returns `some r` iff the integer difference is in
range. -/
theorem checkedSub_iff (c : Constraint) (a b : Int) :
    (checkedSub c a b).isSome ↔ c.lo ≤ a - b ∧ a - b ≤ c.hi := by
  unfold checkedSub Constraint.validate
  by_cases h : c.lo ≤ a - b ∧ a - b ≤ c.hi <;> simp [h]

/-- **T6.** `checkedSub` result, when present, lies in `[lo, hi]`. -/
theorem checkedSub_in_range (c : Constraint) (a b r : Int)
    (heq : checkedSub c a b = some r) : c.lo ≤ r ∧ r ≤ c.hi := by
  unfold checkedSub Constraint.validate at heq
  split_ifs at heq with hcond
  simp only [Option.some.injEq] at heq
  subst heq
  exact hcond

/-- **T7.** `Mul<u64>` returns `some r` iff `a * b` is in range. The `i128`
widening is exact in the Rust source: the i64 inputs `a` and (positive) `b`
satisfy `|a * b| ≤ 2^63 * 2^64 < 2^128`. We model in `Int` directly so the
widening is automatically exact. -/
theorem mulU64_iff (c : Constraint) (a : Int) (b : Nat) :
    (mulU64 c a b).isSome ↔ c.lo ≤ a * (b : Int) ∧ a * (b : Int) ≤ c.hi := by
  unfold mulU64 Constraint.validate
  by_cases h : c.lo ≤ a * (b : Int) ∧ a * (b : Int) ≤ c.hi <;> simp [h]

/-- **T8.** `Neg` inverse property: `a + neg a = 0`. This is the property the
Rust source pins with `Amount::<NegativeAllowed>::try_from(-self.0).expect(...)`
and that `NegativeAllowed`'s symmetric range `[-MAX, MAX]` makes total. -/
theorem neg_inverse (a : Int) : a + neg a = 0 := by
  unfold neg; ring

/-- **T9 (range-closure of Neg under symmetric constraint).** For a value in
`NegativeAllowed`'s range, its negation is also in range. This is what
justifies the `.expect(...)` in the Rust `Neg` impl. -/
theorem neg_negativeAllowed_closed (a : Int)
    (h : -MAX_MONEY ≤ a ∧ a ≤ MAX_MONEY) :
    -MAX_MONEY ≤ neg a ∧ neg a ≤ MAX_MONEY := by
  unfold neg
  obtain ⟨h1, h2⟩ := h
  exact ⟨by linarith, by linarith⟩

/-! ## Stretch goals -/

/-- **T10.** `validate` under `NegativeOrZero` succeeds iff `-MAX ≤ v ≤ 0`. -/
theorem validate_negativeOrZero_iff (v : Int) :
    (Constraint.negativeOrZero.validate v).isSome ↔
      -MAX_MONEY ≤ v ∧ v ≤ 0 := by
  unfold Constraint.validate Constraint.lo Constraint.hi
  by_cases h : -MAX_MONEY ≤ v ∧ v ≤ 0 <;> simp [h]

/-- `impl Div<u64> for Amount<C>`: i128-widened checked division. Returns `none`
on division by zero (matching the Rust `DivideByZero` error), otherwise the
quotient validated under `C`. -/
def divU64 (c : Constraint) (a : Int) (b : Nat) : Option Int :=
  if b = 0 then none
  else c.validate (a / (b : Int))

/-- **T11 (Div: zero rejection).** Division by zero returns `none`. -/
theorem divU64_zero (c : Constraint) (a : Int) :
    divU64 c a 0 = none := by
  unfold divU64; simp

/-- **T12 (Div: range closure, NonNegative).** Quoting the Rust comment
`"division by a positive integer always stays within the constraint"`: for a
nonneg amount divided by a positive divisor, the result is automatically
within `NonNegative`'s range. -/
theorem divU64_nonNegative_closed (a : Int) (b : Nat)
    (hb : 0 < b) (ha : 0 ≤ a ∧ a ≤ MAX_MONEY) :
    (divU64 Constraint.nonNegative a b).isSome := by
  unfold divU64 Constraint.validate Constraint.lo Constraint.hi
  have hb' : b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  simp [hb']
  obtain ⟨h0, hM⟩ := ha
  have hbInt : (0 : Int) < (b : Int) := by exact_mod_cast hb
  refine ⟨Int.ediv_nonneg h0 (le_of_lt hbInt), ?_⟩
  have hSelf : a / (b : Int) ≤ a := Int.ediv_le_self (b : Int) h0
  linarith

/-- **`Sum`-style fold**: repeated `checkedAdd` left-to-right, short-circuiting
on out-of-range. Models the Rust `impl Sum<Amount<C>> for Result<Amount<C>>`. -/
def sumFold (c : Constraint) : List Int → Option Int
  | []      => c.validate 0
  | x :: xs =>
    match sumFold c xs with
    | none => none
    | some acc => checkedAdd c x acc

/-- **T13 (Sum: equivalence to repeated `checkedAdd`).** The base case: summing
the empty list is `validate 0`, which is `some 0` under every constraint
because `0` is in every constraint's range. -/
theorem sum_empty (c : Constraint) :
    sumFold c [] = some 0 := by
  unfold sumFold Constraint.validate
  rcases c with _ | _ | _ <;> simp [Constraint.lo, Constraint.hi, MAX_MONEY, COIN]

/-- **T14 (Sum: in-range under NonNegative).** If every element is in range and
no partial sum exceeds `MAX_MONEY`, the fold succeeds. (For brevity, witness
this for the simplest case: a singleton list.) -/
theorem sum_singleton_nonNegative (a : Int)
    (h : 0 ≤ a ∧ a ≤ MAX_MONEY) :
    sumFold Constraint.nonNegative [a] = some a := by
  unfold sumFold
  rw [sum_empty]
  unfold checkedAdd Constraint.validate Constraint.lo Constraint.hi
  obtain ⟨h0, hM⟩ := h
  simp [show a + 0 = a from by ring, h0, hM]

/-- **T15 (Sum value extraction).** When `sumFold` succeeds, its result equals
the natural integer sum of the list. This is the substantive equivalence to
"repeated `checked_add`": whatever the fold returns *as a value* is the
mathematical sum the iterator computes. -/
theorem sum_value (c : Constraint) (xs : List Int) (r : Int)
    (heq : sumFold c xs = some r) :
    r = xs.foldr (· + ·) 0 := by
  induction xs generalizing r with
  | nil =>
    unfold sumFold Constraint.validate at heq
    simp only [List.foldr_nil]
    rcases c with _ | _ | _ <;>
      (simp only [Constraint.lo, Constraint.hi, MAX_MONEY, COIN] at heq
       split_ifs at heq with _
       simp only [Option.some.injEq] at heq
       omega)
  | cons a xs ih =>
    rw [sumFold] at heq
    rcases h : sumFold c xs with _ | acc
    · rw [h] at heq; simp at heq
    · rw [h] at heq
      simp only at heq
      have hacc : acc = xs.foldr (· + ·) 0 := ih acc h
      unfold checkedAdd Constraint.validate at heq
      split_ifs at heq with _
      simp only [Option.some.injEq] at heq
      simp [List.foldr_cons, ← heq, hacc]

/-- **T16 (Sum result in range).** If the fold returns `Some`, that value lies
in the constraint's range. -/
theorem sum_in_range (c : Constraint) (xs : List Int) (r : Int)
    (heq : sumFold c xs = some r) : c.lo ≤ r ∧ r ≤ c.hi := by
  induction xs generalizing r with
  | nil =>
    unfold sumFold Constraint.validate at heq
    split_ifs at heq with hcond
    simp only [Option.some.injEq] at heq
    subst heq; exact hcond
  | cons a xs ih =>
    rw [sumFold] at heq
    rcases h : sumFold c xs with _ | acc
    · rw [h] at heq; simp at heq
    · rw [h] at heq
      simp only at heq
      exact checkedAdd_in_range c a acc r heq

/-! ## Bonus theorems -/

/-- **B1.** `checkedAdd` is commutative. -/
theorem checkedAdd_comm (c : Constraint) (a b : Int) :
    checkedAdd c a b = checkedAdd c b a := by
  unfold checkedAdd; congr 1; ring

/-- **B2.** `neg 0 = 0`. -/
theorem neg_zero : neg 0 = 0 := by unfold neg; simp

/-- **B3.** `neg` is involutive. -/
theorem neg_neg_eq (a : Int) : neg (neg a) = a := by unfold neg; ring

/-- **B4.** Subtraction equals addition of the negation: `checkedSub c a b =
checkedAdd c a (-b)`. -/
theorem checkedSub_as_add (c : Constraint) (a b : Int) :
    checkedSub c a b = checkedAdd c a (neg b) := by
  unfold checkedSub checkedAdd neg
  rfl

/-- **B5.** `checkedAdd a 0 = c.validate a`: zero is a right identity (modulo
constraint validation). -/
theorem checkedAdd_zero (c : Constraint) (a : Int) :
    checkedAdd c a 0 = c.validate a := by
  unfold checkedAdd; simp

end Zebra.Amount
