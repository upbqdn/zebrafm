import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Height arithmetic from `zebra-chain/src/block/height.rs`

`Height` is a `pub struct Height(u32)` with `Height::MAX = u32::MAX / 2 = 2^31 - 1`,
and `HeightDiff = i64`. `Add<HeightDiff>` / `Sub<HeightDiff>` widen to `i64`,
do the arithmetic, then accept iff the result lies in `[0, MAX_AS_U32]`.

We model the height as `Nat`, `HeightDiff` as `Int`, and the `i64`-widened
arithmetic as `Int` arithmetic.
-/

namespace Zebra.Height

/-- The maximum height as a `Nat`: `u32::MAX / 2 = 2^31 - 1`.
Source: `zebra-chain/src/block/height.rs:67` -/
def MAX_AS_U32 : Nat := 2 ^ 31 - 1

/-- `Height::try_from<u32>`: returns `Some h` iff `h ≤ MAX_AS_U32`.
Source: `zebra-chain/src/block/height.rs:133` (`impl TryFrom<u32> for Height`) -/
def tryFromU32 (n : Nat) : Option Nat :=
  if n ≤ MAX_AS_U32 then some n else none

/-- `Add<HeightDiff> for Height`.
Source: `zebra-chain/src/block/height.rs:264` (`impl Add<HeightDiff> for Height`) -/
def add (h : Nat) (d : Int) : Option Nat :=
  if 0 ≤ (h : Int) + d ∧ (h : Int) + d ≤ (MAX_AS_U32 : Int) then
    some ((h : Int) + d).toNat
  else none

/-- `Sub<HeightDiff> for Height`.
Source: `zebra-chain/src/block/height.rs:248` (`impl Sub<HeightDiff> for Height`) -/
def sub (h : Nat) (d : Int) : Option Nat :=
  if 0 ≤ (h : Int) - d ∧ (h : Int) - d ≤ (MAX_AS_U32 : Int) then
    some ((h : Int) - d).toNat
  else none

/-- `Sub<Height> for Height`: signed difference of two height values.
Source: `zebra-chain/src/block/height.rs:234` (`impl Sub<Height> for Height`) -/
def subH (lhs rhs : Nat) : Int := (lhs : Int) - (rhs : Int)

/-! ## Theorems -/

/-- **T1.** `tryFromU32` succeeds exactly on `[0, MAX_AS_U32]`. -/
theorem tryFromU32_iff (n : Nat) :
    (tryFromU32 n).isSome ↔ n ≤ MAX_AS_U32 := by
  unfold tryFromU32
  by_cases hn : n ≤ MAX_AS_U32 <;> simp [hn]

/-- **T2.** `subH` is the integer difference. -/
theorem subH_eq (lhs rhs : Nat) :
    subH lhs rhs = (lhs : Int) - (rhs : Int) := rfl

/-- **T3.** `add` result is bounded by `MAX_AS_U32`. -/
theorem add_result_bounded (h : Nat) (d : Int) (r : Nat)
    (heq : add h d = some r) : r ≤ MAX_AS_U32 := by
  unfold add at heq
  split_ifs at heq with hcond
  simp only [Option.some.injEq] at heq
  obtain ⟨h0, hMax⟩ := hcond
  omega

/-- **T4.** `sub` result is bounded by `MAX_AS_U32`. -/
theorem sub_result_bounded (h : Nat) (d : Int) (r : Nat)
    (heq : sub h d = some r) : r ≤ MAX_AS_U32 := by
  unfold sub at heq
  split_ifs at heq with hcond
  simp only [Option.some.injEq] at heq
  obtain ⟨h0, hMax⟩ := hcond
  omega

/-- **T5.** Round-trip: if `h ≤ MAX_AS_U32` and `add h d = some r`, then
`sub r d = some h`. -/
theorem add_sub_eq (h : Nat) (d : Int) (r : Nat)
    (hH : h ≤ MAX_AS_U32) (heq : add h d = some r) :
    sub r d = some h := by
  unfold add at heq
  split_ifs at heq with hcond
  simp only [Option.some.injEq] at heq
  obtain ⟨h0, hMax⟩ := hcond
  unfold sub
  have hrInt : (r : Int) = (h : Int) + d := by
    rw [← heq]; exact Int.toNat_of_nonneg h0
  have hdiff : (r : Int) - d = (h : Int) := by linarith
  have h_max : (h : Int) ≤ (MAX_AS_U32 : Int) := by exact_mod_cast hH
  have h_nat : (0 : Int) ≤ (h : Int) := Int.natCast_nonneg h
  rw [hdiff, if_pos ⟨h_nat, h_max⟩, Int.toNat_natCast]

/-- **T6.** `add` is monotone in the diff argument. -/
theorem add_monotone (h : Nat) (d₁ d₂ : Int) (r₁ r₂ : Nat)
    (heq₁ : add h d₁ = some r₁) (heq₂ : add h d₂ = some r₂)
    (hle : d₁ ≤ d₂) : r₁ ≤ r₂ := by
  unfold add at heq₁ heq₂
  split_ifs at heq₁ with hc₁
  split_ifs at heq₂ with hc₂
  simp only [Option.some.injEq] at heq₁ heq₂
  obtain ⟨h0₁, _⟩ := hc₁
  obtain ⟨h0₂, _⟩ := hc₂
  omega

/-! ## Bonus theorems -/

/-- **B1.** `subH` is antisymmetric: `subH a b = -(subH b a)`. -/
theorem subH_antisymm (a b : Nat) : subH a b = -(subH b a) := by
  unfold subH; ring

/-- **B2.** `subH a a = 0`. -/
theorem subH_self (a : Nat) : subH a a = 0 := by
  unfold subH; simp

/-- **B3.** `tryFromU32` is idempotent on valid inputs: if `h ≤ MAX`, then
`tryFromU32 h = some h`. -/
theorem tryFromU32_valid (h : Nat) (hH : h ≤ MAX_AS_U32) :
    tryFromU32 h = some h := by
  unfold tryFromU32; simp [hH]

/-- **B4.** `add h 0 = some h` for valid `h`: zero is a right identity. -/
theorem add_zero_identity (h : Nat) (hH : h ≤ MAX_AS_U32) :
    add h 0 = some h := by
  unfold add
  have h_nat : (0 : Int) ≤ (h : Int) := Int.natCast_nonneg h
  have h_max : (h : Int) ≤ (MAX_AS_U32 : Int) := by exact_mod_cast hH
  simp [h_nat, h_max]

/-- **B5.** `sub h 0 = some h` for valid `h`: zero is a right identity for sub. -/
theorem sub_zero_identity (h : Nat) (hH : h ≤ MAX_AS_U32) :
    sub h 0 = some h := by
  unfold sub
  have h_nat : (0 : Int) ≤ (h : Int) := Int.natCast_nonneg h
  have h_max : (h : Int) ≤ (MAX_AS_U32 : Int) := by exact_mod_cast hH
  simp [h_nat, h_max]

end Zebra.Height
