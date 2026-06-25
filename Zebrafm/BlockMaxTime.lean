import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Block max-time tolerance from the Zcash consensus rules

Zcash inherits Bitcoin's "future block time" check: a block's `header.time`
must be no more than two hours beyond the validator's local clock. In Zebra
this is enforced by `Header::time_is_valid_at` in
`zebra-chain/src/block/header.rs:107-126`, which computes

```rust
let two_hours_in_the_future = now
    .checked_add_signed(Duration::hours(2))
    .expect("calculating 2 hours in the future does not overflow");
if self.time <= two_hours_in_the_future { Ok(()) } else { Err(...) }
```

i.e. the predicate `block_time ≤ now + 2h`.

## Modelling caveats (audit notes)

* **Lean-side label.** Rust does **not** define a named constant for the
  tolerance — `Duration::hours(2)` is used inline at
  `zebra-chain/src/block/header.rs:114`. The name `MAX_BLOCK_TIME_TOLERANCE`
  used here is a Lean-side label introduced for readability; nothing in
  `zebra-chain` exports it. (The label happens to match the Bitcoin
  `nMaxFutureBlockTime` constant from `consensus.h`, which is `2 * 60 * 60`.)
* **`Nat` second counts.** We model times as `Nat` second counts. The Rust
  type is `chrono::DateTime<Utc>`, and the wire timestamp is a `u32` Unix
  epoch second (see `zebra-chain/src/block/serialize.rs:73-77`). This model
  elides:
  - `u32` overflow at Unix time `2^32` (year 2106), and
  - `DateTime<Utc>`'s broader chrono range (and the `checked_add_signed`
    branch that handles arithmetic overflow inside chrono).
  These are out of scope for the arithmetic content captured here. We
  reason about the inequality only, which is the consensus rule.
* **No lower bound from this rule.** `time_is_valid_at` imposes only the
  upper bound. Other rules (median-time-past, the genesis lower bound, etc.)
  are not part of this module.
-/

namespace Zebra.BlockMaxTime

/-- Lean-side label for Zebra's two-hour future-block-time tolerance.
This is not a named constant in `zebra-chain`; Rust inlines
`chrono::Duration::hours(2)` at `block/header.rs:114`. We bind the value
here so the theorems below can talk about it symbolically. Numeric value:
`7200 s = 2 h`. -/
def MAX_BLOCK_TIME_TOLERANCE : Nat := 7200

/-- The predicate: `block_time` is acceptable iff it is no more than
`MAX_BLOCK_TIME_TOLERANCE` seconds beyond `now`. Mirrors the
`self.time <= two_hours_in_the_future` branch of `Header::time_is_valid_at`
in `zebra-chain/src/block/header.rs:116`. Block times in the *past* are
unconstrained by this rule. -/
def isAcceptable (blockTime now : Nat) : Bool :=
  decide (blockTime ≤ now + MAX_BLOCK_TIME_TOLERANCE)

/-- The largest acceptable `block_time` given the current `now`. Mirrors
the `two_hours_in_the_future` quantity computed in
`zebra-chain/src/block/header.rs:113-115`. -/
def maxAcceptable (now : Nat) : Nat := now + MAX_BLOCK_TIME_TOLERANCE

/-! ## Theorems -/

/-- **T1.** `MAX_BLOCK_TIME_TOLERANCE` is exactly two hours of seconds.
Pins the Lean-side label to the inline `Duration::hours(2)` used in
`zebra-chain/src/block/header.rs:114`. -/
theorem tolerance_value : MAX_BLOCK_TIME_TOLERANCE = 2 * 60 * 60 := by
  unfold MAX_BLOCK_TIME_TOLERANCE; decide

/-- **T2.** Acceptance is exactly the linear inequality
`block_time ≤ now + MAX_BLOCK_TIME_TOLERANCE`. Reflects the
`self.time <= two_hours_in_the_future` branch in `header.rs:116`. -/
theorem isAcceptable_iff (blockTime now : Nat) :
    isAcceptable blockTime now = true ↔
      blockTime ≤ now + MAX_BLOCK_TIME_TOLERANCE := by
  unfold isAcceptable
  exact decide_eq_true_iff

/-- **T3.** The current local time `now` is always acceptable as a block time
(no future skew). -/
theorem now_is_acceptable (now : Nat) : isAcceptable now now = true := by
  rw [isAcceptable_iff]; omega

/-- **T4.** Any block time in the past is acceptable. -/
theorem past_is_acceptable (blockTime now : Nat) (h : blockTime ≤ now) :
    isAcceptable blockTime now = true := by
  rw [isAcceptable_iff]; omega

/-- **T5.** The boundary value `now + MAX_BLOCK_TIME_TOLERANCE` is acceptable
(the inequality is non-strict). Matches the `<=` (not `<`) used in
`header.rs:116`. -/
theorem boundary_is_acceptable (now : Nat) :
    isAcceptable (now + MAX_BLOCK_TIME_TOLERANCE) now = true := by
  rw [isAcceptable_iff]

/-- **T6.** One second past the boundary is rejected. This is the
positive-side counterpart of T5 and is directly witnessed by the Rust
test vector `two_hours_and_one_second_in_the_future` in
`zebra-chain/src/block/tests/vectors.rs:418,425`. -/
theorem just_past_boundary_rejected (now : Nat) :
    isAcceptable (now + MAX_BLOCK_TIME_TOLERANCE + 1) now = false := by
  unfold isAcceptable
  simp

/-- **T7.** Monotonicity in `now`: if a block time is acceptable at `now₁`
and `now₁ ≤ now₂`, it is still acceptable at the later `now₂`. -/
theorem acceptable_mono_now (blockTime now₁ now₂ : Nat)
    (h12 : now₁ ≤ now₂) (h : isAcceptable blockTime now₁ = true) :
    isAcceptable blockTime now₂ = true := by
  rw [isAcceptable_iff] at h ⊢
  omega

/-- **T8.** Anti-monotonicity in `blockTime`: if a later block time is
acceptable, then any earlier block time is also acceptable. -/
theorem acceptable_antimono_blockTime (bt₁ bt₂ now : Nat)
    (h12 : bt₁ ≤ bt₂) (h : isAcceptable bt₂ now = true) :
    isAcceptable bt₁ now = true := by
  rw [isAcceptable_iff] at h ⊢
  omega

/-- **T9.** `maxAcceptable now` is itself acceptable. -/
theorem maxAcceptable_acceptable (now : Nat) :
    isAcceptable (maxAcceptable now) now = true := by
  unfold maxAcceptable
  exact boundary_is_acceptable now

/-- **T10.** `maxAcceptable` is the *least upper bound*: any acceptable
`blockTime` is `≤ maxAcceptable now`. -/
theorem maxAcceptable_is_upper_bound (blockTime now : Nat)
    (h : isAcceptable blockTime now = true) :
    blockTime ≤ maxAcceptable now := by
  rw [isAcceptable_iff] at h
  unfold maxAcceptable
  exact h

/-- **T11.** Tightness of the bound: a strictly larger `blockTime` than
`maxAcceptable now` is rejected. -/
theorem above_maxAcceptable_rejected (blockTime now : Nat)
    (h : blockTime > maxAcceptable now) :
    isAcceptable blockTime now = false := by
  unfold isAcceptable maxAcceptable at *
  simp only [decide_eq_false_iff_not, not_le]
  exact h

/-- **T12.** `maxAcceptable` is monotone in `now`. -/
theorem maxAcceptable_mono (now₁ now₂ : Nat) (h : now₁ ≤ now₂) :
    maxAcceptable now₁ ≤ maxAcceptable now₂ := by
  unfold maxAcceptable; omega

/-- **T13.** Decidable trichotomy against the boundary: every `blockTime`
is either at-or-before `maxAcceptable now` (and accepted) or strictly above
(and rejected). This pairs T10/T11 into a single classification statement
mirroring the if/else split in `header.rs:116-125`. -/
theorem accept_or_reject (blockTime now : Nat) :
    (blockTime ≤ maxAcceptable now ∧ isAcceptable blockTime now = true)
    ∨ (blockTime > maxAcceptable now ∧ isAcceptable blockTime now = false) := by
  by_cases h : blockTime ≤ maxAcceptable now
  · left
    refine ⟨h, ?_⟩
    rw [isAcceptable_iff]
    unfold maxAcceptable at h
    exact h
  · right
    have hgt : blockTime > maxAcceptable now := Nat.lt_of_not_le h
    exact ⟨hgt, above_maxAcceptable_rejected blockTime now hgt⟩

/-- **T14.** Concrete vector matching the Rust test
`time_check_now` (`zebra-chain/src/block/tests/vectors.rs:410-437`):
at `now = 0`, the boundary `7200` is accepted and `7201` is rejected. -/
theorem rust_test_vector_boundary :
    isAcceptable 7200 0 = true ∧ isAcceptable 7201 0 = false := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

end Zebra.BlockMaxTime
