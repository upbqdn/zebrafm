import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Inventory registry: time-domain rotation and expiry
(`zebra-network/src/peer_set/inventory_registry.rs`,
 `zebra-network/src/constants.rs`)

Zebra's `InventoryRegistry` keeps two slots — `current` and `prev` — and on
every `INVENTORY_ROTATION_INTERVAL` (53 s) tick the rotation
`prev := current; current := ∅` runs (`inventory_registry.rs:439-441`):

```rust
fn rotate(&mut self) {
    self.prev = std::mem::take(&mut self.current);
}
```

A peer's "missing" / "advertised" marker for a given hash therefore has a
*time-dependent* lifetime:

  * inserted at wall-clock `t₀` → lands in `current`;
  * after the next rotation tick (at wall-clock `(⌊t₀ / 53⌋ + 1) * 53`)
    → demoted to `prev`;
  * after the rotation tick after that (at wall-clock
    `(⌊t₀ / 53⌋ + 2) * 53`) → dropped entirely.

The Rust constant docstring at `constants.rs:152` calls this out explicitly:

> After 2 of these intervals, Zebra's local available and missing inventory
> entries expire.

This module reasons about the **time-domain** consequences of that rule.
The companion module `Zebra.InventoryCacheSize` handles the per-hash and
per-peer cache *size* caps and the structural form of `rotate`. Here we
only care about *when* an entry is present.

## Modelling decisions

* **Time is `Nat` seconds.** The Rust code uses `tokio::time::Instant` with
  a `Duration` ticker, but the `IntervalStream` aligns ticks at multiples
  of the start instant plus `n * INTERVAL`. Reducing everything to seconds
  and using integer-division "tick index" `t / INTERVAL` is faithful for
  an arithmetic model.

* **No drift / `MissedTickBehavior::Burst`.** The Rust `IntervalStream`
  uses `Burst` on missed ticks (`inventory_registry.rs:213`), meaning
  rotations catch up rather than skip. In the arithmetic model we treat
  rotations as happening at exact multiples of `INTERVAL`. The
  interval-derived tick index `t / INTERVAL` then **is** the rotation count
  by time `t`.

* **Slot ∈ {current, prev, absent}.** We model the slot occupied by an
  entry with the inductive type `Slot`. The function `slotAt t₀ t` returns
  the slot the entry registered at `t₀` occupies when observed at `t`.

## What is proved here

* `T1` — interval constant pins to 53 s and the expiry horizon to 106 s.
* `T2` — at registration time, the entry is in `current`.
* `T3` — the entry is in *some* slot (`current` or `prev`) at every time
  before two ticks have elapsed since registration, never absent.
* `T4` — if at least two rotation ticks have elapsed since registration,
  the entry is absent; this is the time-domain *expiry* the Rust docstring
  guarantees.
* `T4b` — wall-clock form of T4: at any time `≥ t₀ + 2 * INTERVAL`, the
  entry is gone.
* `T5` — concrete witness for `t₀ = 0`: in `current` at 0 and 52, in `prev`
  at 53 and 105, absent at 106 onward.
* `T6` — worst-case lifetime, aligned registration: at `t₀ = k * INTERVAL`,
  the entry is present until just before `t₀ + 2 * INTERVAL` and gone at
  exactly `t₀ + 2 * INTERVAL`.
* `T7` — guaranteed-present window: from registration through any time
  strictly less than `t₀ + INTERVAL + 1`, the entry is present regardless
  of where in the cycle registration landed.
* `T8` — registration is in registry: bool form of T2.
* `T9` — monotone disappearance: once absent (with `t ≥ t₀`), the entry
  stays absent at every later time. The registry never re-creates an
  entry.
* `T10` — rotation tick schedule at aligned `t₀`: explicit slot at the
  three tick boundaries `k`, `k+1`, `k+2`.
* `T11` — slot decision is total.
* `T12` — `inRegistry t₀ t = true ↔ slotAt t₀ t ≠ Slot.absent`.
-/

namespace Zebra.NetworkInventoryRotation

/-! ## Constants -/

/-- Rotation interval in seconds. Source: `zebra-network/src/constants.rs:153`
(`pub const INVENTORY_ROTATION_INTERVAL: Duration = Duration::from_secs(53)`). -/
def INTERVAL : Nat := 53

/-- Number of intervals a marker survives before being dropped.
Source: `zebra-network/src/constants.rs:152` ("After 2 of these intervals,
Zebra's local available and missing inventory entries expire."). -/
def EXPIRY_INTERVALS : Nat := 2

/-- Total wall-clock expiry horizon. After this many seconds (counted from
the most recent rotation boundary before registration), the entry is
gone. -/
def EXPIRY_SECONDS : Nat := EXPIRY_INTERVALS * INTERVAL

/-! ## Time domain

`tickIndex t` counts how many rotation ticks have *completed* by wall-clock
`t`. Since rotations fire at `t = INTERVAL, 2 * INTERVAL, ...`, at any
time `t` we have `tickIndex t = t / INTERVAL`. -/

/-- Number of completed rotation ticks by time `t`. -/
def tickIndex (t : Nat) : Nat := t / INTERVAL

/-! ## Slot state -/

inductive Slot
  | current : Slot
  | prev    : Slot
  | absent  : Slot
  deriving DecidableEq, Repr

/-- The slot occupied by an entry registered at time `t₀`, observed at
time `t`. We pin the convention that observation at `t < t₀` yields
`Slot.absent` (the entry has not been registered yet).

For `t ≥ t₀`:

  * `tickIndex t = tickIndex t₀`     → still in `current`;
  * `tickIndex t = tickIndex t₀ + 1` → demoted to `prev`;
  * `tickIndex t ≥ tickIndex t₀ + 2` → dropped (`absent`).

Written without a `let` so that `unfold` and `simp` see through it. -/
def slotAt (t₀ t : Nat) : Slot :=
  if t < t₀ then Slot.absent
  else
    if tickIndex t - tickIndex t₀ = 0 then Slot.current
    else if tickIndex t - tickIndex t₀ = 1 then Slot.prev
    else Slot.absent

/-- An entry is "in the registry" iff its slot is `current` or `prev`
(equivalently, not `absent`). -/
def inRegistry (t₀ t : Nat) : Bool :=
  match slotAt t₀ t with
  | Slot.absent => false
  | _ => true

/-! ## Theorems -/

/-- **T1 (constant pins).** Interval = 53 s, expiry horizon = 106 s. Any
drift in `INTERVAL` or `EXPIRY_INTERVALS` breaks this theorem at build
time. -/
theorem constants_value :
    INTERVAL = 53 ∧ EXPIRY_SECONDS = 106 := by
  refine ⟨?_, ?_⟩
  · unfold INTERVAL; decide
  · unfold EXPIRY_SECONDS EXPIRY_INTERVALS INTERVAL; decide

/-- **T2 (registration in `current`).** At the very moment of registration,
the entry sits in `current`. Models the line
`let hash_peers = self.current.entry(inv).or_default()` at
`inventory_registry.rs:382`. -/
theorem slotAt_registration (t₀ : Nat) :
    slotAt t₀ t₀ = Slot.current := by
  unfold slotAt
  have hnot : ¬ t₀ < t₀ := Nat.lt_irrefl t₀
  have hd : tickIndex t₀ - tickIndex t₀ = 0 := Nat.sub_self _
  rw [if_neg hnot, hd]
  simp

/-- **T3 (present iff before horizon, tick form).** The entry is in the
registry at time `t` iff at least one rotation tick remains before drop. -/
theorem inRegistry_iff (t₀ t : Nat) :
    inRegistry t₀ t = true ↔
      t₀ ≤ t ∧ tickIndex t - tickIndex t₀ ≤ 1 := by
  unfold inRegistry slotAt
  by_cases h_lt : t < t₀
  · -- t < t₀: trivially absent (registration not yet happened).
    simp only [h_lt, if_true, Bool.false_eq_true, false_iff, not_and]
    intro h_ge; omega
  · have h_ge : t₀ ≤ t := Nat.not_lt.mp h_lt
    simp only [h_lt, if_false]
    by_cases h0 : tickIndex t - tickIndex t₀ = 0
    · simp only [h0, if_true]
      refine ⟨fun _ => ⟨h_ge, by omega⟩, fun _ => ?_⟩
      trivial
    · by_cases h1 : tickIndex t - tickIndex t₀ = 1
      · rw [if_neg h0, if_pos h1]
        refine ⟨fun _ => ⟨h_ge, by omega⟩, fun _ => ?_⟩
        trivial
      · rw [if_neg h0, if_neg h1]
        refine ⟨?_, ?_⟩
        · intro hcontra; exact absurd hcontra (by decide)
        · intro ⟨_, h_le⟩; omega

/-- **T4 (expiry after two ticks).** Strictly after two rotation ticks have
elapsed since registration, the entry is absent. This is the formal
version of the Rust docstring "After 2 of these intervals, ... entries
expire." -/
theorem expired_after_two_ticks (t₀ t : Nat)
    (h_ge : t₀ ≤ t)
    (h_ticks : tickIndex t ≥ tickIndex t₀ + 2) :
    inRegistry t₀ t = false := by
  unfold inRegistry slotAt
  have h_not_lt : ¬ t < t₀ := Nat.not_lt.mpr h_ge
  have h0 : tickIndex t - tickIndex t₀ ≠ 0 := by omega
  have h1 : tickIndex t - tickIndex t₀ ≠ 1 := by omega
  simp [h_not_lt, h0, h1]

/-- **T4b (expiry, in wall-clock seconds).** Strictly more conservative —
and the form a Zebra operator would reach for: if the time since
registration is at least `2 * INTERVAL`, the entry is *guaranteed* gone. -/
theorem expired_after_horizon (t₀ t : Nat)
    (h : t ≥ t₀ + EXPIRY_SECONDS) :
    inRegistry t₀ t = false := by
  have h_ge : t₀ ≤ t := by
    have h0 : t₀ ≤ t₀ + EXPIRY_SECONDS := Nat.le_add_right _ _
    exact Nat.le_trans h0 h
  apply expired_after_two_ticks t₀ t h_ge
  -- Need: tickIndex t ≥ tickIndex t₀ + 2.
  unfold tickIndex EXPIRY_SECONDS EXPIRY_INTERVALS at *
  have h_pos : 0 < INTERVAL := by unfold INTERVAL; decide
  have h_split : (t₀ + 2 * INTERVAL) / INTERVAL = t₀ / INTERVAL + 2 := by
    rw [Nat.add_mul_div_right _ _ h_pos]
  have h_mono : (t₀ + 2 * INTERVAL) / INTERVAL ≤ t / INTERVAL :=
    Nat.div_le_div_right h
  omega

/-- **T5 (concrete witness).** Registered at time 0, with `INTERVAL = 53`:

  * present (in `current`) at time 0 and 52,
  * present (in `prev`) at time 53 and 105,
  * absent at time 106 (= `EXPIRY_SECONDS`) and at the membership level
    too.

This is the "height-of-time" witness the task description asks for:
concrete time stamps and concrete slot predictions. -/
theorem witness_at_time_zero :
    slotAt 0 0   = Slot.current ∧
    slotAt 0 52  = Slot.current ∧
    slotAt 0 53  = Slot.prev    ∧
    slotAt 0 105 = Slot.prev    ∧
    slotAt 0 106 = Slot.absent  ∧
    inRegistry 0 52  = true     ∧
    inRegistry 0 105 = true     ∧
    inRegistry 0 106 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **T6 (worst-case lifetime, aligned registration).** If the registration
time is a tick boundary (a multiple of `INTERVAL`), the entry survives
*exactly* until the end of the two-interval window. Formally: at
`t = t₀ + 2 * INTERVAL`, the entry is `absent`; at every earlier time
`t₀ ≤ t < t₀ + 2 * INTERVAL`, the entry is *present*. -/
theorem aligned_worst_case (k : Nat) :
    let t₀ := k * INTERVAL
    inRegistry t₀ (t₀ + 2 * INTERVAL) = false ∧
    ∀ t, t₀ ≤ t → t < t₀ + 2 * INTERVAL →
      inRegistry t₀ t = true := by
  intro t₀
  refine ⟨?_, ?_⟩
  · -- Absent at t = t₀ + 2 * INTERVAL.
    apply expired_after_horizon t₀ (t₀ + 2 * INTERVAL)
    unfold EXPIRY_SECONDS EXPIRY_INTERVALS
    exact Nat.le_refl _
  · -- Present at every earlier time.
    intro t h_ge h_lt
    rw [inRegistry_iff]
    refine ⟨h_ge, ?_⟩
    unfold tickIndex
    have h_pos : 0 < INTERVAL := by unfold INTERVAL; decide
    -- tickIndex t₀ = k.
    have h_t0 : t₀ / INTERVAL = k := by
      change (k * INTERVAL) / INTERVAL = k
      rw [Nat.mul_div_cancel _ h_pos]
    rw [h_t0]
    -- t < (k+2) * INTERVAL, hence t / INTERVAL ≤ k + 1.
    have h_lt' : t < (k + 2) * INTERVAL := by
      have heq : t₀ + 2 * INTERVAL = (k + 2) * INTERVAL := by
        change k * INTERVAL + 2 * INTERVAL = (k + 2) * INTERVAL
        ring
      rw [heq] at h_lt
      exact h_lt
    have h_div_lt : t / INTERVAL < k + 2 :=
      (Nat.div_lt_iff_lt_mul h_pos).mpr h_lt'
    omega

/-- **T7 (guaranteed present within one interval).** Regardless of where in
the cycle the registration lands, the entry is *guaranteed* present at
every time `t` with `t₀ ≤ t < t₀ + INTERVAL + 1`. (One interval plus the
"inclusive boundary" wraps to `t ≤ t₀ + INTERVAL`.) -/
theorem present_window_lower_bound (t₀ t : Nat)
    (h_ge : t₀ ≤ t) (h_lt : t < t₀ + INTERVAL + 1) :
    inRegistry t₀ t = true := by
  rw [inRegistry_iff]
  refine ⟨h_ge, ?_⟩
  unfold tickIndex
  have h_pos : 0 < INTERVAL := by unfold INTERVAL; decide
  -- t ≤ t₀ + INTERVAL.
  have h_le : t ≤ t₀ + INTERVAL := by omega
  have h_div_le : t / INTERVAL ≤ (t₀ + INTERVAL) / INTERVAL :=
    Nat.div_le_div_right h_le
  have h_split : (t₀ + INTERVAL) / INTERVAL = t₀ / INTERVAL + 1 := by
    have := Nat.add_mul_div_right t₀ 1 h_pos
    simpa using this
  omega

/-- **T8 (registration is in registry, bool form).** Companion to T2 in the
`inRegistry` API. -/
theorem present_at_registration (t₀ : Nat) :
    inRegistry t₀ t₀ = true := by
  rw [inRegistry_iff]
  refine ⟨Nat.le_refl _, ?_⟩
  have : tickIndex t₀ - tickIndex t₀ = 0 := Nat.sub_self _
  omega

/-- **T9 (monotone disappearance, post-registration).** Once the entry is
absent at some post-registration time `t ≥ t₀`, it remains absent at every
later time `t' ≥ t`. The registry never re-creates an entry; only an
explicit `register(change)` call can do that, and this theorem speaks
only about the time evolution of an *already registered* entry.

The `t ≥ t₀` precondition is necessary: pre-registration `t < t₀` also
produces `inRegistry = false`, but in that corner case a later observation
at `t' ≥ t₀` legitimately shows the entry as `current`. -/
theorem absent_monotone (t₀ t t' : Nat)
    (h_t0_le_t : t₀ ≤ t)
    (h_le : t ≤ t')
    (h_absent : inRegistry t₀ t = false) :
    inRegistry t₀ t' = false := by
  -- Absence at t with t ≥ t₀ ⇒ tickIndex t ≥ tickIndex t₀ + 2.
  have h_not_lt : ¬ t < t₀ := Nat.not_lt.mpr h_t0_le_t
  unfold inRegistry slotAt at h_absent
  simp only [h_not_lt, if_false] at h_absent
  -- Now case-split on the slot identification.
  by_cases h0 : tickIndex t - tickIndex t₀ = 0
  · simp only [h0, if_true] at h_absent; cases h_absent
  · by_cases h1 : tickIndex t - tickIndex t₀ = 1
    · rw [if_neg h0, if_pos h1] at h_absent; cases h_absent
    · -- The genuine case: tick-difference ≥ 2.
      have hd_ge2 : tickIndex t - tickIndex t₀ ≥ 2 := by omega
      have h_ticks : tickIndex t ≥ tickIndex t₀ + 2 := by omega
      have h_t0_le_t' : t₀ ≤ t' := Nat.le_trans h_t0_le_t h_le
      apply expired_after_two_ticks t₀ t' h_t0_le_t'
      -- tickIndex t' ≥ tickIndex t (monotone in time) ≥ tickIndex t₀ + 2.
      have h_tick_mono : tickIndex t ≤ tickIndex t' := by
        unfold tickIndex; exact Nat.div_le_div_right h_le
      omega

/-- **T10 (rotation tick schedule).** At an aligned-registration entry
(`t₀ = k * INTERVAL`), the slot at each subsequent rotation tick is
exactly as the schedule predicts:

  * `t = k * INTERVAL`           → `current`
  * `t = (k + 1) * INTERVAL`     → `prev`
  * `t = (k + 2) * INTERVAL`     → `absent`

The "height-of-time" terminology in the task corresponds here to the
rotation tick index. -/
theorem rotation_tick_schedule (k : Nat) :
    slotAt (k * INTERVAL) (k * INTERVAL) = Slot.current ∧
    slotAt (k * INTERVAL) ((k + 1) * INTERVAL) = Slot.prev ∧
    slotAt (k * INTERVAL) ((k + 2) * INTERVAL) = Slot.absent := by
  have h_pos : 0 < INTERVAL := by unfold INTERVAL; decide
  have h_t0 : (k * INTERVAL) / INTERVAL = k := Nat.mul_div_cancel _ h_pos
  have h_t1 : ((k + 1) * INTERVAL) / INTERVAL = k + 1 :=
    Nat.mul_div_cancel _ h_pos
  have h_t2 : ((k + 2) * INTERVAL) / INTERVAL = k + 2 :=
    Nat.mul_div_cancel _ h_pos
  refine ⟨?_, ?_, ?_⟩
  · exact slotAt_registration _
  · -- t = (k+1) * INTERVAL → prev.
    unfold slotAt tickIndex
    have h_ord : k * INTERVAL ≤ (k + 1) * INTERVAL :=
      Nat.mul_le_mul_right _ (Nat.le_succ _)
    have h_not_lt : ¬ (k + 1) * INTERVAL < k * INTERVAL := by omega
    rw [if_neg h_not_lt, h_t0, h_t1]
    have hd : k + 1 - k = 1 := by omega
    rw [hd]; simp
  · -- t = (k+2) * INTERVAL → absent.
    unfold slotAt tickIndex
    have h_ord : k * INTERVAL ≤ (k + 2) * INTERVAL :=
      Nat.mul_le_mul_right _ (by omega)
    have h_not_lt : ¬ (k + 2) * INTERVAL < k * INTERVAL := by omega
    rw [if_neg h_not_lt, h_t0, h_t2]
    have hd : k + 2 - k = 2 := by omega
    rw [hd]; decide

/-- **T11 (slot decision is total).** Every observation `(t₀, t)` lands in
exactly one of `current`, `prev`, or `absent`. -/
theorem slot_total (t₀ t : Nat) :
    slotAt t₀ t = Slot.current ∨
    slotAt t₀ t = Slot.prev   ∨
    slotAt t₀ t = Slot.absent := by
  unfold slotAt
  by_cases h_lt : t < t₀
  · right; right; simp [h_lt]
  · simp only [h_lt, if_false]
    by_cases h0 : tickIndex t - tickIndex t₀ = 0
    · left; simp [h0]
    · by_cases h1 : tickIndex t - tickIndex t₀ = 1
      · right; left; rw [if_neg h0, if_pos h1]
      · right; right; rw [if_neg h0, if_neg h1]

/-- **T12 (registry membership ↔ slot ≠ absent).** Connects the
bool-valued `inRegistry` with the slot-valued `slotAt`. -/
theorem inRegistry_eq_not_absent (t₀ t : Nat) :
    inRegistry t₀ t = true ↔ slotAt t₀ t ≠ Slot.absent := by
  unfold inRegistry
  rcases slot_total t₀ t with h | h | h <;> simp [h]

end Zebra.NetworkInventoryRotation
