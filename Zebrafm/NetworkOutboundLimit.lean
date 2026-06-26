import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Outbound peer target vs. outbound peer cap

This module models the *outbound-side* peer-set sizing logic in
`zebra-network` as a layered system:

1. **Target** — `config.peerset_initial_target_size` (default `25`).
   The size Zebra dials up to during the startup demand burst, and the
   value the crawler tries to maintain. Source:
   `zebra-network/src/config.rs:157-165` and
   `zebra-network/src/constants.rs:86`
   (`DEFAULT_PEERSET_INITIAL_TARGET_SIZE = 25`).

2. **Cap** — `peerset_outbound_connection_limit() =
   peerset_initial_target_size * OUTBOUND_PEER_LIMIT_MULTIPLIER`
   (multiplier `= 3`, so default cap `= 75`). Source:
   `zebra-network/src/config.rs:222` and
   `zebra-network/src/constants.rs:69`.

3. **Demand counter** — `target.saturating_sub(active_outbound_count)`.
   Source: `zebra-network/src/peer_set/initialize.rs:278-280`.

4. **Concurrent overflow gate** — drops `MorePeers` if
   `active_outbound_count >= cap`. Source:
   `zebra-network/src/peer_set/initialize.rs:895-902`.

5. **Timer-driven always-dial** — at every `crawl_new_peer_interval`,
   the crawler sets `should_always_dial = (active_outbound_count == 0)`.
   This injects a synthetic `MorePeers` signal even with no demand, so
   that a node which has lost all outbound peers always tries to
   re-establish at least one. Source:
   `zebra-network/src/peer_set/initialize.rs:976`.

6. **Initial-peer fanout** — `update_initial(fanout_limit)` clamps the
   fanout to `min(fanout_limit, GET_ADDR_FANOUT)`, with
   `GET_ADDR_FANOUT = 1`. Source:
   `zebra-network/src/peer_set/candidate_set.rs:285-291` and
   `zebra-network/src/constants.rs:287`.

7. **`limit_initial_peers`** — the initial-peer set is shuffled down to
   at most `peerset_initial_target_size` entries. Source:
   `zebra-network/src/peer_set/initialize.rs:472-538` (esp. line 532:
   `if initial_peers.len() >= config.peerset_initial_target_size { break; }`).

We model each layer as `Nat` arithmetic and prove the **target-≤-cap
hierarchy**, the **saturation predicate**, the **headroom invariant**
(`headroom = cap - active`, additive under accepted dials and dropped on
disconnect), and the **`should_always_dial` semantics**. We deliberately
do not re-prove the multiplier facts already in
`Zebrafm.PeerConnectionLimits` — this module focuses on the
*outbound-side runway* between target and cap, and on the
fanout/initial-peer caps that are *not* covered by that earlier file.

## Why these theorems are useful

The interesting algebraic content here is the *runway* `cap - target =
target * 2`: there is always exactly `2 *
peerset_initial_target_size` worth of room above the demand-counter
target before the concurrent gate fires. This means the demand loop can
never exhaust the cap on its own (proved in T6), so the only way to hit
`DemandDrop` is incoming gossip-driven traffic. The headroom-monotonicity
lemmas pin the additive semantics of the cap so that any future change
to the cap definition is forced through these invariants.
-/

namespace Zebra.NetworkOutboundLimit

/-! ## Constants -/

/-- `OUTBOUND_PEER_LIMIT_MULTIPLIER` — multiplier applied to
`peerset_initial_target_size` to derive the outbound cap.
Source: `zebra-network/src/constants.rs:69`. -/
def OUTBOUND_PEER_LIMIT_MULTIPLIER : Nat := 3

/-- `DEFAULT_PEERSET_INITIAL_TARGET_SIZE` — default outbound target.
Source: `zebra-network/src/constants.rs:86`. -/
def DEFAULT_TARGET : Nat := 25

/-- `GET_ADDR_FANOUT` — number of `GetAddr` requests the candidate-set
crawler is willing to fire in a single fanout, regardless of the
caller's `fanout_limit` argument. Source:
`zebra-network/src/constants.rs:287` (`GET_ADDR_FANOUT = 1`). -/
def GET_ADDR_FANOUT : Nat := 1

/-! ## Derived functions -/

/-- Outbound target = `peerset_initial_target_size`. We use this name
to disambiguate from `outboundCap` below.
Source: `zebra-network/src/config.rs:165`. -/
def outboundTarget (target : Nat) : Nat := target

/-- Outbound cap = `target * OUTBOUND_PEER_LIMIT_MULTIPLIER`.
Source: `zebra-network/src/config.rs:222`. -/
def outboundCap (target : Nat) : Nat :=
  target * OUTBOUND_PEER_LIMIT_MULTIPLIER

/-- Outbound runway = cap - target. The number of outbound connections
the crawler is *allowed* to open above and beyond the demand-counter
target, in response to gossip or load. -/
def outboundRunway (target : Nat) : Nat :=
  outboundCap target - outboundTarget target

/-- Outbound headroom at the current active-count: `cap - active`.
`Nat` truncating subtraction, so headroom is `0` whenever `active ≥ cap`. -/
def headroom (target active : Nat) : Nat :=
  outboundCap target - active

/-- Saturation predicate: the outbound side is "saturated" iff the
active outbound count has reached the cap. This is the exact
condition the concurrent overflow gate checks at
`zebra-network/src/peer_set/initialize.rs:896`. -/
def saturated (target active : Nat) : Bool :=
  decide (outboundCap target ≤ active)

/-- "Want more outbound" predicate, expressed in terms of the *target*:
true iff the active count is strictly below target.
Source: `zebra-network/src/peer_set/initialize.rs:278-280`. -/
def wantMore (target active : Nat) : Bool :=
  decide (active < outboundTarget target)

/-- Timer-driven "always dial" predicate. Set every
`crawl_new_peer_interval` from
`zebra-network/src/peer_set/initialize.rs:976`:
`let should_always_dial = active_outbound_connections.update_count() == 0;`
This forces a re-dial even when no demand signal is pending, so a node
that has lost every outbound peer is guaranteed to retry. -/
def shouldAlwaysDial (active : Nat) : Bool :=
  decide (active = 0)

/-- Fanout limit for `update_initial`:
`fanout_limit.map(|x| min(x, GET_ADDR_FANOUT)).unwrap_or(GET_ADDR_FANOUT)`.
Source: `zebra-network/src/peer_set/candidate_set.rs:285-291`. -/
def initialFanout (fanoutLimit : Option Nat) : Nat :=
  match fanoutLimit with
  | none      => GET_ADDR_FANOUT
  | some n    => min n GET_ADDR_FANOUT

/-- `limit_initial_peers` truncation. The initial-peer set is
randomly sampled down to at most `target` entries (line 532 in
`zebra-network/src/peer_set/initialize.rs`). We model the truncation
arithmetically as `min(allPeers, target)`. -/
def limitInitialPeersCount (allPeers target : Nat) : Nat :=
  min allPeers target

/-! ## Hierarchy: target ≤ cap (T1) -/

/-- **T1 (outbound target ≤ outbound cap).** The configured outbound
target is always at most the outbound cap, because
`OUTBOUND_PEER_LIMIT_MULTIPLIER = 3 ≥ 1`. This is the basic safety
property: Zebra is allowed to dial all the way up to its target without
the concurrent overflow gate firing on its own demand pulses. -/
theorem target_le_cap (target : Nat) :
    outboundTarget target ≤ outboundCap target := by
  unfold outboundTarget outboundCap OUTBOUND_PEER_LIMIT_MULTIPLIER
  have h : target * 1 ≤ target * 3 :=
    Nat.mul_le_mul_left target (by decide : 1 ≤ 3)
  simpa using h

/-! ## Runway: cap − target = 2 · target (T2) -/

/-- **T2 (outbound runway = 2 · target).** The amount of extra outbound
connections allowed above the demand-counter target is exactly
`2 * peerset_initial_target_size`. This is the unique algebraic
consequence of `OUTBOUND_PEER_LIMIT_MULTIPLIER = 3`: the cap sits a
factor of three above the target, leaving room for `2 *
target` synthetic dials from gossip/timer-driven activity before the
overflow gate fires. -/
theorem runway_eq_two_target (target : Nat) :
    outboundRunway target = 2 * target := by
  unfold outboundRunway outboundCap outboundTarget
         OUTBOUND_PEER_LIMIT_MULTIPLIER
  -- target * 3 - target = 2 * target
  have : target * 3 - target = 2 * target := by
    have : target * 3 = target + 2 * target := by ring
    rw [this, Nat.add_sub_cancel_left]
  exact this

/-- **T3 (cap = target + runway).** Reconstructs the cap as `target +
2*target = 3*target`. This is the additive form of T2 and lets the
crawler safely reason about "active < target → there are still target +
runway slots before the cap". -/
theorem cap_eq_target_plus_runway (target : Nat) :
    outboundCap target = outboundTarget target + outboundRunway target := by
  rw [runway_eq_two_target]
  unfold outboundCap outboundTarget OUTBOUND_PEER_LIMIT_MULTIPLIER
  ring

/-! ## Saturation predicate (T4–T6) -/

/-- **T4 (`saturated` ↔ `active ≥ cap`).** The saturation predicate
mirrors the concurrent overflow gate exactly:
`if active_outbound_connections.update_count() >= peerset_outbound_connection_limit()`.
Source: `zebra-network/src/peer_set/initialize.rs:896`. -/
theorem saturated_iff (target active : Nat) :
    saturated target active = true ↔ outboundCap target ≤ active := by
  unfold saturated
  exact decide_eq_true_iff

/-- **T5 (not saturated ⇒ headroom positive).** When the outbound side
is not saturated, there is at least one slot of headroom for a fresh
dial. The headroom predicate is therefore a tight characterisation of
the gate's "go" branch. -/
theorem not_saturated_iff_headroom_pos (target active : Nat) :
    saturated target active = false ↔ 0 < headroom target active := by
  unfold saturated headroom
  constructor
  · intro h
    have hcap : ¬ outboundCap target ≤ active := by
      simpa using h
    have hlt : active < outboundCap target := Nat.lt_of_not_le hcap
    exact Nat.sub_pos_of_lt hlt
  · intro h
    have hlt : active < outboundCap target := Nat.lt_of_sub_pos h
    have hcap : ¬ outboundCap target ≤ active := Nat.not_le_of_lt hlt
    simp [hcap]

/-- **T6 (`wantMore` ⇒ ¬`saturated`, and strict headroom ≥ 2·target).**
The demand-counter signal `wantMore` (active < target) is strictly
stronger than "not saturated": it guarantees not only that the gate
won't fire, but that the runway between active and cap is at least
`2 * target` slots. This is the soundness property tying the demand
counter to the concurrent gate: the demand loop alone can never
trigger the overflow drop, because the runway covered by the demand
counter (target slots) sits strictly inside the cap (cap = 3 · target).

Formally: if `active < target` then `cap - active > 2 * target` is *not*
quite right — the strict inequality only holds when `active < target`.
At `active = target - 1` we have `headroom = 2 * target + 1`. We prove
the looser bound `2 * target ≤ headroom`, which is what the audit
needs: the runway slack is always at least the runway constant
`outboundRunway target`. -/
theorem want_more_runway_bound
    (target active : Nat)
    (hwant : wantMore target active = true) :
    outboundRunway target ≤ headroom target active := by
  -- Unfold the want-more decide.
  have hlt : active < outboundTarget target := by
    have := (decide_eq_true_iff (p := active < outboundTarget target)).mp hwant
    exact this
  -- active < target, so target - active ≥ 1, so cap - active ≥ cap - target = runway
  have hle : active ≤ outboundTarget target := Nat.le_of_lt hlt
  -- headroom = cap - active ≥ cap - target = runway (since active ≤ target)
  unfold headroom outboundRunway
  exact Nat.sub_le_sub_left hle (outboundCap target)

/-! ## Headroom arithmetic (T7–T9) -/

/-- **T7 (headroom at zero active = cap).** Before any outbound
connection is open, the headroom equals the entire cap. -/
theorem headroom_zero (target : Nat) :
    headroom target 0 = outboundCap target := by
  unfold headroom
  exact Nat.sub_zero _

/-- **T8 (headroom is monotone-decreasing in active).** As outbound
connections come up, the headroom never increases. -/
theorem headroom_antimonotone (target : Nat)
    {a₁ a₂ : Nat} (h : a₁ ≤ a₂) :
    headroom target a₂ ≤ headroom target a₁ := by
  unfold headroom
  exact Nat.sub_le_sub_left h (outboundCap target)

/-- **T9 (headroom drops by 1 on successful dial).** A successful new
outbound dial increments `active` by 1, decreasing headroom by exactly
1 — as long as we haven't already saturated. -/
theorem headroom_succ_dial (target active : Nat)
    (h : saturated target active = false) :
    headroom target (active + 1) + 1 = headroom target active := by
  -- Not saturated means active < cap; so cap - active ≥ 1, and we can split off the 1.
  have hpos : 0 < headroom target active :=
    (not_saturated_iff_headroom_pos target active).mp h
  unfold headroom at hpos ⊢
  have hlt : active < outboundCap target := Nat.lt_of_sub_pos hpos
  have hle : active + 1 ≤ outboundCap target := hlt
  -- cap - (active + 1) + 1 = cap - active
  omega

/-! ## `should_always_dial` semantics (T10–T11) -/

/-- **T10 (`shouldAlwaysDial` iff active = 0).** The timer-driven
synthetic-dial signal fires exactly when the active outbound-connection
count has dropped to zero. This pins the line
`let should_always_dial = active_outbound_connections.update_count() == 0;`
(`zebra-network/src/peer_set/initialize.rs:976`). -/
theorem should_always_dial_iff (active : Nat) :
    shouldAlwaysDial active = true ↔ active = 0 := by
  unfold shouldAlwaysDial
  exact decide_eq_true_iff

/-- **T11 (`shouldAlwaysDial` ⇒ `wantMore` when target > 0).** A node
that has lost all outbound peers always also satisfies the demand-loop
condition (active < target), provided the target is positive. So the
timer-driven re-dial path is *redundant* relative to the demand loop
when the demand loop is firing — its real purpose is to cover races
where the demand counter has already been drained but the active count
has since dropped back to zero. -/
theorem should_always_dial_implies_want_more
    (target active : Nat) (htar : 0 < target)
    (h : shouldAlwaysDial active = true) :
    wantMore target active = true := by
  have h0 : active = 0 := (should_always_dial_iff _).mp h
  unfold wantMore outboundTarget
  rw [h0]
  exact decide_eq_true_iff.mpr htar

/-! ## Initial-peer fanout cap (T12–T13) -/

/-- **T12 (`initialFanout` ≤ `GET_ADDR_FANOUT`).** The initial-peer
fanout is bounded above by the static constant `GET_ADDR_FANOUT = 1`,
regardless of the caller-supplied `fanout_limit`. This is the
DoS-prevention pin documented at
`zebra-network/src/constants.rs:273-287`: the fanout has to be greater
than 2 *in principle* (the comment says so), but was lowered to 1 in
issue #3110 to make cached-address responses actually get used.

Source: `zebra-network/src/peer_set/candidate_set.rs:285-291`. -/
theorem initial_fanout_le_static_cap (limit : Option Nat) :
    initialFanout limit ≤ GET_ADDR_FANOUT := by
  unfold initialFanout
  cases limit with
  | none   => exact Nat.le_refl _
  | some n => exact Nat.min_le_right _ _

/-- **T13 (`initialFanout(none) = 1`).** The unbounded-caller branch
yields exactly the static cap. Combined with T12, this completely
characterises the fanout cap arithmetic. -/
theorem initial_fanout_none :
    initialFanout none = 1 := by
  unfold initialFanout GET_ADDR_FANOUT
  decide

/-- **T13a (`initialFanout(some 0) = 0`).** The static cap is
*not* a floor — a caller-supplied `fanout_limit = 0` still produces
zero fanout. This is the documented behaviour at line 290 of
`candidate_set.rs`: `min(fanout_limit, GET_ADDR_FANOUT)`. -/
theorem initial_fanout_some_zero :
    initialFanout (some 0) = 0 := by
  unfold initialFanout GET_ADDR_FANOUT
  decide

/-! ## `limit_initial_peers` truncation (T14–T15) -/

/-- **T14 (limit_initial_peers ≤ target).** The initial peer set after
truncation is at most `peerset_initial_target_size` entries.
Source: `zebra-network/src/peer_set/initialize.rs:532` (the
`break` condition `initial_peers.len() >= peerset_initial_target_size`). -/
theorem limit_initial_peers_le_target (allPeers target : Nat) :
    limitInitialPeersCount allPeers target ≤ target := by
  unfold limitInitialPeersCount
  exact Nat.min_le_right _ _

/-- **T15 (`limit_initial_peers` ≤ `allPeers`).** The truncation never
*adds* peers — it can only shrink the input set. -/
theorem limit_initial_peers_le_input (allPeers target : Nat) :
    limitInitialPeersCount allPeers target ≤ allPeers := by
  unfold limitInitialPeersCount
  exact Nat.min_le_left _ _

/-- **T16 (`limit_initial_peers` is unchanged for small inputs).** When
the input peer set is already at or below target size, no truncation
happens. -/
theorem limit_initial_peers_small (allPeers target : Nat)
    (h : allPeers ≤ target) :
    limitInitialPeersCount allPeers target = allPeers := by
  unfold limitInitialPeersCount
  exact Nat.min_eq_left h

/-! ## Default-config pins (T17–T19) -/

/-- **T17 (default outbound cap = 75).** At default config the outbound
cap pins to `25 * 3 = 75`. (We pin this independently of the existing
`Zebrafm.PeerConnectionLimits.default_outbound_max` because the
constants are reproduced under different names in this module.) -/
theorem default_cap : outboundCap DEFAULT_TARGET = 75 := by
  unfold outboundCap DEFAULT_TARGET OUTBOUND_PEER_LIMIT_MULTIPLIER
  decide

/-- **T18 (default runway = 50).** At default config the outbound
runway (extra room above the demand-counter target) is
`75 - 25 = 50`. This is the audit-relevant "slack" between the
demand loop's target and the concurrent gate's cap. -/
theorem default_runway : outboundRunway DEFAULT_TARGET = 50 := by
  rw [runway_eq_two_target]
  unfold DEFAULT_TARGET
  decide

/-- **T19 (default headroom at zero active = 75).** Before any outbound
peer is connected, the entire 75-slot cap is available. -/
theorem default_headroom_zero : headroom DEFAULT_TARGET 0 = 75 := by
  rw [headroom_zero, default_cap]

/-! ## Saturation vs. demand interplay (T20) -/

/-- **T20 (saturated ⇒ ¬`wantMore`).** Once the cap is reached, the
demand-loop wanted-more predicate is necessarily `false` — because
the cap is at least the target (T1). This is the absorbing-state
property: the demand loop never re-enables itself after saturating
the cap. (It can be re-enabled only by losing connections.) -/
theorem saturated_implies_not_want_more
    (target active : Nat)
    (hsat : saturated target active = true) :
    wantMore target active = false := by
  have hcap : outboundCap target ≤ active := (saturated_iff _ _).mp hsat
  -- target ≤ cap ≤ active, so ¬ (active < target)
  have htar : outboundTarget target ≤ active :=
    Nat.le_trans (target_le_cap target) hcap
  unfold wantMore
  have hnot : ¬ active < outboundTarget target := Nat.not_lt_of_le htar
  simp [hnot]

end Zebra.NetworkOutboundLimit
