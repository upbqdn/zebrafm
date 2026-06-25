import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Peer connection bounds from `zebra-network/src/{config,constants}.rs`

Zebra's peer set is sized by a single config knob,
`peerset_initial_target_size` (default `25`), and two compile-time
multipliers:

```rust
// zebra-network/src/constants.rs:64
pub const INBOUND_PEER_LIMIT_MULTIPLIER:  usize = 5;
// zebra-network/src/constants.rs:69
pub const OUTBOUND_PEER_LIMIT_MULTIPLIER: usize = 3;
// zebra-network/src/constants.rs:86
pub const DEFAULT_PEERSET_INITIAL_TARGET_SIZE: usize = 25;
// zebra-network/src/constants.rs:81
pub const DEFAULT_MAX_CONNS_PER_IP: usize = 1;
```

The three derived peer-set limits live on `Config`:

```rust
// zebra-network/src/config.rs:222
pub fn peerset_outbound_connection_limit(&self) -> usize {
    self.peerset_initial_target_size * OUTBOUND_PEER_LIMIT_MULTIPLIER
}
// zebra-network/src/config.rs:233
pub fn peerset_inbound_connection_limit(&self) -> usize {
    self.peerset_initial_target_size * INBOUND_PEER_LIMIT_MULTIPLIER
}
// zebra-network/src/config.rs:239
pub fn peerset_total_connection_limit(&self) -> usize {
    self.peerset_outbound_connection_limit()
        + self.peerset_inbound_connection_limit()
}
```

The "want more outbound" criterion used by the peer-crawler at startup is

```rust
// zebra-network/src/peer_set/initialize.rs:278-280
let demand_count = config
    .peerset_initial_target_size
    .saturating_sub(active_outbound_connections.update_count());
```

i.e. there is unmet outbound demand iff `current_outbound <
peerset_initial_target_size`.

This module models the bounds purely as `Nat`s and proves:

  * `target  ≤ outbound_max`               (T1)
  * `target  ≤ inbound_max`                (T2, since `5 ≥ 1`)
  * `outbound_max  ≤ inbound_max`         (T3, the security tradeoff
                                              documented at constants.rs:55)
  * `outbound_max + inbound_max = total`   (T4)
  * `total = 8 * target`                   (T5)
  * default-config concrete values:
      `outbound = 75, inbound = 125, total = 200`  (T6/T7/T8)
  * `want_more_outbound peer_count ↔ peer_count < target`  (T9)
  * `demand_count` saturates to zero at/above target       (T10)
  * `max_connections_per_ip ≥ 1`           (T11)
  * monotonicity in `peerset_initial_target_size`           (T12-T14)
-/

namespace Zebra.PeerConnectionLimits

/-! ## Constants -/

/-- `INBOUND_PEER_LIMIT_MULTIPLIER` — the multiplier applied to
`peerset_initial_target_size` to get the inbound connection limit.
Source: `zebra-network/src/constants.rs:64`
(`pub const INBOUND_PEER_LIMIT_MULTIPLIER: usize = 5`). -/
def INBOUND_PEER_LIMIT_MULTIPLIER : Nat := 5

/-- `OUTBOUND_PEER_LIMIT_MULTIPLIER` — the multiplier applied to
`peerset_initial_target_size` to get the outbound connection limit.
Source: `zebra-network/src/constants.rs:69`
(`pub const OUTBOUND_PEER_LIMIT_MULTIPLIER: usize = 3`). -/
def OUTBOUND_PEER_LIMIT_MULTIPLIER : Nat := 3

/-- `DEFAULT_PEERSET_INITIAL_TARGET_SIZE` — the default initial target peer
set size. Used when the config provides no value.
Source: `zebra-network/src/constants.rs:86`
(`pub const DEFAULT_PEERSET_INITIAL_TARGET_SIZE: usize = 25`). -/
def DEFAULT_PEERSET_INITIAL_TARGET_SIZE : Nat := 25

/-- `DEFAULT_MAX_CONNS_PER_IP` — the default maximum number of peer
connections to a single IP. The minimum sensible value is also `1`.
Source: `zebra-network/src/constants.rs:81`
(`pub const DEFAULT_MAX_CONNS_PER_IP: usize = 1`). -/
def DEFAULT_MAX_CONNS_PER_IP : Nat := 1

/-! ## Derived limits -/

/-- `peerset_outbound_connection_limit(config) = target * 3`.
Source: `zebra-network/src/config.rs:222`. -/
def outboundMax (target : Nat) : Nat :=
  target * OUTBOUND_PEER_LIMIT_MULTIPLIER

/-- `peerset_inbound_connection_limit(config) = target * 5`.
Source: `zebra-network/src/config.rs:233`. -/
def inboundMax (target : Nat) : Nat :=
  target * INBOUND_PEER_LIMIT_MULTIPLIER

/-- `peerset_total_connection_limit(config) = outbound_max + inbound_max`.
Source: `zebra-network/src/config.rs:239`. -/
def totalMax (target : Nat) : Nat :=
  outboundMax target + inboundMax target

/-- The "want more outbound" predicate used by the peer crawler at startup.
Returns `true` iff the node should try to open another outbound connection
(because the active outbound count is still below the target).
Source: `zebra-network/src/peer_set/initialize.rs:278-280` (the
`saturating_sub(active_outbound_connections.update_count())` clause). -/
def wantMoreOutbound (target peerCount : Nat) : Bool :=
  decide (peerCount < target)

/-- `demand_count = target.saturating_sub(current_outbound)`. This is the
number of additional outbound connections the crawler tries to open.
Modelled with `Nat`'s built-in truncating subtraction, which is the
semantics of `usize::saturating_sub`.
Source: `zebra-network/src/peer_set/initialize.rs:278-280`. -/
def demandCount (target peerCount : Nat) : Nat :=
  target - peerCount

/-! ## Theorems -/

/-- **T1 (target ≤ outbound_max).** The configured target peer-set size is
always at most the outbound connection limit, because `OUTBOUND_PEER_LIMIT_MULTIPLIER = 3 ≥ 1`.
Said another way: at startup Zebra is allowed to open enough outbound
connections to reach its initial target. -/
theorem target_le_outbound_max (target : Nat) :
    target ≤ outboundMax target := by
  unfold outboundMax OUTBOUND_PEER_LIMIT_MULTIPLIER
  -- target ≤ target * 3
  have h : target * 1 ≤ target * 3 :=
    Nat.mul_le_mul_left target (by decide : 1 ≤ 3)
  simpa using h

/-- **T2 (target ≤ inbound_max).** The configured target peer-set size is
also at most the inbound connection limit (`INBOUND_PEER_LIMIT_MULTIPLIER = 5 ≥ 1`). -/
theorem target_le_inbound_max (target : Nat) :
    target ≤ inboundMax target := by
  unfold inboundMax INBOUND_PEER_LIMIT_MULTIPLIER
  have h : target * 1 ≤ target * 5 :=
    Nat.mul_le_mul_left target (by decide : 1 ≤ 5)
  simpa using h

/-- **T3 (outbound_max ≤ inbound_max).** The inbound limit is always at
least as large as the outbound limit, because `INBOUND > OUTBOUND`
(`5 > 3`). This is the security tradeoff documented at
`zebra-network/src/constants.rs:55` — Zebra deliberately accepts more
inbound peers than it dials, to absorb connection exhaustion. -/
theorem outbound_max_le_inbound_max (target : Nat) :
    outboundMax target ≤ inboundMax target := by
  unfold outboundMax inboundMax OUTBOUND_PEER_LIMIT_MULTIPLIER
                                 INBOUND_PEER_LIMIT_MULTIPLIER
  exact Nat.mul_le_mul_left target (by decide : 3 ≤ 5)

/-- **T4 (total = outbound + inbound).** The total connection limit is by
definition the sum of the outbound and inbound limits.
Source: `zebra-network/src/config.rs:239-241`. -/
theorem total_eq_outbound_plus_inbound (target : Nat) :
    totalMax target = outboundMax target + inboundMax target := rfl

/-- **T5 (total = 8 * target).** Combining T4 with the multiplier
definitions: total = target*3 + target*5 = 8*target. -/
theorem total_eq_eight_target (target : Nat) :
    totalMax target = 8 * target := by
  unfold totalMax outboundMax inboundMax
         OUTBOUND_PEER_LIMIT_MULTIPLIER INBOUND_PEER_LIMIT_MULTIPLIER
  ring

/-- **T6 (default-config outbound limit).** With the default
`peerset_initial_target_size = 25`, the outbound limit is `25 * 3 = 75`. -/
theorem default_outbound_max :
    outboundMax DEFAULT_PEERSET_INITIAL_TARGET_SIZE = 75 := by
  unfold outboundMax DEFAULT_PEERSET_INITIAL_TARGET_SIZE
         OUTBOUND_PEER_LIMIT_MULTIPLIER
  decide

/-- **T7 (default-config inbound limit).** With the default
`peerset_initial_target_size = 25`, the inbound limit is `25 * 5 = 125`. -/
theorem default_inbound_max :
    inboundMax DEFAULT_PEERSET_INITIAL_TARGET_SIZE = 125 := by
  unfold inboundMax DEFAULT_PEERSET_INITIAL_TARGET_SIZE
         INBOUND_PEER_LIMIT_MULTIPLIER
  decide

/-- **T8 (default-config total).** With the default
`peerset_initial_target_size = 25`, the total connection limit is
`75 + 125 = 200`. -/
theorem default_total_max :
    totalMax DEFAULT_PEERSET_INITIAL_TARGET_SIZE = 200 := by
  unfold totalMax outboundMax inboundMax DEFAULT_PEERSET_INITIAL_TARGET_SIZE
         OUTBOUND_PEER_LIMIT_MULTIPLIER INBOUND_PEER_LIMIT_MULTIPLIER
  decide

/-- **T9 (want_more_outbound iff below target).** `wantMoreOutbound` is
`true` exactly when the current outbound peer count is strictly below the
configured target. This is the high-level statement of the crawler's
"open more connections" rule.
Source: `zebra-network/src/peer_set/initialize.rs:278-280`. -/
theorem want_more_outbound_iff (target peerCount : Nat) :
    wantMoreOutbound target peerCount = true ↔ peerCount < target := by
  unfold wantMoreOutbound
  exact decide_eq_true_iff

/-- **T10 (demand zero iff at-or-above target).** The crawler's
`demand_count` is `0` exactly when the current outbound peer count has
reached (or exceeded) the configured target — at which point no further
outbound dials are issued. Verifies the `saturating_sub` semantics.
Source: `zebra-network/src/peer_set/initialize.rs:278-280`. -/
theorem demand_zero_iff_at_target (target peerCount : Nat) :
    demandCount target peerCount = 0 ↔ target ≤ peerCount := by
  unfold demandCount
  exact Nat.sub_eq_zero_iff_le

/-- **T11 (demand = target - count below target).** Below the target,
`demand_count` is exactly the gap between the target and the active
outbound count. Combined with T10, this pins the truncating-sub semantics
fully (zero above, gap below). -/
theorem demand_below_target (target peerCount : Nat)
    (h : peerCount ≤ target) :
    demandCount target peerCount + peerCount = target := by
  unfold demandCount
  exact Nat.sub_add_cancel h

/-- **T12 (max_connections_per_ip default ≥ 1).** The default per-IP
connection cap is `1` — the documented and minimum sensible value.
Source: `zebra-network/src/constants.rs:71-81` and config docs at
`zebra-network/src/config.rs:177-181` ("The default and minimum value are 1"). -/
theorem default_max_conns_per_ip_pos :
    1 ≤ DEFAULT_MAX_CONNS_PER_IP := by
  unfold DEFAULT_MAX_CONNS_PER_IP; decide

/-- **T13 (outbound_max monotone in target).** Increasing the configured
target peer-set size never decreases the outbound limit. -/
theorem outbound_max_monotone {t₁ t₂ : Nat} (h : t₁ ≤ t₂) :
    outboundMax t₁ ≤ outboundMax t₂ := by
  unfold outboundMax
  exact Nat.mul_le_mul_right OUTBOUND_PEER_LIMIT_MULTIPLIER h

/-- **T14 (inbound_max monotone in target).** Increasing the configured
target peer-set size never decreases the inbound limit. -/
theorem inbound_max_monotone {t₁ t₂ : Nat} (h : t₁ ≤ t₂) :
    inboundMax t₁ ≤ inboundMax t₂ := by
  unfold inboundMax
  exact Nat.mul_le_mul_right INBOUND_PEER_LIMIT_MULTIPLIER h

/-- **T15 (total_max monotone in target).** Total connection limit is also
monotone — combining T13 and T14. -/
theorem total_max_monotone {t₁ t₂ : Nat} (h : t₁ ≤ t₂) :
    totalMax t₁ ≤ totalMax t₂ := by
  unfold totalMax
  exact Nat.add_le_add (outbound_max_monotone h) (inbound_max_monotone h)

/-- **T16 (default outbound < default inbound < default total).** The
strict ordering at default-config values: `75 < 125 < 200`. Records the
canonical "inbound is bigger than outbound, total is bigger still"
ordering. -/
theorem default_strict_ordering :
    outboundMax DEFAULT_PEERSET_INITIAL_TARGET_SIZE
      < inboundMax DEFAULT_PEERSET_INITIAL_TARGET_SIZE ∧
    inboundMax DEFAULT_PEERSET_INITIAL_TARGET_SIZE
      < totalMax DEFAULT_PEERSET_INITIAL_TARGET_SIZE := by
  refine ⟨?_, ?_⟩
  · rw [default_outbound_max, default_inbound_max]; decide
  · rw [default_inbound_max, default_total_max]; decide

/-- **T17 (`!want_more_outbound` at exact target).** When the active
outbound peer count equals the configured target, no further outbound
dials are wanted. -/
theorem no_more_outbound_at_target (target : Nat) :
    wantMoreOutbound target target = false := by
  unfold wantMoreOutbound
  simp

/-- **T18 (`want_more_outbound` at zero peers).** When the active outbound
peer count is zero and the target is positive, the crawler always wants
more outbound. -/
theorem want_more_outbound_zero (target : Nat) (h : 0 < target) :
    wantMoreOutbound target 0 = true := by
  unfold wantMoreOutbound
  simp [h]

/-- **T19 (peer_count ≤ outbound_max for any peer_count satisfying
`want_more_outbound`).** If the crawler wants more outbound peers, the
current count is below `target`, and therefore strictly below the outbound
cap (`outbound_max = target * 3 ≥ target`). Composes T1 and T9 to give the
peer-set invariant: every outbound dial happens while
`peer_count < outbound_max`, so the outbound-cap check at
`zebra-network/src/peer_set/initialize.rs:896`
(`if active_outbound_connections.update_count() >=
peerset_outbound_connection_limit()`) is *not* tripped by the demand
loop alone. -/
theorem want_more_implies_lt_outbound_max
    (target peerCount : Nat)
    (hwant : wantMoreOutbound target peerCount = true) :
    peerCount < outboundMax target := by
  have hlt : peerCount < target := (want_more_outbound_iff _ _).mp hwant
  exact Nat.lt_of_lt_of_le hlt (target_le_outbound_max target)

/-- **T20 (peer_count + demand_count = target below target, and equals
peer_count above).** Sums up the saturating-sub semantics: invoking the
demand loop `demand_count` times moves the running outbound count
exactly to `max(target, peer_count)`. -/
theorem demand_plus_count_reaches_target_or_holds
    (target peerCount : Nat) :
    demandCount target peerCount + peerCount = max target peerCount := by
  unfold demandCount
  by_cases h : peerCount ≤ target
  · rw [Nat.sub_add_cancel h]
    exact (Nat.max_eq_left h).symm
  · have hle : target ≤ peerCount := Nat.le_of_not_le h
    rw [Nat.sub_eq_zero_of_le hle, Nat.zero_add]
    exact (Nat.max_eq_right hle).symm

end Zebra.PeerConnectionLimits
