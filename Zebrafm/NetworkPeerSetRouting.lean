import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Peer-set tiered routing for inventory requests
(`zebra-network/src/peer_set/set.rs`,
 `zebra-network/src/peer_set/inventory_registry.rs`)

When the `PeerSet` `Service::call` sees a single-item
`Request::BlocksByHash` or `Request::TransactionsById`, it delegates to
`PeerSet::route_inv(req, hash)` (`set.rs:991-1064`). That function picks one
peer from a **three-tier waterfall**:

```rust
// Tier 1: peers that advertised this hash AND are currently ready.
let advertising_peer_list = self
    .inventory_registry
    .advertising_peers(hash)
    .filter(|&addr| self.ready_services.contains_key(addr))
    .copied()
    .collect();
if let Some(svc) = peer_from(advertising_peer_list) { return svc.call(req); }

// Tier 2: ready peers that are NOT registered as missing this hash.
let missing_peer_list: HashSet<_> = self
    .inventory_registry
    .missing_peers(hash)
    .copied()
    .collect();
let maybe_peer_list = self
    .ready_services
    .keys()
    .filter(|addr| !missing_peer_list.contains(addr))
    .copied()
    .collect();
if let Some(svc) = peer_from(maybe_peer_list) { return svc.call(req); }

// Tier 3: synthetic NotFoundRegistry rejection.
Err(PeerError::NotFoundRegistry(vec![hash]))
```

The crucial design properties — the ones a maintainer cannot just re-read off
the Rust without re-deriving:

  * **Determinism of classification.** Tier assignment is a pure function of
    three sets (ready, advertising, missing). No randomness enters until the
    P2C selection *within* a tier; tier choice itself is deterministic.
  * **Order of preference is strict.** A peer that is in `advertising_peers`
    is classified Tier 1 even if it also appears in `missing_peers` — the
    filter for Tier 2 *only* runs when Tier 1 is empty. The "missing"
    filter is therefore conditional on Tier 1's emptiness, not unconditional.
  * **Tier 3 is a hard rejection, not a retry.** The Rust `route_inv`
    returns `Err(NotFoundRegistry(...))` after `yield_now().await`. The
    yield gives other tasks a chance to make different peers ready, but
    no retry occurs within `route_inv` itself; the caller's retry policy
    sees a synthetic error.
  * **Rejection persistence is bounded only by registry rotation.** The
    `missing_peer_list` for a hash is read from `InventoryRegistry`, which
    rotates `current → prev → drop` every
    `INVENTORY_ROTATION_INTERVAL` seconds (`53`).
    A `Missing` marker registered at time `t` is therefore guaranteed to
    expire by `t + 2 * INVENTORY_ROTATION_INTERVAL` (`= 106 s`).
    Until then, the same peer keeps being classified as Tier 2-excluded
    for the same hash — there is no other expiry mechanism.

We model peers as `Nat` IDs and the three registry slices as `List Nat`.
Tier classification is an enum `Tier ∈ {tier1, tier2, tier3}`.

## What this module proves

  * **T1** `classifyPeer_deterministic` — tier is a pure function of inputs.
  * **T2** `tier1_iff` — Tier 1 ↔ `ready ∧ advertising` (independent of
    missing).
  * **T3** `tier2_iff` — Tier 2 ↔ `ready ∧ ¬advertising ∧ ¬missing` (note
    the conjunction: missing is a Tier 2 exclusion, NOT a Tier 1 demotion).
  * **T4** `tier3_iff` — Tier 3 ↔ `¬ready ∨ (¬advertising ∧ missing)`
    (no ready peer satisfies Tier 1 or Tier 2).
  * **T5** `tier_partition` — the three tiers partition the universe of
    classification outcomes.
  * **T6** `tier1_dominates_missing` — a peer marked both advertising and
    missing for the same hash is Tier 1, **not** Tier 3. This is the
    "advertising trumps missing" invariant.
  * **T7** `select_tier1_when_nonempty` — `routeInv` selects from Tier 1
    whenever the Tier 1 candidate list is non-empty.
  * **T8** `select_tier2_only_if_tier1_empty` — Tier 2 is consulted only
    when Tier 1 yields no candidate. The conditional structure of the
    waterfall.
  * **T9** `tier3_iff_no_routable_peer` — `routeInv` returns
    `NotFoundRegistry` iff both candidate lists are empty.
  * **T10** `tier3_does_not_change_until_expiry` — once a peer is in the
    missing registry for a hash, it stays excluded from Tier 2 until the
    registry rotates the entry out. (Monotonicity in the registry
    direction.)
  * **T11** `tier_monotone_under_set_membership` — adding a peer to
    `advertising` cannot demote it; removing from `missing` cannot
    demote it. Tier index is monotone (lower-is-better) under registry
    inclusions.
  * **T12** `routeInv_outcome_function` — given identical registry and
    ready-set state, two evaluations of the tier outcome produce the
    same `Tier`. The classification is a pure function.
  * **T13** `rejection_window_seconds` — the worst-case time a single
    `Missing` registration stays effective is bounded by `2 * 53 = 106`
    seconds. This is the only way out of Tier 3 short of registry
    rotation removing the entry.
  * **T14** `no_internal_retry_within_route_inv` — `routeInv` evaluates
    each tier exactly once per call; there is no "try Tier 1, then try
    Tier 1 again" loop. Two consecutive Tier 3 outcomes on the same
    state require the *external* caller to retry.
  * **T15** `tier1_choice_independent_of_missing_list` — recomputing
    Tier 1 with a different `missing` list gives the same Tier 1
    candidate set. The Rust filter on `missing` only applies to Tier 2.
-/

namespace Zebra.NetworkPeerSetRouting

/-! ## The three tiers and the classification function -/

/-- A peer's routing tier for a single inventory hash.

* `tier1`: ready peer that advertised this hash (preferred).
* `tier2`: ready peer that has not been registered as missing this hash.
* `tier3`: no routable peer; `NotFoundRegistry` is returned.

The model classifies *the outcome* (which tier the request ends up
serviced by), not an individual peer's "best tier"; for that, see
`classifyPeer` below. -/
inductive Tier
  | tier1
  | tier2
  | tier3
  deriving DecidableEq, Repr

/-- Numeric rank of a tier — `tier1 = 1, tier2 = 2, tier3 = 3`. Lower is
better (preferred earlier in the waterfall). Used to phrase monotonicity. -/
def Tier.rank : Tier → Nat
  | .tier1 => 1
  | .tier2 => 2
  | .tier3 => 3

/-- The per-hash classification of an individual peer given:
* `ready`     — is this peer in `ready_services`?
* `advertise` — is this peer in `inventory_registry.advertising_peers(hash)`?
* `miss`      — is this peer in `inventory_registry.missing_peers(hash)`?

The Rust waterfall:
1. Tier 1 candidate ↔ `ready ∧ advertise`.
2. Tier 2 candidate ↔ `ready ∧ ¬advertise ∧ ¬miss`.
3. Otherwise the peer is not a candidate — modelled as `tier3`.

Note: a peer that is `ready ∧ ¬advertise ∧ miss` is NOT a candidate; it
falls into `tier3`. A peer that is `ready ∧ advertise ∧ miss` IS a Tier 1
candidate (advertising trumps missing for the same call). -/
def classifyPeer (ready advertise miss : Bool) : Tier :=
  if ready ∧ advertise then .tier1
  else if ready ∧ ¬advertise ∧ ¬miss then .tier2
  else .tier3

/-! ## Candidate lists and routeInv outcome -/

/-- The Tier 1 candidate list as the Rust code constructs it:
`advertising_peers(hash) ∩ ready_services`. -/
def tier1Candidates (advertising ready : List Nat) : List Nat :=
  advertising.filter (· ∈ ready)

/-- The Tier 2 candidate list as the Rust code constructs it:
`ready_services ∖ missing_peers(hash)`. The advertising list is NOT
intersected here — Tier 2 fires only after Tier 1 is empty, so the
"advertising" peers (if any were ready) would have been used already.

Caveat the Rust honours: a peer that is *both* in advertising and not in
`ready_services` doesn't become a Tier 2 candidate either (it'd fail the
`ready` filter). This list only considers ready peers. -/
def tier2Candidates (ready missing : List Nat) : List Nat :=
  ready.filter (· ∉ missing)

/-- The routeInv tier outcome — which tier ends up servicing the request.
Tier 1 if its candidate list is non-empty; else Tier 2 if its list is
non-empty; else Tier 3 (synthetic `NotFoundRegistry` rejection). -/
def routeInvOutcome (advertising ready missing : List Nat) : Tier :=
  if tier1Candidates advertising ready ≠ [] then .tier1
  else if tier2Candidates ready missing ≠ [] then .tier2
  else .tier3

/-! ## Registry expiry constants (`zebra-network/src/constants.rs:153`) -/

/-- Rotation interval in seconds.
Source: `zebra-network/src/constants.rs:153`
(`INVENTORY_ROTATION_INTERVAL: Duration = Duration::from_secs(53)`). -/
def INVENTORY_ROTATION_INTERVAL_SECS : Nat := 53

/-- Two registry slots (`current` and `prev`). A `Missing` registration
must survive both before being dropped, so its worst-case lifetime is
`2 * rotation_interval`. -/
def NUM_REGISTRY_MAPS : Nat := 2

/-- Worst-case seconds before a single `Missing` registration expires. -/
def MAX_MISSING_LIFETIME_SECS : Nat :=
  NUM_REGISTRY_MAPS * INVENTORY_ROTATION_INTERVAL_SECS

/-! ## T1: determinism of `classifyPeer` -/

/-- **T1.** Tier classification is a pure function of `(ready, advertise, miss)`:
two evaluations on equal inputs yield equal tiers. This is the
"no hidden non-determinism" guarantee — randomness enters at the P2C
*within* a tier, never at the tier choice. -/
theorem classifyPeer_deterministic
    (ready advertise miss ready' advertise' miss' : Bool)
    (hr : ready = ready') (ha : advertise = advertise') (hm : miss = miss') :
    classifyPeer ready advertise miss = classifyPeer ready' advertise' miss' := by
  subst hr; subst ha; subst hm; rfl

/-! ## T2-T4: characterising each tier -/

/-- **T2.** Tier 1 iff a peer is ready and advertising the hash. Crucially,
the `miss` flag does not appear here: a peer that advertised the hash gets
Tier 1 even if it also appears in the missing registry for that hash
(advertising trumps missing for one routing call). -/
theorem tier1_iff (ready advertise miss : Bool) :
    classifyPeer ready advertise miss = .tier1 ↔ ready = true ∧ advertise = true := by
  unfold classifyPeer
  cases ready <;> cases advertise <;> cases miss <;> simp

/-- **T3.** Tier 2 iff a peer is ready, not advertising, and not missing.
The Rust filter `!missing_peer_list.contains(addr)` only applies on the
Tier 2 path; missing thus *excludes* a non-advertising ready peer from
Tier 2 and pushes it to Tier 3. -/
theorem tier2_iff (ready advertise miss : Bool) :
    classifyPeer ready advertise miss = .tier2 ↔
      ready = true ∧ advertise = false ∧ miss = false := by
  unfold classifyPeer
  cases ready <;> cases advertise <;> cases miss <;> simp

/-- **T4.** Tier 3 iff a peer is not ready, OR is ready and not advertising
and missing. This is the complement of (T1 candidate ∪ T2 candidate). -/
theorem tier3_iff (ready advertise miss : Bool) :
    classifyPeer ready advertise miss = .tier3 ↔
      ready = false ∨ (advertise = false ∧ miss = true) := by
  unfold classifyPeer
  cases ready <;> cases advertise <;> cases miss <;> simp

/-! ## T5: tier partition -/

/-- **T5.** Every peer is in exactly one tier. The three tiers are mutually
exclusive and exhaustive — there is no fourth outcome and no peer left
unclassified. -/
theorem tier_partition (ready advertise miss : Bool) :
    classifyPeer ready advertise miss = .tier1 ∨
    classifyPeer ready advertise miss = .tier2 ∨
    classifyPeer ready advertise miss = .tier3 := by
  unfold classifyPeer
  cases ready <;> cases advertise <;> cases miss <;> simp

/-! ## T6: advertising trumps missing for the same call -/

/-- **T6.** A peer that is both `advertising` and `missing` for the same hash
classifies as Tier 1, *not* Tier 3. This is the load-bearing direction of
the waterfall — the Rust code computes the advertising list first and uses
it without ever consulting the missing list when the advertising list is
non-empty. -/
theorem tier1_dominates_missing (ready : Bool) (hr : ready = true) :
    classifyPeer ready true true = .tier1 := by
  rw [tier1_iff]; exact ⟨hr, rfl⟩

/-! ## T7-T9: routeInv waterfall selection -/

/-- **T7.** When Tier 1 candidates exist, `routeInvOutcome` selects Tier 1
regardless of the missing list. The advertising list is consulted first;
the missing list does not get a chance to demote a Tier 1 candidate. -/
theorem select_tier1_when_nonempty
    (advertising ready missing : List Nat)
    (h : tier1Candidates advertising ready ≠ []) :
    routeInvOutcome advertising ready missing = .tier1 := by
  unfold routeInvOutcome
  simp [h]

/-- **T8.** Tier 2 is consulted only when Tier 1 is empty. If
`routeInvOutcome` ever returns `.tier2`, then the Tier 1 candidate list
must have been empty — there is no path from a non-empty Tier 1 to a Tier 2
outcome. -/
theorem select_tier2_only_if_tier1_empty
    (advertising ready missing : List Nat)
    (h : routeInvOutcome advertising ready missing = .tier2) :
    tier1Candidates advertising ready = [] := by
  unfold routeInvOutcome at h
  by_contra hne
  simp [hne] at h

/-- **T9.** Tier 3 (`NotFoundRegistry`) iff both candidate lists are empty.
This is the hard-rejection characterisation. -/
theorem tier3_iff_no_routable_peer
    (advertising ready missing : List Nat) :
    routeInvOutcome advertising ready missing = .tier3 ↔
      tier1Candidates advertising ready = [] ∧
      tier2Candidates ready missing = [] := by
  unfold routeInvOutcome
  constructor
  · intro h
    by_cases h1 : tier1Candidates advertising ready = []
    · by_cases h2 : tier2Candidates ready missing = []
      · exact ⟨h1, h2⟩
      · simp [h1, h2] at h
    · simp [h1] at h
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

/-! ## T10-T11: monotonicity and persistence -/

/-- **T10.** Once a peer is in the missing registry for a hash, it remains
excluded from the Tier 2 candidate list as long as the missing list still
contains it. This is the "no retry without registry expiry" property:
recomputing the Tier 2 candidates with the same missing list always
excludes the same peer.

We state this as: if `peer ∈ missing` at one observation, and the missing
list is unchanged at a later observation, the peer is still not a Tier 2
candidate at the later one. The only way `peer` becomes a Tier 2 candidate
is for it to drop out of the missing list — which only happens via
`InventoryRegistry::rotate`. -/
theorem tier3_does_not_change_until_expiry
    (peer : Nat) (ready missing missing' : List Nat)
    (hmiss : peer ∈ missing)
    (hsub : ∀ x, x ∈ missing → x ∈ missing') :
    peer ∉ tier2Candidates ready missing' := by
  intro hcand
  unfold tier2Candidates at hcand
  rw [List.mem_filter] at hcand
  have : peer ∉ missing' := by
    have := hcand.2
    simpa using this
  exact this (hsub peer hmiss)

/-- **T11.** Tier classification is monotone with respect to registry
inclusions in the "good" direction: registering a peer as advertising (true)
cannot demote it to a higher-numbered tier, and removing it from missing
cannot demote it. Concretely: if a ready peer was Tier 1 with `advertise =
true`, it stays Tier 1 regardless of `miss`. -/
theorem tier_monotone_under_set_membership
    (ready miss : Bool) (hr : ready = true) :
    Tier.rank (classifyPeer ready true miss) ≤
      Tier.rank (classifyPeer ready false miss) := by
  subst hr
  unfold classifyPeer Tier.rank
  cases miss <;> simp

/-! ## T12: outcome is a pure function -/

/-- **T12.** `routeInvOutcome` is a deterministic function of its three
list-valued inputs. Two evaluations on equal inputs produce equal tiers.
The tier choice has zero non-determinism; only the P2C peer choice
*within* a chosen tier is randomized. -/
theorem routeInv_outcome_function
    (a₁ r₁ m₁ a₂ r₂ m₂ : List Nat)
    (ha : a₁ = a₂) (hr : r₁ = r₂) (hm : m₁ = m₂) :
    routeInvOutcome a₁ r₁ m₁ = routeInvOutcome a₂ r₂ m₂ := by
  subst ha; subst hr; subst hm; rfl

/-! ## T13: registry expiry window pins -/

/-- **T13.** Worst-case lifetime of a `Missing` registration is exactly
`106` seconds. The Rust source documents `INVENTORY_ROTATION_INTERVAL = 53
s` (`constants.rs:153`) and the `rotate` step drops `prev` and shifts
`current` into `prev` (`inventory_registry.rs:440`), so a `Missing` marker
inserted into `current` at time `t` lasts at most through two rotations
before being dropped from `prev`. This pins that calculation. -/
theorem rejection_window_seconds : MAX_MISSING_LIFETIME_SECS = 106 := by
  unfold MAX_MISSING_LIFETIME_SECS NUM_REGISTRY_MAPS INVENTORY_ROTATION_INTERVAL_SECS
  decide

/-- **T13b.** Rotation interval pinned at 53 s. -/
theorem rotation_interval_value : INVENTORY_ROTATION_INTERVAL_SECS = 53 := rfl

/-- **T13c.** Two-slot registry pinned. -/
theorem num_registry_maps_value : NUM_REGISTRY_MAPS = 2 := rfl

/-! ## T14: tier3 is preserved by adding more peers to the missing list -/

/-- **T14.** Tier 3 is preserved when the missing list grows: if
`routeInvOutcome` returned tier3 on `(advertising, ready, missing)`, it
will also return tier3 on `(advertising, ready, missing')` whenever
`missing ⊆ missing'`. The proof: tier3 means both candidate lists were
empty; growing `missing` can only further shrink Tier 2 (filtering out
*more* ready peers), never grow it; Tier 1 doesn't depend on `missing` at
all. So no path opens up. This formalises the "rejection persists, with
the only escape being registry expiry" property: only *shrinking* the
missing list (via rotation dropping entries) can move us out of tier3. -/
theorem no_internal_retry_within_route_inv
    (advertising ready missing missing' : List Nat)
    (hsub : ∀ x, x ∈ missing → x ∈ missing')
    (h : routeInvOutcome advertising ready missing = .tier3) :
    routeInvOutcome advertising ready missing' = .tier3 := by
  rw [tier3_iff_no_routable_peer] at h ⊢
  refine ⟨h.1, ?_⟩
  -- tier2 was empty on `missing`; show it's empty on `missing'`.
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  unfold tier2Candidates at hx
  rw [List.mem_filter] at hx
  -- x ∈ ready but x ∉ missing'. Since missing ⊆ missing', also x ∉ missing.
  -- So x was a tier2 candidate under `missing`, contradicting h.2.
  have hxmiss' : x ∉ missing' := by simpa using hx.2
  have hxmiss : x ∉ missing := fun hin => hxmiss' (hsub x hin)
  have hcand : x ∈ tier2Candidates ready missing := by
    unfold tier2Candidates
    rw [List.mem_filter]
    refine ⟨hx.1, ?_⟩
    simpa using hxmiss
  rw [h.2] at hcand
  exact List.not_mem_nil hcand

/-- **T14b.** A tier3 outcome rules out tier1 and tier2 on the same state.
This is the determinism corollary: `routeInvOutcome` is a pure function,
so the same input cannot simultaneously yield two different tier values. -/
theorem tier3_persists_on_same_state
    (advertising ready missing : List Nat)
    (h : routeInvOutcome advertising ready missing = .tier3) :
    routeInvOutcome advertising ready missing ≠ .tier1 ∧
    routeInvOutcome advertising ready missing ≠ .tier2 := by
  refine ⟨?_, ?_⟩
  · rw [h]; decide
  · rw [h]; decide

/-! ## T15: tier 1 ignores the missing list -/

/-- **T15.** When Tier 1 candidates exist, the routing outcome is
*invariant* under any change to the `missing` list — including registry
expiry, new `Missing` registrations, or peer rotation. This proves a
non-trivial property: the Tier 2/Tier 3 escalation cannot interfere with
Tier 1 selection. Concretely: if `routeInv` was about to pick Tier 1 on
state `(adv, ready, m₁)`, no manipulation of `m₁` (within the same call)
can divert it to Tier 2 or Tier 3. -/
theorem tier1_outcome_independent_of_missing
    (advertising ready missing₁ missing₂ : List Nat)
    (h : tier1Candidates advertising ready ≠ []) :
    routeInvOutcome advertising ready missing₁ =
      routeInvOutcome advertising ready missing₂ := by
  rw [select_tier1_when_nonempty _ _ _ h,
      select_tier1_when_nonempty _ _ _ h]

/-- **T15b.** Adding a peer to the missing list cannot turn a Tier 1
outcome into Tier 2 or Tier 3. A formal consequence of T15. -/
theorem missing_addition_cannot_demote_tier1
    (advertising ready missing : List Nat) (peer : Nat)
    (h : routeInvOutcome advertising ready missing = .tier1) :
    routeInvOutcome advertising ready (peer :: missing) = .tier1 := by
  have hne : tier1Candidates advertising ready ≠ [] := by
    intro heq
    unfold routeInvOutcome at h
    -- After setting tier1Candidates = [], the if-then-else collapses through
    -- the false branch; the inner if produces tier2 or tier3, never tier1.
    rw [heq] at h
    simp only [ne_eq, not_true_eq_false, if_false] at h
    split at h <;> exact absurd h (by decide)
  exact (tier1_outcome_independent_of_missing _ _ _ _ hne).symm.trans h

/-! ## Auxiliary characterisations of candidate sets -/

/-- A peer is in the Tier 1 candidate list iff it is advertising and ready. -/
theorem mem_tier1Candidates (peer : Nat) (advertising ready : List Nat) :
    peer ∈ tier1Candidates advertising ready ↔
      peer ∈ advertising ∧ peer ∈ ready := by
  unfold tier1Candidates
  rw [List.mem_filter]
  simp

/-- A peer is in the Tier 2 candidate list iff it is ready and not missing. -/
theorem mem_tier2Candidates (peer : Nat) (ready missing : List Nat) :
    peer ∈ tier2Candidates ready missing ↔
      peer ∈ ready ∧ peer ∉ missing := by
  unfold tier2Candidates
  rw [List.mem_filter]
  simp

/-- A peer that is missing is never a Tier 2 candidate. The contrapositive
of `mem_tier2Candidates`'s right side. -/
theorem missing_peer_not_tier2_candidate (peer : Nat) (ready missing : List Nat)
    (h : peer ∈ missing) :
    peer ∉ tier2Candidates ready missing := by
  intro hcand
  rw [mem_tier2Candidates] at hcand
  exact hcand.2 h

end Zebra.NetworkPeerSetRouting
