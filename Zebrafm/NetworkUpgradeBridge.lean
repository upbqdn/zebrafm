import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Zebrafm.NetworkUpgrade

set_option maxHeartbeats 1000000

/-!
# NetworkUpgrade bridge: cascade form ↔ indicator-sum form

The existing `Zebra.NetworkUpgrade` module defines two parallel models of the
"current upgrade" function:

  * `current : Nat → NU` — a nested `if … else if …` cascade, matching the
    Rust scan-from-the-back semantics.
  * `currentOrd : Nat → Nat` — the same function expressed as a sum of
    indicator functions, written this way so monotonicity in `h` becomes a
    one-liner (`omega` after monotonicity of each indicator).

That module left the bridge `(current h).toOrd = currentOrd h` as future work
because the natural proof via `split_ifs` explodes to 2^11 subgoals. This
module closes that bridge using 11 band-specific lemmas (one per half-open
activation interval), each proved by establishing the 10 explicit threshold
bounds and then using `simp` plus `omega` to evaluate both sides to the same
literal.

We also derive the universal monotonicity corollary
`(current h₁).toOrd ≤ (current h₂).toOrd` from the bridge plus
`currentOrd_monotone`.

Sources:
  * `zebra-chain/src/parameters/network_upgrade.rs:312` (`NetworkUpgrade::current`)
  * `Zebrafm/NetworkUpgrade.lean` (the cascade and indicator-sum forms)
-/

namespace Zebra.NetworkUpgradeBridge

open Zebra.NetworkUpgrade

/-! ## Constant ordering (sanity for the band ranges) -/

private theorem h_BO_lt_OV : BEFORE_OVERWINTER < OVERWINTER := by
  unfold BEFORE_OVERWINTER OVERWINTER; decide
private theorem h_OV_lt_SA : OVERWINTER < SAPLING := by
  unfold OVERWINTER SAPLING; decide
private theorem h_SA_lt_BL : SAPLING < BLOSSOM := by
  unfold SAPLING BLOSSOM; decide
private theorem h_BL_lt_HE : BLOSSOM < HEARTWOOD := by
  unfold BLOSSOM HEARTWOOD; decide
private theorem h_HE_lt_CA : HEARTWOOD < CANOPY := by
  unfold HEARTWOOD CANOPY; decide
private theorem h_CA_lt_N5 : CANOPY < NU5 := by
  unfold CANOPY NU5; decide
private theorem h_N5_lt_N6 : NU5 < NU6 := by
  unfold NU5 NU6; decide
private theorem h_N6_lt_N61 : NU6 < NU6_1 := by
  unfold NU6 NU6_1; decide
private theorem h_N61_lt_N62 : NU6_1 < NU6_2 := by
  unfold NU6_1 NU6_2; decide

/-! ## Band lemmas

For each half-open activation interval `[h_k, h_{k+1})`, we prove that both
`(current h).toOrd` and `currentOrd h` evaluate to the corresponding ordinal
`k`. Each lemma sets up the 10 explicit threshold bounds (the bounds *above*
the band are derived by transitivity from the upper bound `h < h_{k+1}`; the
bounds *below* are derived from the lower bound `h_k ≤ h`), then `unfold`s
both `current` and `currentOrd` and lets `simp [hypotheses]` discharge the
resulting literal equality.
-/

/-- Band 0: `h ∈ [0, BEFORE_OVERWINTER)` → genesis (ord 0). -/
private theorem band_genesis (h : Nat) (h_upper : h < BEFORE_OVERWINTER) :
    (current h).toOrd = 0 ∧ currentOrd h = 0 := by
  -- All ten thresholds are above `h`.
  have hlt_BO : h < BEFORE_OVERWINTER := h_upper
  have hlt_OV : h < OVERWINTER := lt_of_lt_of_le hlt_BO (le_of_lt h_BO_lt_OV)
  have hlt_SA : h < SAPLING := lt_of_lt_of_le hlt_OV (le_of_lt h_OV_lt_SA)
  have hlt_BL : h < BLOSSOM := lt_of_lt_of_le hlt_SA (le_of_lt h_SA_lt_BL)
  have hlt_HE : h < HEARTWOOD := lt_of_lt_of_le hlt_BL (le_of_lt h_BL_lt_HE)
  have hlt_CA : h < CANOPY := lt_of_lt_of_le hlt_HE (le_of_lt h_HE_lt_CA)
  have hlt_N5 : h < NU5 := lt_of_lt_of_le hlt_CA (le_of_lt h_CA_lt_N5)
  have hlt_N6 : h < NU6 := lt_of_lt_of_le hlt_N5 (le_of_lt h_N5_lt_N6)
  have hlt_N61 : h < NU6_1 := lt_of_lt_of_le hlt_N6 (le_of_lt h_N6_lt_N61)
  have hlt_N62 : h < NU6_2 := lt_of_lt_of_le hlt_N61 (le_of_lt h_N61_lt_N62)
  refine ⟨?_, ?_⟩
  · unfold current
    simp [Nat.not_le.mpr hlt_BO, Nat.not_le.mpr hlt_OV, Nat.not_le.mpr hlt_SA,
          Nat.not_le.mpr hlt_BL, Nat.not_le.mpr hlt_HE, Nat.not_le.mpr hlt_CA,
          Nat.not_le.mpr hlt_N5, Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61,
          Nat.not_le.mpr hlt_N62, NU.toOrd]
  · unfold currentOrd
    simp [Nat.not_le.mpr hlt_BO, Nat.not_le.mpr hlt_OV, Nat.not_le.mpr hlt_SA,
          Nat.not_le.mpr hlt_BL, Nat.not_le.mpr hlt_HE, Nat.not_le.mpr hlt_CA,
          Nat.not_le.mpr hlt_N5, Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61,
          Nat.not_le.mpr hlt_N62]

/-- Band 1: `h ∈ [BEFORE_OVERWINTER, OVERWINTER)` → beforeOverwinter (ord 1). -/
private theorem band_before_overwinter (h : Nat)
    (h_lower : BEFORE_OVERWINTER ≤ h) (h_upper : h < OVERWINTER) :
    (current h).toOrd = 1 ∧ currentOrd h = 1 := by
  have hge_BO : h ≥ BEFORE_OVERWINTER := h_lower
  have hlt_OV : h < OVERWINTER := h_upper
  have hlt_SA : h < SAPLING := lt_of_lt_of_le hlt_OV (le_of_lt h_OV_lt_SA)
  have hlt_BL : h < BLOSSOM := lt_of_lt_of_le hlt_SA (le_of_lt h_SA_lt_BL)
  have hlt_HE : h < HEARTWOOD := lt_of_lt_of_le hlt_BL (le_of_lt h_BL_lt_HE)
  have hlt_CA : h < CANOPY := lt_of_lt_of_le hlt_HE (le_of_lt h_HE_lt_CA)
  have hlt_N5 : h < NU5 := lt_of_lt_of_le hlt_CA (le_of_lt h_CA_lt_N5)
  have hlt_N6 : h < NU6 := lt_of_lt_of_le hlt_N5 (le_of_lt h_N5_lt_N6)
  have hlt_N61 : h < NU6_1 := lt_of_lt_of_le hlt_N6 (le_of_lt h_N6_lt_N61)
  have hlt_N62 : h < NU6_2 := lt_of_lt_of_le hlt_N61 (le_of_lt h_N61_lt_N62)
  refine ⟨?_, ?_⟩
  · unfold current
    simp [Nat.not_le.mpr hlt_OV, Nat.not_le.mpr hlt_SA,
          Nat.not_le.mpr hlt_BL, Nat.not_le.mpr hlt_HE, Nat.not_le.mpr hlt_CA,
          Nat.not_le.mpr hlt_N5, Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61,
          Nat.not_le.mpr hlt_N62, hge_BO, NU.toOrd]
  · unfold currentOrd
    simp [Nat.not_le.mpr hlt_OV, Nat.not_le.mpr hlt_SA,
          Nat.not_le.mpr hlt_BL, Nat.not_le.mpr hlt_HE, Nat.not_le.mpr hlt_CA,
          Nat.not_le.mpr hlt_N5, Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61,
          Nat.not_le.mpr hlt_N62, hge_BO]

/-- Band 2: `h ∈ [OVERWINTER, SAPLING)` → overwinter (ord 2). -/
private theorem band_overwinter (h : Nat)
    (h_lower : OVERWINTER ≤ h) (h_upper : h < SAPLING) :
    (current h).toOrd = 2 ∧ currentOrd h = 2 := by
  have hge_BO : h ≥ BEFORE_OVERWINTER :=
    le_of_lt (lt_of_lt_of_le h_BO_lt_OV h_lower)
  have hge_OV : h ≥ OVERWINTER := h_lower
  have hlt_SA : h < SAPLING := h_upper
  have hlt_BL : h < BLOSSOM := lt_of_lt_of_le hlt_SA (le_of_lt h_SA_lt_BL)
  have hlt_HE : h < HEARTWOOD := lt_of_lt_of_le hlt_BL (le_of_lt h_BL_lt_HE)
  have hlt_CA : h < CANOPY := lt_of_lt_of_le hlt_HE (le_of_lt h_HE_lt_CA)
  have hlt_N5 : h < NU5 := lt_of_lt_of_le hlt_CA (le_of_lt h_CA_lt_N5)
  have hlt_N6 : h < NU6 := lt_of_lt_of_le hlt_N5 (le_of_lt h_N5_lt_N6)
  have hlt_N61 : h < NU6_1 := lt_of_lt_of_le hlt_N6 (le_of_lt h_N6_lt_N61)
  have hlt_N62 : h < NU6_2 := lt_of_lt_of_le hlt_N61 (le_of_lt h_N61_lt_N62)
  refine ⟨?_, ?_⟩
  · unfold current
    simp [Nat.not_le.mpr hlt_SA,
          Nat.not_le.mpr hlt_BL, Nat.not_le.mpr hlt_HE, Nat.not_le.mpr hlt_CA,
          Nat.not_le.mpr hlt_N5, Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61,
          Nat.not_le.mpr hlt_N62, hge_OV, NU.toOrd]
  · unfold currentOrd
    simp [Nat.not_le.mpr hlt_SA,
          Nat.not_le.mpr hlt_BL, Nat.not_le.mpr hlt_HE, Nat.not_le.mpr hlt_CA,
          Nat.not_le.mpr hlt_N5, Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61,
          Nat.not_le.mpr hlt_N62, hge_BO, hge_OV]

/-- Band 3: `h ∈ [SAPLING, BLOSSOM)` → sapling (ord 3). -/
private theorem band_sapling (h : Nat)
    (h_lower : SAPLING ≤ h) (h_upper : h < BLOSSOM) :
    (current h).toOrd = 3 ∧ currentOrd h = 3 := by
  have hge_BO : h ≥ BEFORE_OVERWINTER :=
    le_of_lt (lt_of_lt_of_le h_BO_lt_OV (le_of_lt (lt_of_lt_of_le h_OV_lt_SA h_lower)))
  have hge_OV : h ≥ OVERWINTER := le_of_lt (lt_of_lt_of_le h_OV_lt_SA h_lower)
  have hge_SA : h ≥ SAPLING := h_lower
  have hlt_BL : h < BLOSSOM := h_upper
  have hlt_HE : h < HEARTWOOD := lt_of_lt_of_le hlt_BL (le_of_lt h_BL_lt_HE)
  have hlt_CA : h < CANOPY := lt_of_lt_of_le hlt_HE (le_of_lt h_HE_lt_CA)
  have hlt_N5 : h < NU5 := lt_of_lt_of_le hlt_CA (le_of_lt h_CA_lt_N5)
  have hlt_N6 : h < NU6 := lt_of_lt_of_le hlt_N5 (le_of_lt h_N5_lt_N6)
  have hlt_N61 : h < NU6_1 := lt_of_lt_of_le hlt_N6 (le_of_lt h_N6_lt_N61)
  have hlt_N62 : h < NU6_2 := lt_of_lt_of_le hlt_N61 (le_of_lt h_N61_lt_N62)
  refine ⟨?_, ?_⟩
  · unfold current
    simp [Nat.not_le.mpr hlt_BL, Nat.not_le.mpr hlt_HE, Nat.not_le.mpr hlt_CA,
          Nat.not_le.mpr hlt_N5, Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61,
          Nat.not_le.mpr hlt_N62, hge_BO, hge_OV, hge_SA, NU.toOrd]
  · unfold currentOrd
    simp [Nat.not_le.mpr hlt_BL, Nat.not_le.mpr hlt_HE, Nat.not_le.mpr hlt_CA,
          Nat.not_le.mpr hlt_N5, Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61,
          Nat.not_le.mpr hlt_N62, hge_BO, hge_OV, hge_SA]

/-- Band 4: `h ∈ [BLOSSOM, HEARTWOOD)` → blossom (ord 4). -/
private theorem band_blossom (h : Nat)
    (h_lower : BLOSSOM ≤ h) (h_upper : h < HEARTWOOD) :
    (current h).toOrd = 4 ∧ currentOrd h = 4 := by
  have hge_BO : h ≥ BEFORE_OVERWINTER := by
    have := lt_of_lt_of_le h_BO_lt_OV
              (le_of_lt (lt_of_lt_of_le h_OV_lt_SA
                (le_of_lt (lt_of_lt_of_le h_SA_lt_BL h_lower))))
    exact le_of_lt this
  have hge_OV : h ≥ OVERWINTER :=
    le_of_lt (lt_of_lt_of_le h_OV_lt_SA (le_of_lt (lt_of_lt_of_le h_SA_lt_BL h_lower)))
  have hge_SA : h ≥ SAPLING := le_of_lt (lt_of_lt_of_le h_SA_lt_BL h_lower)
  have hge_BL : h ≥ BLOSSOM := h_lower
  have hlt_HE : h < HEARTWOOD := h_upper
  have hlt_CA : h < CANOPY := lt_of_lt_of_le hlt_HE (le_of_lt h_HE_lt_CA)
  have hlt_N5 : h < NU5 := lt_of_lt_of_le hlt_CA (le_of_lt h_CA_lt_N5)
  have hlt_N6 : h < NU6 := lt_of_lt_of_le hlt_N5 (le_of_lt h_N5_lt_N6)
  have hlt_N61 : h < NU6_1 := lt_of_lt_of_le hlt_N6 (le_of_lt h_N6_lt_N61)
  have hlt_N62 : h < NU6_2 := lt_of_lt_of_le hlt_N61 (le_of_lt h_N61_lt_N62)
  refine ⟨?_, ?_⟩
  · unfold current
    simp [Nat.not_le.mpr hlt_HE, Nat.not_le.mpr hlt_CA,
          Nat.not_le.mpr hlt_N5, Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61,
          Nat.not_le.mpr hlt_N62, hge_BO, hge_OV, hge_SA, hge_BL, NU.toOrd]
  · unfold currentOrd
    simp [Nat.not_le.mpr hlt_HE, Nat.not_le.mpr hlt_CA,
          Nat.not_le.mpr hlt_N5, Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61,
          Nat.not_le.mpr hlt_N62, hge_BO, hge_OV, hge_SA, hge_BL]

/-- Band 5: `h ∈ [HEARTWOOD, CANOPY)` → heartwood (ord 5). -/
private theorem band_heartwood (h : Nat)
    (h_lower : HEARTWOOD ≤ h) (h_upper : h < CANOPY) :
    (current h).toOrd = 5 ∧ currentOrd h = 5 := by
  have hBO_HE : BEFORE_OVERWINTER < HEARTWOOD := by
    unfold BEFORE_OVERWINTER HEARTWOOD; decide
  have hOV_HE : OVERWINTER < HEARTWOOD := by
    unfold OVERWINTER HEARTWOOD; decide
  have hSA_HE : SAPLING < HEARTWOOD := by
    unfold SAPLING HEARTWOOD; decide
  have hBL_HE : BLOSSOM < HEARTWOOD := h_BL_lt_HE
  have hge_BO : h ≥ BEFORE_OVERWINTER := le_of_lt (lt_of_lt_of_le hBO_HE h_lower)
  have hge_OV : h ≥ OVERWINTER := le_of_lt (lt_of_lt_of_le hOV_HE h_lower)
  have hge_SA : h ≥ SAPLING := le_of_lt (lt_of_lt_of_le hSA_HE h_lower)
  have hge_BL : h ≥ BLOSSOM := le_of_lt (lt_of_lt_of_le hBL_HE h_lower)
  have hge_HE : h ≥ HEARTWOOD := h_lower
  have hlt_CA : h < CANOPY := h_upper
  have hlt_N5 : h < NU5 := lt_of_lt_of_le hlt_CA (le_of_lt h_CA_lt_N5)
  have hlt_N6 : h < NU6 := lt_of_lt_of_le hlt_N5 (le_of_lt h_N5_lt_N6)
  have hlt_N61 : h < NU6_1 := lt_of_lt_of_le hlt_N6 (le_of_lt h_N6_lt_N61)
  have hlt_N62 : h < NU6_2 := lt_of_lt_of_le hlt_N61 (le_of_lt h_N61_lt_N62)
  refine ⟨?_, ?_⟩
  · unfold current
    simp [Nat.not_le.mpr hlt_CA,
          Nat.not_le.mpr hlt_N5, Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61,
          Nat.not_le.mpr hlt_N62, hge_BO, hge_OV, hge_SA, hge_BL, hge_HE, NU.toOrd]
  · unfold currentOrd
    simp [Nat.not_le.mpr hlt_CA,
          Nat.not_le.mpr hlt_N5, Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61,
          Nat.not_le.mpr hlt_N62, hge_BO, hge_OV, hge_SA, hge_BL, hge_HE]

/-- Band 6: `h ∈ [CANOPY, NU5)` → canopy (ord 6). -/
private theorem band_canopy (h : Nat)
    (h_lower : CANOPY ≤ h) (h_upper : h < NU5) :
    (current h).toOrd = 6 ∧ currentOrd h = 6 := by
  have hBO_CA : BEFORE_OVERWINTER < CANOPY := by
    unfold BEFORE_OVERWINTER CANOPY; decide
  have hOV_CA : OVERWINTER < CANOPY := by
    unfold OVERWINTER CANOPY; decide
  have hSA_CA : SAPLING < CANOPY := by
    unfold SAPLING CANOPY; decide
  have hBL_CA : BLOSSOM < CANOPY := by
    unfold BLOSSOM CANOPY; decide
  have hHE_CA : HEARTWOOD < CANOPY := h_HE_lt_CA
  have hge_BO : h ≥ BEFORE_OVERWINTER := le_of_lt (lt_of_lt_of_le hBO_CA h_lower)
  have hge_OV : h ≥ OVERWINTER := le_of_lt (lt_of_lt_of_le hOV_CA h_lower)
  have hge_SA : h ≥ SAPLING := le_of_lt (lt_of_lt_of_le hSA_CA h_lower)
  have hge_BL : h ≥ BLOSSOM := le_of_lt (lt_of_lt_of_le hBL_CA h_lower)
  have hge_HE : h ≥ HEARTWOOD := le_of_lt (lt_of_lt_of_le hHE_CA h_lower)
  have hge_CA : h ≥ CANOPY := h_lower
  have hlt_N5 : h < NU5 := h_upper
  have hlt_N6 : h < NU6 := lt_of_lt_of_le hlt_N5 (le_of_lt h_N5_lt_N6)
  have hlt_N61 : h < NU6_1 := lt_of_lt_of_le hlt_N6 (le_of_lt h_N6_lt_N61)
  have hlt_N62 : h < NU6_2 := lt_of_lt_of_le hlt_N61 (le_of_lt h_N61_lt_N62)
  refine ⟨?_, ?_⟩
  · unfold current
    simp [Nat.not_le.mpr hlt_N5, Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61,
          Nat.not_le.mpr hlt_N62, hge_BO, hge_OV, hge_SA, hge_BL, hge_HE, hge_CA,
          NU.toOrd]
  · unfold currentOrd
    simp [Nat.not_le.mpr hlt_N5, Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61,
          Nat.not_le.mpr hlt_N62, hge_BO, hge_OV, hge_SA, hge_BL, hge_HE, hge_CA]

/-- Band 7: `h ∈ [NU5, NU6)` → nu5 (ord 7). -/
private theorem band_nu5 (h : Nat)
    (h_lower : NU5 ≤ h) (h_upper : h < NU6) :
    (current h).toOrd = 7 ∧ currentOrd h = 7 := by
  have hBO_N5 : BEFORE_OVERWINTER < NU5 := by
    unfold BEFORE_OVERWINTER NU5; decide
  have hOV_N5 : OVERWINTER < NU5 := by
    unfold OVERWINTER NU5; decide
  have hSA_N5 : SAPLING < NU5 := by
    unfold SAPLING NU5; decide
  have hBL_N5 : BLOSSOM < NU5 := by
    unfold BLOSSOM NU5; decide
  have hHE_N5 : HEARTWOOD < NU5 := by
    unfold HEARTWOOD NU5; decide
  have hCA_N5 : CANOPY < NU5 := h_CA_lt_N5
  have hge_BO : h ≥ BEFORE_OVERWINTER := le_of_lt (lt_of_lt_of_le hBO_N5 h_lower)
  have hge_OV : h ≥ OVERWINTER := le_of_lt (lt_of_lt_of_le hOV_N5 h_lower)
  have hge_SA : h ≥ SAPLING := le_of_lt (lt_of_lt_of_le hSA_N5 h_lower)
  have hge_BL : h ≥ BLOSSOM := le_of_lt (lt_of_lt_of_le hBL_N5 h_lower)
  have hge_HE : h ≥ HEARTWOOD := le_of_lt (lt_of_lt_of_le hHE_N5 h_lower)
  have hge_CA : h ≥ CANOPY := le_of_lt (lt_of_lt_of_le hCA_N5 h_lower)
  have hge_N5 : h ≥ NU5 := h_lower
  have hlt_N6 : h < NU6 := h_upper
  have hlt_N61 : h < NU6_1 := lt_of_lt_of_le hlt_N6 (le_of_lt h_N6_lt_N61)
  have hlt_N62 : h < NU6_2 := lt_of_lt_of_le hlt_N61 (le_of_lt h_N61_lt_N62)
  refine ⟨?_, ?_⟩
  · unfold current
    simp [Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61, Nat.not_le.mpr hlt_N62,
          hge_BO, hge_OV, hge_SA, hge_BL, hge_HE, hge_CA, hge_N5, NU.toOrd]
  · unfold currentOrd
    simp [Nat.not_le.mpr hlt_N6, Nat.not_le.mpr hlt_N61, Nat.not_le.mpr hlt_N62,
          hge_BO, hge_OV, hge_SA, hge_BL, hge_HE, hge_CA, hge_N5]

/-- Band 8: `h ∈ [NU6, NU6_1)` → nu6 (ord 8). -/
private theorem band_nu6 (h : Nat)
    (h_lower : NU6 ≤ h) (h_upper : h < NU6_1) :
    (current h).toOrd = 8 ∧ currentOrd h = 8 := by
  have hBO_N6 : BEFORE_OVERWINTER < NU6 := by
    unfold BEFORE_OVERWINTER NU6; decide
  have hOV_N6 : OVERWINTER < NU6 := by
    unfold OVERWINTER NU6; decide
  have hSA_N6 : SAPLING < NU6 := by
    unfold SAPLING NU6; decide
  have hBL_N6 : BLOSSOM < NU6 := by
    unfold BLOSSOM NU6; decide
  have hHE_N6 : HEARTWOOD < NU6 := by
    unfold HEARTWOOD NU6; decide
  have hCA_N6 : CANOPY < NU6 := by
    unfold CANOPY NU6; decide
  have hN5_N6 : NU5 < NU6 := h_N5_lt_N6
  have hge_BO : h ≥ BEFORE_OVERWINTER := le_of_lt (lt_of_lt_of_le hBO_N6 h_lower)
  have hge_OV : h ≥ OVERWINTER := le_of_lt (lt_of_lt_of_le hOV_N6 h_lower)
  have hge_SA : h ≥ SAPLING := le_of_lt (lt_of_lt_of_le hSA_N6 h_lower)
  have hge_BL : h ≥ BLOSSOM := le_of_lt (lt_of_lt_of_le hBL_N6 h_lower)
  have hge_HE : h ≥ HEARTWOOD := le_of_lt (lt_of_lt_of_le hHE_N6 h_lower)
  have hge_CA : h ≥ CANOPY := le_of_lt (lt_of_lt_of_le hCA_N6 h_lower)
  have hge_N5 : h ≥ NU5 := le_of_lt (lt_of_lt_of_le hN5_N6 h_lower)
  have hge_N6 : h ≥ NU6 := h_lower
  have hlt_N61 : h < NU6_1 := h_upper
  have hlt_N62 : h < NU6_2 := lt_of_lt_of_le hlt_N61 (le_of_lt h_N61_lt_N62)
  refine ⟨?_, ?_⟩
  · unfold current
    simp [Nat.not_le.mpr hlt_N61, Nat.not_le.mpr hlt_N62,
          hge_BO, hge_OV, hge_SA, hge_BL, hge_HE, hge_CA, hge_N5, hge_N6, NU.toOrd]
  · unfold currentOrd
    simp [Nat.not_le.mpr hlt_N61, Nat.not_le.mpr hlt_N62,
          hge_BO, hge_OV, hge_SA, hge_BL, hge_HE, hge_CA, hge_N5, hge_N6]

/-- Band 9: `h ∈ [NU6_1, NU6_2)` → nu6_1 (ord 9). -/
private theorem band_nu6_1 (h : Nat)
    (h_lower : NU6_1 ≤ h) (h_upper : h < NU6_2) :
    (current h).toOrd = 9 ∧ currentOrd h = 9 := by
  have hBO_N61 : BEFORE_OVERWINTER < NU6_1 := by
    unfold BEFORE_OVERWINTER NU6_1; decide
  have hOV_N61 : OVERWINTER < NU6_1 := by
    unfold OVERWINTER NU6_1; decide
  have hSA_N61 : SAPLING < NU6_1 := by
    unfold SAPLING NU6_1; decide
  have hBL_N61 : BLOSSOM < NU6_1 := by
    unfold BLOSSOM NU6_1; decide
  have hHE_N61 : HEARTWOOD < NU6_1 := by
    unfold HEARTWOOD NU6_1; decide
  have hCA_N61 : CANOPY < NU6_1 := by
    unfold CANOPY NU6_1; decide
  have hN5_N61 : NU5 < NU6_1 := by
    unfold NU5 NU6_1; decide
  have hN6_N61 : NU6 < NU6_1 := h_N6_lt_N61
  have hge_BO : h ≥ BEFORE_OVERWINTER := le_of_lt (lt_of_lt_of_le hBO_N61 h_lower)
  have hge_OV : h ≥ OVERWINTER := le_of_lt (lt_of_lt_of_le hOV_N61 h_lower)
  have hge_SA : h ≥ SAPLING := le_of_lt (lt_of_lt_of_le hSA_N61 h_lower)
  have hge_BL : h ≥ BLOSSOM := le_of_lt (lt_of_lt_of_le hBL_N61 h_lower)
  have hge_HE : h ≥ HEARTWOOD := le_of_lt (lt_of_lt_of_le hHE_N61 h_lower)
  have hge_CA : h ≥ CANOPY := le_of_lt (lt_of_lt_of_le hCA_N61 h_lower)
  have hge_N5 : h ≥ NU5 := le_of_lt (lt_of_lt_of_le hN5_N61 h_lower)
  have hge_N6 : h ≥ NU6 := le_of_lt (lt_of_lt_of_le hN6_N61 h_lower)
  have hge_N61 : h ≥ NU6_1 := h_lower
  have hlt_N62 : h < NU6_2 := h_upper
  refine ⟨?_, ?_⟩
  · unfold current
    simp [Nat.not_le.mpr hlt_N62,
          hge_BO, hge_OV, hge_SA, hge_BL, hge_HE, hge_CA, hge_N5, hge_N6, hge_N61,
          NU.toOrd]
  · unfold currentOrd
    simp [Nat.not_le.mpr hlt_N62,
          hge_BO, hge_OV, hge_SA, hge_BL, hge_HE, hge_CA, hge_N5, hge_N6, hge_N61]

/-- Band 10: `h ∈ [NU6_2, ∞)` → nu6_2 (ord 10). -/
private theorem band_nu6_2 (h : Nat) (h_lower : NU6_2 ≤ h) :
    (current h).toOrd = 10 ∧ currentOrd h = 10 := by
  have hBO_N62 : BEFORE_OVERWINTER < NU6_2 := by
    unfold BEFORE_OVERWINTER NU6_2; decide
  have hOV_N62 : OVERWINTER < NU6_2 := by
    unfold OVERWINTER NU6_2; decide
  have hSA_N62 : SAPLING < NU6_2 := by
    unfold SAPLING NU6_2; decide
  have hBL_N62 : BLOSSOM < NU6_2 := by
    unfold BLOSSOM NU6_2; decide
  have hHE_N62 : HEARTWOOD < NU6_2 := by
    unfold HEARTWOOD NU6_2; decide
  have hCA_N62 : CANOPY < NU6_2 := by
    unfold CANOPY NU6_2; decide
  have hN5_N62 : NU5 < NU6_2 := by
    unfold NU5 NU6_2; decide
  have hN6_N62 : NU6 < NU6_2 := by
    unfold NU6 NU6_2; decide
  have hN61_N62 : NU6_1 < NU6_2 := h_N61_lt_N62
  have hge_BO : h ≥ BEFORE_OVERWINTER := le_of_lt (lt_of_lt_of_le hBO_N62 h_lower)
  have hge_OV : h ≥ OVERWINTER := le_of_lt (lt_of_lt_of_le hOV_N62 h_lower)
  have hge_SA : h ≥ SAPLING := le_of_lt (lt_of_lt_of_le hSA_N62 h_lower)
  have hge_BL : h ≥ BLOSSOM := le_of_lt (lt_of_lt_of_le hBL_N62 h_lower)
  have hge_HE : h ≥ HEARTWOOD := le_of_lt (lt_of_lt_of_le hHE_N62 h_lower)
  have hge_CA : h ≥ CANOPY := le_of_lt (lt_of_lt_of_le hCA_N62 h_lower)
  have hge_N5 : h ≥ NU5 := le_of_lt (lt_of_lt_of_le hN5_N62 h_lower)
  have hge_N6 : h ≥ NU6 := le_of_lt (lt_of_lt_of_le hN6_N62 h_lower)
  have hge_N61 : h ≥ NU6_1 := le_of_lt (lt_of_lt_of_le hN61_N62 h_lower)
  have hge_N62 : h ≥ NU6_2 := h_lower
  refine ⟨?_, ?_⟩
  · unfold current
    simp [hge_BO, hge_OV, hge_SA, hge_BL, hge_HE, hge_CA, hge_N5, hge_N6, hge_N61,
          hge_N62, NU.toOrd]
  · unfold currentOrd
    simp [hge_BO, hge_OV, hge_SA, hge_BL, hge_HE, hge_CA, hge_N5, hge_N6, hge_N61,
          hge_N62]

/-! ## Master bridge theorem -/

/-- **T1 (bridge: cascade ↔ indicator sum).** The two parallel models of the
"current upgrade" map — the nested cascade `current` (followed by `toOrd`)
and the indicator sum `currentOrd` — agree pointwise for every height `h`.

The proof partitions `Nat` into the 11 half-open activation bands; within
each band, both sides evaluate to the band's ordinal. -/
theorem current_toOrd_eq_currentOrd (h : Nat) :
    (current h).toOrd = currentOrd h := by
  by_cases h0 : h < BEFORE_OVERWINTER
  · obtain ⟨e1, e2⟩ := band_genesis h h0
    rw [e1, e2]
  by_cases h1 : h < OVERWINTER
  · have hLB : BEFORE_OVERWINTER ≤ h := Nat.not_lt.mp h0
    obtain ⟨e1, e2⟩ := band_before_overwinter h hLB h1
    rw [e1, e2]
  by_cases h2 : h < SAPLING
  · have hLB : OVERWINTER ≤ h := Nat.not_lt.mp h1
    obtain ⟨e1, e2⟩ := band_overwinter h hLB h2
    rw [e1, e2]
  by_cases h3 : h < BLOSSOM
  · have hLB : SAPLING ≤ h := Nat.not_lt.mp h2
    obtain ⟨e1, e2⟩ := band_sapling h hLB h3
    rw [e1, e2]
  by_cases h4 : h < HEARTWOOD
  · have hLB : BLOSSOM ≤ h := Nat.not_lt.mp h3
    obtain ⟨e1, e2⟩ := band_blossom h hLB h4
    rw [e1, e2]
  by_cases h5 : h < CANOPY
  · have hLB : HEARTWOOD ≤ h := Nat.not_lt.mp h4
    obtain ⟨e1, e2⟩ := band_heartwood h hLB h5
    rw [e1, e2]
  by_cases h6 : h < NU5
  · have hLB : CANOPY ≤ h := Nat.not_lt.mp h5
    obtain ⟨e1, e2⟩ := band_canopy h hLB h6
    rw [e1, e2]
  by_cases h7 : h < NU6
  · have hLB : NU5 ≤ h := Nat.not_lt.mp h6
    obtain ⟨e1, e2⟩ := band_nu5 h hLB h7
    rw [e1, e2]
  by_cases h8 : h < NU6_1
  · have hLB : NU6 ≤ h := Nat.not_lt.mp h7
    obtain ⟨e1, e2⟩ := band_nu6 h hLB h8
    rw [e1, e2]
  by_cases h9 : h < NU6_2
  · have hLB : NU6_1 ≤ h := Nat.not_lt.mp h8
    obtain ⟨e1, e2⟩ := band_nu6_1 h hLB h9
    rw [e1, e2]
  · have hLB : NU6_2 ≤ h := Nat.not_lt.mp h9
    obtain ⟨e1, e2⟩ := band_nu6_2 h hLB
    rw [e1, e2]

/-! ## Universal monotonicity (via the bridge) -/

/-- **T2 (universal monotonicity of `current` via `toOrd`).** For any two
heights `h₁ ≤ h₂`, the ordinal of the upgrade in force at `h₂` is at least
that at `h₁`. Combined with `current_at_activation_height` (from the parent
module), this implies that crossing more activation heights moves you to
later upgrades, never earlier ones.

This is the universal version of `current_monotone_at_nu6`, lifted out of
the boundary-specific argument by routing through the bridge to the
indicator-sum form (where monotonicity is one line of `omega`). -/
theorem current_toOrd_monotone (h₁ h₂ : Nat) (hle : h₁ ≤ h₂) :
    (current h₁).toOrd ≤ (current h₂).toOrd := by
  rw [current_toOrd_eq_currentOrd h₁, current_toOrd_eq_currentOrd h₂]
  exact currentOrd_monotone h₁ h₂ hle

/-! ## Concrete consequences -/

/-- **T3 (currentOrd at 0 is 0).** The indicator-sum form, at height 0,
fires no indicators. -/
theorem currentOrd_zero : currentOrd 0 = 0 := by
  rw [← current_toOrd_eq_currentOrd 0, current_zero]
  decide

/-- **T4 (currentOrd at every scheduled activation height equals that
upgrade's ordinal).** Specialisation of `current_at_activation_height` to
the indicator-sum form. Excludes `.nu7`, which has no scheduled mainnet
height (see NetworkUpgrade module's coverage note). -/
theorem currentOrd_at_activation_height (nu : NU) (hsched : Scheduled nu) :
    currentOrd (activationHeight nu) = nu.toOrd := by
  rw [← current_toOrd_eq_currentOrd (activationHeight nu),
      current_at_activation_height nu hsched]

/-- A single indicator is at most 1. -/
private theorem indicator_le_one (X h : Nat) :
    (if h ≥ X then 1 else 0) ≤ (1 : Nat) := by
  by_cases hX : h ≥ X <;> simp [hX]

/-- **T5 (range of `(current h).toOrd` is 0 ≤ _ ≤ 10).** Since there are
exactly 10 indicators (each at most 1), `currentOrd` is between 0 and 10,
and so is the ordinal of `current h` (after the bridge). -/
theorem current_toOrd_le_ten (h : Nat) : (current h).toOrd ≤ 10 := by
  rw [current_toOrd_eq_currentOrd]
  unfold currentOrd
  have b1 := indicator_le_one NU6_2 h
  have b2 := indicator_le_one NU6_1 h
  have b3 := indicator_le_one NU6   h
  have b4 := indicator_le_one NU5   h
  have b5 := indicator_le_one CANOPY h
  have b6 := indicator_le_one HEARTWOOD h
  have b7 := indicator_le_one BLOSSOM h
  have b8 := indicator_le_one SAPLING h
  have b9 := indicator_le_one OVERWINTER h
  have b10 := indicator_le_one BEFORE_OVERWINTER h
  omega

end Zebra.NetworkUpgradeBridge
