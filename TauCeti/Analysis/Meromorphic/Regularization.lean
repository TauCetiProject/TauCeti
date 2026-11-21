/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order

/-!
# Local power regularization of meromorphic maps

On an open set, a meromorphic map into a normed space can be described on balls by clearing
powers of the centred coordinate. The regularized map is analytic on the entire ball, but
only has to agree with the cleared product away from the centre. In particular for a map into
bounded operators the exponent clears the whole operator in operator norm, not just each of
its matrix coefficients separately.

Postcomposition with a continuous linear map preserves meromorphy, without requiring either
target to be complete. This includes fixed compositions of operator families by applying the
continuous linear maps built from `ContinuousLinearMap.compL`.

The ball criterion does not require completeness: meromorphy on the domain, rather than just
at the centre, supplies analyticity in the punctured ball via `MeromorphicOn.eventually_analyticAt`.
-/

public section

open Filter Metric Set
open scoped Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : 𝕜 → E} {c : 𝕜} {U : Set 𝕜}

/-- Postcomposition with a continuous linear map preserves meromorphy at a point. -/
@[fun_prop]
theorem MeromorphicAt.continuousLinearMap_comp (hf : MeromorphicAt f c) (L : E →L[𝕜] F) :
    MeromorphicAt (fun z ↦ L (f z)) c := by
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, by simpa only [Function.comp_def, map_smul] using (L.analyticAt _).comp hn⟩

/-- Postcomposition with a continuous linear map preserves meromorphy on a set. -/
theorem MeromorphicOn.continuousLinearMap_comp (hf : MeromorphicOn f U) (L : E →L[𝕜] F) :
    MeromorphicOn (fun z ↦ L (f z)) U :=
  fun z hz ↦ (hf z hz).continuousLinearMap_comp L

/-- On an open domain, normed-space-valued meromorphy is equivalent to admitting an analytic
power regularization on a ball around each point. Agreement is only required on the
punctured ball; the assigned value of `f` at its centre does not enter the criterion. -/
theorem meromorphicOn_iff_exists_analyticOnNhd_ball (hU : IsOpen U) :
    MeromorphicOn f U ↔ ∀ c ∈ U, ∃ (n : ℕ) (r : ℝ) (g : 𝕜 → E),
      0 < r ∧ ball c r ⊆ U ∧ AnalyticOnNhd 𝕜 g (ball c r) ∧
        EqOn g (fun z ↦ (z - c) ^ n • f z) (ball c r \ {c}) := by
  constructor
  · intro hf c hc
    obtain ⟨n, hn⟩ := hf c hc
    obtain ⟨r₁, hr₁, h₁⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hc)
    obtain ⟨r₂, hr₂, h₂⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp
      (hf.eventually_analyticAt hc)
    have hsub : ball c (min r₁ r₂) ⊆ U := (ball_subset_ball (min_le_left _ _)).trans h₁
    refine ⟨n, min r₁ r₂, _, lt_min hr₁ hr₂, hsub, ?_, fun _ _ ↦ rfl⟩
    intro z hz
    rcases eq_or_ne z c with rfl | hne
    · exact hn
    · have hz₂ := ball_subset_ball (min_le_right r₁ r₂) hz
      have hza := h₂ ⟨hz₂, hsub hz, hne⟩
      exact ((analyticAt_id.sub analyticAt_const).pow n).fun_smul hza
  · intro h c hc
    obtain ⟨n, r, g, hr, -, hg, hfg⟩ := h c hc
    refine (MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt).2
      ⟨-(n : ℤ), g, hg c (mem_ball_self hr), ?_⟩
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds c hr), self_mem_nhdsWithin]
      with z hz (hne : z ≠ c)
    rw [hfg ⟨hz, hne⟩, zpow_neg, zpow_natCast, inv_smul_smul₀ (pow_ne_zero _ (sub_ne_zero.2 hne))]
