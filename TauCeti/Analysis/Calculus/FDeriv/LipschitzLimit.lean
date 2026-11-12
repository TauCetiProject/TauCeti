/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Lipschitz control of limits of maps with bounded derivatives

A pointwise limit of maps differentiable on an open set `Ω` of a finite-dimensional real normed
space, whose derivatives are eventually bounded on every compact subset of `Ω`, is locally
Lipschitz on `Ω` (`TauCeti.locallyLipschitzOn_of_tendsto`), and its derivative is bounded on every
compact subset of `Ω` (`TauCeti.exists_forall_norm_fderiv_le_of_tendsto`). On a ball, a bound `C`
on the derivatives makes the maps `C`-Lipschitz there, by the mean value inequality, and the
`C`-Lipschitz maps form a closed set for pointwise convergence
(`TauCeti.lipschitzOnWith_ball_of_tendsto`).

No convergence of the derivatives is assumed or concluded. With a common Hölder bound on the
derivatives they do converge, which is `TauCeti.Analysis.Calculus.FDeriv.HolderLimit`.
-/

public section

namespace TauCeti

open Filter Metric Set
open scoped NNReal Topology

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {l : Filter ι} {u : ι → E → F} {v : E → F}
  {Ω : Set E}

omit [FiniteDimensional ℝ E] in
/-- If maps are eventually differentiable on a ball with derivatives bounded by `C` there, then
their pointwise limit on the ball is `C`-Lipschitz on it. -/
theorem lipschitzOnWith_ball_of_tendsto [l.NeBot] {x : E} {r C : ℝ}
    (hu : ∀ᶠ i in l, ∀ y ∈ ball x r, DifferentiableAt ℝ (u i) y ∧ ‖fderiv ℝ (u i) y‖ ≤ C)
    (hlim : ∀ y ∈ ball x r, Tendsto (fun i ↦ u i y) l (𝓝 (v y))) :
    LipschitzOnWith C.toNNReal v (ball x r) := by
  refine lipschitzOnWith_iff_restrict.2 <| (isClosed_setOfPred_lipschitzWith _).mem_of_tendsto
    (tendsto_pi_nhds.2 fun y ↦ hlim y y.2) (hu.mono fun i hi ↦ ?_)
  refine lipschitzOnWith_iff_restrict.1 <| Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    (fun y hy ↦ (hi y hy).1) (fun y hy ↦ ?_) (convex_ball x r)
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  exact (hi y hy).2.trans (le_max_left _ _)

/-- The pointwise limit on an open set `Ω` of maps differentiable on `Ω`, whose derivatives are
eventually bounded on every compact subset of `Ω`, is locally Lipschitz on `Ω`. -/
theorem locallyLipschitzOn_of_tendsto [l.NeBot] (hΩ : IsOpen Ω)
    (hu : ∀ᶠ i in l, DifferentiableOn ℝ (u i) Ω)
    (hbd : ∀ K, IsCompact K → K ⊆ Ω → ∃ C, ∀ᶠ i in l, ∀ x ∈ K, ‖fderiv ℝ (u i) x‖ ≤ C)
    (hlim : ∀ x ∈ Ω, Tendsto (fun i ↦ u i x) l (𝓝 (v x))) : LocallyLipschitzOn Ω v := by
  intro x hx
  obtain ⟨r, hr, hrΩ⟩ := nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds hx)
  obtain ⟨C, hC⟩ := hbd _ (isCompact_closedBall x r) hrΩ
  have hball : ball x r ⊆ Ω := ball_subset_closedBall.trans hrΩ
  refine ⟨C.toNNReal, ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr),
    lipschitzOnWith_ball_of_tendsto ?_ fun y hy ↦ hlim y (hball hy)⟩
  filter_upwards [hu, hC] with i hui hCi
  exact fun y hy ↦ ⟨hui.differentiableAt (hΩ.mem_nhds (hball hy)),
    hCi y (ball_subset_closedBall hy)⟩

/-- The derivative of the pointwise limit on an open set `Ω` of maps differentiable on `Ω`, whose
derivatives are eventually bounded on every compact subset of `Ω`, is bounded on every compact
subset of `Ω`. -/
theorem exists_forall_norm_fderiv_le_of_tendsto [l.NeBot] (hΩ : IsOpen Ω)
    (hu : ∀ᶠ i in l, DifferentiableOn ℝ (u i) Ω)
    (hbd : ∀ K, IsCompact K → K ⊆ Ω → ∃ C, ∀ᶠ i in l, ∀ x ∈ K, ‖fderiv ℝ (u i) x‖ ≤ C)
    (hlim : ∀ x ∈ Ω, Tendsto (fun i ↦ u i x) l (𝓝 (v x))) {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : ∃ C, ∀ x ∈ K, ‖fderiv ℝ v x‖ ≤ C := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨C, hC⟩ := hbd _ hK.cthickening hδΩ
  refine ⟨max C 0, fun x hx ↦ ?_⟩
  have hball : ball x δ ⊆ cthickening δ K :=
    (ball_subset_thickening hx δ).trans (thickening_subset_cthickening δ K)
  have hlip := lipschitzOnWith_ball_of_tendsto (x := x) (r := δ) (C := C) ?_
    fun y hy ↦ hlim y (hδΩ (hball hy))
  · simpa [Real.coe_toNNReal'] using norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds x hδ) hlip
  filter_upwards [hu, hC] with i hui hCi
  exact fun y hy ↦ ⟨hui.differentiableAt (hΩ.mem_nhds (hδΩ (hball hy))), hCi y (hball hy)⟩

end TauCeti
