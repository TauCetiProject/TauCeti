/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Equicontinuity from bounds on derivatives

A family of differentiable maps on an open subset of a proper real normed space is
equicontinuous if its derivatives are uniformly bounded on each compact subset. The
mean-value inequality supplies a common Lipschitz bound on a small ball around each point.
This criterion is useful when applying Arzelà–Ascoli to families controlled by interior
estimates, without requiring a global bound on the derivatives.
-/

public section

open Filter Metric Set Topology
open scoped NNReal

namespace TauCeti

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Set E} {u : ι → E → F}

/-- Uniform bounds on derivatives on compact subsets of an open set imply equicontinuity
there. No compactness or completeness assumption on the target is needed. -/
theorem equicontinuousOn_of_forall_isCompact_norm_fderiv_le
    (hΩ : IsOpen Ω) (hu : ∀ i, DifferentiableOn ℝ (u i) Ω)
    (hb : ∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ i, ∀ x ∈ C, ‖fderiv ℝ (u i) x‖ ≤ M) :
    EquicontinuousOn u Ω := by
  rw [← equicontinuous_restrict_iff]
  intro x
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩ x x.2
  have hball : closedBall (x : E) (r / 2) ⊆ Ω :=
    (closedBall_subset_ball (by linarith : r / 2 < r)).trans hrΩ
  obtain ⟨M, hM⟩ := hb _ (isCompact_closedBall (x : E) (r / 2)) hball
  let L : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hLip : ∀ i, LipschitzOnWith L (u i) (closedBall (x : E) (r / 2)) := by
    intro i
    apply (convex_closedBall (x : E) (r / 2)).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro y hy
      exact (hu i y (hball hy)).differentiableAt (hΩ.mem_nhds (hball hy))
    · intro y hy
      exact_mod_cast (hM i y hy).trans (le_max_left M 0)
  have hmod : Continuous (fun y : Ω ↦ (L : ℝ) * dist (x : E) (y : E)) :=
    continuous_const.mul (continuous_const.dist continuous_subtype_val)
  apply Metric.equicontinuousAt_of_continuity_modulus
    (fun y : Ω ↦ (L : ℝ) * dist (x : E) (y : E))
    (by simpa using (hmod.continuousAt (x := x)).tendsto) _
  have hnear : ∀ᶠ y : Ω in 𝓝 x, (y : E) ∈ ball (x : E) (r / 2) :=
    continuous_subtype_val.continuousAt (ball_mem_nhds (x : E) (by positivity))
  filter_upwards [hnear] with y hy i
  exact (hLip i).dist_le_mul _ (mem_closedBall_self (by positivity)) _
    (ball_subset_closedBall hy)

end TauCeti
