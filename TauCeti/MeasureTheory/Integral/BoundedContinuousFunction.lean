/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Pairing bounded continuous functions with an integrable weight

For an integrable `ψ : X → 𝕜` and a bounded continuous `u : X →ᵇ F`, the product `ψ • u` is
integrable (`MeasureTheory.Integrable.smul_boundedContinuousFunction`), and the pairing
`u ↦ ∫ ψ • u` is continuous for the supremum norm on `X →ᵇ F`
(`TauCeti.continuous_integral_smul_boundedContinuousFunction`). This is what lets an identity
between such pairings pass to uniform limits; for instance, the pairs `(f, g)` with
`∫ Δφ • f = ∫ φ • g` for all test functions `φ` form a closed set of pairs of bounded continuous
functions.
-/

public section

open BoundedContinuousFunction Filter Metric

variable {X 𝕜 F : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [NormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [SecondCountableTopologyEither X F]
  {μ : MeasureTheory.Measure X} {ψ : X → 𝕜}

/-- The product of an integrable function with a bounded continuous function is integrable. -/
theorem MeasureTheory.Integrable.smul_boundedContinuousFunction (hψ : Integrable ψ μ)
    (u : X →ᵇ F) : Integrable (fun x ↦ ψ x • u x) μ :=
  hψ.smul_bdd ‖u‖ u.continuous.aestronglyMeasurable (ae_of_all _ u.norm_coe_le_norm)

namespace TauCeti

open MeasureTheory

/-- Pairing with an integrable function is continuous on bounded continuous functions with the
supremum norm. -/
theorem continuous_integral_smul_boundedContinuousFunction [NormedSpace ℝ F]
    (hψ : Integrable ψ μ) : Continuous fun u : X →ᵇ F ↦ ∫ x, ψ x • u x ∂μ := by
  refine continuous_iff_continuousAt.2 fun u₀ ↦ continuousAt_of_dominated
    (Eventually.of_forall fun u ↦ (hψ.smul_boundedContinuousFunction u).aestronglyMeasurable) ?_
    (hψ.norm.mul_const (‖u₀‖ + 1))
    (ae_of_all _ fun x ↦ (continuous_const.smul (continuous_eval_const x)).continuousAt)
  filter_upwards [ball_mem_nhds u₀ one_pos] with u hu
  refine ae_of_all _ fun x ↦ ?_
  rw [norm_smul]
  have hu' : ‖u‖ ≤ ‖u₀‖ + 1 := by
    have := norm_le_norm_add_norm_sub' u u₀
    rw [← dist_eq_norm] at this
    linarith [mem_ball.1 hu]
  exact mul_le_mul_of_nonneg_left ((u.norm_coe_le_norm x).trans hu') (norm_nonneg _)

end TauCeti
