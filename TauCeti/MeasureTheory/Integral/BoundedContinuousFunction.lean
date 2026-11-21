/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Integrating bounded continuous functions against an integrable weight

On a space `α` with a measure `μ`, where `α` or `F` is second-countable, a bounded continuous
function `u : α →ᵇ F` times an integrable scalar weight `w` is integrable, and the integral
`∫ w • u ∂μ` depends Lipschitz continuously on `u` for the supremum norm, with constant
`∫ ‖w‖ ∂μ` (`MeasureTheory.Integrable.lipschitzWith_integral_smul`). The space need not
be compact, and the measure need not be finite. This is what lets an integral identity against a
fixed weight pass to uniform limits, for instance from smooth functions to all bounded uniformly
continuous ones in a distributional identity tested against a compactly supported function.
-/

public section

namespace MeasureTheory

open scoped BoundedContinuousFunction

variable {α 𝕜 F : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  {μ : Measure α} [NormedRing 𝕜] [NormedAddCommGroup F] [SecondCountableTopologyEither α F]
  [Module 𝕜 F] [IsBoundedSMul 𝕜 F] {w : α → 𝕜}

/-- A bounded continuous function times an integrable scalar weight is integrable. -/
theorem _root_.BoundedContinuousFunction.integrable_smul (u : α →ᵇ F) (hw : Integrable w μ) :
    Integrable (fun x ↦ w x • u x) μ :=
  hw.smul_of_top_left (memLp_top_of_bound u.continuous.aestronglyMeasurable ‖u‖
    (ae_of_all _ u.norm_coe_le_norm))

variable [NormedSpace ℝ F]

/-- **Integration against an integrable weight is Lipschitz in the supremum norm.** For an
integrable scalar weight `w`, the map `u ↦ ∫ w • u ∂μ` on bounded continuous functions is
Lipschitz with constant `∫ ‖w‖ ∂μ`. -/
theorem Integrable.lipschitzWith_integral_smul (hw : Integrable w μ) :
    LipschitzWith (∫ x, ‖w x‖ ∂μ).toNNReal fun u : α →ᵇ F ↦ ∫ x, w x • u x ∂μ := by
  refine LipschitzWith.of_dist_le_mul fun u v ↦ ?_
  rw [dist_eq_norm, ← integral_sub (u.integrable_smul hw) (v.integrable_smul hw), dist_eq_norm,
    Real.coe_toNNReal _ (integral_nonneg fun _ ↦ norm_nonneg _), ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hw.norm.mul_const _) (ae_of_all _ fun x ↦ ?_)
  rw [← smul_sub]
  exact (norm_smul_le _ _).trans
    (mul_le_mul_of_nonneg_left ((u - v).norm_coe_le_norm x) (norm_nonneg _))

/-- Integration against an integrable weight is continuous in the supremum norm. -/
theorem Integrable.continuous_integral_smul (hw : Integrable w μ) :
    Continuous fun u : α →ᵇ F ↦ ∫ x, w x • u x ∂μ :=
  hw.lipschitzWith_integral_smul.continuous

end MeasureTheory
