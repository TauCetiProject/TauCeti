/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import TauCeti.Analysis.Calculus.ContDiff.FDerivApply

/-!
# `Lᵖ` seminorms of derivatives

The sum `‖u‖_{Lᵖ} + ‖Du‖_{Lᵖ}` of the `Lᵖ` seminorms of a function and of its derivative, the
`W^{1,p}` seminorm of a differentiable function, satisfies the triangle inequality for
differences of almost everywhere differentiable functions
(`TauCeti.eLpNorm_sub_add_eLpNorm_fderiv_sub_le`). The `Lᵖ` seminorm of a directional derivative
`x ↦ Du(x) v` is at most `‖v‖ ‖Du‖_{Lᵖ}` (`TauCeti.eLpNorm_fderiv_apply_le`).

Let `a : E → (F →L[ℝ] F')` be a `C¹` field of operators that is `K`-Lipschitz. Its derivative is
bounded by `K`, so for every direction `v` the multiplication operator `u ↦ (∂ᵥ a) u` is bounded on
`Lᵖ` with norm at most `K ‖v‖`: `‖x ↦ fderiv a x v (u x)‖_p ≤ K ‖v‖ ‖u‖_p`
(`LipschitzWith.eLpNorm_fderiv_apply_apply_le`). This is the bound for the first-order term in the
product rule `∂ᵥ (a u) = (∂ᵥ a) u + a ∂ᵥ u`.

## Main results

* `TauCeti.eLpNorm_sub_add_eLpNorm_fderiv_sub_le`: the triangle inequality for the `W^{1,p}`
  seminorm `‖u‖_{Lᵖ} + ‖Du‖_{Lᵖ}` of almost everywhere differentiable functions.
* `TauCeti.eLpNorm_fderiv_apply_le`: the `Lᵖ` bound `‖∂ᵥ u‖_{Lᵖ} ≤ ‖v‖ ‖Du‖_{Lᵖ}` for a
  directional derivative.
* `LipschitzWith.eLpNorm_fderiv_apply_apply_le`: the `Lᵖ` bound for the directional derivative of
  a `C¹` Lipschitz field of operators applied to a function.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [MeasurableSpace E]

/-- The `W^{1,p}` seminorm `‖u‖_{Lᵖ} + ‖Du‖_{Lᵖ}` of a difference of maps that are differentiable
almost everywhere is at most the sum of their seminorms. -/
theorem eLpNorm_sub_add_eLpNorm_fderiv_sub_le {ν : Measure E} {q : ℝ≥0∞} (hq : 1 ≤ q)
    {u₁ u₂ : E → F} (hu₁ : ∀ᵐ x ∂ν, DifferentiableAt 𝕜 u₁ x)
    (hu₂ : ∀ᵐ x ∂ν, DifferentiableAt 𝕜 u₂ x) :
    eLpNorm (u₁ - u₂) q ν + eLpNorm (fderiv 𝕜 (u₁ - u₂)) q ν ≤
      eLpNorm u₁ q ν + eLpNorm (fderiv 𝕜 u₁) q ν +
        (eLpNorm u₂ q ν + eLpNorm (fderiv 𝕜 u₂) q ν) := by
  have hfd : fderiv 𝕜 (u₁ - u₂) =ᵐ[ν] fderiv 𝕜 u₁ - fderiv 𝕜 u₂ := by
    filter_upwards [hu₁, hu₂] with x hx₁ hx₂ using fderiv_sub hx₁ hx₂
  calc _ ≤ eLpNorm u₁ q ν + eLpNorm u₂ q ν +
        (eLpNorm (fderiv 𝕜 u₁) q ν + eLpNorm (fderiv 𝕜 u₂) q ν) := by
        gcongr
        · exact eLpNorm_sub_le hq
        · rw [eLpNorm_congr_ae hfd]
          exact eLpNorm_sub_le hq
    _ = _ := by ring

/-- The `Lᵖ` seminorm of the directional derivative `x ↦ Du(x) v` is at most `‖v‖` times the `Lᵖ`
seminorm of the derivative `Du`. -/
theorem eLpNorm_fderiv_apply_le {ν : Measure E} {u : E → F}
    (hu : AEStronglyMeasurable (fderiv 𝕜 u) ν) (v : E) (q : ℝ≥0∞) :
    eLpNorm (fun x ↦ fderiv 𝕜 u x v) q ν ≤ ‖v‖ₑ * eLpNorm (fderiv 𝕜 u) q ν := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' q ?_ (.of_forall fun x ↦ ?_)
  · exact (ContinuousLinearMap.apply 𝕜 F v).continuous.comp_aestronglyMeasurable hu
  · exact ((fderiv 𝕜 u x).le_opENorm v).trans_eq (mul_comm _ _)

end TauCeti

variable {E F F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [SecondCountableTopology E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {μ : Measure E} {a : E → F →L[ℝ] F'} {K : ℝ≥0}

namespace LipschitzWith

/-- **The directional derivative of a Lipschitz field of operators on `Lᵖ`.** If
`a : E → F →L[ℝ] F'` is `C¹` and `K`-Lipschitz, then `‖(∂ᵥ a) u‖_p ≤ K ‖v‖ ‖u‖_p`. -/
theorem eLpNorm_fderiv_apply_apply_le (haK : LipschitzWith K a) (ha : ContDiff ℝ 1 a) {u : E → F}
    (hu : AEStronglyMeasurable u μ) (v : E) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ fderiv ℝ a x v (u x)) p μ ≤ K * ‖v‖ₑ * eLpNorm u p μ := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
  · exact (ContinuousLinearMap.id ℝ (F →L[ℝ] F')).aestronglyMeasurable_comp₂
      (ha.continuous_fderiv_apply_const one_ne_zero v).aestronglyMeasurable hu
  · have hda : ‖fderiv ℝ a x‖ₑ ≤ K := by
      rw [eNorm_eq_nnNorm]
      exact_mod_cast norm_fderiv_le_of_lipschitz ℝ haK
    calc ‖fderiv ℝ a x v (u x)‖ₑ ≤ ‖fderiv ℝ a x‖ₑ * ‖v‖ₑ * ‖u x‖ₑ :=
          ((fderiv ℝ a x v).le_opENorm _).trans (by gcongr; exact (fderiv ℝ a x).le_opENorm v)
      _ ≤ K * ‖v‖ₑ * ‖u x‖ₑ := by gcongr

end LipschitzWith
