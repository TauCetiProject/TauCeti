/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import TauCeti.Analysis.Calculus.ContDiff.FDerivApply

/-!
# Directional derivatives of Lipschitz operator fields on `Lᵖ`

Let `a : E → (F →L[ℝ] F')` be a `C¹` field of operators that is `K`-Lipschitz. Its derivative is
bounded by `K`, so for every direction `v` the multiplication operator `u ↦ (∂ᵥ a) u` is bounded on
`Lᵖ` with norm at most `K ‖v‖`: `‖x ↦ fderiv a x v (u x)‖_p ≤ K ‖v‖ ‖u‖_p`
(`LipschitzWith.eLpNorm_fderiv_apply_apply_le`). This is the bound for the first-order term in the
product rule `∂ᵥ (a u) = (∂ᵥ a) u + a ∂ᵥ u`.

## Main results

* `LipschitzWith.eLpNorm_fderiv_apply_apply_le`: the `Lᵖ` bound for the directional derivative of
  a `C¹` Lipschitz field of operators applied to a function.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

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
