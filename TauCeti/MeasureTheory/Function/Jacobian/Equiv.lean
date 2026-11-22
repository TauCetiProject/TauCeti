/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Change of variables along a bijection of the whole space

For a bijection `φ` of a finite-dimensional real vector space whose inverse is differentiable,
Mathlib's change of variables formula
(`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`) applied to `φ⁻¹` on the whole
space reads `∫ g(φ x) dμ(x) = ∫ |det Dφ⁻¹(y)| • g(y) dμ(y)` for every function `g` and every
additive Haar measure `μ`, with no integrability assumption.

## Main results

* `TauCeti.integral_comp_equiv_eq_integral_abs_det_fderiv_symm_smul`: the change of variables
  formula along a bijection.
-/

public section

open MeasureTheory

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {φ : E ≃ E}

/-- **Change of variables along a bijection.** If `φ⁻¹` is differentiable, then
`∫ g(φ x) dμ(x) = ∫ |det Dφ⁻¹(y)| • g(y) dμ(y)` for every function `g`. No integrability is needed:
both sides are the two sides of the change of variables formula for `φ⁻¹`. -/
theorem integral_comp_equiv_eq_integral_abs_det_fderiv_symm_smul [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hψ : Differentiable ℝ φ.symm) (g : E → F) :
    ∫ x, g (φ x) ∂μ = ∫ y, |(fderiv ℝ φ.symm y).det| • g y ∂μ := by
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul μ MeasurableSet.univ
    (fun y _ ↦ (hψ y).hasFDerivAt.hasFDerivWithinAt) φ.symm.injective.injOn fun x ↦ g (φ x)
  rw [Set.image_univ_of_surjective φ.symm.surjective] at hcv
  simpa only [Measure.restrict_univ, Equiv.apply_symm_apply] using hcv

end TauCeti
