/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Change of variables in the plane for densities scaling by the Jacobian

A density `f` on a region `s` of `ℝ × ℝ` that is `|det dφ|` times `g ∘ φ`, for an injective
differentiable change of coordinates `φ`, has the same integral over `s` as `g` over `φ '' s`. If
instead `f` is the signed `det dφ` times `g ∘ φ`, then the lower Lebesgue integral of `‖f‖ₑ` over
`s` equals that of `‖g‖ₑ` over `φ '' s`, without any orientation assumption. This packages
Mathlib's change of variables formula
(`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`) for Lebesgue measure on the
plane, where densities of this kind arise as coefficients of two-forms.

## Main results

* `TauCeti.integral_image_eq_integral_of_eq_abs_det_smul`: the Bochner integral of a density
  scaling by `|det dφ|`.
* `TauCeti.lintegral_enorm_image_eq_lintegral_enorm_of_eq_det_smul`: the lower Lebesgue integral
  of the size of a density scaling by `det dφ`.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : ℝ × ℝ → ℝ × ℝ}
  {s : Set (ℝ × ℝ)} {f g : ℝ × ℝ → F}

/-- **Change of variables for a density.** If a density `f` on a measurable set `s` is
`|det dφ|` times `g ∘ φ`, for a change of coordinates `φ` that is injective and differentiable on
`s`, then the integral of `g` over `φ '' s` is the integral of `f` over `s`. -/
theorem integral_image_eq_integral_of_eq_abs_det_smul (hs : MeasurableSet s) (hinj : InjOn φ s)
    (hφ : ∀ w ∈ s, DifferentiableAt ℝ φ w)
    (hf : ∀ w ∈ s, f w = |(fderiv ℝ φ w).det| • g (φ w)) :
    ∫ z in φ '' s, g z = ∫ w in s, f w := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun w hw ↦ (hφ w hw).hasFDerivAt.hasFDerivWithinAt) hinj]
  exact setIntegral_congr_fun hs fun w hw ↦ (hf w hw).symm

/-- **Change of variables for the size of a density.** If a density `f` on a measurable set `s`
is `det dφ` times `g ∘ φ`, for a change of coordinates `φ` that is injective and differentiable
on `s`, then the lower Lebesgue integral of `‖g‖ₑ` over `φ '' s` is that of `‖f‖ₑ` over `s`. No
orientation, integrability or measurability hypothesis is needed. -/
theorem lintegral_enorm_image_eq_lintegral_enorm_of_eq_det_smul (hs : MeasurableSet s)
    (hinj : InjOn φ s) (hφ : ∀ w ∈ s, DifferentiableAt ℝ φ w)
    (hf : ∀ w ∈ s, f w = (fderiv ℝ φ w).det • g (φ w)) :
    ∫⁻ z in φ '' s, ‖g z‖ₑ = ∫⁻ w in s, ‖f w‖ₑ := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun w hw ↦ (hφ w hw).hasFDerivAt.hasFDerivWithinAt) hinj]
  refine setLIntegral_congr_fun hs fun w hw ↦ ?_
  rw [hf w hw, enorm_smul, Real.enorm_eq_ofReal_abs]

end TauCeti
