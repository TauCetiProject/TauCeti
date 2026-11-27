/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import TauCeti.Analysis.Complex.RealChart

/-!
# Change of variables in the plane for densities scaling by the Jacobian

A density `f` on a region `s` of `ℝ × ℝ` that is `|det dφ|` times `g ∘ φ`, for an injective
differentiable change of coordinates `φ`, is integrable on `s` exactly when `g` is integrable on
`φ '' s`, and has the same integral over `s` as `g` over `φ '' s`. If
instead `f` is the signed `det dφ` times `g ∘ φ`, then the lower Lebesgue integral of `‖f‖ₑ` over
`s` equals that of `‖g‖ₑ` over `φ '' s`, without any orientation assumption. This packages
Mathlib's change of variables formula
(`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`) for Lebesgue measure on the
plane, where densities of this kind arise as coefficients of two-forms.

## Main results

* `TauCeti.integral_image_eq_integral_of_eq_abs_det_smul`,
  `TauCeti.integrableOn_image_iff_of_eq_abs_det_smul`: the Bochner integral and the integrability
  of a density scaling by `|det dφ|`.
* `TauCeti.setIntegral_det_mul_comp_le_integral`: for a nonnegative Jacobian and a nonnegative
  integrable `g`, the integral of `det dφ · g ∘ φ` over `s` is at most the integral of `g`.
* `TauCeti.lintegral_enorm_image_eq_lintegral_enorm_of_eq_det_smul`: the lower Lebesgue integral
  of the size of a density scaling by `det dφ`.
* `TauCeti.lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul`: the lower Lebesgue
  integral of the positive part of a real density scaling by `|det dφ|`.
* `TauCeti.Complex.setIntegral_image_realChart_inv`: the change of variables along the inversion
  `ζ ↦ ζ⁻¹` in real coordinates, whose Jacobian is `|ζ⁻¹|⁴`.
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

/-- **Change of variables for the integrability of a density.** If a density `f` on a measurable
set `s` is `|det dφ|` times `g ∘ φ`, for a change of coordinates `φ` that is injective and
differentiable on `s`, then `g` is integrable on `φ '' s` exactly when `f` is integrable on `s`. -/
theorem integrableOn_image_iff_of_eq_abs_det_smul (hs : MeasurableSet s) (hinj : InjOn φ s)
    (hφ : ∀ w ∈ s, DifferentiableAt ℝ φ w)
    (hf : ∀ w ∈ s, f w = |(fderiv ℝ φ w).det| • g (φ w)) :
    IntegrableOn g (φ '' s) ↔ IntegrableOn f s := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (fun w hw ↦ (hφ w hw).hasFDerivAt.hasFDerivWithinAt) hinj]
  exact integrableOn_congr_fun (fun w hw ↦ (hf w hw).symm) hs

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
  rw [hf w hw, eNorm_smul, Real.eNorm_eq_ofReal_abs]

/-- **Change of variables for the positive part of a density.** If a real density `f` on a
measurable set `s` is `|det dφ|` times `g ∘ φ`, for a change of coordinates `φ` that is injective
and differentiable on `s`, then the lower Lebesgue integral of the positive part of `g` over
`φ '' s` is that of `f` over `s`. No integrability or measurability hypothesis is needed. -/
theorem lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul {f g : ℝ × ℝ → ℝ}
    (hs : MeasurableSet s) (hinj : InjOn φ s) (hφ : ∀ w ∈ s, DifferentiableAt ℝ φ w)
    (hf : ∀ w ∈ s, f w = |(fderiv ℝ φ w).det| * g (φ w)) :
    ∫⁻ z in φ '' s, ENNReal.ofReal (g z) = ∫⁻ w in s, ENNReal.ofReal (f w) := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun w hw ↦ (hφ w hw).hasFDerivAt.hasFDerivWithinAt) hinj]
  refine setLIntegral_congr_fun hs fun w hw ↦ ?_
  rw [hf w hw, ENNReal.ofReal_mul (abs_nonneg _)]

/-- **Change of variables as an inequality.** For a change of coordinates `φ` that is injective and
differentiable on a measurable set `s`, with nonnegative Jacobian there, and a nonnegative
integrable function `g`, the integral of `det dφ · g ∘ φ` over `s` is at most the integral of `g`:
it is the integral of `g` over `φ '' s`. -/
theorem setIntegral_det_mul_comp_le_integral {g : ℝ × ℝ → ℝ} (hs : MeasurableSet s)
    (hinj : InjOn φ s) (hφ : ∀ w ∈ s, DifferentiableAt ℝ φ w)
    (hdet : ∀ w ∈ s, 0 ≤ (fderiv ℝ φ w).det) (hg : ∀ z, 0 ≤ g z) (hgi : Integrable g) :
    ∫ w in s, (fderiv ℝ φ w).det * g (φ w) ≤ ∫ z, g z := by
  rw [← integral_image_eq_integral_of_eq_abs_det_smul hs hinj hφ fun w hw ↦ by
    rw [abs_of_nonneg (hdet w hw), smul_eq_mul]]
  exact setIntegral_le_integral hgi (ae_of_all _ hg)

namespace Complex

/-- **Changing variables along the inversion.** On a measurable set `S` avoiding `ζ = 0`, the
integral of `g` over the image of `S` under the inversion `ζ ↦ ζ⁻¹` is the integral over `S` of
`|ζ⁻¹|⁴ g(ζ⁻¹)`, the Jacobian of the inversion being `|ζ⁻¹|⁴`. -/
theorem setIntegral_image_realChart_inv {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hS0 : ∀ ζ ∈ S, Complex.equivRealProdCLM.symm ζ ≠ 0) (g : ℝ × ℝ → ℝ) :
    ∫ w in realChart (·⁻¹) '' S, g w =
      ∫ ζ in S, ‖Complex.equivRealProdCLM.symm (realChart (·⁻¹) ζ)‖ ^ 4 *
        g (realChart (·⁻¹) ζ) :=
  integral_image_eq_integral_of_eq_abs_det_smul hS realChart_inv_involutive.injective.injOn
    (fun ζ hζ ↦ (contDiffAt_realChart_inv (hS0 ζ hζ) (n := 1)).differentiableAt one_ne_zero)
    fun ζ hζ ↦ by
      rw [det_fderiv_realChart_inv (hS0 ζ hζ), abs_of_nonneg (by positivity), smul_eq_mul]

end Complex

end TauCeti
