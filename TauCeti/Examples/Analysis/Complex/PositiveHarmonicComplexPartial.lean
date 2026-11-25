/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.Complex.Harmonic.ComplexPartial

/-!
# Complex partials in the Checks for positive harmonic functions on the half-plane

The Herglotz representation of a positive harmonic function `u` on the upper half-plane writes
`u = Im F` for a holomorphic `F` with `F' = i (∂ₓu - i ∂ᵧu)`, where `∂ₓu - i ∂ᵧu` is the complex
partial `fderiv ℝ u z 1 - I * fderiv ℝ u z I`
(`HasDerivAt.I_mul_fderiv_im_one_sub_I_mul_fderiv_im_I`). These examples compute the complex
partial for two positive harmonic functions on the upper half-plane, `Im z` and `P[δ₀]`:

* for `u = Im z`, the complex partial is `-i`, and `F' = i · (-i) = 1` is the derivative of
  `F = z`; the conjugate partial `∂ₓu + i ∂ᵧu = i` is not `F'`;
* for `u = P[δ₀] = Im (-1 / (π z))`, the complex partial is `-i / (π z²)`, and
  `F' = 1 / (π z²) = i (∂ₓu - i ∂ᵧu)` is the derivative of `F = -1 / (π z)`.
-/

public section

open Complex MeasureTheory TauCeti
open scoped Real

namespace TauCeti.PositiveHarmonicComplexPartialExamples

/-! ### `u = Im z` -/

-- The complex partial of `Im` is `-i`.
example (z : ℂ) :
    (fderiv ℝ (fun w : ℂ => w.im) z 1 : ℂ) - I * fderiv ℝ (fun w : ℂ => w.im) z I = -I := by
  have h : fderiv ℝ (fun w : ℂ => w.im) z = imCLM := imCLM.fderiv
  simp [h]

-- `F = z` has `Im F = Im z`, and `F' = 1 = i · (-i)`.
example (z : ℂ) :
    I * ((fderiv ℝ (fun w : ℂ => w.im) z 1 : ℂ) - I * fderiv ℝ (fun w : ℂ => w.im) z I) =
      deriv (fun w : ℂ => w) z := by
  rw [deriv_id'']
  exact (hasDerivAt_id' z).I_mul_fderiv_im_one_sub_I_mul_fderiv_im_I

-- The conjugate partial `∂ₓu + i ∂ᵧu` of `Im` is `i`, which is not `F' = 1`.
example (z : ℂ) :
    (fderiv ℝ (fun w : ℂ => w.im) z 1 : ℂ) + I * fderiv ℝ (fun w : ℂ => w.im) z I = I ∧
      I ≠ deriv (fun w : ℂ => w) z := by
  have h : fderiv ℝ (fun w : ℂ => w.im) z = imCLM := imCLM.fderiv
  refine ⟨by simp [h], by rw [deriv_id'']; exact fun h => by simpa using congrArg re h⟩

/-! ### `u = P[δ₀]` -/

/-- `F = -1 / (π z)` has derivative `1 / (π z²)` at `z ≠ 0`. -/
theorem hasDerivAt_neg_inv_pi_mul (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (fun w : ℂ => -((π : ℂ) * w)⁻¹) (1 / ((π : ℂ) * z ^ 2)) z := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have h1 : HasDerivAt (fun w : ℂ => (π : ℂ) * w) π z := by
    simpa using (hasDerivAt_id z).const_mul (π : ℂ)
  convert (h1.inv (mul_ne_zero hπ hz)).neg using 1
  field_simp

-- `F = -1 / (π z)` has `Im F = P[δ₀]` and `F' = 1 / (π z²) = i (∂ₓu - i ∂ᵧu)`.
example (z : ℂ) (hz : z ≠ 0) :
    I * ((fderiv ℝ (upperHalfPlanePoissonIntegral (Measure.dirac 0)) z 1 : ℂ) -
      I * fderiv ℝ (upperHalfPlanePoissonIntegral (Measure.dirac 0)) z I) =
        1 / ((π : ℂ) * z ^ 2) := by
  rw [upperHalfPlanePoissonIntegral_dirac_zero_eq_im]
  exact (hasDerivAt_neg_inv_pi_mul z hz).I_mul_fderiv_im_one_sub_I_mul_fderiv_im_I

-- The complex partial of `P[δ₀]` is `-i / (π z²)`.
example (z : ℂ) (hz : z ≠ 0) :
    (fderiv ℝ (upperHalfPlanePoissonIntegral (Measure.dirac 0)) z 1 : ℂ) -
      I * fderiv ℝ (upperHalfPlanePoissonIntegral (Measure.dirac 0)) z I =
        -I / ((π : ℂ) * z ^ 2) := by
  rw [upperHalfPlanePoissonIntegral_dirac_zero_eq_im]
  linear_combination (norm := (ring_nf; simp))
    -I * (hasDerivAt_neg_inv_pi_mul z hz).I_mul_fderiv_im_one_sub_I_mul_fderiv_im_I

end TauCeti.PositiveHarmonicComplexPartialExamples
