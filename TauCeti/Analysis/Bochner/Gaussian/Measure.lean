/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Bochner.BochnerTheorem
public import TauCeti.Analysis.Bochner.Gaussian.Basic
import TauCeti.Analysis.Bochner.Fourier.Convention

/-!
# The Bochner measure of a Gaussian

This file identifies the measure in Bochner's theorem for the Gaussian positive-definite
function

`a ↦ exp (-c ‖a‖²)`.

With the Fourier convention `exp (-2πi⟪a, q⟫)`, its representing measure is the image of the
standard Gaussian under the dilation

`q ↦ (√(2c) / (2π)) q`.

The endpoint `c = 0` is included: the dilation is then constant, so its image is the Dirac mass at
the origin, representing the constant function `1`.

## Main declarations

* `TauCeti.integral_fourierAtom_map_smul_stdGaussian`: the Fourier transform of the dilated
  standard Gaussian.
* `TauCeti.map_smul_stdGaussian_eq_bochnerMeasure_cexp_neg_mul_sq_norm`: identification with the
  canonical measure chosen by Bochner's theorem.
* `TauCeti.map_smul_stdGaussian_eq_bochnerMeasure_cexp_neg_sq_norm`: the specialization `c = 1`.

## References

* W. Rudin, *Fourier Analysis on Groups* (1962), Chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier-convention transform of the standard Gaussian dilated by `√(2c) / (2π)` is
`a ↦ exp (-c ‖a‖²)`. -/
theorem integral_fourierAtom_map_smul_stdGaussian {c : ℝ} (hc : 0 ≤ c) (a : V) :
    ∫ q, fourierAtom a q
        ∂(stdGaussian V).map ((Real.sqrt (2 * c) / (2 * Real.pi)) • ·) =
      Complex.exp (-(c * ‖a‖ ^ 2 : ℝ)) := by
  rw [integral_fourierAtom_eq_charFun_neg_two_pi_smul,
    MeasureTheory.charFun_map_smul, charFun_stdGaussian]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hscale :
      (Real.sqrt (2 * c) / (2 * Real.pi)) * (-2 * Real.pi) = -Real.sqrt (2 * c) := by
    field_simp [hpi]
  have hnorm :
      ‖(Real.sqrt (2 * c) / (2 * Real.pi)) • ((-2 * Real.pi) • a)‖ ^ 2 =
        2 * c * ‖a‖ ^ 2 := by
    rw [smul_smul, hscale, neg_smul, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by positivity)]
  have hnorm_complex :
      (‖(Real.sqrt (2 * c) / (2 * Real.pi)) • ((-2 * Real.pi) • a)‖ : ℂ) ^ 2 =
        (2 * c * ‖a‖ ^ 2 : ℝ) := by
    exact_mod_cast hnorm
  rw [hnorm_complex]
  congr 1
  push_cast
  ring

/-- The Bochner measure of `a ↦ exp (-c ‖a‖²)` is the standard Gaussian dilated by
`√(2c) / (2π)`. -/
theorem map_smul_stdGaussian_eq_bochnerMeasure_cexp_neg_mul_sq_norm {c : ℝ} (hc : 0 ≤ c) :
    (stdGaussian V).map ((Real.sqrt (2 * c) / (2 * Real.pi)) • ·) =
      bochnerMeasure (fun a : V => Complex.exp (-(c * ‖a‖ ^ 2 : ℝ))) :=
  eq_bochnerMeasure _ fun a => (integral_fourierAtom_map_smul_stdGaussian hc a).symm

/-- The Bochner measure of the Gaussian acceptance example `a ↦ exp (-‖a‖²)` is the standard
Gaussian dilated by `√2 / (2π)`. -/
theorem map_smul_stdGaussian_eq_bochnerMeasure_cexp_neg_sq_norm :
    (stdGaussian V).map ((Real.sqrt 2 / (2 * Real.pi)) • ·) =
      bochnerMeasure (fun a : V => Complex.exp (-(‖a‖ ^ 2 : ℝ))) := by
  simpa only [one_mul, mul_one] using
    (map_smul_stdGaussian_eq_bochnerMeasure_cexp_neg_mul_sq_norm (V := V) (c := 1) zero_le_one)

end TauCeti

end
