/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian densities and complex-kernel estimates

For `c > 0`, the function `t ↦ c exp (-(c t)²) / √π` is the density of the centred Gaussian law
of variance `(2 c²)⁻¹`, that is, of width `c⁻¹`. This file identifies the density with
Mathlib’s Gaussian probability density and records that its total mass is one.

This file also records the complex Gaussian estimates needed to differentiate integrals against
the translated kernel `z ↦ exp (-(c (t - z))²)` under the integral sign: a Gaussian bound in `t`,
uniform for `z` in a ball, and the complex derivative in `z`.

## Main definitions

* `Real.gaussianDensity`: the function `t ↦ c exp (-(c t)²) / √π`.

## Main statements

* `Real.gaussianDensity_eq_gaussianPDFReal`: for `c > 0` it is Mathlib's Gaussian
  density `ProbabilityTheory.gaussianPDFReal` with mean `0` and variance `(2 c²)⁻¹`.
* `Real.integral_gaussianDensity`: for `c > 0` it has total mass one.
* `Complex.norm_cexp_neg_mul_sub_sq_le`: the Gaussian bound
  `‖exp (-(c (t - z))²)‖ ≤ exp (c² D²) exp (-(c² / 2) t²)` for `‖z‖ ≤ D`.
* `Complex.hasDerivAt_cexp_neg_mul_sub_sq`: the complex derivative of
  `z ↦ exp (-(c (t - z))²)`, for complex `c` and `t`.
* `Complex.hasDerivAt_cexp_neg_add_sq_div_two`: the complex derivative of
  `w ↦ exp (-(z + w)² / 2)`.
-/

public section

noncomputable section

open Complex MeasureTheory Real

namespace Real

/-- The real Gaussian density `t ↦ c exp (-(c t)²) / √π` of width `c⁻¹`. It is odd in `c`, and
for `c > 0` it is the density of the centred Gaussian law of variance `(2 c²)⁻¹`. -/
def gaussianDensity (c t : ℝ) : ℝ := c * ((√π)⁻¹ * rexp (-(c * t) ^ 2))

/-- The defining formula of the Gaussian density. -/
theorem gaussianDensity_def (c t : ℝ) :
    gaussianDensity c t = c * ((√π)⁻¹ * rexp (-(c * t) ^ 2)) := by
  rw [gaussianDensity]

/-- For `c ≥ 0` the Gaussian density is nonnegative. -/
theorem gaussianDensity_nonneg {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : 0 ≤ gaussianDensity c t := by
  rw [gaussianDensity]
  positivity

/-- For `c > 0`, the Gaussian density of width `c⁻¹` is the centred Gaussian probability density
of variance `(2 c²)⁻¹`. -/
theorem gaussianDensity_eq_gaussianPDFReal {c : ℝ} (hc : 0 < c) :
    gaussianDensity c = ProbabilityTheory.gaussianPDFReal 0 (2 * c ^ 2)⁻¹.toNNReal := by
  ext t
  simp [gaussianDensity, ProbabilityTheory.gaussianPDFReal, hc.le]
  field_simp

/-- For `c > 0`, the Gaussian density of width `c⁻¹` has total mass one. -/
theorem integral_gaussianDensity {c : ℝ} (hc : 0 < c) : ∫ t, gaussianDensity c t = 1 := by
  rw [gaussianDensity_eq_gaussianPDFReal hc]
  exact ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 (by positivity)

end Real

namespace Complex

/-- The Gaussian bound `‖exp (-(c (t - z))²)‖ ≤ exp (c² D²) exp (-(c² / 2) t²)` for `‖z‖ ≤ D`. -/
theorem norm_cexp_neg_mul_sub_sq_le (c t : ℝ) {z : ℂ} {D : ℝ} (hz : ‖z‖ ≤ D) :
    ‖cexp (-(c * (t - z)) ^ 2)‖ ≤ rexp (c ^ 2 * D ^ 2) * rexp (-(c ^ 2 / 2) * t ^ 2) := by
  have hz' : ‖z‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  rw [norm_exp, ← Real.exp_add, Real.exp_le_exp]
  rw [Complex.sq_norm, normSq_apply] at hz'
  simp only [sq, neg_re, mul_re, mul_im, sub_re, sub_im, ofReal_re, ofReal_im] at hz' ⊢
  nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg (t - 2 * z.re)), mul_le_mul_of_nonneg_left hz'
    (sq_nonneg c)]

/-- The complex derivative of the translated Gaussian `z ↦ exp (-(c (t - z))²)`, for complex
scale `c` and centre `t`. -/
theorem hasDerivAt_cexp_neg_mul_sub_sq (c t z : ℂ) :
    HasDerivAt (fun z : ℂ => cexp (-(c * (t - z)) ^ 2))
      (cexp (-(c * (t - z)) ^ 2) * (2 * c ^ 2 * (t - z))) z := by
  have h := (((hasDerivAt_id' z).const_sub t).const_mul c).fun_pow 2 |>.fun_neg.cexp
  convert h using 1
  ring

/-- The complex derivative of the translated Gaussian `w ↦ exp (-(z + w)² / 2)`: it is
`-(z + w) exp (-(z + w)² / 2)`. This is `Complex.hasDerivAt_cexp_neg_mul_sub_sq` at scale
`1 / √2` and centre `0`, composed with the translation `w ↦ z + w`. -/
theorem hasDerivAt_cexp_neg_add_sq_div_two (z w : ℂ) :
    HasDerivAt (fun v : ℂ => cexp (-((z + v) ^ 2) / 2)) (cexp (-((z + w) ^ 2) / 2) * -(z + w))
      w := by
  have hc : ((√2 : ℝ) : ℂ)⁻¹ ^ 2 = 1 / 2 := by
    rw [inv_pow, ← ofReal_pow, Real.sq_sqrt zero_le_two, ofReal_ofNat, one_div]
  -- At scale `1 / √2` and centre `0` the Gaussian exponent is `-u² / 2`.
  have hexp (u : ℂ) : -(((√2 : ℝ) : ℂ)⁻¹ * (0 - u)) ^ 2 = -(u ^ 2) / 2 := by
    rw [mul_pow, hc]
    ring
  have h := (hasDerivAt_cexp_neg_mul_sub_sq ((√2 : ℝ) : ℂ)⁻¹ 0 (z + w)).comp w
    ((hasDerivAt_id' w).const_add z)
  simp only [Function.comp_def, hexp, hc] at h
  convert h using 1
  ring

end Complex
