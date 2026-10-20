/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.MeasureTheory.Integral.PeakFunction

/-!
# Concentration of Gaussian densities

For `c > 0`, the function `t ↦ c exp (-(c t)²) / √π` is the density of the centred Gaussian law
of variance `(2 c²)⁻¹`, that is, of width `c⁻¹`. As `c → ∞` these densities concentrate at `0`:
for every integrable `g` continuous at `0`, `∫ t, c exp (-(c t)²) / √π • g t → g 0`. This is the
approximate-identity property used to smear elements along a one-parameter flow.

This file also records the complex Gaussian estimates needed to differentiate integrals against
the translated kernel `z ↦ exp (-(c (t - z))²)` under the integral sign: a Gaussian bound in `t`,
uniform for `z` in a ball, and the complex derivative in `z`.

## Main definitions

* `TauCeti.Real.gaussianDensity`: the function `t ↦ c exp (-(c t)²) / √π`.

## Main statements

* `TauCeti.Real.gaussianDensity_eq_gaussianPDFReal`: for `c > 0` it is Mathlib's Gaussian
  density `ProbabilityTheory.gaussianPDFReal` with mean `0` and variance `(2 c²)⁻¹`.
* `TauCeti.Real.integral_gaussianDensity`: for `c > 0` it has total mass one.
* `TauCeti.Real.tendsto_integral_gaussianDensity_smul`: the densities concentrate at `0` as
  `c → ∞`.
* `TauCeti.Complex.norm_cexp_neg_mul_sub_sq_le`: the Gaussian bound
  `‖exp (-(c (t - z))²)‖ ≤ exp (c² D²) exp (-(c² / 2) t²)` for `‖z‖ ≤ D`.
* `TauCeti.Complex.hasDerivAt_cexp_neg_mul_sub_sq`: the complex derivative of
  `z ↦ exp (-(c (t - z))²)`.
-/

public section

noncomputable section

open Complex MeasureTheory Filter Topology Real

namespace TauCeti

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
  have hv : (0 : ℝ) ≤ (2 * c ^ 2)⁻¹ := by positivity
  rw [gaussianDensity, ProbabilityTheory.gaussianPDFReal, Real.coe_toNNReal _ hv, sub_zero,
    show 2 * π * (2 * c ^ 2)⁻¹ = π / c ^ 2 by field_simp,
    Real.sqrt_div' _ (sq_nonneg c), Real.sqrt_sq hc.le,
    show -t ^ 2 / (2 * (2 * c ^ 2)⁻¹) = -(c * t) ^ 2 by field_simp]
  field_simp

/-- For `c > 0`, the Gaussian density of width `c⁻¹` has total mass one. -/
theorem integral_gaussianDensity {c : ℝ} (hc : 0 < c) : ∫ t, gaussianDensity c t = 1 := by
  rw [gaussianDensity_eq_gaussianPDFReal hc]
  refine ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 ?_
  simpa using pow_pos hc 2

/-- The Gaussian densities concentrate at `0` as their width tends to zero. -/
theorem tendsto_integral_gaussianDensity_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {g : ℝ → E} (hg : Integrable g)
    (h'g : ContinuousAt g 0) :
    Tendsto (fun c : ℝ => ∫ t, gaussianDensity c t • g t) atTop (𝓝 (g 0)) := by
  have h := tendsto_integral_comp_smul_smul_of_integrable (μ := volume)
    (φ := fun x : ℝ => (√π)⁻¹ * rexp (-x ^ 2)) (fun x => by positivity) ?_ ?_ hg h'g
  · simpa [gaussianDensity, Module.finrank_self, smul_eq_mul] using h
  · simpa [gaussianDensity] using integral_gaussianDensity one_pos
  · rw [Metric.cobounded_eq_cocompact]
    simpa [Module.finrank_self, mul_left_comm] using
      (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact one_pos 1).const_mul (√π)⁻¹

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

/-- The complex derivative of the translated Gaussian `z ↦ exp (-(c (t - z))²)`. -/
theorem hasDerivAt_cexp_neg_mul_sub_sq (c t : ℝ) (z : ℂ) :
    HasDerivAt (fun z : ℂ => cexp (-(c * (t - z)) ^ 2))
      (cexp (-(c * (t - z)) ^ 2) * (2 * c ^ 2 * (t - z))) z := by
  have h := (((hasDerivAt_id' z).const_sub (t : ℂ)).const_mul (c : ℂ)).fun_pow 2 |>.fun_neg.cexp
  convert h using 1
  ring

end Complex

end TauCeti
