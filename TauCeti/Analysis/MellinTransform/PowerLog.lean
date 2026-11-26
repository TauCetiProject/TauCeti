/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.LaplaceTransform.Elementary
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Upper Mellin integrals of powers and logarithms

On `(1, ∞)`, the integral of `y ^ p * (log y) ^ k` converges absolutely exactly when
`Re p < -1`, and is `k! / (-(p + 1)) ^ (k + 1)`. With `y = exp u` the integrand,
including the Jacobian, becomes an exponentially damped monomial. The affine-logarithm
case evaluates the elementary terms in smoothed prime sums: `y * (c - log y)` at a pole at
one and `a + b * log y` for the contribution at zero.

The main-term application occurs in Levent Alpöge's `Deduction.mellin_Gchi_modOne`
(<https://github.com/leanprover-community/riemann-hypothesis>). Here the evaluation uses the
one-sided Laplace transform of a monomial, for arbitrary complex power and natural log degree.
-/

public section

open MeasureTheory Set TauCeti

namespace Complex

private theorem powerLog_exp_pullback (p : ℂ) (k : ℕ) (u : ℝ) :
    Real.exp u • (((Real.exp u : ℝ) : ℂ) ^ p * (Real.log (Real.exp u) : ℂ) ^ k) =
      Complex.exp ((p + 1) * u) * (u : ℂ) ^ k := by
  rw [Real.log_exp, Complex.real_smul, ofReal_exp_cpow, Complex.ofReal_exp,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The upper-tail logarithmic moment of a complex power is absolutely convergent exactly when
its power has real part strictly below `-1`. -/
@[simp]
theorem integrableOn_cpow_mul_log_pow_Ioi_one_iff (p : ℂ) (k : ℕ) :
    IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ p * (Real.log y : ℂ) ^ k) (Ioi 1) ↔
      p.re < -1 := by
  conv_lhs => rw [← Real.exp_zero, ← integrableOn_comp_exp_Ioi]
  simp only [powerLog_exp_pullback]
  constructor
  · intro hi
    -- For `u > 1`, the power of `u` cannot improve integrability of the exponential.
    have hnorm := (hi.mono_set (Ioi_subset_Ioi zero_le_one)).norm
    have hdecay : IntegrableOn (fun u : ℝ ↦ Real.exp ((p.re + 1) * u)) (Ioi 1) := by
      refine Integrable.mono' hnorm (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu' : 1 ≤ u := le_of_lt (mem_Ioi.mp hu)
      rw [norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg (zero_le_one.trans hu'), Real.norm_of_nonneg (Real.exp_pos _).le]
      simp only [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero,
        Complex.add_re, Complex.one_re]
      exact le_mul_of_one_le_right (Real.exp_pos _).le (one_le_pow₀ hu')
    linarith [integrableOn_exp_mul_Ioi_iff.mp hdecay]
  · intro hp
    have hs : 0 < (-(p + 1)).re := by
      simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
      linarith
    simpa only [neg_neg, smul_eq_mul] using (hasLaplace_pow k hs).integrableOn

/-- For `Re p < -1`, the integral of `y ^ p * (log y) ^ k` over `(1, ∞)` is
`k! / (-(p + 1)) ^ (k + 1)`. -/
theorem integral_cpow_mul_log_pow_Ioi_one {p : ℂ} (hp : p.re < -1) (k : ℕ) :
    ∫ y in Ioi (1 : ℝ), (y : ℂ) ^ p * (Real.log y : ℂ) ^ k =
      (k.factorial : ℂ) / (-(p + 1)) ^ (k + 1) := by
  rw [← Real.exp_zero, ← integral_comp_exp_Ioi]
  simp only [powerLog_exp_pullback]
  have hs : 0 < (-(p + 1)).re := by
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    linarith
  simpa only [neg_neg, smul_eq_mul] using (hasLaplace_pow k hs).integral_eq

private theorem cpow_mul_affine_log_eq (p a b : ℂ) (y : ℝ) :
    (y : ℂ) ^ p * (a + b * (Real.log y : ℂ)) =
      a * ((y : ℂ) ^ p * (Real.log y : ℂ) ^ 0) + b * ((y : ℂ) ^ p * (Real.log y : ℂ) ^ 1) := by
  simp only [pow_zero, pow_one, mul_one]
  ring

/-- An affine polynomial in `log y`, multiplied by a complex power with real part less than
`-1`, is integrable over `(1, ∞)`. -/
theorem integrableOn_cpow_mul_affine_log_Ioi_one (a b : ℂ) {p : ℂ} (hp : p.re < -1) :
    IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ p * (a + b * (Real.log y : ℂ))) (Ioi 1) := by
  have h0 := (integrableOn_cpow_mul_log_pow_Ioi_one_iff p 0).mpr hp
  have h1 := (integrableOn_cpow_mul_log_pow_Ioi_one_iff p 1).mpr hp
  exact ((h0.const_mul a).add (h1.const_mul b)).congr (.of_forall fun y ↦
    (cpow_mul_affine_log_eq p a b y).symm)

/-- The upper-tail integral of a complex power times `a + b * log y` is the sum of a simple
and a double reciprocal power at `p = -1`. -/
theorem integral_cpow_mul_affine_log_Ioi_one (a b : ℂ) {p : ℂ} (hp : p.re < -1) :
    ∫ y in Ioi (1 : ℝ), (y : ℂ) ^ p * (a + b * (Real.log y : ℂ)) =
      a / (-(p + 1)) + b / (-(p + 1)) ^ 2 := by
  have h0 := (integrableOn_cpow_mul_log_pow_Ioi_one_iff p 0).mpr hp
  have h1 := (integrableOn_cpow_mul_log_pow_Ioi_one_iff p 1).mpr hp
  simp_rw [cpow_mul_affine_log_eq]
  rw [integral_add (h0.const_mul a) (h1.const_mul b), integral_const_mul, integral_const_mul,
    integral_cpow_mul_log_pow_Ioi_one hp 0, integral_cpow_mul_log_pow_Ioi_one hp 1]
  simp [div_eq_mul_inv]

end Complex
