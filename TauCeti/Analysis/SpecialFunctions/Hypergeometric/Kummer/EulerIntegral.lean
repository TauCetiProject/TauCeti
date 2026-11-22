/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Contiguous

/-!
# Kummer's integral for the regularized confluent hypergeometric function

Write `𝐌(a, b, z) = Complex.regularizedHGFun {a} {b} z = ∑ (a)ₙ zⁿ / (n! Γ(b + n))` for Olver's
regularized Kummer function. When `0 < re a < re b`, it has the integral representation
(DLMF 13.4.1)

`Γ(a) Γ(b - a) 𝐌(a, b, z) = ∫₀¹ t ^ (a - 1) (1 - t) ^ (b - a - 1) e^{z t} dt`

for every complex `z`, with principal powers of the positive reals `t` and `1 - t`. Expanding
`e^{z t}` in its power series and integrating term by term against the Beta weight turns the
`n`-th term into `zⁿ / n!` times the Beta integral `B(a + n, b - a)`, which is the `n`-th term of
`Γ(a) Γ(b - a) 𝐌(a, b, z)`. The interchange is dominated convergence: the exponential series is
dominated by `e^{‖z‖}` on `[0, 1]`.

This is the confluent limit of Euler's integral for the Gauss function,
`Complex.regularizedGaussHGFun_eq_eulerIntegral`, and the integral representation behind the
Whittaker function `M_{κ,μ}`.

## Main results

* `Complex.regularizedHGFun_singleton_eq_integral` — Kummer's integral (DLMF 13.4.1).

## References

* *NIST Digital Library of Mathematical Functions*, [§13.4](https://dlmf.nist.gov/13.4),
  equation 13.4.1.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Nat

namespace Complex

/-- The `n`-th term of the exponential series integrated against the Beta weight is the `n`-th
term of the Kummer series. -/
private theorem inv_Gamma_mul_integral_mul_pow_div_factorial {a b : ℂ} (ha : 0 < a.re)
    (hab : a.re < b.re) (z : ℂ) (n : ℕ) :
    (Gamma a * Gamma (b - a))⁻¹ *
        (∫ t : ℝ in 0..1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) *
          ((z * t) ^ n / n !)) =
      regularizedHGFunCoeff {a} {b} n * z ^ n := by
  have hba : 0 < (b - a).re := by simpa using sub_pos.mpr hab
  have hint :
      (∫ t : ℝ in 0..1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) *
          ((z * t) ^ n / n !)) =
        z ^ n / n ! * betaIntegral (a + n) (b - a) := by
    rw [betaIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le zero_le_one] at ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    have hpow : (t : ℂ) ^ (a - 1) * (t : ℂ) ^ n = (t : ℂ) ^ (a + n - 1) := by
      rw [← cpow_natCast, ← cpow_add _ _ ht0, sub_add_eq_add_sub]
    rw [mul_pow]
    linear_combination z ^ n / n ! * (1 - (t : ℂ)) ^ (b - a - 1) * hpow
  have han : 0 < (a + n).re := by
    simp only [add_re, natCast_re]
    linarith [n.cast_nonneg (α := ℝ)]
  have hpoch := Gamma_add_nat_div_Gamma_eq (n := n) a (ne_neg_natCast_of_re_pos ha)
  have hsum : a + (n : ℂ) + (b - a) = b + n := by ring
  rw [hint, betaIntegral_eq_Gamma_mul_div (a + n) (b - a) han hba, hsum,
    regularizedHGFunCoeff_singleton, ← hpoch]
  field_simp [Gamma_ne_zero_of_re_pos ha, Gamma_ne_zero_of_re_pos hba]

/-- **Kummer's integral** (DLMF 13.4.1): when `0 < re a < re b`, the regularized Kummer function
is the normalized Beta-weighted Laplace-type integral
`𝐌(a, b, z) = (Γ(a) Γ(b - a))⁻¹ ∫₀¹ t ^ (a - 1) (1 - t) ^ (b - a - 1) e^{z t} dt`, for every
`z : ℂ`. -/
theorem regularizedHGFun_singleton_eq_integral {a b : ℂ} (ha : 0 < a.re) (hab : a.re < b.re)
    (z : ℂ) :
    regularizedHGFun {a} {b} z = (Gamma a * Gamma (b - a))⁻¹ *
      ∫ t : ℝ in 0..1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) * exp (z * t) := by
  have hba : 0 < (b - a).re := by simpa using sub_pos.mpr hab
  let w : ℝ → ℂ := fun t => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1)
  have hw_int : IntervalIntegrable w volume 0 1 := betaIntegral_convergent ha hba
  have hpoly_cont (n : ℕ) : Continuous fun t : ℝ => (z * (t : ℂ)) ^ n / n ! := by fun_prop
  -- Expand `e^{z t}` in its power series and swap sum and integral by dominated convergence
  -- against `‖w t‖ e^{‖z‖}`.
  have hdct := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun n t => w t * ((z * (t : ℂ)) ^ n / n !))
    (f := fun t => w t * exp (z * t))
    (μ := volume) (a := 0) (b := 1)
    (fun n t => ‖w t‖ * (‖z‖ ^ n / n !))
    (fun n => by
      rw [uIoc_of_le zero_le_one]
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (hw_int.mul_continuousOn (hpoly_cont n).continuousOn)).aestronglyMeasurable)
    (fun n => ae_of_all _ fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      have hzt : ‖z * (t : ℂ)‖ ≤ ‖z‖ := by
        rw [norm_mul, Complex.norm_of_nonneg ht.1.le]
        exact mul_le_of_le_one_right (norm_nonneg z) ht.2
      rw [norm_mul (w t), norm_div, norm_pow, norm_natCast]
      gcongr)
    (ae_of_all _ fun t _ => (Real.summable_pow_div_factorial ‖z‖).mul_left ‖w t‖)
    (by
      simp_rw [tsum_mul_left]
      exact hw_int.norm.mul_const _)
    (ae_of_all _ fun t _ => by
      have h := NormedSpace.expSeries_div_hasSum_exp (z * (t : ℂ))
      rw [← exp_eq_exp_ℂ] at h
      exact h.mul_left (w t))
  have hkummer := (hdct.mul_left (Gamma a * Gamma (b - a))⁻¹).congr_fun fun n =>
    (inv_Gamma_mul_integral_mul_pow_div_factorial ha hab z n).symm
  exact (hasSum_regularizedHGFun (by simp) z).unique hkummer

end Complex
