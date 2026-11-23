/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeriesComplex
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import TauCeti.Analysis.MellinTransform.ExpKernel
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate

/-!
# Mellin integral representation of the Riemann zeta function

Evaluates the Mellin–Laplace integral `∫₀^∞ t^{s−1}/(e^t − 1) dt = Γ(s) ζ(s)` for `1 < Re s`
(DLMF 25.5.1) directly from the termwise exponential-kernel expansion
`TauCeti.hasSum_setIntegral_cpow_mul_exp_neg_mul` at `c = 1`, the Gamma integral
`TauCeti.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos`, and Mathlib's
`zeta_eq_tsum_one_div_nat_add_one_cpow`, together with the `s = 2` specialization
`∫₀^∞ t/(e^t − 1) dt = π²/6`.

## Main results

* `TauCeti.integral_cpow_div_exp_sub_one_eq_Gamma_mul_riemannZeta`:
  `∫₀^∞ t^{s−1}/(e^t − 1) dt = Γ(s) ζ(s)` for `1 < Re s`.
* `TauCeti.integral_Ioi_div_exp_sub_one_eq_pi_sq_div_six`: `∫₀^∞ t/(e^t − 1) dt = π²/6`.
-/

public section

noncomputable section

open Complex MeasureTheory Set

namespace TauCeti

/-- **DLMF 25.5.1**: `∫₀^∞ t^{s−1}/(e^t − 1) dt = Γ(s) ζ(s)` for `1 < Re s`. -/
theorem integral_cpow_div_exp_sub_one_eq_Gamma_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) / (cexp t - 1) = Gamma s * riemannZeta s := by
  have hs0 : 0 < s.re := by linarith
  have hsum := hasSum_setIntegral_cpow_mul_exp_neg_mul (c := 1) hs one_pos subset_rfl
  simp only [sub_self, zero_mul, exp_zero, mul_one_div] at hsum
  have hterm : (fun k : ℕ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + 1) * t))) =
      fun k : ℕ => Gamma s * (1 / ((k : ℂ) + 1) ^ s) := funext fun k => by
    have hk : 0 < ((k : ℂ) + 1).re := by simp only [add_re, natCast_re, one_re]; positivity
    rw [integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs0 hk, cpow_neg, one_div]
  rw [hterm] at hsum
  have hsumm : Summable fun k : ℕ => 1 / ((k : ℂ) + 1) ^ s := by
    simpa only [Function.comp_def, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, one_div] using
      (Complex.summable_one_div_nat_cpow.mpr hs).comp_injective Nat.succ_injective
  have hzeta_sum : HasSum (fun k : ℕ => Gamma s * (1 / ((k : ℂ) + 1) ^ s))
      (Gamma s * riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    exact hsumm.hasSum.mul_left (Gamma s)
  exact hsum.unique hzeta_sum

/-- DLMF 8.22.3 at `s = 2`: `∫₀^∞ t/(e^t − 1) dt = π²/6`. -/
theorem integral_Ioi_div_exp_sub_one_eq_pi_sq_div_six :
    ∫ t in Ioi (0 : ℝ), t / (Real.exp t - 1) = Real.pi ^ 2 / 6 := by
  have h := integral_cpow_div_exp_sub_one_eq_Gamma_mul_riemannZeta (s := 2) (by norm_num)
  rw [Complex.Gamma_ofNat_eq_factorial, riemannZeta_two, Nat.factorial_one,
    Nat.cast_one, one_mul] at h
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  push_cast
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  norm_num

end TauCeti

end
