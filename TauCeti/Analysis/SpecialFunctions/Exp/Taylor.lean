/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exact Taylor integral remainder for the exponential function

For any order `n : ℕ` and any complex or real argument, the difference between `exp` and its
degree-`n` Taylor partial sum `∑ k ∈ range (n + 1), z ^ k / k!` equals the scaled integral
`z ^ (n + 1) / n! * ∫ s in 0..1, (1 - s) ^ n * exp (z * s)`. This specializes Mathlib's
`taylor_integral_remainder` to `s ↦ exp (z * s)` on `[0, 1]`.

## Main results

* `Complex.exp_sub_sum_range_succ_eq_integral`: exact integral remainder for `Complex.exp`.
* `Real.exp_sub_sum_range_succ_eq_integral`: exact integral remainder for `Real.exp`.
-/

public section

noncomputable section

open Set
open scoped Nat

namespace Complex

private theorem iteratedDeriv_cexp_mul_ofReal (z : ℂ) (k : ℕ) :
    iteratedDeriv k (fun s : ℝ => cexp (z * s)) = fun s : ℝ => z ^ k * cexp (z * s) := by
  induction k with
  | zero =>
    ext s
    simp
  | succ k ih =>
    ext s
    rw [iteratedDeriv_succ, ih]
    have hlin : HasDerivAt (fun t : ℝ => z * (t : ℂ)) z s := by
      simpa using ((hasDerivAt_id s).ofReal_comp).const_mul z
    refine ((hlin.cexp.const_mul (z ^ k)).congr_deriv ?_).deriv
    rw [pow_succ]
    ring

private theorem contDiff_cexp_mul_ofReal (z : ℂ) {m : WithTop ℕ∞} :
    ContDiff ℝ m (fun t : ℝ => cexp (z * t)) :=
  ((Complex.contDiff_exp : ContDiff ℂ m cexp).restrict_scalars ℝ).comp
    (contDiff_const.mul Complex.ofRealCLM.contDiff)

private theorem iteratedDerivWithin_Icc_cexp_mul_ofReal (z : ℂ) (k : ℕ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    iteratedDerivWithin k (fun t : ℝ => cexp (z * t)) (Icc 0 1) s = z ^ k * cexp (z * s) := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      (contDiff_cexp_mul_ofReal z).contDiffAt hs,
    iteratedDeriv_cexp_mul_ofReal]

/-- Exact integral remainder for the partial sums of `Complex.exp` at any order `n` and `z ∈ ℂ`:
`e^z - ∑_{k ≤ n} z^k / k! = z^{n + 1} / n! * ∫₀¹ (1 - s)^n e^{z s} ds`. -/
theorem exp_sub_sum_range_succ_eq_integral (n : ℕ) (z : ℂ) :
    exp z - ∑ k ∈ Finset.range (n + 1), z ^ k / (k ! : ℂ) =
      z ^ (n + 1) / (n ! : ℂ) * ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) ^ n * exp (z * s) := by
  let f : ℝ → ℂ := fun s => cexp (z * s)
  have hf : ContDiffOn ℝ (n + 1 : ℕ) f (uIcc 0 1) := (contDiff_cexp_mul_ofReal z).contDiffOn
  have hrem := taylor_integral_remainder (x₀ := (0 : ℝ)) (x := 1) (n := n) hf
  rw [Set.uIcc_of_le zero_le_one] at hrem
  have hf1 : f 1 = exp z := by simp [f]
  have hpoly : taylorWithinEval f n (Icc 0 1) 0 1 =
      ∑ k ∈ Finset.range (n + 1), z ^ k / (k ! : ℂ) := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hd0 : iteratedDerivWithin k f (Icc 0 1) 0 = z ^ k := by
      simpa using iteratedDerivWithin_Icc_cexp_mul_ofReal z k
        (left_mem_Icc.mpr zero_le_one)
    rw [hd0, sub_zero, one_pow, mul_one, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_natCast, inv_mul_eq_div]
  have hint : (∫ s in (0 : ℝ)..1,
        ((1 - s) ^ n / (n ! : ℝ)) • iteratedDerivWithin (n + 1) f (Icc 0 1) s) =
      z ^ (n + 1) / (n ! : ℂ) * ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) ^ n * exp (z * s) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le zero_le_one] at hs
    rw [iteratedDerivWithin_Icc_cexp_mul_ofReal z (n + 1) hs, Complex.real_smul]
    simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_natCast]
    ring
  rw [hf1, hpoly, hint] at hrem
  exact hrem

end Complex

namespace Real

private theorem ofReal_one_sub_pow_mul_exp (n : ℕ) (x s : ℝ) :
    (((1 - s) ^ n * Real.exp (x * s) : ℝ) : ℂ) =
      (1 - (s : ℂ)) ^ n * Complex.exp ((x : ℂ) * s) := by
  simp [Complex.ofReal_exp]

private theorem ofReal_exp_sub_sum_range_succ (n : ℕ) (x : ℝ) :
    ((Real.exp x - ∑ k ∈ Finset.range (n + 1), x ^ k / (k ! : ℝ) : ℝ) : ℂ) =
      Complex.exp x - ∑ k ∈ Finset.range (n + 1), (x : ℂ) ^ k / (k ! : ℂ) := by
  simp [Complex.ofReal_exp]

/-- Exact integral remainder for the partial sums of `Real.exp` at any order `n` and `x ∈ ℝ`:
`e^x - ∑_{k ≤ n} x^k / k! = x^{n + 1} / n! * ∫₀¹ (1 - s)^n e^{x s} ds`. -/
theorem exp_sub_sum_range_succ_eq_integral (n : ℕ) (x : ℝ) :
    Real.exp x - ∑ k ∈ Finset.range (n + 1), x ^ k / (k ! : ℝ) =
      x ^ (n + 1) / (n ! : ℝ) * ∫ s in (0 : ℝ)..1, (1 - s) ^ n * Real.exp (x * s) := by
  apply Complex.ofReal_inj.mp
  rw [ofReal_exp_sub_sum_range_succ, Complex.exp_sub_sum_range_succ_eq_integral,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast,
    ← intervalIntegral.integral_ofReal]
  congr 1
  exact intervalIntegral.integral_congr fun s _ => (ofReal_one_sub_pow_mul_exp n x s).symm

end Real

end
