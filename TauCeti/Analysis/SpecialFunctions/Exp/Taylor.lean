/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.PowerSeries.Exp
public import TauCeti.Analysis.Analytic.TaylorSeries

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv

/-!
# Exact Taylor integral remainder and formal Taylor series for the exponential function

For any order `n : ℕ` and any complex or real argument, the difference between `exp` and its
degree-`n` Taylor partial sum `∑ k ∈ range (n + 1), z ^ k / k!` equals the scaled integral
`z ^ (n + 1) / n! * ∫ s in 0..1, (1 - s) ^ n * exp (z * s)`. This specializes Mathlib's
`taylor_integral_remainder` to `s ↦ exp (z * s)` on `[0, 1]`.

At `z = 0`, the formal Taylor series of `z ↦ Complex.exp (a * z)` is
`PowerSeries.rescale a (PowerSeries.exp ℂ)`, and consequently `z ↦ Complex.exp z - 1` has
formal Taylor series `PowerSeries.exp ℂ - 1`.

## Main results

* `Complex.exp_sub_sum_range_succ_eq_integral`: exact integral remainder for `Complex.exp`.
* `Real.exp_sub_sum_range_succ_eq_integral`: exact integral remainder for `Real.exp`.
* `Complex.taylorSeries_exp_mul_zero`, `Complex.taylorSeries_exp_zero`, and
  `Complex.taylorSeries_exp_sub_one_zero`: formal `TauCeti.taylorSeries` identities at `0` for
  `Complex.exp (a * ·)`, `Complex.exp`, and `Complex.exp · - 1`.
-/

public section

noncomputable section

open Set
open scoped Nat

namespace Complex

private theorem iteratedDerivWithin_Icc_cexp_mul_ofReal (z : ℂ) (k : ℕ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    iteratedDerivWithin k (fun t : ℝ => cexp (z * t)) (Icc 0 1) s = z ^ k * cexp (z * s) := by
  have hc : ContDiffAt ℝ k (fun t : ℝ => cexp (z * t)) s :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp.contDiffAt
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) hc hs,
    TauCeti.iteratedDeriv_cexp_const_mul_ofReal]

/-- Exact integral remainder for the partial sums of `Complex.exp` at any order `n` and `z ∈ ℂ`:
`e^z - ∑_{k ≤ n} z^k / k! = z^{n + 1} / n! * ∫₀¹ (1 - s)^n e^{z s} ds`. -/
theorem exp_sub_sum_range_succ_eq_integral (n : ℕ) (z : ℂ) :
    exp z - ∑ k ∈ Finset.range (n + 1), z ^ k / (k ! : ℂ) =
      z ^ (n + 1) / (n ! : ℂ) * ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) ^ n * exp (z * s) := by
  let f : ℝ → ℂ := fun s => cexp (z * s)
  have hf : ContDiffOn ℝ (n + 1 : ℕ) f (uIcc 0 1) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp.contDiffOn
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
    rw [hd0, sub_zero, one_pow, mul_one, Complex.real_smul]
    push_cast
    rw [inv_mul_eq_div]
  have hint : (∫ s in (0 : ℝ)..1,
        ((1 - s) ^ n / (n ! : ℝ)) • iteratedDerivWithin (n + 1) f (Icc 0 1) s) =
      z ^ (n + 1) / (n ! : ℂ) * ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) ^ n * exp (z * s) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le zero_le_one] at hs
    rw [iteratedDerivWithin_Icc_cexp_mul_ofReal z (n + 1) hs, Complex.real_smul]
    push_cast
    ring
  rw [hf1, hpoly, hint] at hrem
  exact hrem

/-- The formal Taylor series at `0` of `z ↦ Complex.exp (a * z)` is
`PowerSeries.rescale a (PowerSeries.exp ℂ)`. -/
theorem taylorSeries_exp_mul_zero (a : ℂ) :
    TauCeti.taylorSeries (fun z : ℂ => Complex.exp (a * z)) 0 =
      PowerSeries.rescale a (PowerSeries.exp ℂ) := by
  have hexp : AnalyticAt ℂ (fun z : ℂ => Complex.exp (a * z)) 0 := by fun_prop
  ext n
  rw [hexp.coeff_taylorSeries_eq_inv_factorial_smul_iteratedDeriv n,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp, _root_.iteratedDeriv_cexp_const_mul]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The formal Taylor series at `0` of `Complex.exp` is `PowerSeries.exp ℂ`. -/
theorem taylorSeries_exp_zero :
    TauCeti.taylorSeries Complex.exp 0 = PowerSeries.exp ℂ := by
  simpa using taylorSeries_exp_mul_zero (1 : ℂ)

/-- The formal Taylor series at `0` of `z ↦ Complex.exp z - 1` is `PowerSeries.exp ℂ - 1`. -/
theorem taylorSeries_exp_sub_one_zero :
    TauCeti.taylorSeries (fun z : ℂ => Complex.exp z - 1) 0 = PowerSeries.exp ℂ - 1 := by
  change TauCeti.taylorSeries (Complex.exp - fun _ : ℂ => (1 : ℂ)) 0 = PowerSeries.exp ℂ - 1
  rw [TauCeti.taylorSeries_sub (by fun_prop) (by fun_prop), taylorSeries_exp_zero,
    TauCeti.taylorSeries_const, map_one]

end Complex

namespace Real

/-- Exact integral remainder for the partial sums of `Real.exp` at any order `n` and `x ∈ ℝ`:
`e^x - ∑_{k ≤ n} x^k / k! = x^{n + 1} / n! * ∫₀¹ (1 - s)^n e^{x s} ds`. -/
theorem exp_sub_sum_range_succ_eq_integral (n : ℕ) (x : ℝ) :
    Real.exp x - ∑ k ∈ Finset.range (n + 1), x ^ k / (k ! : ℝ) =
      x ^ (n + 1) / (n ! : ℝ) * ∫ s in (0 : ℝ)..1, (1 - s) ^ n * Real.exp (x * s) := by
  apply Complex.ofReal_inj.mp
  push_cast [Complex.ofReal_exp]
  rw [Complex.exp_sub_sum_range_succ_eq_integral, ← intervalIntegral.integral_ofReal]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  push_cast [Complex.ofReal_exp]
  rfl

end Real

end
