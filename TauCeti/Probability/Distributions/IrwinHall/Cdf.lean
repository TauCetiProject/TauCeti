/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.IrwinHall.Basic
public import TauCeti.Probability.Cdf
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.PositivePart
public import TauCeti.Data.Nat.Choose.Sum

/-!
# Cumulative distribution functions of Irwin–Hall laws

The cdf of a sum of `n > 0` independent unit-uniform variables is an alternating finite sum
of truncated powers, divided by `n!`. The formula holds on the entire real line, including
the integer knots and both support endpoints. Convolution with one further uniform variable
gives an integral recursion for these piecewise polynomials.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 26.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory

namespace TauCeti.Probability

/-- Appending a unit-uniform summand averages the preceding Irwin–Hall cdf over a unit interval.
This also holds for the empty-sum law at order zero. -/
theorem cdf_irwinHallMeasure_succ (n : ℕ) (x : ℝ) :
    cdf (irwinHallMeasure (n + 1)) x = ∫ y in 0..1, cdf (irwinHallMeasure n) (x - y) := by
  rw [irwinHallMeasure_succ, Measure.conv_comm, Measure.cdf_conv,
    uniformMeasure_eq_smul]
  norm_num only [sub_zero, ENNReal.ofReal_one, inv_one, one_smul]
  rw [intervalIntegral.integral_of_le zero_le_one]

/-- The cdf of a positive-order Irwin–Hall law is an alternating sum of truncated powers.
In particular the same expression applies at the integer knots, without choosing a polynomial
branch. -/
theorem cdf_irwinHallMeasure_eq {n : ℕ} (hn : 0 < n) (x : ℝ) :
    cdf (irwinHallMeasure n) x =
      (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) *
        max (x - k) 0 ^ n) / n.factorial := by
  induction n generalizing x with
  | zero => omega
  | succ n ih =>
    -- Start from the unit-uniform cdf; order zero is atomic and has a different formula.
    by_cases hn0 : n = 0
    · subst n
      rw [irwinHallMeasure_one, cdf_uniformMeasure zero_lt_one]
      split_ifs with hx hx1
      · simp [Finset.sum_range_succ, max_eq_right hx, max_eq_right (by linarith : x - 1 ≤ 0)]
      · simp [Finset.sum_range_succ, max_eq_left (by linarith : 0 ≤ x),
          max_eq_left (by linarith : 0 ≤ x - 1)]
      · simp [Finset.sum_range_succ, max_eq_left (by linarith : 0 ≤ x),
          max_eq_right (by linarith : x - 1 ≤ 0)]
    have hn' : 0 < n := Nat.pos_of_ne_zero hn0
    -- Each integration increases the truncated-power degree and takes a unit difference.
    have hint (k : ℕ) : IntervalIntegrable
        (fun y : ℝ ↦ (-1 : ℝ) ^ k * (n.choose k : ℝ) * max (x - y - k) 0 ^ n)
        volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable _ _
    rw [cdf_irwinHallMeasure_succ]
    simp_rw [ih hn']
    rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul, sub_right_comm x _ (↑(_ : ℕ) : ℝ),
        intervalIntegral.integral_max_sub_zero_pow hn', sub_zero, ← mul_div_assoc]
      rw [← Finset.sum_div, div_div, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one, sum_neg_one_pow_mul_choose_succ]
      simp only [Nat.cast_add, Nat.cast_one, sub_sub]
    · exact fun k _ ↦ hint k

end TauCeti.Probability
