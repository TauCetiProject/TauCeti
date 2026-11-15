/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.IrwinHall.Support
public import TauCeti.Probability.Cdf
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.PositivePart
public import TauCeti.Algebra.Group.ForwardDiff
import TauCeti.Probability.Distributions.Dirac

/-!
# Cumulative distribution functions of Irwin–Hall laws

The cdf of a sum of `n > 0` independent unit-uniform variables is an alternating finite sum
of truncated powers, divided by `n!`. The formula holds on the entire real line, including
the integer knots and both support endpoints. Convolution with one further uniform variable
gives an integral recursion for these piecewise polynomials.
At positive order the cdf is continuous and increases strictly on `[0, n]`, with values
strictly between zero and one exactly on `(0, n)`.

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
    · calc
        _ = (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) *
            (max (x - k) 0 ^ (n + 1) - max (x - k - 1) 0 ^ (n + 1)) /
              (n + 1)) / n.factorial := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          rw [intervalIntegral.integral_const_mul]
          simp_rw [sub_right_comm x _ (k : ℝ)]
          rw [intervalIntegral.integral_max_sub_zero_pow hn']
          simp [mul_div_assoc, sub_sub]
        _ = _ := by
          rw [← Finset.sum_div, sum_neg_one_pow_mul_choose_succ]
          push_cast [Nat.factorial_succ]
          simp [sub_add_eq_sub_sub, div_div, mul_comm]
    · exact fun k _ ↦ hint k

/-- A positive-order Irwin–Hall cdf is continuous, including at its integer knots. -/
theorem continuous_cdf_irwinHallMeasure {n : ℕ} (hn : 0 < n) :
    Continuous (cdf (irwinHallMeasure n)) := by
  let : NeZero n := ⟨hn.ne'⟩
  exact Measure.continuous_cdf_of_noAtoms _

/-- The Irwin–Hall cdf increases strictly throughout its closed support interval. -/
theorem strictMonoOn_cdf_irwinHallMeasure (n : ℕ) :
    StrictMonoOn (cdf (irwinHallMeasure n)) (Icc 0 (n : ℝ)) := by
  exact Measure.strictMonoOn_cdf_of_subset_support _ ordConnected_Icc
    (by rw [support_irwinHallMeasure n])

/-- A positive-order Irwin–Hall cdf vanishes at and below zero. -/
@[simp]
theorem cdf_irwinHallMeasure_of_nonpos {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : x ≤ 0) :
    cdf (irwinHallMeasure n) x = 0 := by
  rw [cdf_irwinHallMeasure_eq hn]
  have hterm (k : ℕ) : max (x - k) 0 ^ n = 0 := by
    rw [max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) k]), zero_pow hn.ne']
  simp [hterm]

/-- The Irwin–Hall cdf is one at and above its upper support endpoint. -/
@[simp]
theorem cdf_irwinHallMeasure_of_natCast_le (n : ℕ) {x : ℝ} (hx : (n : ℝ) ≤ x) :
    cdf (irwinHallMeasure n) x = 1 := by
  rw [cdf_eq_real]
  have heq : Iic x =ᵐ[irwinHallMeasure n] univ :=
    Filter.eventuallyEqSet_univ.2 ((ae_mem_Icc_irwinHallMeasure n).mono fun _ hy ↦ hy.2.trans hx)
  rw [measureReal_congr heq, probReal_univ]

/-- A positive-order Irwin–Hall cdf is positive exactly above zero. -/
@[simp]
theorem cdf_irwinHallMeasure_pos_iff {n : ℕ} (hn : 0 < n) {x : ℝ} :
    0 < cdf (irwinHallMeasure n) x ↔ 0 < x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · contrapose!
    intro hx
    simp [cdf_irwinHallMeasure_of_nonpos hn hx]
  · intro hx
    by_cases hxn : (n : ℝ) ≤ x
    · simp [cdf_irwinHallMeasure_of_natCast_le n hxn]
    · exact (cdf_nonneg _ 0).trans_lt
        (strictMonoOn_cdf_irwinHallMeasure n ⟨le_rfl, hnR.le⟩
          ⟨hx.le, (not_le.1 hxn).le⟩ hx)

/-- An Irwin–Hall cdf leaves positive upper-tail probability exactly below `n`. -/
@[simp]
theorem cdf_irwinHallMeasure_lt_one_iff (n : ℕ) {x : ℝ} :
    cdf (irwinHallMeasure n) x < 1 ↔ x < n := by
  by_cases hn : n = 0
  · subst n
    simp only [irwinHallMeasure_zero, Nat.cast_zero, cdf_dirac]
    split_ifs <;> grind
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · contrapose!
    intro hx
    simp [cdf_irwinHallMeasure_of_natCast_le n hx]
  · intro hx
    by_cases hx0 : x ≤ 0
    · simp [cdf_irwinHallMeasure_of_nonpos hn hx0]
    · exact (strictMonoOn_cdf_irwinHallMeasure n ⟨(not_le.1 hx0).le, hx.le⟩
        ⟨hnR.le, le_rfl⟩ hx).trans_le (cdf_le_one _ _)

end TauCeti.Probability
