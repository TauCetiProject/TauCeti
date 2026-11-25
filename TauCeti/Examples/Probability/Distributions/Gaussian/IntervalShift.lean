/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Cdf
import TauCeti.Analysis.SpecialFunctions.Gaussian.DecimalBounds
import TauCeti.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Decimal checks for shifting intervals under the standard Gaussian measure

With `φ = gaussianPDFReal 0 1` and `Φ = cdf (gaussianReal 0 1)`, the interval `(a, b)` has
Gaussian measure `Φ(b) − Φ(a)` and Gaussian perimeter `φ(a) + φ(b)`.

* `(0, 1)` has measure `0.341345` and perimeter `0.640913`; its right shift to a half-line is
  `(0.408796, ∞)`, of measure `0.341345` and perimeter `0.366963`, up to `10⁻⁶`.
* Negative control: `(−1, 0)` has `a + b < 0`, and its right shifts `(−0.9, 0.063724)` and
  `(−0.5, 0.385003)`, of the same measure up to `10⁻⁶`, have perimeters `0.664218` and `0.722510`,
  both larger than `0.640913`.

The value `v` is checked as `|x − v| < 5 · 10⁻⁷`, or `< 10⁻⁶` where the endpoints are rounded.
The tails come from partial sums of the alternating Maclaurin series of the error function
(`TauCeti.Probability.mul_sum_range_two_mul_le_cdf_gaussianReal_sub_half`,
`TauCeti.Probability.cdf_gaussianReal_sub_half_le_mul_sum_range_two_mul_add_one`), the density
from Mathlib's `Real.exp_bound` and the bounds `Real.inv_sqrt_two_mul_pi_gt_d8`,
`Real.inv_sqrt_two_mul_pi_lt_d8` on `(2π)^{−1/2}`.
-/

open Finset ProbabilityTheory Real TauCeti.Probability

public noncomputable section

namespace TauCeti.Examples.GaussianIntervalShift

/-- Two-sided bounds on `Φ(1) − 1/2` from the error function series. -/
private theorem cdf_bounds_one :
    1 / √(2 * π) * ∑ i ∈ range (2 * 5),
        (-1) ^ i * ((1 : ℝ) ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1)) ≤
      cdf (gaussianReal 0 1) 1 - 1 / 2 ∧
    cdf (gaussianReal 0 1) 1 - 1 / 2 ≤
      1 / √(2 * π) * ∑ i ∈ range (2 * 5 + 1),
        (-1) ^ i * ((1 : ℝ) ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1)) :=
  ⟨mul_sum_range_two_mul_le_cdf_gaussianReal_sub_half (by norm_num) (by norm_num) 5,
    cdf_gaussianReal_sub_half_le_mul_sum_range_two_mul_add_one (by norm_num) (by norm_num) 5⟩

/-- Two-sided bounds on `Φ(0.408796) − 1/2` from the error function series. -/
private theorem cdf_bounds_shift :
    0.408796 / √(2 * π) * ∑ i ∈ range (2 * 5),
        (-1) ^ i * ((0.408796 : ℝ) ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1)) ≤
      cdf (gaussianReal 0 1) 0.408796 - 1 / 2 ∧
    cdf (gaussianReal 0 1) 0.408796 - 1 / 2 ≤
      0.408796 / √(2 * π) * ∑ i ∈ range (2 * 5 + 1),
        (-1) ^ i * ((0.408796 : ℝ) ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1)) :=
  ⟨mul_sum_range_two_mul_le_cdf_gaussianReal_sub_half (by norm_num) (by norm_num) 5,
    cdf_gaussianReal_sub_half_le_mul_sum_range_two_mul_add_one (by norm_num) (by norm_num) 5⟩

/-- Two-sided bounds on `Φ(0.063724) − 1/2` from the error function series. -/
private theorem cdf_bounds_shift_one :
    0.063724 / √(2 * π) * ∑ i ∈ range (2 * 5),
        (-1) ^ i * ((0.063724 : ℝ) ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1)) ≤
      cdf (gaussianReal 0 1) 0.063724 - 1 / 2 ∧
    cdf (gaussianReal 0 1) 0.063724 - 1 / 2 ≤
      0.063724 / √(2 * π) * ∑ i ∈ range (2 * 5 + 1),
        (-1) ^ i * ((0.063724 : ℝ) ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1)) :=
  ⟨mul_sum_range_two_mul_le_cdf_gaussianReal_sub_half (by norm_num) (by norm_num) 5,
    cdf_gaussianReal_sub_half_le_mul_sum_range_two_mul_add_one (by norm_num) (by norm_num) 5⟩

/-- Two-sided bounds on `Φ(0.9) − 1/2` from the error function series. -/
private theorem cdf_bounds_nine_tenths :
    0.9 / √(2 * π) * ∑ i ∈ range (2 * 5),
        (-1) ^ i * ((0.9 : ℝ) ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1)) ≤
      cdf (gaussianReal 0 1) 0.9 - 1 / 2 ∧
    cdf (gaussianReal 0 1) 0.9 - 1 / 2 ≤
      0.9 / √(2 * π) * ∑ i ∈ range (2 * 5 + 1),
        (-1) ^ i * ((0.9 : ℝ) ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1)) :=
  ⟨mul_sum_range_two_mul_le_cdf_gaussianReal_sub_half (by norm_num) (by norm_num) 5,
    cdf_gaussianReal_sub_half_le_mul_sum_range_two_mul_add_one (by norm_num) (by norm_num) 5⟩

/-- Two-sided bounds on `Φ(0.385003) − 1/2` from the error function series. -/
private theorem cdf_bounds_shift_two :
    0.385003 / √(2 * π) * ∑ i ∈ range (2 * 5),
        (-1) ^ i * ((0.385003 : ℝ) ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1)) ≤
      cdf (gaussianReal 0 1) 0.385003 - 1 / 2 ∧
    cdf (gaussianReal 0 1) 0.385003 - 1 / 2 ≤
      0.385003 / √(2 * π) * ∑ i ∈ range (2 * 5 + 1),
        (-1) ^ i * ((0.385003 : ℝ) ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1)) :=
  ⟨mul_sum_range_two_mul_le_cdf_gaussianReal_sub_half (by norm_num) (by norm_num) 5,
    cdf_gaussianReal_sub_half_le_mul_sum_range_two_mul_add_one (by norm_num) (by norm_num) 5⟩

/-- Two-sided bounds on `Φ(0.5) − 1/2` from the error function series. -/
private theorem cdf_bounds_half :
    0.5 / √(2 * π) * ∑ i ∈ range (2 * 5),
        (-1) ^ i * ((0.5 : ℝ) ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1)) ≤
      cdf (gaussianReal 0 1) 0.5 - 1 / 2 ∧
    cdf (gaussianReal 0 1) 0.5 - 1 / 2 ≤
      0.5 / √(2 * π) * ∑ i ∈ range (2 * 5 + 1),
        (-1) ^ i * ((0.5 : ℝ) ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1)) :=
  ⟨mul_sum_range_two_mul_le_cdf_gaussianReal_sub_half (by norm_num) (by norm_num) 5,
    cdf_gaussianReal_sub_half_le_mul_sum_range_two_mul_add_one (by norm_num) (by norm_num) 5⟩

/-- `γ¹((0, 1)) = Φ(1) − Φ(0) = 0.341345`. -/
theorem measure_Ioo_zero_one : |(cdf (gaussianReal 0 1) 1 - cdf (gaussianReal 0 1) 0) - 0.341345| <
    5e-7 := by
  obtain ⟨hlo, hhi⟩ := cdf_bounds_one
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  rw [cdf_gaussianReal_self 0 one_ne_zero, abs_sub_lt_iff]
  rw [one_div √(2 * π)] at hlo hhi
  generalize (√(2 * π))⁻¹ = s at hlo hhi h1 h2
  norm_num [sum_range_succ, Nat.factorial] at hlo hhi h1 h2 ⊢
  constructor <;> linarith

/-- `φ(0) + φ(1) = 0.640913`: the Gaussian perimeter of `(0, 1)`. -/
theorem perimeter_Ioo_zero_one :
    |(gaussianPDFReal 0 1 0 + gaussianPDFReal 0 1 1) - 0.640913| < 5e-7 := by
  rw [gaussianPDFReal_zero_one, gaussianPDFReal_zero_one, abs_sub_lt_iff]
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  have h3 := exp_neg_half_gt_d8
  have h4 := exp_neg_half_lt_d8
  norm_num at h1 h2 h3 h4 ⊢
  constructor <;> nlinarith

/-- `γ¹((0.408796, ∞)) = 1 − Φ(0.408796) = 0.341345`, up to `10⁻⁶`. -/
theorem measure_Ioi_shift : |(1 - cdf (gaussianReal 0 1) 0.408796) - 0.341345| < 1e-6 := by
  obtain ⟨hlo, hhi⟩ := cdf_bounds_shift
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  rw [abs_sub_lt_iff]
  rw [div_eq_mul_inv _ √(2 * π)] at hlo hhi
  generalize (√(2 * π))⁻¹ = s at hlo hhi h1 h2
  norm_num [sum_range_succ, Nat.factorial] at hlo hhi h1 h2 ⊢
  constructor <;> nlinarith

/-- `φ(0.408796) = 0.366963`, up to `10⁻⁶`. -/
theorem gaussianPDFReal_shift : |gaussianPDFReal 0 1 0.408796 - 0.366963| < 1e-6 := by
  rw [gaussianPDFReal_zero_one, abs_sub_lt_iff]
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  have he := Real.exp_bound (x := -((0.408796 : ℝ) ^ 2 / 2)) (by norm_num [abs_le]) (n := 8)
    (by norm_num)
  norm_num [sum_range_succ, Nat.factorial, abs_le] at he h1 h2 ⊢
  constructor <;> nlinarith

/-- The right shift `(0.408796, ∞)` of `(0, 1)` has smaller Gaussian perimeter. -/
theorem gaussianPDFReal_shift_lt :
    gaussianPDFReal 0 1 0.408796 < gaussianPDFReal 0 1 0 + gaussianPDFReal 0 1 1 := by
  have h1 := gaussianPDFReal_shift
  have h2 := perimeter_Ioo_zero_one
  rw [abs_sub_lt_iff] at h1 h2
  linarith [h1.1, h2.2]

/-- `γ¹((−0.9, 0.063724)) = Φ(0.063724) − Φ(−0.9) = 0.341345`, up to `10⁻⁶`. -/
theorem measure_Ioo_shift_one :
    |(cdf (gaussianReal 0 1) 0.063724 - cdf (gaussianReal 0 1) (-0.9)) - 0.341345| < 1e-6 := by
  obtain ⟨hlo, hhi⟩ := cdf_bounds_shift_one
  obtain ⟨hlo', hhi'⟩ := cdf_bounds_nine_tenths
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  rw [cdf_gaussianReal_zero_one_neg, abs_sub_lt_iff]
  rw [div_eq_mul_inv _ √(2 * π)] at hlo hhi hlo' hhi'
  generalize (√(2 * π))⁻¹ = s at hlo hhi hlo' hhi' h1 h2
  norm_num [sum_range_succ, Nat.factorial] at hlo hhi hlo' hhi' h1 h2 ⊢
  constructor <;> nlinarith

/-- `γ¹((−0.5, 0.385003)) = Φ(0.385003) − Φ(−0.5) = 0.341345`, up to `10⁻⁶`. -/
theorem measure_Ioo_shift_two :
    |(cdf (gaussianReal 0 1) 0.385003 - cdf (gaussianReal 0 1) (-0.5)) - 0.341345| < 1e-6 := by
  obtain ⟨hlo, hhi⟩ := cdf_bounds_shift_two
  obtain ⟨hlo', hhi'⟩ := cdf_bounds_half
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  rw [cdf_gaussianReal_zero_one_neg, abs_sub_lt_iff]
  rw [div_eq_mul_inv _ √(2 * π)] at hlo hhi hlo' hhi'
  generalize (√(2 * π))⁻¹ = s at hlo hhi hlo' hhi' h1 h2
  norm_num [sum_range_succ, Nat.factorial] at hlo hhi hlo' hhi' h1 h2 ⊢
  constructor <;> nlinarith

/-- `φ(−0.9) = 0.2660852`, up to `10⁻⁷`. -/
theorem gaussianPDFReal_neg_nine_tenths : |gaussianPDFReal 0 1 (-0.9) - 0.2660852| < 1e-7 := by
  rw [gaussianPDFReal_zero_one, abs_sub_lt_iff]
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  have he := Real.exp_bound (x := -(((-0.9) : ℝ) ^ 2 / 2)) (by norm_num [abs_le]) (n := 8)
    (by norm_num)
  norm_num [sum_range_succ, Nat.factorial, abs_le] at he h1 h2 ⊢
  constructor <;> nlinarith

/-- `φ(0.063724) = 0.3981331`, up to `10⁻⁷`. -/
theorem gaussianPDFReal_shift_one : |gaussianPDFReal 0 1 0.063724 - 0.3981331| < 1e-7 := by
  rw [gaussianPDFReal_zero_one, abs_sub_lt_iff]
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  have he := Real.exp_bound (x := -((0.063724 : ℝ) ^ 2 / 2)) (by norm_num [abs_le]) (n := 8)
    (by norm_num)
  norm_num [sum_range_succ, Nat.factorial, abs_le] at he h1 h2 ⊢
  constructor <;> nlinarith

/-- `φ(−0.5) = 0.3520653`, up to `10⁻⁷`. -/
theorem gaussianPDFReal_neg_half : |gaussianPDFReal 0 1 (-0.5) - 0.3520653| < 1e-7 := by
  rw [gaussianPDFReal_zero_one, abs_sub_lt_iff]
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  have he := Real.exp_bound (x := -(((-0.5) : ℝ) ^ 2 / 2)) (by norm_num [abs_le]) (n := 8)
    (by norm_num)
  norm_num [sum_range_succ, Nat.factorial, abs_le] at he h1 h2 ⊢
  constructor <;> nlinarith

/-- `φ(0.385003) = 0.3704443`, up to `10⁻⁷`. -/
theorem gaussianPDFReal_shift_two : |gaussianPDFReal 0 1 0.385003 - 0.3704443| < 1e-7 := by
  rw [gaussianPDFReal_zero_one, abs_sub_lt_iff]
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  have he := Real.exp_bound (x := -((0.385003 : ℝ) ^ 2 / 2)) (by norm_num [abs_le]) (n := 8)
    (by norm_num)
  norm_num [sum_range_succ, Nat.factorial, abs_le] at he h1 h2 ⊢
  constructor <;> nlinarith

/-- The right shifts of `(−1, 0)` have perimeters `0.664218` and `0.722510`, both larger than
the perimeter `0.640913` of `(0, 1)`: the shift lemma needs `a + b ≥ 0`. -/
theorem perimeter_shifts :
    |(gaussianPDFReal 0 1 (-0.9) + gaussianPDFReal 0 1 0.063724) - 0.664218| < 1e-6 ∧
      |(gaussianPDFReal 0 1 (-0.5) + gaussianPDFReal 0 1 0.385003) - 0.722510| < 1e-6 ∧
      gaussianPDFReal 0 1 0 + gaussianPDFReal 0 1 1 <
        gaussianPDFReal 0 1 (-0.9) + gaussianPDFReal 0 1 0.063724 ∧
      gaussianPDFReal 0 1 0 + gaussianPDFReal 0 1 1 <
        gaussianPDFReal 0 1 (-0.5) + gaussianPDFReal 0 1 0.385003 := by
  have h1 := gaussianPDFReal_neg_nine_tenths
  have h2 := gaussianPDFReal_shift_one
  have h3 := gaussianPDFReal_neg_half
  have h4 := gaussianPDFReal_shift_two
  have h0 := perimeter_Ioo_zero_one
  rw [abs_sub_lt_iff] at h0 h1 h2 h3 h4 ⊢
  rw [abs_sub_lt_iff]
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

end TauCeti.Examples.GaussianIntervalShift
