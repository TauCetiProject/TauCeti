/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.IsoperimetricProfile
public import TauCeti.Probability.Distributions.Gaussian.Cdf
import TauCeti.Analysis.SpecialFunctions.Gaussian.DecimalBounds
import TauCeti.Probability.Distributions.Gaussian.Basic
import TauCeti.Probability.Distributions.Gaussian.DecimalBounds
import TauCeti.Probability.Distributions.Gaussian.Quantile

/-!
# Decimal checks for the Gaussian isoperimetric function

With `φ = gaussianPDFReal 0 1`, `Φ = cdf (gaussianReal 0 1)`, `Φ⁻¹` its quantile and
`I = φ ∘ Φ⁻¹` (`TauCeti.Probability.gaussianIsoperimetricProfile`):

* `Φ⁻¹(1/3) = −0.430727` and `I(1/3) = I(2/3) = 0.363600`;
* `I'(0.3) = −Φ⁻¹(0.3) = 0.524401` and `I''(0.3) = −1/I(0.3) = −2.876104`, up to `10⁻⁶`;
* `Φ(1) = 0.841345`, `1 − Φ(√1.5) = 0.110336` and `(2π)⁻¹ = 0.159155`.

Each value `v` is checked as `|x − v| < 5 · 10⁻⁷`, or `< 10⁻⁶` where stated. Quantiles are
located by evaluating `Φ` at two decimal points around them, through partial sums of the
alternating error-function series
(`TauCeti.Probability.mul_sum_range_two_mul_le_cdf_gaussianReal_sub_half`,
`TauCeti.Probability.cdf_gaussianReal_sub_half_le_mul_sum_range_two_mul_add_one`); values of `φ`
at an unknown point come from its values at decimal points of larger and smaller modulus
(`TauCeti.Probability.gaussianPDFReal_le_of_sq_le`,
`TauCeti.Probability.gaussianPDFReal_zero_one_bounds`).
-/

open Finset ProbabilityTheory Real Set TauCeti.Probability

public noncomputable section

namespace TauCeti.Examples.GaussianIsoperimetryDecimal

/-- A lower bound on `Φ(r)` from the first ten terms of the error-function series. -/
private theorem le_cdf {r c : ℝ} (hr : 0 ≤ r) (hr6 : r ^ 2 ≤ 6)
    (hsum : 0 ≤ ∑ i ∈ range (2 * 5), (-1) ^ i * (r ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1)))
    (hc : c ≤ 1 / 2 + r * 0.39894228 *
      ∑ i ∈ range (2 * 5), (-1) ^ i * (r ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1))) :
    c ≤ cdf (gaussianReal 0 1) r := by
  have hlo := mul_sum_range_two_mul_le_cdf_gaussianReal_sub_half hr hr6 5
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  rw [div_eq_mul_inv _ √(2 * π)] at hlo
  generalize (√(2 * π))⁻¹ = s at hlo h1
  nlinarith [mul_le_mul_of_nonneg_left h1.le (mul_nonneg hr hsum)]

/-- An upper bound on `Φ(r)` from the first eleven terms of the error-function series. -/
private theorem cdf_le {r c : ℝ} (hr : 0 ≤ r) (hr6 : r ^ 2 ≤ 6)
    (hsum : 0 ≤ ∑ i ∈ range (2 * 5 + 1),
      (-1) ^ i * (r ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1)))
    (hc : 1 / 2 + r * 0.39894229 * ∑ i ∈ range (2 * 5 + 1),
      (-1) ^ i * (r ^ 2 / 2) ^ i / (i.factorial * (2 * i + 1)) ≤ c) :
    cdf (gaussianReal 0 1) r ≤ c := by
  have hhi := cdf_gaussianReal_sub_half_le_mul_sum_range_two_mul_add_one hr hr6 5
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  rw [div_eq_mul_inv _ √(2 * π)] at hhi
  generalize (√(2 * π))⁻¹ = s at hhi h2
  nlinarith [mul_le_mul_of_nonneg_left h2.le (mul_nonneg hr hsum)]

/-- A quantile lies strictly between two points where `Φ` is below and above the level. -/
private theorem quantile_mem_Ioo {u a b : ℝ} (hu : u ∈ Set.Ioo 0 1)
    (ha : cdf (gaussianReal 0 1) a < u) (hb : u < cdf (gaussianReal 0 1) b) :
    (gaussianReal 0 1).quantile u ∈ Set.Ioo a b := by
  have hq := cdf_quantile_gaussianReal (m := 0) (v := 1) one_ne_zero hu
  have hm := strictMono_cdf_gaussianReal 0 (v := 1) one_ne_zero
  rw [← hq] at ha hb
  exact ⟨hm.lt_iff_lt.1 ha, hm.lt_iff_lt.1 hb⟩

/-- `Φ⁻¹(1/3)` lies in `(−0.4307275, −0.4307265)`. -/
private theorem quantile_one_third_mem :
    (gaussianReal 0 1).quantile (1 / 3) ∈ Set.Ioo (-0.4307275 : ℝ) (-0.4307265) := by
  refine quantile_mem_Ioo (by norm_num) ?_ ?_ <;> rw [cdf_gaussianReal_zero_one_neg]
  · have := le_cdf (r := 0.4307275) (c := 0.66666668) (by norm_num) (by norm_num)
      (by norm_num [sum_range_succ, Nat.factorial]) (by norm_num [sum_range_succ, Nat.factorial])
    linarith
  · have := cdf_le (r := 0.4307265) (c := 0.66666665) (by norm_num) (by norm_num)
      (by norm_num [sum_range_succ, Nat.factorial]) (by norm_num [sum_range_succ, Nat.factorial])
    linarith

/-- `Φ⁻¹(1/3) = −0.430727`. -/
theorem abs_quantile_one_third_add_lt :
    |(gaussianReal 0 1).quantile (1 / 3) + 0.430727| < 5e-7 := by
  obtain ⟨h₁, h₂⟩ := quantile_one_third_mem
  rw [abs_lt]
  constructor <;> linarith

/-- `I(1/3) = 0.363600`. -/
theorem abs_gaussianIsoperimetricProfile_one_third_sub_lt :
    |gaussianIsoperimetricProfile (1 / 3) - 0.363600| < 5e-7 := by
  rw [gaussianIsoperimetricProfile_of_mem_Ioo (by norm_num)]
  obtain ⟨h₁, h₂⟩ := quantile_one_third_mem
  set x := (gaussianReal 0 1).quantile (1 / 3)
  have hlo := gaussianPDFReal_le_of_sq_le (μ := 0) (v := 1) (x := x) (y := 0.4307275)
    (by simp only [sub_zero]; nlinarith)
  have hhi := gaussianPDFReal_le_of_sq_le (μ := 0) (v := 1) (x := 0.4307265) (y := x)
    (by simp only [sub_zero]; nlinarith)
  have b₁ := (gaussianPDFReal_zero_one_bounds (x := 0.4307275) (by norm_num)).1
  have b₂ := (gaussianPDFReal_zero_one_bounds (x := 0.4307265) (by norm_num)).2
  norm_num [sum_range_succ, Nat.factorial] at b₁ b₂
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- `I(2/3) = 0.363600`. -/
example : |gaussianIsoperimetricProfile (2 / 3) - 0.363600| < 5e-7 := by
  rw [← gaussianIsoperimetricProfile_one_sub, show (1 : ℝ) - 2 / 3 = 1 / 3 by norm_num]
  exact abs_gaussianIsoperimetricProfile_one_third_sub_lt

/-- `Φ⁻¹(0.3)` lies in `(−0.5244006, −0.5244004)`. -/
private theorem quantile_three_tenths_mem :
    (gaussianReal 0 1).quantile 0.3 ∈ Set.Ioo (-0.5244006 : ℝ) (-0.5244004) := by
  refine quantile_mem_Ioo (by norm_num) ?_ ?_ <;> rw [cdf_gaussianReal_zero_one_neg]
  · have := le_cdf (r := 0.5244006) (c := 0.70000002) (by norm_num) (by norm_num)
      (by norm_num [sum_range_succ, Nat.factorial]) (by norm_num [sum_range_succ, Nat.factorial])
    linarith
  · have := cdf_le (r := 0.5244004) (c := 0.69999998) (by norm_num) (by norm_num)
      (by norm_num [sum_range_succ, Nat.factorial]) (by norm_num [sum_range_succ, Nat.factorial])
    linarith

/-- `I'(0.3) = −Φ⁻¹(0.3) = 0.524401`, up to `10⁻⁶`. -/
example : ∃ d, HasDerivAt gaussianIsoperimetricProfile d 0.3 ∧ |d - 0.524401| < 1e-6 := by
  refine ⟨_, hasDerivAt_gaussianIsoperimetricProfile (by norm_num), ?_⟩
  obtain ⟨h₁, h₂⟩ := quantile_three_tenths_mem
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- `I(0.3)` lies in `(0.3476925, 0.34769265)`. -/
private theorem gaussianIsoperimetricProfile_three_tenths_mem :
    gaussianIsoperimetricProfile 0.3 ∈ Set.Ioo (0.3476925 : ℝ) 0.34769265 := by
  rw [gaussianIsoperimetricProfile_of_mem_Ioo (by norm_num)]
  obtain ⟨h₁, h₂⟩ := quantile_three_tenths_mem
  set x := (gaussianReal 0 1).quantile 0.3
  have hlo := gaussianPDFReal_le_of_sq_le (μ := 0) (v := 1) (x := x) (y := 0.5244006)
    (by simp only [sub_zero]; nlinarith)
  have hhi := gaussianPDFReal_le_of_sq_le (μ := 0) (v := 1) (x := 0.5244004) (y := x)
    (by simp only [sub_zero]; nlinarith)
  have b₁ := (gaussianPDFReal_zero_one_bounds (x := 0.5244006) (by norm_num)).1
  have b₂ := (gaussianPDFReal_zero_one_bounds (x := 0.5244004) (by norm_num)).2
  norm_num [sum_range_succ, Nat.factorial] at b₁ b₂
  constructor <;> linarith

/-- `I''(0.3) = −1/I(0.3) = −2.876104`, up to `10⁻⁶`. -/
example : ∃ d, HasDerivAt (deriv gaussianIsoperimetricProfile) d 0.3 ∧
    |d + 2.876104| < 1e-6 := by
  refine ⟨_, hasDerivAt_deriv_gaussianIsoperimetricProfile (by norm_num), ?_⟩
  obtain ⟨h₁, h₂⟩ := gaussianIsoperimetricProfile_three_tenths_mem
  set I := gaussianIsoperimetricProfile 0.3
  norm_num at h₁ h₂
  have hI : 0 < I := by linarith
  have h₃ : I⁻¹ < 2.876105 := by
    rw [inv_lt_comm₀ hI (by norm_num)]
    norm_num
    linarith
  have h₄ : 2.876103 < I⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hI]
    norm_num
    linarith
  rw [abs_lt]
  constructor <;> linarith

/-- `Φ(1) = 0.841345`. -/
example : |cdf (gaussianReal 0 1) 1 - 0.841345| < 5e-7 := by
  have hlo := le_cdf (r := 1) (c := 0.84134460) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ, Nat.factorial]) (by norm_num [sum_range_succ, Nat.factorial])
  have hhi := cdf_le (r := 1) (c := 0.84134490) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ, Nat.factorial]) (by norm_num [sum_range_succ, Nat.factorial])
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- `1 − Φ(√1.5) = 0.110336`. -/
example : |(1 - cdf (gaussianReal 0 1) √1.5) - 0.110336| < 5e-7 := by
  have hs₁ : (1.22474487 : ℝ) < √1.5 := by
    rw [lt_sqrt (by norm_num)]
    norm_num
  have hs₂ : √1.5 < (1.22474488 : ℝ) := by
    rw [sqrt_lt' (by norm_num)]
    norm_num
  have hm := strictMono_cdf_gaussianReal 0 (v := 1) one_ne_zero
  have hlo := le_cdf (r := 1.22474487) (c := 0.88966420) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ, Nat.factorial]) (by norm_num [sum_range_succ, Nat.factorial])
  have hhi := cdf_le (r := 1.22474488) (c := 0.88966440) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ, Nat.factorial]) (by norm_num [sum_range_succ, Nat.factorial])
  have := hm hs₁
  have := hm hs₂
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- `(2π)⁻¹ = 0.159155`. -/
example : |(2 * π)⁻¹ - 0.159155| < 5e-7 := by
  have h₁ := pi_gt_d6
  have h₂ := pi_lt_d6
  rw [abs_sub_lt_iff, inv_eq_one_div]
  constructor
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ (by positivity)]
    nlinarith
  · rw [sub_lt_comm, lt_div_iff₀ (by positivity)]
    nlinarith

end TauCeti.Examples.GaussianIsoperimetryDecimal
