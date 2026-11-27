/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Cdf
import TauCeti.Analysis.SpecialFunctions.Gaussian.DecimalBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Decimal checks for the standard Gaussian density and tails

Decimal values of the standard Gaussian density `φ` and of the upper tail `1 - Φ`, to six
decimal places, which show how far the tail bounds `1 - Φ(r) < φ(r) / r` and
`1 - Φ(r) < ½ e^{-r²/2}` are from sharp:

* `φ(0) = 0.398942` and `φ(1) = 0.241971`;
* `½ e^{-1/2} = 0.303265` and `½ e^{-2} = 0.067668`;
* `1 - Φ(1) = 0.158655`, against `φ(1) = 0.241971` and `½ e^{-1/2} = 0.303265`, and
  `1 - Φ(2) = 0.022750`, against `½ e^{-2} = 0.067668`;
* at `r = 0` the bound `1 - Φ(r) ≤ ½ e^{-r²/2}` is an equality, `1 - Φ(0) = 1/2`, so the constant
  `1/4` in place of `1/2` fails.

Each value `v` is checked as `|x - v| < 5 · 10⁻⁷`. The constants `(2π)^{-1/2}` and `e^{-1/2}`
come from `Real.inv_sqrt_two_mul_pi_gt_d8` and its companions, and `e^{-2}` from Mathlib's bounds
on `e^{-1}`. The tails come from partial sums of the alternating Maclaurin series of the error
function, in the form `Φ(r) - 1/2 = (r / √(2π)) ∑ₙ (-1)ⁿ (r²/2)ⁿ / (n! (2n + 1))`
(`TauCeti.Probability.mul_sum_range_two_mul_le_cdf_gaussianReal_sub_half` and
`TauCeti.Probability.cdf_gaussianReal_sub_half_le_mul_sum_range_two_mul_add_one`).
-/

open Finset ProbabilityTheory Real TauCeti.Probability

public noncomputable section

namespace TauCeti.Examples.GaussianTails

/-- `φ(0) ≈ 0.398942`, to within `5 · 10⁻⁷`. -/
theorem abs_gaussianPDFReal_zero_sub_lt : |gaussianPDFReal 0 1 0 - 0.398942| < 5e-7 := by
  rw [gaussianPDFReal_zero_one, abs_sub_lt_iff]
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  norm_num at h1 h2 ⊢
  constructor <;> linarith

/-- `φ(1) ≈ 0.241971`, to within `5 · 10⁻⁷`. -/
theorem abs_gaussianPDFReal_one_sub_lt : |gaussianPDFReal 0 1 1 - 0.241971| < 5e-7 := by
  rw [gaussianPDFReal_zero_one, abs_sub_lt_iff]
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  have h3 := exp_neg_half_gt_d8
  have h4 := exp_neg_half_lt_d8
  norm_num at h1 h2 h3 h4 ⊢
  constructor <;> nlinarith

/-- `½ e^{-1/2} = 0.303265`. -/
example : |rexp (-1 ^ 2 / 2) / 2 - 0.303265| < 5e-7 := by
  rw [abs_sub_lt_iff]
  have h3 := exp_neg_half_gt_d8
  have h4 := exp_neg_half_lt_d8
  norm_num at h3 h4 ⊢
  constructor <;> linarith

/-- `½ e^{-2} = 0.067668`. -/
example : |rexp (-2 ^ 2 / 2) / 2 - 0.067668| < 5e-7 := by
  have hsq : rexp (-2 ^ 2 / 2) = rexp (-1) ^ 2 := by
    rw [← exp_natCast_mul]
    norm_num
  have hlo := exp_neg_one_gt_d9
  have hhi := exp_neg_one_lt_d9
  rw [hsq, abs_sub_lt_iff]
  constructor <;> nlinarith

/-- `1 - Φ(1) = 0.158655`. -/
example : |(1 - cdf (gaussianReal 0 1) 1) - 0.158655| < 5e-7 := by
  have hlo := mul_sum_range_two_mul_le_cdf_gaussianReal_sub_half zero_le_one (by norm_num) 5
  have hhi := cdf_gaussianReal_sub_half_le_mul_sum_range_two_mul_add_one zero_le_one
    (by norm_num) 5
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  rw [one_div √(2 * π)] at hlo hhi
  generalize (√(2 * π))⁻¹ = s at hlo hhi h1 h2
  norm_num [sum_range_succ, Nat.factorial] at hlo hhi h1 h2
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- `1 - Φ(2) = 0.022750`. -/
example : |(1 - cdf (gaussianReal 0 1) 2) - 0.022750| < 5e-7 := by
  have hlo := mul_sum_range_two_mul_le_cdf_gaussianReal_sub_half zero_le_two (by norm_num) 8
  have hhi := cdf_gaussianReal_sub_half_le_mul_sum_range_two_mul_add_one zero_le_two
    (by norm_num) 8
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  rw [div_eq_mul_inv 2 √(2 * π)] at hlo hhi
  generalize (√(2 * π))⁻¹ = s at hlo hhi h1 h2
  norm_num [sum_range_succ, Nat.factorial] at hlo hhi h1 h2
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- At `r = 0` the tail bound `1 - Φ(r) ≤ ½ e^{-r²/2}` is an equality. -/
example : 1 - cdf (gaussianReal 0 1) 0 = rexp (-0 ^ 2 / 2) / 2 := by
  rw [cdf_gaussianReal_self 0 one_ne_zero]
  norm_num

/-- At `r = 0` the tail bound fails with the constant `1/4` in place of `1/2`. -/
example : ¬ 1 - cdf (gaussianReal 0 1) 0 ≤ rexp (-0 ^ 2 / 2) / 4 := by
  rw [cdf_gaussianReal_self 0 one_ne_zero]
  norm_num

end TauCeti.Examples.GaussianTails
