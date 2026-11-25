/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Cdf
import TauCeti.Analysis.SpecialFunctions.Erf.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Decimal checks for the standard Gaussian density and tails

Decimal values of the standard Gaussian density `φ` and of the upper tail `1 - Φ`, to six
decimal places, as in the Checks of §§1.1-1.2 of the GaussianIsoperimetryAndClusters roadmap:

* `φ(0) = 0.398942` and `φ(1) = 0.241971`;
* `½ e^{-1/2} = 0.303265` and `½ e^{-2} = 0.067668`;
* `1 - Φ(1) = 0.158655` and `1 - Φ(2) = 0.022750`, so the tail bounds
  `1 - Φ(r) < φ(r) / r` and `1 - Φ(r) < ½ e^{-r²/2}` are far from equality at `r = 1, 2`;
* at `r = 0` the bound `1 - Φ(r) ≤ ½ e^{-r²/2}` is an equality, `1 - Φ(0) = 1/2`, so the constant
  `1/4` in place of `1/2` fails.

Each value `v` is checked as `|x - v| < 5 · 10⁻⁷`. The tails come from the alternating Maclaurin
series of the error function (`TauCeti.Real.hasSum_erf`): for `r > 0`,
`1 - Φ(r) = 1/2 - (r / √(2π)) ∑ₙ (-1)ⁿ (r²/2)ⁿ / (n! (2n + 1))`, and partial sums with an even or
odd number of terms bound the alternating series from below or above. The constants `(2π)^{-1/2}`
and `e^{-1/2}` are bounded through their squares, from Mathlib's bounds on `π` and on `e^{-1}`.
-/

open Filter Finset ProbabilityTheory Real TauCeti.Probability
open scoped Nat Topology

public noncomputable section

namespace TauCeti.Examples.GaussianTails

/-- The magnitude `yⁿ / (n! (2n + 1))` of the `n`-th term of the erf series in `y = x²`. -/
noncomputable def term (y : ℝ) (n : ℕ) : ℝ := y ^ n / (n ! * (2 * n + 1))

/-- The terms decrease when `0 ≤ y ≤ 3`. -/
lemma term_antitone {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 3) : Antitone (term y) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [term, term, div_le_div_iff₀ (by positivity) (by positivity), Nat.factorial_succ]
  push_cast
  have h : y * (2 * n + 1) ≤ (n + 1) * (2 * (n + 1) + 1) := by
    have hn0 : (n : ℝ) ≤ n * n := by exact_mod_cast Nat.le_mul_self n
    nlinarith [mul_le_mul_of_nonneg_right hy (by positivity : (0 : ℝ) ≤ 2 * n + 1)]
  calc y ^ (n + 1) * (n ! * (2 * n + 1)) = y ^ n * n ! * (y * (2 * n + 1)) := by ring
    _ ≤ y ^ n * n ! * ((n + 1) * (2 * (n + 1) + 1)) := by gcongr
    _ = y ^ n * ((n + 1) * n ! * (2 * (n + 1) + 1)) := by ring

/-- The alternating series `∑ₙ (-1)ⁿ (r²/2)ⁿ / (n! (2n + 1))` sums to `(Φ(r) - 1/2) √(2π) / r`. -/
lemma hasSum_term (r : ℝ) (hr : r ≠ 0) :
    HasSum (fun n => (-1) ^ n * term (r ^ 2 / 2) n)
      ((1 / 2 - (1 - cdf (gaussianReal 0 1) r)) * √(2 * π) / r) := by
  set x := r / √2 with hx
  have h2 : √2 ≠ 0 := by positivity
  have hπ : √π ≠ 0 := by positivity
  have hc : 2 * x / √π ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero (div_ne_zero hr h2)) hπ
  have hxsq : x ^ 2 = r ^ 2 / 2 := by rw [hx, div_pow, sq_sqrt zero_le_two]
  have h := TauCeti.Real.hasSum_erf x
  have h' : HasSum (fun n => 2 * x / √π * ((-1) ^ n * term (r ^ 2 / 2) n))
      (2 * x / √π * ((1 / 2 - (1 - cdf (gaussianReal 0 1) r)) * √(2 * π) / r)) := by
    convert h using 1
    · ext n
      rw [term, ← hxsq]
      field_simp
      ring
    · rw [one_sub_cdf_gaussianReal_eq_erfc, TauCeti.Real.erfc_def, sqrt_mul zero_le_two, hx]
      field_simp
      ring
  exact (hasSum_mul_left_iff hc).1 h'

/-- Partial sums with an even or odd number of terms bound the series from below or above. -/
lemma bounds_term (r : ℝ) (hr : r ≠ 0) (hr3 : r ^ 2 / 2 ≤ 3) (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1) ^ i * term (r ^ 2 / 2) i ≤
        (1 / 2 - (1 - cdf (gaussianReal 0 1) r)) * √(2 * π) / r ∧
      (1 / 2 - (1 - cdf (gaussianReal 0 1) r)) * √(2 * π) / r ≤
        ∑ i ∈ range (2 * k + 1), (-1) ^ i * term (r ^ 2 / 2) i := by
  have h := (hasSum_term r hr).tendsto_sum_nat
  have ha := term_antitone (by positivity) hr3
  exact ⟨ha.alternating_series_le_tendsto h k, ha.tendsto_le_alternating_series h k⟩

/-- `(2π)^{-1/2}` to eight decimal places. -/
lemma inv_sqrt_two_pi_mem : 0.39894228 < (√(2 * π))⁻¹ ∧ (√(2 * π))⁻¹ < 0.39894229 := by
  have hpos : 0 < (√(2 * π))⁻¹ := by positivity
  have hsq : ((√(2 * π))⁻¹) ^ 2 = (2 * π)⁻¹ := by
    rw [inv_pow, sq_sqrt (by positivity)]
  have hlo := pi_gt_d20
  have hhi := pi_lt_d20
  constructor
  · refine lt_of_pow_lt_pow_left₀ 2 hpos.le ?_
    rw [hsq, lt_inv_comm₀ (by norm_num) (by positivity)]
    nlinarith
  · refine lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_
    rw [hsq, inv_lt_comm₀ (by positivity) (by norm_num)]
    nlinarith

/-- `e^{-1/2}` to eight decimal places. -/
lemma exp_neg_half_mem : 0.60653065 < rexp (-(1 / 2)) ∧ rexp (-(1 / 2)) < 0.60653067 := by
  have hsq : rexp (-(1 / 2)) ^ 2 = rexp (-1) := by
    rw [sq, ← exp_add]
    norm_num
  have hlo := exp_neg_one_gt_d9
  have hhi := exp_neg_one_lt_d9
  constructor
  · refine lt_of_pow_lt_pow_left₀ 2 (exp_pos _).le ?_
    rw [hsq]
    linarith
  · refine lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_
    rw [hsq]
    linarith

/-- `φ(0) = 0.398942`. -/
example : |gaussianPDFReal 0 1 0 - 0.398942| < 5e-7 := by
  rw [gaussianPDFReal_zero_one]
  have := inv_sqrt_two_pi_mem
  rw [abs_sub_lt_iff]
  norm_num at this ⊢
  constructor <;> linarith

/-- `φ(1) = 0.241971`. -/
example : |gaussianPDFReal 0 1 1 - 0.241971| < 5e-7 := by
  rw [gaussianPDFReal_zero_one]
  obtain ⟨h1, h2⟩ := inv_sqrt_two_pi_mem
  obtain ⟨h3, h4⟩ := exp_neg_half_mem
  rw [abs_sub_lt_iff]
  norm_num at h1 h2 h3 h4 ⊢
  constructor <;> nlinarith

/-- `½ e^{-1/2} = 0.303265`. -/
example : |rexp (-1 ^ 2 / 2) / 2 - 0.303265| < 5e-7 := by
  obtain ⟨h3, h4⟩ := exp_neg_half_mem
  rw [abs_sub_lt_iff]
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
  obtain ⟨hlo, hhi⟩ := bounds_term 1 one_ne_zero (by norm_num) 5
  obtain ⟨h1, h2⟩ := inv_sqrt_two_pi_mem
  have hs : 0 < √(2 * π) := by positivity
  generalize √(2 * π) = s at hlo hhi h1 h2 hs
  generalize 1 - cdf (gaussianReal 0 1) 1 = c at hlo hhi
  set T := (1 / 2 - c) * s / 1
  have hc : 1 / 2 - c = T * s⁻¹ * 1 := by simp only [T]; field_simp
  simp only [term, sum_range_succ, sum_range_zero, Nat.factorial] at hlo hhi
  norm_num at hlo hhi h1 h2
  have hT : 0 ≤ T := le_trans (by norm_num) hlo
  have hl := mul_le_mul hlo h1.le (by norm_num) hT
  have hu := mul_le_mul hhi h2.le (inv_nonneg.2 hs.le) (le_trans hT hhi)
  rw [abs_sub_lt_iff]
  constructor <;> nlinarith

/-- `1 - Φ(2) = 0.022750`. -/
example : |(1 - cdf (gaussianReal 0 1) 2) - 0.022750| < 5e-7 := by
  obtain ⟨hlo, hhi⟩ := bounds_term 2 two_ne_zero (by norm_num) 8
  obtain ⟨h1, h2⟩ := inv_sqrt_two_pi_mem
  have hs : 0 < √(2 * π) := by positivity
  generalize √(2 * π) = s at hlo hhi h1 h2 hs
  generalize 1 - cdf (gaussianReal 0 1) 2 = c at hlo hhi
  set T := (1 / 2 - c) * s / 2
  have hc : 1 / 2 - c = T * s⁻¹ * 2 := by simp only [T]; field_simp
  simp only [term, sum_range_succ, sum_range_zero, Nat.factorial] at hlo hhi
  norm_num at hlo hhi h1 h2
  have hT : 0 ≤ T := le_trans (by norm_num) hlo
  have hl := mul_le_mul hlo h1.le (by norm_num) hT
  have hu := mul_le_mul hhi h2.le (inv_nonneg.2 hs.le) (le_trans hT hhi)
  rw [abs_sub_lt_iff]
  constructor <;> nlinarith

/-- At `r = 0` the tail bound `1 - Φ(r) ≤ ½ e^{-r²/2}` is an equality. -/
example : 1 - cdf (gaussianReal 0 1) 0 = rexp (-0 ^ 2 / 2) / 2 := by
  rw [cdf_gaussianReal_self 0 one_ne_zero]
  norm_num

/-- At `r = 0` the tail bound fails with the constant `1/4` in place of `1/2`. -/
example : ¬ 1 - cdf (gaussianReal 0 1) 0 ≤ rexp (-0 ^ 2 / 2) / 4 := by
  rw [cdf_gaussianReal_self 0 one_ne_zero]
  norm_num

end TauCeti.Examples.GaussianTails
