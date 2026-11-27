/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Complex.Log.UnitCircle
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Harmonic sine and cosine series

On `(0, 2π)`, `Real.tendsto_sum_Icc_cos_mul_div` gives the cosine series limit
`-log (2 * sin (θ / 2))`. On the same interval, `Real.tendsto_sum_Icc_sin_mul_div` gives the
sawtooth series limit `(π - θ) / 2`. Both limits follow from the remainder estimates below.

The remainder estimates `Real.abs_pi_sub_div_two_sub_sum_Icc_sin_mul_div_le` and
`Real.abs_neg_log_two_mul_sin_half_sub_sum_Icc_cos_mul_div_le` follow from the joint bound
`Complex.norm_sub_sum_Icc_exp_mul_I_div_le`, which uses
`Complex.norm_neg_log_one_sub_sub_sum_Icc_pow_div_le` and the chord length formula
`Complex.norm_exp_I_mul_ofReal_sub_one`. The imaginary part of the logarithm is computed
using `Complex.arg_one_sub_exp_mul_I`.

The sine remainder is the pointwise bound in C. Pomerance,
*Remarks on the Pólya–Vinogradov inequality*, proof of Lemma 4.
-/

public section

open Filter Finset
open scoped Topology

open Real in
/-- The complex logarithmic remainder at `exp (θ * I)`, with its real and imaginary limits
written in terms of the angle, has norm at most `1 / ((N + 1) * sin (θ / 2))` on `(0, 2π)`. -/
theorem Complex.norm_sub_sum_Icc_exp_mul_I_div_le {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * π))
    (N : ℕ) :
    ‖(-Real.log (2 * Real.sin (θ / 2)) : ℝ) + (((π - θ) / 2 : ℝ) : ℂ) * Complex.I -
      ∑ j ∈ Icc 1 N, Complex.exp ((j * θ : ℝ) * Complex.I) / j‖ ≤
        1 / ((N + 1 : ℝ) * Real.sin (θ / 2)) := by
  have hsin : 0 < Real.sin (θ / 2) :=
    sin_pos_of_pos_of_lt_pi (half_pos hθ.1) (by linarith [hθ.2])
  set z := Complex.exp (θ * Complex.I) with hzdef
  have hchord : ‖z - 1‖ = 2 * Real.sin (θ / 2) := by
    rw [hzdef, mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one,
      Real.norm_of_nonneg (by positivity)]
  have hchord_pos : 0 < ‖z - 1‖ := hchord ▸ mul_pos two_pos hsin
  have hz₁ : z ≠ 1 := sub_ne_zero.mp (norm_pos_iff.mp hchord_pos)
  have hz : ‖z‖ ≤ 1 := (Complex.norm_exp_ofReal_mul_I θ).le
  have hlog : -Complex.log (1 - z) =
      (-Real.log (2 * Real.sin (θ / 2)) : ℝ) + (((π - θ) / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [Complex.neg_re, Complex.log_re, norm_sub_rev 1 z, hchord]
      simp
    · rw [Complex.neg_im, Complex.log_im, hzdef, Complex.arg_one_sub_exp_mul_I hθ]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
      ring
  have hsum : ∑ j ∈ Icc 1 N, z ^ j / (j : ℂ) =
      ∑ j ∈ Icc 1 N, Complex.exp ((j * θ : ℝ) * Complex.I) / j := by
    simp only [hzdef, ← Complex.exp_natCast_mul, ← mul_assoc, Complex.ofReal_mul,
      Complex.ofReal_natCast]
  calc
    _ ≤ 2 / ((N + 1 : ℝ) * ‖z - 1‖) := by
      rw [← hlog, ← hsum]
      exact Complex.norm_neg_log_one_sub_sub_sum_Icc_pow_div_le hz hz₁ N
    _ = _ := by
      rw [hchord]
      field_simp [hsin.ne']

namespace Real

/-- For `0 < θ < 2π`, the difference between the cosine partial sum through `N` and its
limit `-log (2 * sin (θ / 2))` is at most `1 / ((N + 1) * sin (θ / 2))` in absolute value. -/
theorem abs_neg_log_two_mul_sin_half_sub_sum_Icc_cos_mul_div_le {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (2 * π)) (N : ℕ) :
    |-log (2 * sin (θ / 2)) - ∑ j ∈ Icc 1 N, cos (j * θ) / j| ≤
      1 / ((N + 1 : ℝ) * sin (θ / 2)) := by
  refine le_trans ?_ (Complex.norm_sub_sum_Icc_exp_mul_I_div_le hθ N)
  convert Complex.abs_re_le_norm _ using 1
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
    Complex.ofReal_im, neg_zero, add_zero, Complex.re_sum, Complex.div_natCast_re,
    Complex.exp_ofReal_mul_I_re]

/-- **Sine series remainder bound.** For `0 < θ < 2π`, the sine series beyond the first
`N` terms has absolute value at most `1 / ((N + 1) * sin (θ / 2))`
(Pomerance, proof of Lemma 4). -/
theorem abs_pi_sub_div_two_sub_sum_Icc_sin_mul_div_le {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (2 * π)) (N : ℕ) :
    |(π - θ) / 2 - ∑ j ∈ Icc 1 N, sin (j * θ) / j| ≤ 1 / ((N + 1 : ℝ) * sin (θ / 2)) := by
  refine le_trans ?_ (Complex.norm_sub_sum_Icc_exp_mul_I_div_le hθ N)
  convert Complex.abs_im_le_norm _ using 1
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
    Complex.ofReal_re, zero_add, Complex.im_sum, Complex.div_natCast_im,
    Complex.exp_ofReal_mul_I_im]

/-- An absolute error bounded by `1 / ((N + 1) * c)` gives convergence to the target. -/
private theorem tendsto_of_abs_sub_le {f : ℕ → ℝ} {a c : ℝ}
    (h : ∀ N, |a - f N| ≤ 1 / ((N + 1 : ℝ) * c)) : Tendsto f atTop (𝓝 a) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun N : ℕ ↦ 1 / ((N + 1 : ℝ) * c))
    (fun _ ↦ dist_nonneg) (fun N ↦ ?_) ?_
  · rw [dist_comm, Real.dist_eq]
    exact h N
  · simpa only [div_mul_eq_div_div, zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const c

/-- For `0 < θ < 2π`, the ordered partial sums of `∑ cos (j * θ) / j` converge to
`-log (2 * sin (θ / 2))`. -/
theorem tendsto_sum_Icc_cos_mul_div {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * π)) :
    Tendsto (fun N : ℕ ↦ ∑ j ∈ Icc 1 N, cos (j * θ) / j) atTop
      (𝓝 (-log (2 * sin (θ / 2)))) :=
  tendsto_of_abs_sub_le (abs_neg_log_two_mul_sin_half_sub_sum_Icc_cos_mul_div_le hθ)

/-- **The sawtooth series.** For `0 < θ < 2π`, the ordered partial sums of `∑ sin (n θ) / n`
tend to `(π - θ) / 2`. -/
theorem tendsto_sum_Icc_sin_mul_div {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * π)) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, sin (n * θ) / n) atTop (𝓝 ((π - θ) / 2)) :=
  tendsto_of_abs_sub_le (abs_pi_sub_div_two_sub_sum_Icc_sin_mul_div_le hθ)

end Real
