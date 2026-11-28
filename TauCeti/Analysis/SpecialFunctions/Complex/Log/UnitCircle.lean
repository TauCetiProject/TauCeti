/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.AbelLimit
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.UnitCircle
import TauCeti.Analysis.SpecificLimits.Normed

/-!
# The logarithmic series on the closed unit disc

Mathlib's `Complex.hasSum_taylorSeries_neg_log` sums `∑ zⁿ / n` to `-log (1 - z)` on the open
unit disc. This file extends the identity to every `z ≠ 1` of the closed unit disc. On the unit
circle the series converges only conditionally, so the statement is a limit of the ordered
partial sums. Its proof combines Dirichlet's test, which gives convergence, with Abel's limit
theorem, which identifies the limit with the radial limit of `-log (1 - r z)`.

At `z = exp (θ i)`, the imaginary part gives the sawtooth series used to evaluate the Hurwitz
and Dirichlet L-functions at `s = 0`. The real part gives the logarithmic cosine series.
Applying `TauCeti.norm_sum_range_smul_le_of_antitone` to the shifted geometric sums bounds the
errors in both evaluations.

## Main results

* `Complex.tendsto_sum_range_taylorSeries_neg_log`: the partial sums of `∑ zⁿ / n` tend to
  `-log (1 - z)` for `‖z‖ ≤ 1` and `z ≠ 1`.
* `Real.tendsto_sum_Icc_sin_mul_div`: the sawtooth series
  `∑_{n=1}^N sin (n θ) / n → (π - θ) / 2` for `0 < θ < 2π`, using the argument
  `Complex.arg_one_sub_exp_mul_I` of `1 - exp (θ i)`.
* `Real.tendsto_sum_Icc_cos_mul_div`: the cosine series `∑ cos (n θ) / n → -log (2 sin (θ / 2))`
  on the same interval, using `Complex.log_re` and the chord length.
* `Complex.norm_sum_range_pow_div_natCast_add_le`: a bound on finite blocks of the logarithmic
  series, giving the truncation bound `Complex.norm_neg_log_one_sub_sub_sum_range_le` on the disc.
  At `z = exp (θ i)`, the errors in the sine and cosine sums through `N` are at most
  `1 / ((N + 1) * sin (θ / 2))`
  (`Real.abs_sub_sum_Icc_sin_mul_div_le`, `Real.abs_sub_sum_Icc_cos_mul_div_le`).
-/

public section

open Filter Finset
open scoped Topology Real

namespace Complex

/-- **The logarithmic series on the closed unit disc.** For `‖z‖ ≤ 1` and `z ≠ 1`, the ordered
partial sums of `∑ zⁿ / n` tend to `-log (1 - z)`. On the open disc the series converges
absolutely (`Complex.hasSum_taylorSeries_neg_log`); on the unit circle only this ordered limit
holds. -/
theorem tendsto_sum_range_taylorSeries_neg_log {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    Tendsto (fun n : ℕ ↦ ∑ i ∈ range n, z ^ i / i) atTop (𝓝 (-log (1 - z))) := by
  -- the shifted terms `f i = zⁱ⁺¹ / (i + 1)`
  set f : ℕ → ℂ := fun i ↦ z ^ (i + 1) / (i + 1) with hf
  -- Dirichlet's test: the shifted partial sums converge to some `l`
  obtain ⟨l, hl⟩ : ∃ l, Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l) := by
    refine cauchySeq_tendsto_of_complete ?_
    have hanti : Antitone fun i : ℕ ↦ (1 : ℝ) / (i + 1) := fun a b hab ↦
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hab)
    have h0 : Tendsto (fun i : ℕ ↦ (1 : ℝ) / (i + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    -- the shifted geometric partial sums `∑ zⁱ⁺¹ = (∑ zⁱ) z` stay bounded
    have hbdd (n : ℕ) : ‖∑ i ∈ range n, z ^ (i + 1)‖ ≤ 2 / ‖z - 1‖ := by
      simp_rw [pow_succ, ← sum_mul, norm_mul]
      calc _ ≤ 2 / ‖z - 1‖ * 1 := by gcongr; exact TauCeti.norm_geom_sum_le hz hz1 n
        _ = 2 / ‖z - 1‖ := mul_one _
    convert hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded h0 hbdd using 3 with n i
    simp [hf, div_eq_inv_mul, Complex.real_smul]
  -- Abel's theorem identifies `l` with the radial limit of `-log (1 - r z) / r`
  have habel := tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hradial : Tendsto (fun r : ℂ ↦ ∑' n, f n * r ^ n) ((𝓝[<] (1 : ℝ)).map ofReal)
      (𝓝 (-log (1 - z))) := by
    rw [tendsto_map'_iff]
    have hcont : ContinuousAt (fun r : ℝ ↦ -log (1 - (r : ℂ) * z) / r) 1 := by
      have hslit : 1 - ((1 : ℝ) : ℂ) * z ∈ slitPlane := by
        simpa using mem_slitPlane_iff.mpr (Or.inl (re_one_sub_pos hz hz1))
      refine ContinuousAt.div ?_ (by fun_prop) (by simp)
      exact (ContinuousAt.comp (g := log) (f := fun r : ℝ ↦ 1 - (r : ℂ) * z) (x := 1)
        (continuousAt_clog hslit) (by fun_prop)).neg
    have hlim : Tendsto (fun r : ℝ ↦ -log (1 - (r : ℂ) * z) / r) (𝓝[<] 1)
        (𝓝 (-log (1 - z))) := by
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have hrz : ‖(r : ℂ) * z‖ < 1 := by
      rw [norm_mul, norm_real, Real.norm_of_nonneg hr.1.le]
      calc r * ‖z‖ ≤ r * 1 := by gcongr; exact hr.1.le
        _ < 1 := by linarith [hr.2]
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.1.ne'
    have hsum := (hasSum_taylorSeries_neg_log' hrz).div_const (r : ℂ)
    rw [← hsum.tsum_eq]
    refine tsum_congr fun n ↦ ?_
    simp only [hf, mul_pow, pow_succ]
    field_simp
  have hl' : l = -log (1 - z) := tendsto_nhds_unique habel hradial
  -- undo the shift by one; the term at `0` vanishes
  rw [← hl', ← tendsto_add_atTop_iff_nat 1]
  refine hl.congr fun n ↦ ?_
  rw [sum_range_succ']
  simp [hf]

/-- A finite block of the logarithmic series starting at index `N + 1` is bounded in norm by
`2 * ‖z‖ ^ (N + 1) / (‖z - 1‖ * (N + 1))` on the closed unit disc away from `1`. -/
theorem norm_sum_range_pow_div_natCast_add_le {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1)
    (N H : ℕ) :
    ‖∑ i ∈ range H, z ^ (N + 1 + i) / (↑(N + 1 + i) : ℂ)‖ ≤
      2 * ‖z‖ ^ (N + 1) / (‖z - 1‖ * (N + 1)) := by
  have hprefix (k : ℕ) : ‖∑ i ∈ range k, z ^ (N + 1 + i)‖ ≤
      ‖z‖ ^ (N + 1) * (2 / ‖z - 1‖) := by
    simp only [pow_add z (N + 1), ← mul_sum, norm_mul, norm_pow]
    gcongr
    exact TauCeti.norm_geom_sum_le hz hz1 k
  have hw (i j : ℕ) (hij : i ≤ j) :
      (↑(N + 1 + j) : ℝ)⁻¹ ≤ (↑(N + 1 + i) : ℝ)⁻¹ := by
    refine inv_anti₀ (by positivity) ?_
    exact_mod_cast Nat.add_le_add_left hij (N + 1)
  have hweighted := TauCeti.norm_sum_range_smul_le_of_antitone (n := H)
    (w := fun i ↦ (↑(N + 1 + i) : ℝ)⁻¹) (fun k _ ↦ hprefix k)
    (fun i _ j _ hij ↦ hw i j hij) (by positivity)
  have hrhs :
      ‖z‖ ^ (N + 1) * (2 / ‖z - 1‖) * (↑(N + 1 + 0) : ℝ)⁻¹ =
        2 * ‖z‖ ^ (N + 1) / (‖z - 1‖ * (N + 1)) := by grind
  rw [← hrhs]
  simpa only [real_smul, ofReal_inv, ofReal_natCast, div_eq_inv_mul] using hweighted

/-- The error after truncating the logarithmic series on the closed unit disc away from
`1` is bounded by the geometric prefix bound times the first omitted reciprocal index. -/
theorem norm_neg_log_one_sub_sub_sum_range_le {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1)
    (N : ℕ) :
    ‖-log (1 - z) - ∑ n ∈ range (N + 1), z ^ n / n‖ ≤
      2 * ‖z‖ ^ (N + 1) / (‖z - 1‖ * (N + 1)) := by
  have hlim := ((tendsto_sum_range_taylorSeries_neg_log hz hz1).comp
    ((tendsto_add_atTop_nat (N + 1)).congr fun m ↦ Nat.add_comm m (N + 1))).sub_const
      (∑ n ∈ range (N + 1), z ^ n / n)
  refine le_of_tendsto' hlim.norm fun m ↦ ?_
  have hsplit :
      (∑ n ∈ range (N + 1 + m), z ^ n / n) - ∑ n ∈ range (N + 1), z ^ n / n =
        ∑ i ∈ range m, z ^ (N + 1 + i) / (↑(N + 1 + i) : ℂ) := by
    rw [sum_range_add, add_sub_cancel_left]
  rw [Function.comp_apply, hsplit]
  exact norm_sum_range_pow_div_natCast_add_le hz hz1 N m

end Complex

namespace Real

private theorem sum_range_exp_mul_I_pow_div (θ : ℝ) (N : ℕ) :
    ∑ n ∈ range (N + 1), Complex.exp (θ * Complex.I) ^ n / (n : ℂ) =
      ∑ n ∈ Icc 1 N, Complex.exp (((n : ℝ) * θ) * Complex.I) / (n : ℂ) := by
  rw [sum_range_succ', ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp only [CharP.cast_eq_zero, div_zero, add_zero]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [← Complex.exp_natCast_mul, ← mul_assoc, Complex.ofReal_natCast,
    add_comm n 1]

/-- **The sawtooth series.** For `0 < θ < 2π`, the ordered partial sums of `∑ sin (n θ) / n`
tend to `(π - θ) / 2`. -/
theorem tendsto_sum_Icc_sin_mul_div {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * π)) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, sin (n * θ) / n) atTop (𝓝 ((π - θ) / 2)) := by
  have h := ((Complex.continuous_im.tendsto _).comp
    (Complex.tendsto_sum_range_taylorSeries_neg_log
      (by rw [Complex.norm_exp_ofReal_mul_I]) (Complex.exp_ofReal_mul_I_ne_one_of_mem_Ioo hθ))).comp
    (tendsto_add_atTop_nat 1)
  rw [Complex.neg_im, Complex.log_im, Complex.arg_one_sub_exp_mul_I hθ, neg_div', neg_sub] at h
  refine h.congr fun N ↦ ?_
  simp only [Function.comp_apply]
  rw [sum_range_exp_mul_I_pow_div]
  simp only [Complex.im_sum, Complex.div_natCast_im, ← Complex.ofReal_mul,
    Complex.exp_ofReal_mul_I_im]

/-- **The logarithmic cosine series.** For `0 < θ < 2π`, the ordered partial sums of
`∑ cos (n θ) / n` tend to `-log (2 sin (θ / 2))`. -/
theorem tendsto_sum_Icc_cos_mul_div {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * π)) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, cos (n * θ) / n) atTop
      (𝓝 (-log (2 * sin (θ / 2)))) := by
  have h := ((Complex.continuous_re.tendsto _).comp
    (Complex.tendsto_sum_range_taylorSeries_neg_log
      (by rw [Complex.norm_exp_ofReal_mul_I]) (Complex.exp_ofReal_mul_I_ne_one_of_mem_Ioo hθ))).comp
    (tendsto_add_atTop_nat 1)
  rw [Complex.neg_re, Complex.log_re, norm_sub_rev (1 : ℂ),
    Complex.norm_exp_ofReal_mul_I_sub_one_of_mem_Icc (Set.Ioo_subset_Icc_self hθ)] at h
  refine h.congr fun N ↦ ?_
  simp only [Function.comp_apply]
  rw [sum_range_exp_mul_I_pow_div]
  simp only [Complex.re_sum, Complex.div_natCast_re, ← Complex.ofReal_mul,
    Complex.exp_ofReal_mul_I_re]

private theorem norm_neg_log_one_sub_exp_sub_sum_Icc_le {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * π))
    (N : ℕ) :
    ‖-Complex.log (1 - Complex.exp (θ * Complex.I)) -
      ∑ n ∈ Icc 1 N, Complex.exp (((n : ℝ) * θ) * Complex.I) / (n : ℂ)‖ ≤
      1 / ((N + 1) * sin (θ / 2)) := by
  have h := Complex.norm_neg_log_one_sub_sub_sum_range_le
    (by rw [Complex.norm_exp_ofReal_mul_I]) (Complex.exp_ofReal_mul_I_ne_one_of_mem_Ioo hθ) N
  rw [sum_range_exp_mul_I_pow_div,
    Complex.norm_exp_ofReal_mul_I_sub_one_of_mem_Icc (Set.Ioo_subset_Icc_self hθ),
    Complex.norm_exp_ofReal_mul_I, one_pow, mul_one] at h
  convert h using 1
  field_simp

/-- The error after the first `N` terms of the sawtooth series is at most
`1 / ((N + 1) * sin (θ / 2))` when `0 < θ < 2π`. See Pomerance, *Remarks on the
Pólya–Vinogradov inequality*, Lemma 4. -/
theorem abs_sub_sum_Icc_sin_mul_div_le {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * π)) (N : ℕ) :
    |(π - θ) / 2 - ∑ n ∈ Icc 1 N, sin (n * θ) / n| ≤
      1 / ((N + 1) * sin (θ / 2)) := by
  simpa only [Complex.sub_im, Complex.neg_im, Complex.log_im, Complex.im_sum,
    Complex.div_natCast_im, ← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_im,
    Complex.arg_one_sub_exp_mul_I hθ, neg_div', neg_sub] using
    (Complex.abs_im_le_norm _).trans (norm_neg_log_one_sub_exp_sub_sum_Icc_le hθ N)

/-- The error after the first `N` terms of the logarithmic cosine series is at most
`1 / ((N + 1) * sin (θ / 2))` when `0 < θ < 2π`. -/
theorem abs_sub_sum_Icc_cos_mul_div_le {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * π)) (N : ℕ) :
    |-log (2 * sin (θ / 2)) - ∑ n ∈ Icc 1 N, cos (n * θ) / n| ≤
      1 / ((N + 1) * sin (θ / 2)) := by
  simpa only [Complex.sub_re, Complex.neg_re, Complex.log_re, Complex.re_sum, norm_sub_rev (1 : ℂ),
    Complex.div_natCast_re, ← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Complex.norm_exp_ofReal_mul_I_sub_one_of_mem_Icc (Set.Ioo_subset_Icc_self hθ)] using
    (Complex.abs_re_le_norm _).trans (norm_neg_log_one_sub_exp_sub_sum_Icc_le hθ N)

end Real
