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
import TauCeti.Analysis.SpecificLimits.Normed

/-!
# The logarithmic series on the closed unit disc

Mathlib's `Complex.hasSum_taylorSeries_neg_log` sums `∑ zⁿ / n` to `-log (1 - z)` on the open
unit disc. This file extends the identity to every `z ≠ 1` of the closed unit disc. On the unit
circle the series converges only conditionally, so the statement is a limit of the ordered
partial sums. Its proof combines Dirichlet's test, which gives convergence, with Abel's limit
theorem, which identifies the limit with the radial limit of `-log (1 - r z)`.

Taking imaginary parts at `z = exp (θ i)` gives the classical sawtooth series
`∑ sin (n θ) / n = (π - θ) / 2` for `0 < θ < 2π`. This is the conditionally convergent input that
evaluates the Hurwitz and Dirichlet L-functions at `s = 0`.

## Main results

* `Complex.tendsto_sum_range_taylorSeries_neg_log`: the partial sums of `∑ zⁿ / n` tend to
  `-log (1 - z)` for `‖z‖ ≤ 1` and `z ≠ 1`.
* `Real.tendsto_sum_Icc_sin_mul_div`: the sawtooth series
  `∑_{n=1}^N sin (n θ) / n → (π - θ) / 2` for `0 < θ < 2π`, using the argument
  `Complex.arg_one_sub_exp_mul_I` of `1 - exp (θ i)`.
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

end Complex

namespace Real

/-- **The sawtooth series.** For `0 < θ < 2π`, the ordered partial sums of `∑ sin (n θ) / n`
tend to `(π - θ) / 2`. The series converges only conditionally. -/
theorem tendsto_sum_Icc_sin_mul_div {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * π)) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, sin (n * θ) / n) atTop (𝓝 ((π - θ) / 2)) := by
  set w : ℂ := Complex.exp (θ * Complex.I) with hw
  have hnorm : ‖w‖ ≤ 1 := by rw [hw, Complex.norm_exp_ofReal_mul_I]
  have hw1 : w ≠ 1 := by
    intro h
    have hcos : Real.cos θ = 1 := by
      rw [← Complex.exp_ofReal_mul_I_re, ← hw, h, Complex.one_re]
    have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [hθ.1, Real.pi_pos]) hθ.2).mp hcos
    linarith [hθ.1]
  have h := ((Complex.continuous_im.tendsto _).comp
    (Complex.tendsto_sum_range_taylorSeries_neg_log hnorm hw1)).comp (tendsto_add_atTop_nat 1)
  rw [Complex.neg_im, Complex.log_im, hw, Complex.arg_one_sub_exp_mul_I hθ,
    show -((θ - π) / 2) = (π - θ) / 2 by ring] at h
  refine h.congr fun N ↦ ?_
  simp only [Function.comp_apply, Complex.im_sum]
  rw [sum_range_succ', ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp only [CharP.cast_eq_zero, div_zero, Complex.zero_im, add_zero]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [add_comm 1 i, ← Complex.exp_natCast_mul, ← mul_assoc,
    show ((i + 1 : ℕ) : ℂ) * θ = (((i + 1 : ℕ) * θ : ℝ) : ℂ) by push_cast; ring,
    Complex.div_natCast_im, Complex.exp_ofReal_mul_I_im]

end Real
