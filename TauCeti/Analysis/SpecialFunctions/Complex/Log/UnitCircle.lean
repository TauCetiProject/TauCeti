/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.AbelLimit
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecificLimits.Normed

/-!
# The logarithmic series on the closed unit disc

Mathlib's `Complex.hasSum_taylorSeries_neg_log` sums `∑ zⁿ / n` to `-log (1 - z)` on the open
unit disc. This file extends the identity to every `z ≠ 1` of the closed unit disc. On the unit
circle the series converges only conditionally, so the statement is a limit of the ordered
partial sums. Its proof combines Dirichlet's test, which gives convergence, with Abel's limit
theorem, which identifies the limit with the radial limit of `-log (1 - r z)`.

## Main results

* `Complex.tendsto_sum_range_taylorSeries_neg_log`: the partial sums of `∑ zⁿ / n` tend to
  `-log (1 - z)` for `‖z‖ ≤ 1` and `z ≠ 1`.
* `Complex.norm_neg_log_one_sub_sub_sum_Icc_pow_div_le`: the remainder after the terms through
  degree `N` is bounded by `2 / ((N + 1) * ‖z - 1‖)` on the same domain, by
  `Finset.norm_sum_range_smul_le_of_antitoneOn` and the geometric sum bound.
-/

public section

open Filter Finset
open scoped Topology

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

/-- On the closed unit disc away from `1`, the remainder of the logarithmic series after
degree `N` is bounded by `2 / ((N + 1) * ‖z - 1‖)`. -/
theorem norm_neg_log_one_sub_sub_sum_Icc_pow_div_le {z : ℂ} (hz : ‖z‖ ≤ 1) (hz₁ : z ≠ 1)
    (N : ℕ) :
    ‖-log (1 - z) - ∑ j ∈ Icc 1 N, z ^ j / j‖ ≤ 2 / ((N + 1 : ℝ) * ‖z - 1‖) := by
  have hhead : ∑ j ∈ range (N + 1), z ^ j / (j : ℂ) =
      ∑ j ∈ Icc 1 N, z ^ j / (j : ℂ) := by
    rw [sum_range_eq_add_Ico _ (Nat.succ_pos N)]
    simp [Nat.succ_eq_add_one, Ico_add_one_right_eq_Icc]
  have hlim := ((tendsto_sum_range_taylorSeries_neg_log hz hz₁).comp
    (tendsto_add_atTop_nat (N + 1))).sub_const (∑ j ∈ range (N + 1), z ^ j / (j : ℂ))
  rw [← hhead]
  refine le_of_tendsto hlim.norm (Eventually.of_forall fun M ↦ ?_)
  simp only [Function.comp_apply, Nat.add_comm M (N + 1), sum_range_add, add_sub_cancel_left]
  have hanti : Antitone fun j : ℕ ↦ (N + 1 + (j : ℝ))⁻¹ := by
    intro i j hij
    exact inv_anti₀ (by positivity) (add_le_add_right (Nat.cast_le.mpr hij) _)
  have hgeom (L : ℕ) : ‖∑ j ∈ range L, z ^ (N + 1 + j)‖ ≤ 2 / ‖z - 1‖ := by
    simp only [pow_add z (N + 1), ← mul_sum, norm_mul]
    have hpow : ‖z ^ (N + 1)‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hz
    exact (mul_le_of_le_one_left (norm_nonneg _) hpow).trans
      (TauCeti.norm_geom_sum_le hz hz₁ L)
  calc
    _ = ‖∑ j ∈ range M, (N + 1 + (j : ℝ))⁻¹ • z ^ (N + 1 + j)‖ := by
      congr 1
      refine sum_congr rfl fun j _ ↦ ?_
      rw [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      push_cast
      ring
    _ ≤ (N + 1 : ℝ)⁻¹ * (2 / ‖z - 1‖) := by
      simpa only [Nat.cast_zero, add_zero] using
        norm_sum_range_smul_le_of_antitoneOn (hanti.antitoneOn (Set.Iio M))
          (by positivity) (fun L _ ↦ hgeom L)
    _ = _ := by
      field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz₁)]

end Complex
