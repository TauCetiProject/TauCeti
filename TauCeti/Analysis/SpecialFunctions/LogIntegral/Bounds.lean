/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Unoffset
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Analysis.SpecialFunctions.Exp.Integrals
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Log.Deriv

/-!
# Explicit bounds for the logarithmic integral

This file establishes explicit numerical enclosures and analytical inequalities for both the
unoffset logarithmic integral `TauCeti.Real.li` (`li`) and the offset logarithmic integral
`TauCeti.Real.logIntegral` (`Li`):

* `TauCeti.Real.tsum_pow_div_mul_factorial_log_two_ge`,
  `TauCeti.Real.tsum_pow_div_mul_factorial_log_two_le`,
  `TauCeti.Real.log_log_two_ge`, `TauCeti.Real.log_log_two_le`: unconditional rational
  enclosures `0.834438 ≤ ∑_{n ≥ 1} (log 2)^n / (n · n!) ≤ 0.834462` and
  `-0.366513 ≤ log (log 2) ≤ -0.366512`.
* `TauCeti.Real.li_two_gt`, `TauCeti.Real.li_two_lt`,
  `TauCeti.Real.li_two_mem_Icc`: unconditional bounds `0.96 < li 2 < 1.14`, and
  the sharp enclosure `1.0451 ≤ li 2 ≤ 1.0452` (hence `1.039 ≤ li 2 ≤ 1.06`) conditional on
  `|γ - 0.5772156649| < 1e-9`.
* `TauCeti.Real.li_three_div_two_gt`: `0.04 < li (3 / 2)`.
* `TauCeti.Real.integral_inv_log_rpow_lt_div_add`,
  `TauCeti.Real.integral_inv_log_pow_seven_lt`: strict explicit upper bounds for
  `∫ t in 2..x, (log t ^ k)⁻¹` for real exponents `k ≥ 0`, together with the `k = 7`
  specialization.
* `TauCeti.Real.strictMonoOn_logIntegral_sub_div_log`,
  `TauCeti.Real.le_logIntegral_sub_div_log`, `TauCeti.Real.lt_logIntegral_sub_div_log`,
  `TauCeti.Real.logIntegral_sub_div_log_eq_iff`, `TauCeti.Real.logIntegral_sub_div_log_lt`,
  `TauCeti.Real.existsUnique_logIntegral_sub_div_log_eq_zero`,
  `TauCeti.Real.mem_Ioo_of_logIntegral_sub_div_log_eq_zero`,
  `TauCeti.Real.sub_div_log_sq_le_logIntegral_sub_div_log`: monotonicity, explicit envelopes,
  localization of the unique zero in `(6.5797, 6.5798)`, and the lower bound
  `(x - 6.58) / (log x) ^ 2 ≤ Li x - x / log x` for `6.58 ≤ x` (Fiori–Kadiri–Swidinsky, Lemma 20).
-/

public section

namespace TauCeti.Real

open Filter MeasureTheory Set
open scoped Nat Topology

/-! ### Enclosures of `li 2` and `li (3 / 2)` -/

private theorem liSeries_log_two_lower :
    (0.834461034 : ℝ) ≤ liSeries (Real.log 2) := by
  have hq : (0.69314718 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmono : liSeries (0.69314718 : ℝ) ≤
      liSeries (Real.log 2) :=
    strictMono_liSeries.monotone hq
  have hpart : (0.834461034 : ℝ) ≤ liSeriesPartial 10 (0.69314718 : ℝ) := by
    simp only [liSeriesPartial_def, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.factorial_succ, Nat.factorial_zero]
    norm_num
  exact hpart.trans
    (((by rw [liSeriesPartial_def]; exact sum_range_le_liSeries (by norm_num) 10) :
      liSeriesPartial 10 (0.69314718 : ℝ) ≤ liSeries (0.69314718 : ℝ)).trans hmono)

private theorem liSeries_log_two_upper :
    liSeries (Real.log 2) ≤ (0.834461037 : ℝ) := by
  have hq : Real.log 2 ≤ (0.693147181 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hmono : liSeries (Real.log 2) ≤
      liSeries (0.693147181 : ℝ) :=
    strictMono_liSeries.monotone hq
  have htail := liSeries_le_partial_add 10 (y := (0.693147181 : ℝ))
    (by norm_num) (by norm_num)
  have hnum : liSeriesPartial 10 (0.693147181 : ℝ) +
      ((0.693147181 : ℝ) ^ (10 + 1) / (((10 : ℝ) + 1) * ((10 + 1)! : ℝ))) *
        (((10 : ℝ) + 2) / ((10 : ℝ) + 2 - (0.693147181 : ℝ))) ≤ (0.834461037 : ℝ) := by
    simp only [liSeriesPartial_def, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.factorial_succ, Nat.factorial_zero]
    norm_num
  exact hmono.trans (htail.trans hnum)

/-- Lower bound `0.834438 ≤ ∑' n, (log 2) ^ (n + 1) / ((n + 1) * (n + 1)!)`. -/
theorem tsum_pow_div_mul_factorial_log_two_ge :
    (0.834438 : ℝ) ≤
      ∑' n : ℕ, Real.log 2 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  rw [← liSeries_def]
  exact (by norm_num : (0.834438 : ℝ) ≤ 0.834461034).trans liSeries_log_two_lower

/-- Upper bound `∑' n, (log 2) ^ (n + 1) / ((n + 1) * (n + 1)!) ≤ 0.834462`. -/
theorem tsum_pow_div_mul_factorial_log_two_le :
    ∑' n : ℕ, Real.log 2 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) ≤
      (0.834462 : ℝ) := by
  rw [← liSeries_def]
  exact liSeries_log_two_upper.trans (by norm_num)

private theorem log_log_two_lower_tight : (-0.36651295 : ℝ) ≤ Real.log (Real.log 2) := by
  have hq : (0.69314718 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmono : Real.log (0.69314718 : ℝ) ≤ Real.log (Real.log 2) :=
    Real.log_le_log (by norm_num) hq
  have hlow := neg_two_mul_artanhPartial_add_le_log (a := (0.69314718 : ℝ))
    (by norm_num) (by norm_num) 5
  have hnum : (-0.36651295 : ℝ) ≤
      -2 * (artanhPartial 5 ((1 - (0.69314718 : ℝ)) / (1 + (0.69314718 : ℝ))) +
        ((1 - (0.69314718 : ℝ)) / (1 + (0.69314718 : ℝ))) ^ (2 * 5 + 1) /
          (1 - ((1 - (0.69314718 : ℝ)) / (1 + (0.69314718 : ℝ))) ^ 2)) := by
    simp only [artanhPartial_def, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  exact hnum.trans (hlow.trans hmono)

private theorem log_log_two_upper_tight : Real.log (Real.log 2) ≤ (-0.36651290 : ℝ) := by
  have hq : Real.log 2 ≤ (0.693147181 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hmono : Real.log (Real.log 2) ≤ Real.log (0.693147181 : ℝ) :=
    Real.log_le_log (Real.log_pos one_lt_two) hq
  have hup := log_le_neg_two_mul_artanhPartial (a := (0.693147181 : ℝ))
    (by norm_num) (by norm_num) 5
  have hnum : -2 * artanhPartial 5 ((1 - (0.693147181 : ℝ)) / (1 + (0.693147181 : ℝ))) ≤
      (-0.36651290 : ℝ) := by
    simp only [artanhPartial_def, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  exact hmono.trans (hup.trans hnum)

/-- Lower bound `-0.366513 ≤ log (log 2)`. -/
theorem log_log_two_ge : (-0.366513 : ℝ) ≤ Real.log (Real.log 2) :=
  (by norm_num : (-0.366513 : ℝ) ≤ -0.36651295).trans log_log_two_lower_tight

/-- Upper bound `log (log 2) ≤ -0.366512`. -/
theorem log_log_two_le : Real.log (Real.log 2) ≤ (-0.366512 : ℝ) :=
  log_log_two_upper_tight.trans (by norm_num)

private theorem li_two_eq :
    li 2 = Real.eulerMascheroniConstant + Real.log (Real.log 2) +
      ∑' n : ℕ, Real.log 2 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  rw [li_eq_add_liSeries, liSeries_def]

/-- Unconditional lower bound `0.96 < li 2`. -/
theorem li_two_gt : (0.96 : ℝ) < li 2 := by
  rw [li_two_eq]
  linarith [Real.one_half_lt_eulerMascheroniConstant, log_log_two_ge,
    tsum_pow_div_mul_factorial_log_two_ge]

/-- Unconditional upper bound `li 2 < 1.14`. -/
theorem li_two_lt : li 2 < (1.14 : ℝ) := by
  rw [li_two_eq]
  linarith [Real.eulerMascheroniConstant_lt_two_thirds, log_log_two_le,
    tsum_pow_div_mul_factorial_log_two_le]

/-- Conditional sharp enclosure of `li 2` from `|γ - 0.5772156649| < 1e-9`:
`1.0451 ≤ li 2 ≤ 1.0452`. -/
theorem li_two_mem_Icc
    (hγ : |Real.eulerMascheroniConstant - 0.5772156649| < 1e-9) :
    li 2 ∈ Icc (1.0451 : ℝ) 1.0452 := by
  rw [mem_Icc, li_two_eq]
  have hγ_bounds := abs_lt.mp hγ
  refine ⟨?_, ?_⟩ <;>
    linarith [hγ_bounds.1, hγ_bounds.2, log_log_two_ge, log_log_two_le,
      tsum_pow_div_mul_factorial_log_two_ge, tsum_pow_div_mul_factorial_log_two_le]

/-- Coarse conditional enclosure `1.039 ≤ li 2 ≤ 1.06` from `|γ - 0.5772156649| < 1e-9`. -/
theorem li_two_mem_Icc_coarse
    (hγ : |Real.eulerMascheroniConstant - 0.5772156649| < 1e-9) :
    li 2 ∈ Icc (1.039 : ℝ) 1.06 := by
  have h := li_two_mem_Icc hγ
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem log_three_div_two_lower : (0.40546 : ℝ) ≤ Real.log (3 / 2) := by
  have hle := two_mul_artanhPartial_le_log (a := (3 / 2 : ℝ)) (by norm_num) 4
  have hnum : (0.40546 : ℝ) ≤
      2 * artanhPartial 4 (((3 / 2 : ℝ) - 1) / ((3 / 2 : ℝ) + 1)) := by
    simp only [artanhPartial_def, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  exact hnum.trans hle

private theorem log_log_three_div_two_gt : (-0.903 : ℝ) < Real.log (Real.log (3 / 2)) := by
  have h2_lo : (0.81092 : ℝ) ≤ 2 * Real.log (3 / 2) := by linarith [log_three_div_two_lower]
  have hlog2_hi : Real.log 2 ≤ (0.69315 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hsplit : Real.log (Real.log (3 / 2)) = Real.log (2 * Real.log (3 / 2)) - Real.log 2 := by
    rw [Real.log_mul two_ne_zero (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)).ne']
    ring
  have hmono : Real.log (0.81092 : ℝ) ≤ Real.log (2 * Real.log (3 / 2)) :=
    Real.log_le_log (by norm_num) h2_lo
  have hlow := neg_two_mul_artanhPartial_add_le_log (a := (0.81092 : ℝ))
    (by norm_num) (by norm_num) 3
  have hnum : (-0.20985 : ℝ) <
      -2 * (artanhPartial 3 ((1 - (0.81092 : ℝ)) / (1 + (0.81092 : ℝ))) +
        ((1 - (0.81092 : ℝ)) / (1 + (0.81092 : ℝ))) ^ (2 * 3 + 1) /
          (1 - ((1 - (0.81092 : ℝ)) / (1 + (0.81092 : ℝ))) ^ 2)) := by
    simp only [artanhPartial_def, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  linarith

/-- Unconditional lower bound `0.04 < li (3 / 2)`. -/
theorem li_three_div_two_gt : (0.04 : ℝ) < li (3 / 2) := by
  have hlog32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hser_lo : (0.446 : ℝ) < liSeries (Real.log (3 / 2)) := by
    have hge := sum_range_le_liSeries hlog32.le 2
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at hge
    norm_num at hge
    have hq := log_three_div_two_lower
    have h2 : (0.40546 : ℝ) + (0.40546 : ℝ) ^ 2 / 4 ≤
        Real.log (3 / 2) + Real.log (3 / 2) ^ 2 / 4 := by
      gcongr
    have hnum : (0.446 : ℝ) < (0.40546 : ℝ) + (0.40546 : ℝ) ^ 2 / 4 := by norm_num
    linarith [hge, h2, hnum]
  rw [li_def, ← liSeries_def]
  linarith [Real.one_half_lt_eulerMascheroniConstant, log_log_three_div_two_gt]

/-! ### Strict explicit upper bounds for integrals of `(log t ^ k)⁻¹` -/

/-- Strict explicit upper bound for `k ≥ 0` and `x ≥ 2`:
`∫ t in 2..x, (log t ^ k)⁻¹ <`
`  x / log x ^ k + k * (√x / log 2 ^ (k + 1) + 2 ^ (k + 1) * x / log x ^ (k + 1))`. -/
theorem integral_inv_log_rpow_lt_div_add {k x : ℝ} (hk : 0 ≤ k) (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, (Real.log t ^ k)⁻¹) < x / Real.log x ^ k +
      k * (√x / Real.log 2 ^ (k + 1) + (2 : ℝ) ^ (k + 1) * x / Real.log x ^ (k + 1)) := by
  have hibp := integral_inv_log_rpow_eq_sub_add k one_lt_two (one_lt_two.trans_le hx)
  have hlog2_pos : 0 < Real.log 2 ^ k := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) k
  have hrem := integral_inv_log_rpow_le_sqrt_div_add (k := k + 1) (by linarith) hx
  calc (∫ t in (2 : ℝ)..x, (Real.log t ^ k)⁻¹)
      = x / Real.log x ^ k - 2 / Real.log 2 ^ k +
          k * ∫ t in (2 : ℝ)..x, (Real.log t ^ (k + 1))⁻¹ := hibp
    _ < x / Real.log x ^ k + k * ∫ t in (2 : ℝ)..x, (Real.log t ^ (k + 1))⁻¹ := by
          linarith [div_pos two_pos hlog2_pos]
    _ ≤ x / Real.log x ^ k +
          k * (√x / Real.log 2 ^ (k + 1) + (2 : ℝ) ^ (k + 1) * x / Real.log x ^ (k + 1)) := by
          gcongr

/-- Explicit upper bound at exponent `k = 7`:
`∫ t in 2..x, (log t ^ 7)⁻¹ < x / log x ^ 7 + 7 * (√x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8)`. -/
theorem integral_inv_log_pow_seven_lt {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, (Real.log t ^ 7)⁻¹) < x / Real.log x ^ 7 +
      7 * (√x / Real.log 2 ^ 8 + (2 : ℝ) ^ 8 * x / Real.log x ^ 8) := by
  have h := integral_inv_log_rpow_lt_div_add (k := ((7 : ℕ) : ℝ)) (by norm_num) hx
  rw [show ((7 : ℕ) : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num] at h
  simp only [Real.rpow_natCast] at h
  simpa only [Nat.cast_ofNat] using h

/-! ### Estimates and zero of `Li x - x / log x` -/

/-- `x ↦ Li x - x / log x` is strictly increasing on `(1, ∞)`. -/
theorem strictMonoOn_logIntegral_sub_div_log :
    StrictMonoOn (fun x : ℝ ↦ logIntegral x - x / Real.log x) (Ioi 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 1) ?_ fun x hx ↦ ?_
  · refine ContinuousOn.sub differentiableOn_logIntegral.continuousOn ?_
    exact continuousOn_id.div (Real.continuousOn_log.mono fun x hx ↦ (zero_lt_one.trans hx).ne')
      fun x hx ↦ (Real.log_pos hx).ne'
  · rw [interior_Ioi] at hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    have h1 := hasDerivAt_logIntegral hx
    have h2 : HasDerivAt (fun u : ℝ ↦ u / Real.log u)
        ((Real.log x)⁻¹ - (Real.log x ^ 2)⁻¹) x := by
      simpa only [pow_one, Nat.cast_one, one_mul, one_add_one_eq_two] using
        hasDerivAt_div_log_pow 1 hlog.ne'
    rw [(h1.fun_sub h2).deriv]
    have heq : (Real.log x)⁻¹ - ((Real.log x)⁻¹ - (Real.log x ^ 2)⁻¹) =
        (Real.log x ^ 2)⁻¹ := by ring
    rw [heq]
    positivity

private theorem logIntegral_sub_div_log_eq_integral {x : ℝ} (hx : 2 ≤ x) :
    logIntegral x - x / Real.log x =
      (∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹) - 2 / Real.log 2 := by
  rw [logIntegral_eq_div_log_sub_add hx]
  ring

/-- Lower bound for `Li x - x / log x` on `[2, ∞)`:
`x / log x ^ 2 - 2 / log 2 - 2 / log 2 ^ 2 ≤ Li x - x / log x`. -/
theorem le_logIntegral_sub_div_log {x : ℝ} (hx : 2 ≤ x) :
    x / Real.log x ^ 2 - 2 / Real.log 2 - 2 / Real.log 2 ^ 2 ≤ logIntegral x - x / Real.log x := by
  have hint := le_integral_inv_log_pow 2 one_lt_two hx
  have h2_le : 2 / Real.log x ^ 2 ≤ 2 / Real.log 2 ^ 2 := by gcongr
  rw [logIntegral_sub_div_log_eq_integral hx]
  have hdiv : (x - 2) / Real.log x ^ 2 = x / Real.log x ^ 2 - 2 / Real.log x ^ 2 := by ring
  linarith

/-- Strict lower bound for `Li x - x / log x` on `(2, ∞)`, showing equality in
`TauCeti.Real.le_logIntegral_sub_div_log` holds only at `x = 2`. -/
theorem lt_logIntegral_sub_div_log {x : ℝ} (hx : 2 < x) :
    x / Real.log x ^ 2 - 2 / Real.log 2 - 2 / Real.log 2 ^ 2 < logIntegral x - x / Real.log x := by
  have hmid : (x - 2) / Real.log x ^ 2 ≤ ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹ :=
    le_integral_inv_log_pow 2 one_lt_two hx.le
  have h2_lt : 2 / Real.log x ^ 2 < 2 / Real.log 2 ^ 2 := by gcongr
  rw [logIntegral_sub_div_log_eq_integral hx.le]
  have hdiv : (x - 2) / Real.log x ^ 2 = x / Real.log x ^ 2 - 2 / Real.log x ^ 2 := by ring
  linarith

/-- For `x ≥ 2`, equality `Li x - x / log x = x / log x ^ 2 - 2 / log 2 - 2 / log 2 ^ 2` holds
if and only if `x = 2`. -/
theorem logIntegral_sub_div_log_eq_iff {x : ℝ} (hx : 2 ≤ x) :
    logIntegral x - x / Real.log x = x / Real.log x ^ 2 - 2 / Real.log 2 - 2 / Real.log 2 ^ 2 ↔
      x = 2 := by
  refine ⟨fun h ↦ (hx.eq_or_lt.resolve_right fun hgt ↦ (lt_logIntegral_sub_div_log hgt).ne' h).symm,
    ?_⟩
  rintro rfl
  rw [logIntegral_two]
  ring

/-- Strict upper bound for `Li x - x / log x` on `[2, ∞)`:
`Li x - x / log x < x / log x ^ 2 + 2 * √x / log 2 ^ 3 + 16 * x / log x ^ 3 - 2 / log 2`. -/
theorem logIntegral_sub_div_log_lt {x : ℝ} (hx : 2 ≤ x) :
    logIntegral x - x / Real.log x <
      x / Real.log x ^ 2 + 2 * √x / Real.log 2 ^ 3 + 16 * x / Real.log x ^ 3 - 2 / Real.log 2 := by
  have hlt := integral_inv_log_rpow_lt_div_add (k := 2) zero_le_two hx
  have h21 : (2 : ℝ) + 1 = ((3 : ℕ) : ℝ) := by norm_num
  have h2n : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h21, h2n] at hlt
  simp only [Real.rpow_natCast] at hlt
  rw [logIntegral_sub_div_log_eq_integral hx]
  have hrhs : x / Real.log x ^ 2 + 2 * (√x / Real.log 2 ^ 3 + (2 : ℝ) ^ 3 * x / Real.log x ^ 3) =
      x / Real.log x ^ 2 + 2 * √x / Real.log 2 ^ 3 + 16 * x / Real.log x ^ 3 := by
    ring
  linarith

private theorem logIntegral_sub_div_log_eq_series_diff {x : ℝ} (hx : 1 < x) :
    logIntegral x - x / Real.log x =
      (Real.log (Real.log x) + liSeries (Real.log x)) -
        (Real.log (Real.log 2) + liSeries (Real.log 2)) - x / Real.log x := by
  rw [logIntegral_eq_li_sub_li_two hx, li_eq_add_liSeries, li_eq_add_liSeries]
  ring

private theorem log_x_enclosure {x d_lo d_hi : ℝ} (hx : 4 ≤ x)
    (hd_lo : d_lo ≤ 2 * artanhPartial 6 ((x / 4 - 1) / (x / 4 + 1)))
    (hd_hi : 2 * (artanhPartial 6 ((x / 4 - 1) / (x / 4 + 1)) +
      ((x / 4 - 1) / (x / 4 + 1)) ^ (2 * 6 + 1) / (1 - ((x / 4 - 1) / (x / 4 + 1)) ^ 2)) ≤ d_hi) :
    2 * (6931471803 / 10000000000 : ℝ) + d_lo ≤ Real.log x ∧
      Real.log x ≤ 2 * (6931471808 / 10000000000 : ℝ) + d_hi := by
  have hsplit : Real.log x = 2 * Real.log 2 + Real.log (x / 4) := by
    rw [Real.log_div (by linarith) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  have hx4 : 1 ≤ x / 4 := by linarith
  have hlo := hd_lo.trans (two_mul_artanhPartial_le_log hx4 6)
  have hhi := (log_le_two_mul_artanhPartial_add hx4 6).trans hd_hi
  rw [hsplit]
  exact ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩

private theorem log_log_x_enclosure {lx lx_lo lx_hi dlx_lo dlx_hi : ℝ}
    (hlx_lo : lx_lo ≤ lx) (hlx_hi : lx ≤ lx_hi)
    (hlx_lo0 : 0 < lx_lo) (hlx_hi2 : lx_hi ≤ 2)
    (hdlx_lo : dlx_lo ≤ -2 * (artanhPartial 3 ((1 - lx_lo / 2) / (1 + lx_lo / 2)) +
      ((1 - lx_lo / 2) / (1 + lx_lo / 2)) ^ (2 * 3 + 1) /
        (1 - ((1 - lx_lo / 2) / (1 + lx_lo / 2)) ^ 2)))
    (hdlx_hi : -2 * artanhPartial 3 ((1 - lx_hi / 2) / (1 + lx_hi / 2)) ≤ dlx_hi) :
    (6931471803 / 10000000000 : ℝ) + dlx_lo ≤ Real.log lx ∧
      Real.log lx ≤ (6931471808 / 10000000000 : ℝ) + dlx_hi := by
  have hlx_pos : 0 < lx := hlx_lo0.trans_le hlx_lo
  have hsplit : Real.log lx = Real.log 2 + Real.log (lx / 2) := by
    rw [Real.log_div hlx_pos.ne' two_ne_zero]
    ring
  have h_lo_mono : Real.log (lx_lo / 2) ≤ Real.log (lx / 2) :=
    Real.log_le_log (half_pos hlx_lo0) (div_le_div_of_nonneg_right hlx_lo zero_le_two)
  have h_hi_mono : Real.log (lx / 2) ≤ Real.log (lx_hi / 2) :=
    Real.log_le_log (half_pos hlx_pos) (div_le_div_of_nonneg_right hlx_hi zero_le_two)
  have hlo := hdlx_lo.trans (neg_two_mul_artanhPartial_add_le_log (half_pos hlx_lo0)
    (by linarith [hlx_lo.trans hlx_hi]) 3)
  have hhi := (log_le_neg_two_mul_artanhPartial
    (by linarith [hlx_lo0.trans_le (hlx_lo.trans hlx_hi)]) (by linarith) 3).trans hdlx_hi
  rw [hsplit]
  exact ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩

private theorem liSeries_fourteen_lower {y lx_lo c : ℝ} (hy : lx_lo ≤ y)
    (h0 : 0 ≤ lx_lo) (hc : c ≤ liSeriesPartial 14 lx_lo) :
    c ≤ liSeries y :=
  hc.trans (((by rw [liSeriesPartial_def]; exact sum_range_le_liSeries h0 14) :
    liSeriesPartial 14 lx_lo ≤ liSeries lx_lo).trans (strictMono_liSeries.monotone hy))

private theorem liSeries_fourteen_upper {y lx_hi c : ℝ} (hy0 : 0 ≤ y)
    (hy : y ≤ lx_hi) (hlx : lx_hi < 16)
    (hc : liSeriesPartial 14 lx_hi +
      (lx_hi ^ (14 + 1) / (((14 : ℝ) + 1) * ((14 + 1)! : ℝ))) *
        (((14 : ℝ) + 2) / ((14 : ℝ) + 2 - lx_hi)) ≤ c) :
    liSeries y ≤ c :=
  (strictMono_liSeries.monotone hy).trans
    ((liSeries_le_partial_add 14 (hy0.trans hy) (by push_cast; linarith)).trans hc)

private theorem logIntegral_sub_div_log_lower_of_bounds {x lx_lo llx_lo Sx_lo : ℝ}
    (hx : 4 < x) (hlx_lo : lx_lo ≤ Real.log x)
    (hlx_lo0 : 0 < lx_lo) (hllx_lo : llx_lo ≤ Real.log (Real.log x))
    (hSx_lo : Sx_lo ≤ liSeries (Real.log x)) :
    (llx_lo + Sx_lo) - ((-0.36651290 : ℝ) + (0.834461037 : ℝ)) - x / lx_lo ≤
      logIntegral x - x / Real.log x := by
  rw [logIntegral_sub_div_log_eq_series_diff (by linarith)]
  have hdiv : x / Real.log x ≤ x / lx_lo := div_le_div_of_nonneg_left (by linarith) hlx_lo0 hlx_lo
  have h2 : liSeries (Real.log 2) ≤ (0.834461037 : ℝ) :=
    liSeries_log_two_upper
  have hll2 : Real.log (Real.log 2) ≤ (-0.36651290 : ℝ) := log_log_two_upper_tight
  linarith

private theorem logIntegral_sub_div_log_upper_of_bounds {x lx_hi llx_hi Sx_hi : ℝ}
    (hx : 4 < x) (hlx_hi : Real.log x ≤ lx_hi) (hllx_hi : Real.log (Real.log x) ≤ llx_hi)
    (hSx_hi : liSeries (Real.log x) ≤ Sx_hi) :
    logIntegral x - x / Real.log x ≤
      (llx_hi + Sx_hi) - ((-0.36651295 : ℝ) + (0.834461034 : ℝ)) - x / lx_hi := by
  rw [logIntegral_sub_div_log_eq_series_diff (by linarith)]
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hdiv : x / lx_hi ≤ x / Real.log x := div_le_div_of_nonneg_left (by linarith) hlogx hlx_hi
  have h2 : (0.834461034 : ℝ) ≤ liSeries (Real.log 2) :=
    liSeries_log_two_lower
  have hll2 : (-0.36651295 : ℝ) ≤ Real.log (Real.log 2) := log_log_two_lower_tight
  linarith

private theorem logIntegral_sub_div_log_lt_of_cert
    {x c d_lo d_hi lx_lo lx_hi dlx_lo dlx_hi llx_hi Sx_hi : ℝ}
    (hx : 4 < x)
    (hd_lo : d_lo ≤ 2 * artanhPartial 6 ((x / 4 - 1) / (x / 4 + 1)))
    (hd_hi : 2 * (artanhPartial 6 ((x / 4 - 1) / (x / 4 + 1)) +
      ((x / 4 - 1) / (x / 4 + 1)) ^ (2 * 6 + 1) /
        (1 - ((x / 4 - 1) / (x / 4 + 1)) ^ 2)) ≤ d_hi)
    (hlx_lo_bd : lx_lo ≤ 2 * (6931471803 / 10000000000 : ℝ) + d_lo)
    (hlx_hi_bd : 2 * (6931471808 / 10000000000 : ℝ) + d_hi ≤ lx_hi)
    (hlx_lo0 : 0 < lx_lo) (hlx_hi2 : lx_hi ≤ 2)
    (hdlx_lo : dlx_lo ≤ -2 * (artanhPartial 3 ((1 - lx_lo / 2) / (1 + lx_lo / 2)) +
      ((1 - lx_lo / 2) / (1 + lx_lo / 2)) ^ (2 * 3 + 1) /
        (1 - ((1 - lx_lo / 2) / (1 + lx_lo / 2)) ^ 2)))
    (hdlx_hi : -2 * artanhPartial 3 ((1 - lx_hi / 2) / (1 + lx_hi / 2)) ≤ dlx_hi)
    (hllx_hi_bd : (6931471808 / 10000000000 : ℝ) + dlx_hi ≤ llx_hi)
    (hSx_hi_bd : liSeriesPartial 14 lx_hi +
      (lx_hi ^ (14 + 1) / (((14 : ℝ) + 1) * ((14 + 1)! : ℝ))) *
        (((14 : ℝ) + 2) / ((14 : ℝ) + 2 - lx_hi)) ≤ Sx_hi)
    (hc : (llx_hi + Sx_hi) - ((-0.36651295 : ℝ) + (0.834461034 : ℝ)) - x / lx_hi < c) :
    logIntegral x - x / Real.log x < c := by
  have hxenc := log_x_enclosure hx.le hd_lo hd_hi
  have hlx_lo : lx_lo ≤ Real.log x := hlx_lo_bd.trans hxenc.1
  have hlx_hi : Real.log x ≤ lx_hi := hxenc.2.trans hlx_hi_bd
  have hllx := log_log_x_enclosure hlx_lo hlx_hi hlx_lo0 hlx_hi2 hdlx_lo hdlx_hi
  have hllx_hi : Real.log (Real.log x) ≤ llx_hi := hllx.2.trans hllx_hi_bd
  have hSx_hi : liSeries (Real.log x) ≤ Sx_hi :=
    liSeries_fourteen_upper (Real.log_pos (by linarith)).le hlx_hi
      (by linarith) hSx_hi_bd
  exact (logIntegral_sub_div_log_upper_of_bounds hx hlx_hi hllx_hi hSx_hi).trans_lt hc

private theorem lt_logIntegral_sub_div_log_of_cert
    {x c d_lo d_hi lx_lo lx_hi dlx_lo dlx_hi llx_lo Sx_lo : ℝ}
    (hx : 4 < x)
    (hd_lo : d_lo ≤ 2 * artanhPartial 6 ((x / 4 - 1) / (x / 4 + 1)))
    (hd_hi : 2 * (artanhPartial 6 ((x / 4 - 1) / (x / 4 + 1)) +
      ((x / 4 - 1) / (x / 4 + 1)) ^ (2 * 6 + 1) /
        (1 - ((x / 4 - 1) / (x / 4 + 1)) ^ 2)) ≤ d_hi)
    (hlx_lo_bd : lx_lo ≤ 2 * (6931471803 / 10000000000 : ℝ) + d_lo)
    (hlx_hi_bd : 2 * (6931471808 / 10000000000 : ℝ) + d_hi ≤ lx_hi)
    (hlx_lo0 : 0 < lx_lo) (hlx_hi2 : lx_hi ≤ 2)
    (hdlx_lo : dlx_lo ≤ -2 * (artanhPartial 3 ((1 - lx_lo / 2) / (1 + lx_lo / 2)) +
      ((1 - lx_lo / 2) / (1 + lx_lo / 2)) ^ (2 * 3 + 1) /
        (1 - ((1 - lx_lo / 2) / (1 + lx_lo / 2)) ^ 2)))
    (hdlx_hi : -2 * artanhPartial 3 ((1 - lx_hi / 2) / (1 + lx_hi / 2)) ≤ dlx_hi)
    (hllx_lo_bd : llx_lo ≤ (6931471803 / 10000000000 : ℝ) + dlx_lo)
    (hSx_lo_bd : Sx_lo ≤ liSeriesPartial 14 lx_lo)
    (hc : c < (llx_lo + Sx_lo) - ((-0.36651290 : ℝ) + (0.834461037 : ℝ)) - x / lx_lo) :
    c < logIntegral x - x / Real.log x := by
  have hxenc := log_x_enclosure hx.le hd_lo hd_hi
  have hlx_lo : lx_lo ≤ Real.log x := hlx_lo_bd.trans hxenc.1
  have hlx_hi : Real.log x ≤ lx_hi := hxenc.2.trans hlx_hi_bd
  have hllx := log_log_x_enclosure hlx_lo hlx_hi hlx_lo0 hlx_hi2 hdlx_lo hdlx_hi
  have hllx_lo : llx_lo ≤ Real.log (Real.log x) := hllx_lo_bd.trans hllx.1
  have hSx_lo : Sx_lo ≤ liSeries (Real.log x) :=
    liSeries_fourteen_lower hlx_lo hlx_lo0.le hSx_lo_bd
  exact hc.trans_le (logIntegral_sub_div_log_lower_of_bounds hx hlx_lo hlx_lo0 hllx_lo hSx_lo)

private theorem logIntegral_sub_div_log_at_65797 :
    logIntegral (65797 / 10000) - (65797 / 10000 : ℝ) / Real.log (65797 / 10000) < 0 := by
  refine logIntegral_sub_div_log_lt_of_cert (x := 65797 / 10000) (c := 0)
    (d_lo := 0.49769478) (d_hi := 0.49769482) (lx_lo := 1.883989140) (lx_hi := 1.883989182)
    (dlx_lo := -0.05975577) (dlx_hi := -0.05975574) (llx_hi := 0.63339145)
    (Sx_hi := 3.32697870)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · try simp only [liSeriesPartial_def, artanhPartial_def,
        Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ, Nat.factorial_zero]
      norm_num

private theorem logIntegral_sub_div_log_at_65798 :
    0 < logIntegral (65798 / 10000) - (65798 / 10000 : ℝ) / Real.log (65798 / 10000) := by
  refine lt_logIntegral_sub_div_log_of_cert (x := 65798 / 10000) (c := 0)
    (d_lo := 0.49770998) (d_hi := 0.49771001) (lx_lo := 1.884004340) (lx_hi := 1.884004372)
    (dlx_lo := -0.05974771) (dlx_hi := -0.05974768) (llx_lo := 0.63339947)
    (Sx_lo := 3.32702358)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · try simp only [liSeriesPartial_def, artanhPartial_def,
        Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ, Nat.factorial_zero]
      norm_num

private theorem logIntegral_sub_div_log_at_658 :
    (7e-5 : ℝ) < logIntegral (658 / 100) - (658 / 100 : ℝ) / Real.log (658 / 100) := by
  refine lt_logIntegral_sub_div_log_of_cert (x := 658 / 100) (c := 7e-5)
    (d_lo := 0.49774038) (d_hi := 0.49774041) (lx_lo := 1.884034740) (lx_hi := 1.884034772)
    (dlx_lo := -0.05973157) (dlx_hi := -0.05973154) (llx_lo := 0.63341561)
    (Sx_lo := 3.32711361)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · try simp only [liSeriesPartial_def, artanhPartial_def,
        Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ, Nat.factorial_zero]
      norm_num

/-- `Li x - x / log x` has a unique zero on `(1, ∞)`. -/
theorem existsUnique_logIntegral_sub_div_log_eq_zero :
    ∃! x ∈ Ioi (1 : ℝ), logIntegral x - x / Real.log x = 0 := by
  let g (x : ℝ) : ℝ := logIntegral x - x / Real.log x
  have hg_cont : ContinuousOn g (Icc (65797 / 10000) (65798 / 10000)) := by
    refine ContinuousOn.sub (differentiableOn_logIntegral.continuousOn.mono fun x hx ↦
      mem_Ioi.mpr (by linarith [hx.1])) ?_
    refine continuousOn_id.div (Real.continuousOn_log.mono fun x hx ↦
      (by linarith [hx.1] : x ≠ 0)) fun x hx ↦ (Real.log_pos (by linarith [hx.1])).ne'
  obtain ⟨x₀, hx₀_mem, hx₀_eq⟩ := intermediate_value_Icc
    (by norm_num : (65797 / 10000 : ℝ) ≤ 65798 / 10000) hg_cont
    ⟨logIntegral_sub_div_log_at_65797.le, logIntegral_sub_div_log_at_65798.le⟩
  have hx₀_Ioi : x₀ ∈ Ioi (1 : ℝ) := mem_Ioi.mpr (by linarith [hx₀_mem.1])
  refine ⟨x₀, ⟨hx₀_Ioi, hx₀_eq⟩, fun y hy ↦ ?_⟩
  rcases lt_trichotomy y x₀ with hlt | rfl | hgt
  · exact absurd (strictMonoOn_logIntegral_sub_div_log hy.1 hx₀_Ioi hlt)
      (by linarith [hy.2, hx₀_eq])
  · rfl
  · exact absurd (strictMonoOn_logIntegral_sub_div_log hx₀_Ioi hy.1 hgt)
      (by linarith [hy.2, hx₀_eq])

/-- Any zero of `Li x - x / log x` on `(1, ∞)` lies in `(6.5797, 6.5798)`. -/
theorem mem_Ioo_of_logIntegral_sub_div_log_eq_zero {x : ℝ} (hx : 1 < x)
    (h : logIntegral x - x / Real.log x = 0) :
    x ∈ Ioo (65797 / 10000 : ℝ) (65798 / 10000) := by
  refine ⟨?_, ?_⟩
  · by_contra! hle
    have hmono := strictMonoOn_logIntegral_sub_div_log.monotoneOn
      (mem_Ioi.mpr hx) (mem_Ioi.mpr (by norm_num)) hle
    linarith [logIntegral_sub_div_log_at_65797]
  · by_contra! hle
    have hmono := strictMonoOn_logIntegral_sub_div_log.monotoneOn
      (mem_Ioi.mpr (by norm_num)) (mem_Ioi.mpr hx) hle
    linarith [logIntegral_sub_div_log_at_65798]

/-- **Fiori–Kadiri–Swidinsky (2023), Lemma 20**: for every `x ≥ 6.58`,
`(x - 6.58) / (log x) ^ 2 ≤ Li x - x / log x`, and in particular `0 < Li x - x / log x`
for `6.58 < x`. -/
theorem sub_div_log_sq_le_logIntegral_sub_div_log {x : ℝ} (hx : (658 / 100 : ℝ) ≤ x) :
    (x - 658 / 100) / Real.log x ^ 2 ≤ logIntegral x - x / Real.log x := by
  let h (t : ℝ) : ℝ := logIntegral t - t / Real.log t - (t - 658 / 100) / Real.log x ^ 2
  have hderiv : ∀ t ∈ Icc (658 / 100 : ℝ) x,
      HasDerivAt h ((Real.log t ^ 2)⁻¹ - (Real.log x ^ 2)⁻¹) t := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have hlogt : 0 < Real.log t := Real.log_pos ht1
    have h1 := hasDerivAt_logIntegral ht1
    have h2 : HasDerivAt (fun u : ℝ ↦ u / Real.log u)
        ((Real.log t)⁻¹ - (Real.log t ^ 2)⁻¹) t := by
      simpa only [pow_one, Nat.cast_one, one_mul, one_add_one_eq_two] using
        hasDerivAt_div_log_pow 1 hlogt.ne'
    have h3 : HasDerivAt (fun u : ℝ ↦ (u - 658 / 100) / Real.log x ^ 2)
        (Real.log x ^ 2)⁻¹ t := by
      simpa [div_eq_mul_inv] using
        ((hasDerivAt_id t).sub_const (658 / 100 : ℝ)).div_const (Real.log x ^ 2)
    refine ((h1.fun_sub h2).fun_sub h3).congr_deriv ?_
    ring
  have hmono : MonotoneOn h (Icc (658 / 100 : ℝ) x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc (658 / 100) x)
      (fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      fun t ht ↦ ?_
    rw [interior_Icc] at ht
    rw [(hderiv t ⟨ht.1.le, ht.2.le⟩).deriv, sub_nonneg]
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    exact inv_anti₀ (pow_pos hlogt 2)
      (pow_le_pow_left₀ hlogt.le (Real.log_le_log (by linarith [ht.1]) ht.2.le) 2)
  have h0_lt : 0 < h (658 / 100) := by
    simp only [h, sub_self, zero_div, sub_zero]
    exact (by norm_num : (0 : ℝ) < 7e-5).trans logIntegral_sub_div_log_at_658
  have hx_pos := h0_lt.trans_le (hmono (left_mem_Icc.mpr hx) (right_mem_Icc.mpr hx) hx)
  dsimp only [h] at hx_pos
  linarith

end TauCeti.Real
