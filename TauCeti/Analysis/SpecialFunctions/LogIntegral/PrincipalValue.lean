/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Unoffset
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference
import TauCeti.Analysis.SpecialFunctions.Log.InvLog

/-!
# Principal value and regularised integrals for the unoffset logarithmic integral

This file establishes the integral representations of `TauCeti.Real.li` in the variable `t`:

* on `(0, 1)`, `li x = ∫ t in 0..x, (log t)⁻¹` as an ordinary Lebesgue interval integral;
* on `(1, ∞)`, `li x = lim_{ε → 0⁺} (∫ t in 0..(1 - ε), (log t)⁻¹ + ∫ t in (1 + ε)..x, (log t)⁻¹)`
  (the Cauchy principal value);
* subtracting the pole `(t - 1)⁻¹` gives the absolutely convergent representation
  `li x = log |x - 1| + ∫ t in 0..x, ((log t)⁻¹ - (t - 1)⁻¹)` for all `x > 0`, `x ≠ 1`, where
  the regularised integrand `(log t)⁻¹ - (t - 1)⁻¹` lies in `(0, 1)` (and in `(0, 1 / 2)` for
  `t > 1`), tending to `1` as `t → 0⁺` and to `1 / 2` as `t → 1`;
* at `x = 2`, folding around `t = 1` gives the symmetric integral
  `li 2 = ∫ u in 0..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹)`, whose integrand lies in `(0, 3 / 2)`
  on `(0, 1)`, tending to `1` as `u → 0⁺` and to `(log 2)⁻¹` as `u → 1⁻`.

## Main declarations

* `TauCeti.Real.li_eq_integral_of_lt_one` — ordinary integral on `(0, 1)`.
* `TauCeti.Real.tendsto_pv_inv_log_eq_li` — Cauchy principal value on `(1, ∞)`.
* `TauCeti.Real.li_eq_log_abs_sub_one_add_integral` — regularised integral for `x > 0`, `x ≠ 1`.
* `TauCeti.Real.li_two_eq_integral_symm` — symmetric integral for `li 2`.
-/

public section

namespace TauCeti.Real

open Filter MeasureTheory Set
open scoped Topology

/-! ### Integral on `(0, 1)` and Cauchy principal value on `(1, ∞)` -/

/-- The inverse logarithm `(log t)⁻¹` is continuous on `[0, 1)`, using Mathlib's convention
`(log 0)⁻¹ = 0`. -/
theorem continuousOn_inv_log_Ico : ContinuousOn (fun t : ℝ ↦ (Real.log t)⁻¹) (Ico 0 1) := by
  intro t ht
  rcases ht.1.eq_or_lt with rfl | ht0
  · exact Real.continuousAt_inv_log_zero.continuousWithinAt
  · exact ((Real.continuousAt_log ht0.ne').inv₀ (Real.log_neg ht0 ht.2).ne).continuousWithinAt

/-- `(log t)⁻¹` is interval integrable on any interval inside `[0, 1)`. -/
theorem intervalIntegrable_inv_log_of_lt_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹) volume a b := by
  refine (continuousOn_inv_log_Ico.mono fun t ht ↦ ?_).intervalIntegrable
  rcases mem_uIcc.mp ht with h | h
  · exact ⟨ha0.trans h.1, h.2.trans_lt hb1⟩
  · exact ⟨hb0.trans h.1, h.2.trans_lt ha1⟩

/-- For `0 < x < 1`, `li x` equals the ordinary integral `∫ t in 0..x, (log t)⁻¹`. -/
theorem li_eq_integral_of_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    li x = ∫ t in (0 : ℝ)..x, (Real.log t)⁻¹ := by
  have hint : IntegrableOn (fun t : ℝ ↦ (Real.log t)⁻¹) (uIcc 0 x) := by
    rw [uIcc_of_le hx0.le, integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx0.le).mp
      (intervalIntegrable_inv_log_of_lt_one le_rfl zero_lt_one hx0.le hx1)
  have hLHS : Tendsto (fun ε : ℝ ↦ ∫ t in ε..x, (Real.log t)⁻¹)
      (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..x, (Real.log t)⁻¹)) := by
    have hcont := intervalIntegral.continuousOn_primitive_interval_left (μ := volume) hint
    refine ((hcont 0 left_mem_uIcc).mono_of_mem_nhdsWithin ?_).tendsto
    filter_upwards [Ioo_mem_nhdsGT hx0] with ε hε
    rw [uIcc_of_le hx0.le]
    exact ⟨hε.1.le, hε.2.le⟩
  have hRHS : Tendsto (fun ε : ℝ ↦ li x - li ε) (𝓝[>] 0) (𝓝 (li x)) := by
    simpa using (tendsto_const_nhds (x := li x)).sub tendsto_li_nhdsGT_zero
  have hEq : (fun ε : ℝ ↦ ∫ t in ε..x, (Real.log t)⁻¹) =ᶠ[𝓝[>] 0] fun ε : ℝ ↦ li x - li ε := by
    filter_upwards [Ioo_mem_nhdsGT hx0] with ε hε
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ ?_)
      (intervalIntegrable_inv_log_of_lt_one hε.1.le (hε.2.trans hx1) hx0.le hx1)
    rw [uIcc_of_le hε.2.le] at ht
    exact hasDerivAt_li (hε.1.trans_le ht.1) (ht.2.trans_lt hx1).ne
  exact (tendsto_nhds_unique (hLHS.congr' hEq) hRHS).symm

/-- Near the logarithmic singularity `t = 1`, the symmetric difference `li (1 - ε) - li (1 + ε)`
tends to `0` as `ε → 0⁺`. -/
theorem tendsto_li_one_sub_sub_li_one_add :
    Tendsto (fun ε : ℝ ↦ li (1 - ε) - li (1 + ε)) (𝓝[>] 0) (𝓝 0) := by
  have hlog_ratio : Tendsto (fun ε : ℝ ↦ Real.log (Real.log (1 - ε)) - Real.log (Real.log (1 + ε)))
      (𝓝[>] 0) (𝓝 0) := by
    have hpos : Tendsto (fun ε : ℝ ↦ Real.log (1 + ε) / ε) (𝓝[>] 0) (𝓝 1) := by
      have hd := (Real.hasDerivAt_log one_ne_zero).tendsto_slope_zero_right
      simpa [slope_def_field, Real.log_one, div_eq_inv_mul] using hd
    have hneg : Tendsto (fun ε : ℝ ↦ -Real.log (1 - ε) / ε) (𝓝[>] 0) (𝓝 1) := by
      have hsub : HasDerivAt (fun ε : ℝ ↦ 1 - ε) (-1) 0 := by
        simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_sub (hasDerivAt_id (0 : ℝ))
      have hlog1 : HasDerivAt Real.log 1 ((fun ε : ℝ ↦ 1 - ε) 0) := by
        simpa using Real.hasDerivAt_log one_ne_zero
      have hcomp : HasDerivAt (fun ε : ℝ ↦ Real.log (1 - ε)) (-1) 0 := by
        simpa only [Function.comp_def, one_mul] using hlog1.comp (0 : ℝ) hsub
      have hd : Tendsto (fun ε : ℝ ↦ Real.log (1 - ε) / ε) (𝓝[>] 0) (𝓝 (-1)) := by
        simpa [slope_def_field, Real.log_one, div_eq_inv_mul] using hcomp.tendsto_slope_zero_right
      simpa [neg_div] using hd.neg
    have hdiv : Tendsto (fun ε : ℝ ↦ (-Real.log (1 - ε) / ε) / (Real.log (1 + ε) / ε))
        (𝓝[>] 0) (𝓝 1) := by
      simpa only [Pi.div_def, div_one] using hneg.div hpos one_ne_zero
    have hlog : Tendsto (fun ε : ℝ ↦ Real.log ((-Real.log (1 - ε) / ε) / (Real.log (1 + ε) / ε)))
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [Function.comp_def, Real.log_one] using
        (Real.continuousAt_log one_ne_zero).tendsto.comp hdiv
    refine hlog.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    have h1 : 0 < -Real.log (1 - ε) :=
      neg_pos.mpr (Real.log_neg (by linarith [hε.2]) (by linarith [hε.1]))
    have h2 : 0 < Real.log (1 + ε) := Real.log_pos (by linarith [hε.1])
    rw [div_div_div_cancel_right₀ hε.1.ne', Real.log_div h1.ne' h2.ne', Real.log_neg_eq_log]
  have hS : Continuous (fun y : ℝ ↦
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ))) :=
    continuous_iff_continuousAt.mpr fun y ↦ (hasDerivAt_tsum_pow_div_mul_factorial y).continuousAt
  have hSdiff : Tendsto
      (fun ε : ℝ ↦
        (∑' n : ℕ, Real.log (1 - ε) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ))) -
        (∑' n : ℕ, Real.log (1 + ε) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ))))
      (𝓝[>] 0) (𝓝 0) := by
    have hleft : Tendsto (fun ε : ℝ ↦ Real.log (1 - ε)) (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun ε : ℝ ↦ Real.log (1 - ε)) 0 :=
        (Real.continuousAt_log (by norm_num)).comp
          (by fun_prop : Continuous fun ε : ℝ ↦ 1 - ε).continuousAt
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hright : Tendsto (fun ε : ℝ ↦ Real.log (1 + ε)) (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun ε : ℝ ↦ Real.log (1 + ε)) 0 :=
        (Real.continuousAt_log (by norm_num)).comp
          (by fun_prop : Continuous fun ε : ℝ ↦ 1 + ε).continuousAt
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have h1 := (hS.continuousAt (x := (0 : ℝ))).tendsto.comp hleft
    have h2 := (hS.continuousAt (x := (0 : ℝ))).tendsto.comp hright
    simpa only [Function.comp_def, sub_self] using h1.sub h2
  have h := hlog_ratio.add hSdiff
  rw [add_zero] at h
  refine h.congr fun ε ↦ ?_
  simp only [li_def]
  ring

/-- **Cauchy principal value for `li x`** (`x > 1`):
`lim_{ε → 0⁺} (∫ t in 0..(1 - ε), (log t)⁻¹ + ∫ t in (1 + ε)..x, (log t)⁻¹) = li x`. -/
theorem tendsto_pv_inv_log_eq_li {x : ℝ} (hx : 1 < x) :
    Tendsto
      (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..(1 - ε), (Real.log t)⁻¹) +
        ∫ t in (1 + ε)..x, (Real.log t)⁻¹)
      (𝓝[>] 0) (𝓝 (li x)) := by
  have hsymm : Tendsto (fun ε : ℝ ↦ li x + (li (1 - ε) - li (1 + ε))) (𝓝[>] 0) (𝓝 (li x)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := li x)).add tendsto_li_one_sub_sub_li_one_add
  refine hsymm.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one (sub_pos.mpr hx))] with ε hε
  have hε1 : ε < 1 := lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hεx : 1 + ε < x := by linarith [lt_of_lt_of_le hε.2 (min_le_right _ _)]
  rw [← li_eq_integral_of_lt_one (by linarith : 0 < 1 - ε) (by linarith [hε.1] : 1 - ε < 1)]
  have hFTC : (∫ t in (1 + ε)..x, (Real.log t)⁻¹) = li x - li (1 + ε) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ ?_) ?_
    · rw [uIcc_of_le hεx.le] at ht
      have ht1 : 1 < t := by linarith [hε.1, ht.1]
      exact hasDerivAt_li (zero_lt_one.trans ht1) ht1.ne'
    · simpa only [pow_one] using intervalIntegrable_inv_log_pow 1 (by linarith [hε.1]) hx
  rw [hFTC]
  ring

/-! ### The regularised integrand `(log t)⁻¹ - (t - 1)⁻¹` -/

/-- For every `t > 0` with `t ≠ 1`, `(log t)⁻¹ - (t - 1)⁻¹ > 0`. -/
theorem inv_log_sub_inv_sub_one_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t ≠ 1) :
    0 < (Real.log t)⁻¹ - (t - 1)⁻¹ := by
  have hlt := Real.log_lt_sub_one_of_pos ht0 ht1
  rcases lt_or_gt_of_ne ht1 with h | h
  · have hlog : Real.log t < 0 := Real.log_neg ht0 h
    have hsub : t - 1 < 0 := sub_neg.mpr h
    exact sub_pos.mpr ((inv_lt_inv_of_neg hsub hlog).mpr hlt)
  · have hlog : 0 < Real.log t := Real.log_pos h
    exact sub_pos.mpr ((inv_lt_inv₀ (sub_pos.mpr h) hlog).mpr hlt)

/-- Reflection identity: `((log t)⁻¹ - (t - 1)⁻¹) + ((log t⁻¹)⁻¹ - (t⁻¹ - 1)⁻¹) = 1` for
`t > 0`, `t ≠ 1`. -/
theorem inv_log_sub_inv_sub_one_add_inv {t : ℝ} (ht0 : 0 < t) (ht1 : t ≠ 1) :
    ((Real.log t)⁻¹ - (t - 1)⁻¹) + ((Real.log t⁻¹)⁻¹ - (t⁻¹ - 1)⁻¹) = 1 := by
  rw [Real.log_inv, inv_neg]
  have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hsub' : t⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (inv_ne_one.mpr ht1)
  field_simp [ht0.ne', hsub, hsub']
  ring

/-- For every `t > 0` with `t ≠ 1`, `(log t)⁻¹ - (t - 1)⁻¹ < 1`. -/
theorem inv_log_sub_inv_sub_one_lt_one {t : ℝ} (ht0 : 0 < t) (ht1 : t ≠ 1) :
    (Real.log t)⁻¹ - (t - 1)⁻¹ < 1 := by
  have hpos := inv_log_sub_inv_sub_one_pos (inv_pos.mpr ht0) (inv_ne_one.mpr ht1)
  linarith [inv_log_sub_inv_sub_one_add_inv ht0 ht1]

/-- For every `t > 1`, `(log t)⁻¹ - (t - 1)⁻¹ < 1 / 2`. -/
theorem inv_log_sub_inv_sub_one_lt_half {t : ℝ} (ht : 1 < t) :
    (Real.log t)⁻¹ - (t - 1)⁻¹ < 1 / 2 := by
  have ht1 : 0 < t - 1 := sub_pos.mpr ht
  have hlog : 2 * (t - 1) / (t + 1) < Real.log t := by
    have h := Real.lt_log_one_add_of_pos ht1
    have hadd : t - 1 + 2 = t + 1 := by ring
    rwa [add_sub_cancel, hadd] at h
  have h1 : 0 < 2 * (t - 1) / (t + 1) := by positivity
  have hinv := (inv_lt_inv₀ (Real.log_pos ht) h1).mpr hlog
  have heq : (2 * (t - 1) / (t + 1))⁻¹ - (t - 1)⁻¹ = 1 / 2 := by
    field_simp [ht1.ne', (by linarith : t + 1 ≠ 0)]
    ring
  linarith

/-- As `t → 0⁺`, `(log t)⁻¹ - (t - 1)⁻¹ → 1`. -/
theorem tendsto_inv_log_sub_inv_sub_one_nhdsGT_zero :
    Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) (𝓝[>] 0) (𝓝 1) := by
  have h1 : Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    (Real.continuousAt_inv_log_zero.tendsto.mono_left nhdsWithin_le_nhds).trans (by simp)
  have h2 : Tendsto (fun t : ℝ ↦ (t - 1)⁻¹) (𝓝[>] 0) (𝓝 (-1)) := by
    have hc : ContinuousAt (fun t : ℝ ↦ (t - 1)⁻¹) 0 :=
      (continuousAt_id.sub continuousAt_const).inv₀ (by norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa using h1.sub h2

/-- As `t → 1` (`t ≠ 1`), `(log t)⁻¹ - (t - 1)⁻¹ → 1 / 2`. -/
theorem tendsto_inv_log_sub_inv_sub_one_nhdsNE_one :
    Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) (𝓝[≠] 1) (𝓝 (1 / 2)) := by
  -- With `y = log t`, `(log t)⁻¹ - (t - 1)⁻¹ = ((e^y - 1 - y) / y²) / ((e^y - 1) / y) → (1/2) / 1`.
  have hquad : Tendsto (fun y : ℝ ↦ (Real.exp y - 1 - y) / y ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) (lt_min zero_lt_one hε)),
      self_mem_nhdsWithin] with y hy (hy0 : y ≠ 0)
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
    have hy1 : |y| ≤ 1 := (lt_of_lt_of_le hy (min_le_left _ _)).le
    have hyε : |y| < ε := lt_of_lt_of_le hy (min_le_right _ _)
    have hb := Real.exp_bound hy1 (n := 3) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero, Nat.factorial_one,
      Nat.factorial_two, pow_zero, pow_one, Nat.cast_one, Nat.cast_ofNat, div_one, zero_add] at hb
    rw [Real.dist_eq]
    have hdiff : (Real.exp y - 1 - y) / y ^ 2 - 1 / 2 =
        (Real.exp y - (1 + y + y ^ 2 / 2)) / y ^ 2 := by
      field_simp [hy0]
      ring
    rw [hdiff, abs_div, abs_pow, sq_abs]
    have hbound : |Real.exp y - (1 + y + y ^ 2 / 2)| / y ^ 2 ≤ |y| * (4 / 18) := by
      rw [div_le_iff₀ (sq_pos_of_ne_zero hy0)]
      have hfac : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num
      rw [hfac] at hb
      calc |Real.exp y - (1 + y + y ^ 2 / 2)|
          ≤ |y| ^ 3 * ((3 + 1 : ℕ) / (6 * (3 : ℕ))) := hb
        _ = |y| * (4 / 18) * y ^ 2 := by
            rw [pow_succ', sq_abs]
            push_cast
            ring
    linarith [abs_nonneg y]
  have hlin : Tendsto (fun y : ℝ ↦ (Real.exp y - 1) / y) (𝓝[≠] 0) (𝓝 1) := by
    have h := (continuous_dslope_exp_zero.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
    rw [dslope_same, (Real.hasDerivAt_exp 0).deriv, Real.exp_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : y ≠ 0)
    rw [dslope_of_ne _ hy, slope_def_field, sub_zero, Real.exp_zero]
  have hlog_map : Tendsto Real.log (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Real.continuousAt_log one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds |>.trans
        (by rw [Real.log_one])) ?_
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one), self_mem_nhdsWithin]
      with t (ht0 : 0 < t) (ht1 : t ≠ 1)
    exact Real.log_ne_zero_of_pos_of_ne_one ht0 ht1
  have hquot : Tendsto (fun y : ℝ ↦ ((Real.exp y - 1 - y) / y ^ 2) / ((Real.exp y - 1) / y))
      (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    simpa only [Pi.div_def, div_one] using hquad.div hlin one_ne_zero
  refine (hquot.comp hlog_map).congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one), self_mem_nhdsWithin]
    with t (ht0 : 0 < t) (ht1 : t ≠ 1)
  have hlog : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht0 ht1
  have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  dsimp only [Function.comp_def]
  rw [Real.exp_log ht0]
  field_simp [hlog, hsub]

/-- The regularised integrand `t ↦ (log t)⁻¹ - (t - 1)⁻¹` is interval integrable on `[a, b]`
for all `0 ≤ a`, `0 ≤ b`. -/
theorem intervalIntegrable_inv_log_sub_inv_sub_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) volume a b := by
  let g : ℝ → ℝ := fun t ↦ if t = 1 then 1 / 2 else (Real.log t)⁻¹ - (t - 1)⁻¹
  have hg_cont : ContinuousOn g (Ici 0) := by
    intro t (ht : 0 ≤ t)
    by_cases ht1 : t = 1
    · subst ht1
      have hne : Tendsto g (𝓝[≠] 1) (𝓝 (g 1)) := by
        simp only [g, ite_true]
        refine tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 1)
        simp [hs]
      exact (continuousWithinAt_compl_self.mp hne).continuousWithinAt
    · rcases ht.eq_or_lt with rfl | ht0
      · have h0 : g 0 = 1 := by simp [g]
        have hIci : Ici (0 : ℝ) = insert 0 (Ioi 0) := by
          ext s; simp [le_iff_eq_or_lt, eq_comm]
        rw [ContinuousWithinAt, h0, hIci, nhdsWithin_insert, tendsto_sup]
        refine ⟨by simpa [h0] using tendsto_pure_nhds g 0, ?_⟩
        refine tendsto_inv_log_sub_inv_sub_one_nhdsGT_zero.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with s hs
        simp [g, hs.2.ne]
      · have hc : ContinuousAt (fun s : ℝ ↦ (Real.log s)⁻¹ - (s - 1)⁻¹) t :=
          ((Real.continuousAt_log ht0.ne').inv₀ (Real.log_ne_zero_of_pos_of_ne_one ht0 ht1)).sub
            ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr ht1))
        refine (hc.congr ?_).continuousWithinAt
        filter_upwards [isOpen_ne.mem_nhds ht1] with s hs
        simp [g, hs]
  have hint_g : IntervalIntegrable g volume a b := by
    refine (hg_cont.mono fun t ht ↦ ?_).intervalIntegrable
    rcases mem_uIcc.mp ht with h | h
    · exact ha.trans h.1
    · exact hb.trans h.1
  refine hint_g.congr_ae ?_
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
    rw [ae_iff]
    simp
  filter_upwards [MeasureTheory.ae_restrict_of_ae hne] with t ht
  simp [g, ht]

/-! ### Absolutely convergent integral representations -/

/-- **Absolutely convergent integral for `li x`**: for every `x > 0` with `x ≠ 1`,
`li x = log |x - 1| + ∫ t in 0..x, ((log t)⁻¹ - (t - 1)⁻¹)`. -/
theorem li_eq_log_abs_sub_one_add_integral {x : ℝ} (hx0 : 0 < x) (hx1 : x ≠ 1) :
    li x = Real.log |x - 1| + ∫ t in (0 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹) := by
  -- Antiderivative of `(t - 1)⁻¹` on any interval avoiding `1`.
  have hint_sub : ∀ {a b : ℝ}, (∀ t ∈ uIcc a b, t ≠ 1) →
      (∫ t in a..b, (t - 1)⁻¹) = Real.log |b - 1| - Real.log |a - 1| := by
    intro a b hne
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
      (f := fun t : ℝ ↦ Real.log (t - 1)) (f' := fun t : ℝ ↦ (t - 1)⁻¹)
      (fun t ht ↦ by
        have h := (Real.hasDerivAt_log (sub_ne_zero.mpr (hne t ht))).comp t
          ((hasDerivAt_id' t).fun_sub (hasDerivAt_const t (1 : ℝ)))
        simpa only [Function.comp_def, sub_zero, mul_one] using h)
      (ContinuousOn.intervalIntegrable fun t ht ↦
        ((continuousAt_id.sub continuousAt_const).inv₀
          (sub_ne_zero.mpr (hne t ht))).continuousWithinAt)
    simpa [Real.log_abs] using hFTC
  rcases lt_or_gt_of_ne hx1 with hx | hx
  · -- Case 1: `0 < x < 1`, split the convergent integral directly.
    have h1 := intervalIntegrable_inv_log_of_lt_one le_rfl zero_lt_one hx0.le hx
    have h2 : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume 0 x :=
      ContinuousOn.intervalIntegrable fun t ht ↦ by
        rw [uIcc_of_le hx0.le] at ht
        exact ((continuousAt_id.sub continuousAt_const).inv₀
          (sub_ne_zero.mpr (ht.2.trans_lt hx).ne)).continuousWithinAt
    rw [intervalIntegral.integral_sub h1 h2, ← li_eq_integral_of_lt_one hx0 hx,
      hint_sub (fun t ht ↦ by rw [uIcc_of_le hx0.le] at ht; exact (ht.2.trans_lt hx).ne)]
    norm_num
  · -- Case 2: `1 < x`, excise `(1 - ε, 1 + ε)` and compare with the Cauchy principal value.
    have hint_g : IntegrableOn (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) (uIcc 0 x) := by
      rw [uIcc_of_le hx0.le, integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx0.le).mp
        (intervalIntegrable_inv_log_sub_inv_sub_one le_rfl hx0.le)
    have hL1 : Tendsto (fun ε : ℝ ↦ ∫ t in (0 : ℝ)..(1 - ε), ((Real.log t)⁻¹ - (t - 1)⁻¹))
        (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..1, ((Real.log t)⁻¹ - (t - 1)⁻¹))) := by
      have hcont := intervalIntegral.continuousOn_primitive_interval (μ := volume) hint_g
      have h1 : (1 : ℝ) ∈ uIcc 0 x := by rw [uIcc_of_le hx0.le]; exact ⟨zero_le_one, hx.le⟩
      have hmap : Tendsto (fun ε : ℝ ↦ 1 - ε) (𝓝[>] 0) (𝓝[uIcc 0 x] 1) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (by
            simpa using
              ((by fun_prop : Continuous fun ε : ℝ ↦ 1 - ε).continuousAt
                (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds) ?_
        filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
        rw [uIcc_of_le hx0.le]
        exact ⟨by linarith [hε.2], by linarith [hε.1, hx]⟩
      exact (hcont 1 h1).tendsto.comp hmap
    have hL2 : Tendsto (fun ε : ℝ ↦ ∫ t in (1 + ε)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹))
        (𝓝[>] 0) (𝓝 (∫ t in (1 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹))) := by
      have hcont := intervalIntegral.continuousOn_primitive_interval_left (μ := volume) hint_g
      have h1 : (1 : ℝ) ∈ uIcc 0 x := by rw [uIcc_of_le hx0.le]; exact ⟨zero_le_one, hx.le⟩
      have hmap : Tendsto (fun ε : ℝ ↦ 1 + ε) (𝓝[>] 0) (𝓝[uIcc 0 x] 1) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (by
            simpa using
              ((by fun_prop : Continuous fun ε : ℝ ↦ 1 + ε).continuousAt
                (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds) ?_
        filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hx)] with ε hε
        rw [uIcc_of_le hx0.le]
        exact ⟨by linarith [hε.1], by linarith [hε.2]⟩
      exact (hcont 1 h1).tendsto.comp hmap
    have hLHS : Tendsto
        (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..(1 - ε), ((Real.log t)⁻¹ - (t - 1)⁻¹)) +
          ∫ t in (1 + ε)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹))
        (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹))) := by
      have h := hL1.add hL2
      rwa [intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_inv_log_sub_inv_sub_one le_rfl zero_le_one)
        (intervalIntegrable_inv_log_sub_inv_sub_one zero_le_one hx0.le)] at h
    have hRHS : Tendsto
        (fun ε : ℝ ↦ ((∫ t in (0 : ℝ)..(1 - ε), (Real.log t)⁻¹) +
          ∫ t in (1 + ε)..x, (Real.log t)⁻¹) - Real.log |x - 1|)
        (𝓝[>] 0) (𝓝 (li x - Real.log |x - 1|)) :=
      (tendsto_pv_inv_log_eq_li hx).sub tendsto_const_nhds
    have hEq :
        (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..(1 - ε), ((Real.log t)⁻¹ - (t - 1)⁻¹)) +
          ∫ t in (1 + ε)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹)) =ᶠ[𝓝[>] 0]
        fun ε : ℝ ↦ ((∫ t in (0 : ℝ)..(1 - ε), (Real.log t)⁻¹) +
          ∫ t in (1 + ε)..x, (Real.log t)⁻¹) - Real.log |x - 1| := by
      filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one (sub_pos.mpr hx))] with ε hε
      have hε1 : ε < 1 := lt_of_lt_of_le hε.2 (min_le_left _ _)
      have hεx : 1 + ε < x := by linarith [lt_of_lt_of_le hε.2 (min_le_right _ _)]
      have hi1 := intervalIntegrable_inv_log_of_lt_one (a := 0) (b := 1 - ε)
        le_rfl zero_lt_one (by linarith) (by linarith [hε.1])
      have hi2 : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume 0 (1 - ε) :=
        ContinuousOn.intervalIntegrable fun t ht ↦ by
          rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ 1 - ε)] at ht
          have hne : t - 1 ≠ 0 := by linarith [ht.2, hε.1]
          exact ((continuousAt_id.sub continuousAt_const).inv₀ hne).continuousWithinAt
      have hi3 : IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹) volume (1 + ε) x := by
        simpa only [pow_one] using intervalIntegrable_inv_log_pow 1 (by linarith [hε.1]) hx
      have hi4 : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume (1 + ε) x :=
        ContinuousOn.intervalIntegrable fun t ht ↦ by
          rw [uIcc_of_le hεx.le] at ht
          have hne : t - 1 ≠ 0 := by linarith [ht.1, hε.1]
          exact ((continuousAt_id.sub continuousAt_const).inv₀ hne).continuousWithinAt
      rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_sub hi3 hi4,
        hint_sub (fun t ht ↦ by rw [uIcc_of_le (by linarith)] at ht; linarith [ht.2, hε.1]),
        hint_sub (fun t ht ↦ by rw [uIcc_of_le hεx.le] at ht; linarith [ht.1, hε.1])]
      have habs : |(1 - ε) - 1| = |(1 + ε) - 1| := by
        rw [sub_sub_cancel_left, add_sub_cancel_left, abs_neg]
      rw [habs]
      norm_num
      ring
    linarith [tendsto_nhds_unique (hLHS.congr' hEq) hRHS]

/-- **Symmetric integral for `li 2`**:
`li 2 = ∫ u in 0..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹)`. -/
theorem li_two_eq_integral_symm :
    li 2 = ∫ u in (0 : ℝ)..1, ((Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) := by
  have hli2 := li_eq_log_abs_sub_one_add_integral two_pos (by norm_num)
  norm_num at hli2
  rw [hli2, ← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_inv_log_sub_inv_sub_one le_rfl zero_le_one)
    (intervalIntegrable_inv_log_sub_inv_sub_one zero_le_one zero_le_two)]
  have h1 : (∫ t in (0 : ℝ)..1, ((Real.log t)⁻¹ - (t - 1)⁻¹)) =
      ∫ u in (0 : ℝ)..1, ((Real.log (1 - u))⁻¹ + u⁻¹) := by
    have hcomp := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (f := fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) 1
    simpa [sub_sub_cancel_left, inv_neg, sub_neg_eq_add] using hcomp.symm
  have h2 : (∫ t in (1 : ℝ)..2, ((Real.log t)⁻¹ - (t - 1)⁻¹)) =
      ∫ u in (0 : ℝ)..1, ((Real.log (1 + u))⁻¹ - u⁻¹) := by
    have hcomp := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := 1)
      (f := fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) 1
    simpa [add_sub_cancel_left, one_add_one_eq_two] using hcomp.symm
  have hint1 : IntervalIntegrable (fun u : ℝ ↦ (Real.log (1 - u))⁻¹ + u⁻¹) volume 0 1 := by
    have h := ((intervalIntegrable_inv_log_sub_inv_sub_one le_rfl zero_le_one).comp_sub_left 1).symm
    rw [sub_zero, sub_self] at h
    have heq : (fun u : ℝ ↦ (Real.log (1 - u))⁻¹ - (1 - u - 1)⁻¹) =
        fun u : ℝ ↦ (Real.log (1 - u))⁻¹ + u⁻¹ := by
      ext u; simp only [sub_sub_cancel_left, inv_neg, sub_neg_eq_add]
    rwa [heq] at h
  have hint2 : IntervalIntegrable (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ - u⁻¹) volume 0 1 := by
    have h := (intervalIntegrable_inv_log_sub_inv_sub_one zero_le_one zero_le_two).comp_add_left 1
    norm_num at h
    exact h
  rw [h1, h2, ← intervalIntegral.integral_add hint1 hint2]
  congr 1; ext u; ring

/-- The symmetric integrand `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` is strictly positive on `(0, 1)`. -/
theorem inv_log_one_add_add_inv_log_one_sub_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 < (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹ := by
  have h1 := inv_log_sub_inv_sub_one_pos (by linarith : 0 < 1 + u) (by linarith : 1 + u ≠ 1)
  have h2 := inv_log_sub_inv_sub_one_pos (by linarith : 0 < 1 - u) (by linarith : 1 - u ≠ 1)
  have heq : ((Real.log (1 + u))⁻¹ - (1 + u - 1)⁻¹) +
      ((Real.log (1 - u))⁻¹ - (1 - u - 1)⁻¹) =
      (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹ := by
    have : (1 - u - 1)⁻¹ = -u⁻¹ := by rw [sub_sub_cancel_left, inv_neg]
    rw [add_sub_cancel_left, this]
    ring
  linarith

/-- The symmetric integrand `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` is strictly less than `3 / 2`
on `(0, 1)`. -/
theorem inv_log_one_add_add_inv_log_one_sub_lt_three_halves {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹ < 3 / 2 := by
  have h1 := inv_log_sub_inv_sub_one_lt_half (by linarith : 1 < 1 + u)
  have h2 := inv_log_sub_inv_sub_one_lt_one (by linarith : 0 < 1 - u) (by linarith : 1 - u ≠ 1)
  have heq : ((Real.log (1 + u))⁻¹ - (1 + u - 1)⁻¹) +
      ((Real.log (1 - u))⁻¹ - (1 - u - 1)⁻¹) =
      (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹ := by
    have : (1 - u - 1)⁻¹ = -u⁻¹ := by rw [sub_sub_cancel_left, inv_neg]
    rw [add_sub_cancel_left, this]
    ring
  linarith

/-- As `u → 0⁺`, `(log (1 + u))⁻¹ + (log (1 - u))⁻¹ → 1`. -/
theorem tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsGT_zero :
    Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) (𝓝[>] 0) (𝓝 1) := by
  have h1 : Tendsto (fun u : ℝ ↦ 1 + u) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by
        simpa using
          ((by fun_prop : Continuous fun u : ℝ ↦ 1 + u).continuousAt
            (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
    exact ne_of_gt (by linarith)
  have h2 : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by
        simpa using
          ((by fun_prop : Continuous fun u : ℝ ↦ 1 - u).continuousAt
            (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
    exact ne_of_lt (by linarith)
  have hsum : Tendsto
      (fun u : ℝ ↦ ((Real.log (1 + u))⁻¹ - (1 + u - 1)⁻¹) +
        ((Real.log (1 - u))⁻¹ - (1 - u - 1)⁻¹)) (𝓝[>] 0) (𝓝 (1 / 2 + 1 / 2)) :=
    (tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.comp h1).add
      (tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.comp h2)
  rw [add_halves] at hsum
  refine hsum.congr fun u ↦ ?_
  have : (1 - u - 1)⁻¹ = -u⁻¹ := by rw [sub_sub_cancel_left, inv_neg]
  rw [add_sub_cancel_left, this]
  ring

/-- As `u → 1⁻`, `(log (1 + u))⁻¹ + (log (1 - u))⁻¹ → (log 2)⁻¹`. -/
theorem tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsLT_one :
    Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) (𝓝[<] 1)
      (𝓝 (Real.log 2)⁻¹) := by
  have h1 : Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹) (𝓝[<] 1) (𝓝 (Real.log 2)⁻¹) := by
    have hc : ContinuousAt (fun u : ℝ ↦ (Real.log (1 + u))⁻¹) 1 :=
      ((Real.continuousAt_log (by norm_num)).comp
        (by fun_prop : Continuous fun u : ℝ ↦ 1 + u).continuousAt).inv₀
        (by
          dsimp only [Function.comp_def]
          rw [one_add_one_eq_two]
          exact (Real.log_pos one_lt_two).ne')
    simpa [one_add_one_eq_two] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun u : ℝ ↦ (Real.log (1 - u))⁻¹) (𝓝[<] 1) (𝓝 0) := by
    have hmap : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[<] 1) (𝓝 0) := by
      simpa using
        ((by fun_prop : Continuous fun u : ℝ ↦ 1 - u).continuousAt
          (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [Function.comp_def, Real.log_zero, inv_zero] using
      Real.continuousAt_inv_log_zero.tendsto.comp hmap
  simpa using h1.add h2

end TauCeti.Real
