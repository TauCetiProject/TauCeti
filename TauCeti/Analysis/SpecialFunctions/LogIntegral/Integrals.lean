/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Principal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integral representations of the logarithmic integral

This file proves the exponential-integral and absolutely convergent integral representations of
`TauCeti.Real.principalLogIntegral`:

* Exponential-integral form on `(-∞, 0)` and as a Cauchy principal value on `(0, ∞)`:
  `∫_{-∞}^y (e^u / u) du = li (e^y)` for `y < 0`, and
  `lim_{ε → 0⁺} (∫_{-1/ε}^{-ε} (e^u / u) du + ∫_ε^y (e^u / u) du) = li (e^y)` for `y > 0`.
* Desingularized absolutely convergent integral for every `x > 0`:
  `li x = log |x - 1| + ∫₀ˣ ((log t)⁻¹ - (t - 1)⁻¹) dt`, with removable singularities at `0` and
  `1`, and at `x = 1` the Euler–Mascheroni integral
  `γ = ∫₀¹ ((log t)⁻¹ - (t - 1)⁻¹) dt`.
* Symmetric absolutely convergent integral for `li 2`:
  `li 2 = ∫₀¹ ((log (1 + u))⁻¹ + (log (1 - u))⁻¹) du`, together with its boundary limits and the
  explicit uniform bound `|(log (1 + u))⁻¹ + (log (1 - u))⁻¹| ≤ (16 / 3) log (4 / 3)` for
  `|u| ≤ 1 / 2`.

## References

* NIST Digital Library of Mathematical Functions (DLMF), §6.2 (Exponential and Logarithmic
  Integrals).
-/

public section

namespace TauCeti.Real

open Filter MeasureTheory Set
open scoped Topology Nat

/-! ### Exponential-integral representations -/

/-- For `y < 0`, `u ↦ exp u / u` is integrable on `(-∞, y]`. -/
theorem integrableOn_exp_div_Iic {y : ℝ} (hy : y < 0) :
    IntegrableOn (fun u : ℝ ↦ Real.exp u / u) (Iic y) := by
  have hexp : IntegrableOn (fun u : ℝ ↦ (-y)⁻¹ * Real.exp (1 * u)) (Iic y) :=
    (integrableOn_exp_mul_Iic one_pos y).const_mul (-y)⁻¹
  have hmeas : AEStronglyMeasurable (fun u : ℝ ↦ Real.exp u / u) (volume.restrict (Iic y)) :=
    (Real.continuous_exp.measurable.div measurable_id).aestronglyMeasurable
  refine hexp.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
  have huy : u ≤ y := hu
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _), abs_of_neg (huy.trans_lt hy),
    one_mul, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ (neg_pos.mpr hy) (neg_le_neg huy))
    (Real.exp_pos _).le

/-- For `y < 0`, `∫_{-∞}^y (e^u / u) du = li (e^y)`. -/
theorem integral_exp_div_Iic_eq_principalLogIntegral_exp {y : ℝ} (hy : y < 0) :
    (∫ u in Iic y, Real.exp u / u) = principalLogIntegral (Real.exp y) := by
  have hlim_lhs : Tendsto (fun R : ℝ ↦ ∫ u in (-R)..y, Real.exp u / u) atTop
      (𝓝 (∫ u in Iic y, Real.exp u / u)) :=
    intervalIntegral_tendsto_integral_Iic y (integrableOn_exp_div_Iic hy) tendsto_neg_atTop_atBot
  have hcont : ContinuousOn (fun δ : ℝ ↦ ∫ t in δ..Real.exp y, (Real.log t)⁻¹)
      (uIcc 0 (Real.exp y)) := by
    refine intervalIntegral.continuousOn_primitive_interval_left ?_
    rw [uIcc_of_le (Real.exp_pos y).le, integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (Real.exp_pos y).le).mp
      (intervalIntegrable_inv_log_of_mem_Ioo ⟨by norm_num, zero_lt_one⟩
        ⟨by linarith [Real.exp_pos y], Real.exp_lt_one_iff.mpr hy⟩)
  have hmem : uIcc (0 : ℝ) (Real.exp y) ∈ 𝓝[>] (0 : ℝ) := by
    rw [uIcc_of_le (Real.exp_pos y).le]
    exact mem_nhdsWithin.mpr ⟨Iio (Real.exp y), isOpen_Iio, Real.exp_pos y,
      fun t ht ↦ ⟨ht.2.le, ht.1.le⟩⟩
  have hlim_rhs : Tendsto (fun R : ℝ ↦ ∫ t in Real.exp (-R)..Real.exp y, (Real.log t)⁻¹) atTop
      (𝓝 (∫ t in (0 : ℝ)..Real.exp y, (Real.log t)⁻¹)) :=
    ((hcont 0 left_mem_uIcc).tendsto.mono_left (nhdsWithin_le_iff.mpr hmem)).comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
        (Eventually.of_forall fun _ ↦ Real.exp_pos _))
  have heq : ∀ᶠ R in atTop,
      (∫ u in (-R)..y, Real.exp u / u) = ∫ t in Real.exp (-R)..Real.exp y, (Real.log t)⁻¹ := by
    filter_upwards [eventually_gt_atTop (-y)] with R hR
    have hsub := intervalIntegral.integral_comp_mul_deriv' (a := -R) (b := y)
      (f := Real.exp) (f' := Real.exp) (g := fun t : ℝ ↦ (Real.log t)⁻¹)
      (fun u _ ↦ Real.hasDerivAt_exp u) Real.continuous_exp.continuousOn ?_
    · rw [← hsub]
      refine intervalIntegral.integral_congr fun u _ ↦ ?_
      simp only [Function.comp_apply, Real.log_exp, div_eq_mul_inv, mul_comm]
    · intro t ht
      obtain ⟨u, hu, rfl⟩ := ht
      rw [uIcc_of_le (by linarith : -R ≤ y)] at hu
      have hpos : 0 < Real.exp u := Real.exp_pos u
      have hlt : Real.exp u < 1 := Real.exp_lt_one_iff.mpr (hu.2.trans_lt hy)
      exact ((Real.continuousAt_log hpos.ne').inv₀ (Real.log_neg hpos hlt).ne).continuousWithinAt
  rw [principalLogIntegral_eq_integral (Real.exp_pos y) (Real.exp_lt_one_iff.mpr hy)]
  exact tendsto_nhds_unique (hlim_lhs.congr' heq) hlim_rhs

/-- Algebraic rearrangement of the symmetric cutoff exponential integral for `0 < ε < min 1 y`. -/
private theorem integral_exp_div_pv_eq {y ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hεy : ε < y) :
    (∫ u in (-ε⁻¹)..(-ε), Real.exp u / u) + (∫ u in ε..y, Real.exp u / u) =
      ((∫ t in ε..1, (1 - Real.exp (-t)) / t) - ∫ t in (1 : ℝ)..ε⁻¹, Real.exp (-t) / t) +
        Real.log y + ∫ u in ε..y, (Real.exp u - 1) / u := by
  have hy : 0 < y := hε0.trans hεy
  have h1inv : 1 < ε⁻¹ := (one_lt_inv₀ hε0).mpr hε1
  have hcont_exp : ∀ {a b : ℝ}, 0 < a → a ≤ b →
      IntervalIntegrable (fun t : ℝ ↦ Real.exp (-t) / t) volume a b := by
    intro a b ha hab
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hab] at ht
    have hne : t ≠ 0 := (ha.trans_le ht.1).ne'
    fun_prop (disch := assumption)
  have hleft : (∫ u in (-ε⁻¹)..(-ε), Real.exp u / u) =
      -(∫ t in ε..1, Real.exp (-t) / t) - ∫ t in (1 : ℝ)..ε⁻¹, Real.exp (-t) / t := by
    have hneg := intervalIntegral.integral_comp_neg (a := ε) (b := ε⁻¹)
      (f := fun u : ℝ ↦ Real.exp u / u)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hcont_exp hε0 hε1.le) (hcont_exp one_pos h1inv.le)
    have hcongr : (∫ t in ε..ε⁻¹, Real.exp (-t) / -t) = -(∫ t in ε..ε⁻¹, Real.exp (-t) / t) := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr fun t _ ↦ by ring
    linarith [hneg, hsplit, hcongr]
  have hi_inv : ∀ {b : ℝ}, ε ≤ b → IntervalIntegrable (fun u : ℝ ↦ u⁻¹) volume ε b := by
    intro b hεb
    exact intervalIntegral.intervalIntegrable_inv
      (fun t ht ↦ by rw [uIcc_of_le hεb] at ht; exact (hε0.trans_le ht.1).ne') continuousOn_id
  have hright : (∫ u in ε..y, Real.exp u / u) =
      (∫ u in ε..y, (Real.exp u - 1) / u) + Real.log y + ∫ t in ε..1, t⁻¹ := by
    have hadd : (∫ u in ε..y, Real.exp u / u) =
        (∫ u in ε..y, (Real.exp u - 1) / u) + ∫ u in ε..y, u⁻¹ := by
      rw [← intervalIntegral.integral_add (intervalIntegrable_exp_sub_one_div ε y) (hi_inv hεy.le)]
      exact intervalIntegral.integral_congr fun u _ ↦ by ring
    have hlog1 : (∫ u in ε..y, u⁻¹) = Real.log y - Real.log ε := by
      rw [integral_inv_of_pos hε0 hy, Real.log_div hy.ne' hε0.ne']
    have hlog2 : (∫ t in ε..1, t⁻¹) = -Real.log ε := by
      rw [integral_inv_of_pos hε0 one_pos, Real.log_div one_ne_zero hε0.ne', Real.log_one, zero_sub]
    linarith
  have hcomb : (∫ t in ε..1, (1 - Real.exp (-t)) / t) =
      (∫ t in ε..1, t⁻¹) - ∫ t in ε..1, Real.exp (-t) / t := by
    rw [← intervalIntegral.integral_sub (hi_inv hε1.le) (hcont_exp hε0 hε1.le)]
    exact intervalIntegral.integral_congr fun t _ ↦ by ring
  linarith

/-- **Exponential-integral form of the Cauchy principal value**: for `y > 0`,
`lim_{ε → 0⁺} (∫_{-1/ε}^{-ε} (e^u / u) du + ∫_ε^y (e^u / u) du) = li (e^y)`. -/
theorem tendsto_integral_exp_div_pv {y : ℝ} (hy : 0 < y) :
    Tendsto
      (fun ε : ℝ ↦ (∫ u in (-ε⁻¹)..(-ε), Real.exp u / u) + ∫ u in ε..y, Real.exp u / u)
      (𝓝[>] 0) (𝓝 (principalLogIntegral (Real.exp y))) := by
  have hmem : ∀ {b : ℝ}, 0 < b → uIcc (0 : ℝ) b ∈ 𝓝[>] (0 : ℝ) := fun {b} hb ↦ by
    rw [uIcc_of_le hb.le]
    exact mem_nhdsWithin.mpr ⟨Iio b, isOpen_Iio, hb, fun t ht ↦ ⟨ht.2.le, ht.1.le⟩⟩
  have hlim1 : Tendsto (fun ε : ℝ ↦ ∫ t in ε..1, (1 - Real.exp (-t)) / t) (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t)) := by
    have hi : IntegrableOn (fun t : ℝ ↦ (1 - Real.exp (-t)) / t) (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one, integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegrable_one_sub_exp_neg_div 0 1)
    exact ((intervalIntegral.continuousOn_primitive_interval_left hi) 0
      left_mem_uIcc).tendsto.mono_left (nhdsWithin_le_iff.mpr (hmem zero_lt_one))
  have hlim2 : Tendsto (fun ε : ℝ ↦ ∫ t in (1 : ℝ)..ε⁻¹, Real.exp (-t) / t) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (1 : ℝ), Real.exp (-t) / t)) :=
    intervalIntegral_tendsto_integral_Ioi 1 (integrableOn_exp_neg_div_Ioi one_pos)
      tendsto_inv_nhdsGT_zero
  have hlim3 : Tendsto (fun ε : ℝ ↦ ∫ u in ε..y, (Real.exp u - 1) / u) (𝓝[>] 0)
      (𝓝 (∫ u in (0 : ℝ)..y, (Real.exp u - 1) / u)) := by
    have hi : IntegrableOn (fun u : ℝ ↦ (Real.exp u - 1) / u) (uIcc 0 y) := by
      rw [uIcc_of_le hy.le, integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hy.le).mp
        (intervalIntegrable_exp_sub_one_div 0 y)
    exact ((intervalIntegral.continuousOn_primitive_interval_left hi) 0
      left_mem_uIcc).tendsto.mono_left (nhdsWithin_le_iff.mpr (hmem hy))
  have htot : Tendsto (fun ε : ℝ ↦
      ((∫ t in ε..1, (1 - Real.exp (-t)) / t) - ∫ t in (1 : ℝ)..ε⁻¹, Real.exp (-t) / t) +
        Real.log y + ∫ u in ε..y, (Real.exp u - 1) / u)
      (𝓝[>] 0) (𝓝 (principalLogIntegral (Real.exp y))) := by
    rw [principalLogIntegral_eq_add_integral, Real.log_exp,
      eulerMascheroniConstant_eq_integral_sub_integral]
    exact (((hlim1.sub hlim2).add tendsto_const_nhds).add hlim3)
  refine htot.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one hy)] with ε hε
  exact (integral_exp_div_pv_eq hε.1 (hε.2.trans_le (min_le_left _ _))
    (hε.2.trans_le (min_le_right _ _))).symm

/-! ### Absolutely convergent integral representations -/

/-- Exact integral formula `u - log (1 + u) = ∫₀^u t / (1 + t) dt` for `|u| < 1 / 2`. -/
private theorem sub_log_one_add_eq_integral {u : ℝ} (hu : |u| < 1 / 2) :
    (∫ t in (0 : ℝ)..u, t / (1 + t)) = u - Real.log (1 + u) := by
  have hderiv : ∀ t ∈ uIcc 0 u, HasDerivAt (fun s : ℝ ↦ s - Real.log (1 + s)) (t / (1 + t)) t := by
    intro t ht
    have h1t : 0 < 1 + t := by rcases mem_uIcc.mp ht with h | h <;> linarith [(abs_lt.mp hu).1]
    have hd := (hasDerivAt_id t).sub
      ((Real.hasDerivAt_log h1t.ne').comp t ((hasDerivAt_id t).const_add 1))
    refine hd.congr_deriv ?_
    field_simp [h1t.ne']; ring
  have hcont : ContinuousOn (fun t : ℝ ↦ t / (1 + t)) (uIcc 0 u) := by
    intro t ht
    have h1t : 1 + t ≠ 0 := by rcases mem_uIcc.mp ht with h | h <;> linarith [(abs_lt.mp hu).1]
    fun_prop (disch := assumption)
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-- For `|u| < 1 / 2`, the remainder `u - log (1 + u)` lies between `u² / 2` and
`u² / (2 (1 + u))`. -/
private theorem sub_log_one_add_between {u : ℝ} (hu : |u| < 1 / 2) :
    min (u ^ 2 / 2) (u ^ 2 / (2 * (1 + u))) ≤ u - Real.log (1 + u) ∧
      u - Real.log (1 + u) ≤ max (u ^ 2 / 2) (u ^ 2 / (2 * (1 + u))) := by
  have h1u : 0 < 1 + u := by linarith [(abs_lt.mp hu).1]
  have hFTC := sub_log_one_add_eq_integral hu
  have hcont : ContinuousOn (fun t : ℝ ↦ t / (1 + t)) (uIcc 0 u) := fun t ht ↦ by
    have h1t : 1 + t ≠ 0 := by rcases mem_uIcc.mp ht with h | h <;> linarith [(abs_lt.mp hu).1]
    fun_prop (disch := assumption)
  have hint_id : ∀ c : ℝ, (∫ t in (0 : ℝ)..u, t / c) = u ^ 2 / (2 * c) := fun c ↦ by
    rw [intervalIntegral.integral_div, integral_id]; ring
  rcases le_or_gt 0 u with hu0 | hu0
  · have hlo : u ^ 2 / (2 * (1 + u)) ≤ u - Real.log (1 + u) := by
      rw [← hFTC, ← hint_id (1 + u)]
      refine intervalIntegral.integral_mono_on hu0
        ((continuous_id.div_const (1 + u)).intervalIntegrable 0 u) hcont.intervalIntegrable
        fun t ht ↦ div_le_div_of_nonneg_left ht.1 (by linarith [ht.1]) (by linarith [ht.2])
    have hhi : u - Real.log (1 + u) ≤ u ^ 2 / 2 := by
      have h1 := hint_id 1; rw [mul_one] at h1
      rw [← hFTC, ← h1]
      refine intervalIntegral.integral_mono_on hu0 hcont.intervalIntegrable
        ((continuous_id.div_const 1).intervalIntegrable 0 u) fun t ht ↦ by
          simpa using div_le_self ht.1 (by linarith [ht.1])
    exact ⟨(min_le_right _ _).trans hlo, hhi.trans (le_max_left _ _)⟩
  · have hsym : u - Real.log (1 + u) = ∫ t in u..(0 : ℝ), (-t) / (1 + t) := by
      rw [← hFTC, intervalIntegral.integral_symm 0 u, ← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr fun t _ ↦ by ring
    have hcont_neg : ContinuousOn (fun t : ℝ ↦ (-t) / (1 + t)) (uIcc u 0) := fun t ht ↦ by
      have h1t : 1 + t ≠ 0 := by rcases mem_uIcc.mp ht with h | h <;> linarith [(abs_lt.mp hu).1]
      fun_prop (disch := assumption)
    have hint_neg : ∀ c : ℝ, (∫ t in u..(0 : ℝ), (-t) / c) = u ^ 2 / (2 * c) := fun c ↦ by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_neg, integral_id]; ring
    have hlo : u ^ 2 / 2 ≤ u - Real.log (1 + u) := by
      have h1 := hint_neg 1; rw [mul_one] at h1
      rw [hsym, ← h1]
      refine intervalIntegral.integral_mono_on hu0.le
        ((continuous_neg.div_const 1).intervalIntegrable u 0) hcont_neg.intervalIntegrable
        fun t ht ↦ by
          rw [div_one]
          exact (le_div_iff₀ (by linarith [ht.1])).mpr (by nlinarith [ht.2])
    have hhi : u - Real.log (1 + u) ≤ u ^ 2 / (2 * (1 + u)) := by
      rw [hsym, ← hint_neg (1 + u)]
      refine intervalIntegral.integral_mono_on hu0.le hcont_neg.intervalIntegrable
        ((continuous_neg.div_const (1 + u)).intervalIntegrable u 0) fun t ht ↦
        div_le_div_of_nonneg_left (by linarith [ht.2]) h1u (by linarith [ht.1])
    exact ⟨(min_le_left _ _).trans hlo, hhi.trans (le_max_right _ _)⟩

/-- Quadratic limit `(u - log (1 + u)) / u² → 1 / 2` as `u → 0` along `𝓝[≠] 0`. -/
private theorem tendsto_sub_log_one_add_div_sq :
    Tendsto (fun u : ℝ ↦ (u - Real.log (1 + u)) / u ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have hhalf : Tendsto (fun u : ℝ ↦ (2 * (1 + u))⁻¹) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    have hc : ContinuousAt (fun u : ℝ ↦ (2 * (1 + u))⁻¹) 0 := by fun_prop (disch := norm_num)
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hlo_t : Tendsto (fun u : ℝ ↦ min (1 / 2 : ℝ) (2 * (1 + u))⁻¹) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    simpa only [min_self] using tendsto_const_nhds (x := (1 / 2 : ℝ)).min hhalf
  have hhi_t : Tendsto (fun u : ℝ ↦ max (1 / 2 : ℝ) (2 * (1 + u))⁻¹) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    simpa only [max_self] using tendsto_const_nhds (x := (1 / 2 : ℝ)).max hhalf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo_t hhi_t ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))] with
      u hu hball
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hball
    have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero hu
    rw [le_div_iff₀ hu2, min_mul_of_nonneg _ _ hu2.le]
    simpa [div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using
      (sub_log_one_add_between hball).1
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))] with
      u hu hball
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hball
    have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero hu
    rw [div_le_iff₀ hu2, max_mul_of_nonneg _ _ hu2.le]
    simpa [div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using
      (sub_log_one_add_between hball).2

/-- The removable singularity at `t = 1`: `(log t)⁻¹ - (t - 1)⁻¹ → 1 / 2` as `t → 1`. -/
theorem tendsto_inv_log_sub_inv_sub_one_at_one :
    Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) (𝓝[≠] 1) (𝓝 (1 / 2)) := by
  have hshift : Tendsto (fun t : ℝ ↦ t - 1) (𝓝[≠] 1) (𝓝[≠] 0) := by
    have h0 : Tendsto (fun t : ℝ ↦ t - 1) (𝓝[≠] 1) (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℝ ↦ t - 1) 1 := by fun_prop
      simpa only [sub_self] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h0 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_ne_zero.mpr ht
  suffices h : Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ - u⁻¹) (𝓝[≠] 0) (𝓝 (1 / 2)) by
    exact (h.comp hshift).congr fun t ↦ by simp
  have hden : Tendsto (fun u : ℝ ↦ Real.log (1 + u) / u) (𝓝[≠] 0) (𝓝 1) := by
    have hd : HasDerivAt Real.log 1 1 := by simpa using Real.hasDerivAt_log one_ne_zero
    simpa [hasDerivAt_iff_tendsto_slope_zero, smul_eq_mul, div_eq_inv_mul] using hd
  have hquot := tendsto_sub_log_one_add_div_sq.div hden one_ne_zero
  rw [div_one] at hquot
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))] with
    u hu hball
  have hu0 : u ≠ 0 := hu
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hball
  have h1u : 0 < 1 + u := by linarith [(abs_lt.mp hball).1]
  have hlog_ne : Real.log (1 + u) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one h1u (fun h ↦ hu0 (by linarith))
  simp only [Pi.div_apply]
  field_simp [hu0, hlog_ne]

/-- `(log t)⁻¹ - (t - 1)⁻¹ → 1` as `t → 0⁺`. -/
theorem tendsto_inv_log_sub_inv_sub_one_nhdsGT_zero :
    Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) (𝓝[>] 0) (𝓝 1) := by
  have h1 : Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero
  have h2 : Tendsto (fun t : ℝ ↦ (t - 1)⁻¹) (𝓝[>] 0) (𝓝 (-1)) := by
    have hc : ContinuousAt (fun t : ℝ ↦ (t - 1)⁻¹) 0 := by fun_prop (disch := norm_num)
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simpa using h1.sub h2

/-- The continuous extension of `t ↦ (log t)⁻¹ - (t - 1)⁻¹` to `[0, ∞)`. -/
private theorem continuousOn_inv_log_sub_inv_sub_one_ext :
    ContinuousOn (fun t : ℝ ↦ if t = 0 then (1 : ℝ) else if t = 1 then 1 / 2 else
      (Real.log t)⁻¹ - (t - 1)⁻¹) (Ici 0) := by
  intro t ht
  by_cases ht0 : t = 0
  · subst ht0
    rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt]
    simp only [↓reduceIte]
    have hsub : Ici (0 : ℝ) \ {0} ⊆ Ioi 0 := fun s hs ↦ lt_of_le_of_ne hs.1 (Ne.symm hs.2)
    refine (tendsto_inv_log_sub_inv_sub_one_nhdsGT_zero.mono_left
      (nhdsWithin_mono 0 hsub)).congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_ne_nhds (zero_ne_one' ℝ))] with s hs hs1
    have hs0 : s ≠ 0 := hs.2
    simp [hs0, hs1]
  · by_cases ht1 : t = 1
    · subst ht1
      rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt]
      simp only [one_ne_zero, ↓reduceIte]
      have hsub : Ici (0 : ℝ) \ {1} ⊆ {1}ᶜ := fun _ h ↦ h.2
      refine (tendsto_inv_log_sub_inv_sub_one_at_one.mono_left
        (nhdsWithin_mono 1 hsub)).congr' ?_
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_ne_nhds one_ne_zero)] with s hs hs0
      have hs1 : s ≠ 1 := hs.2
      simp [hs0, hs1]
    · have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hlog_ne : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht_pos ht1
      have hsub_ne : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
      have hev : (fun s : ℝ ↦ if s = 0 then (1 : ℝ) else if s = 1 then 1 / 2 else
          (Real.log s)⁻¹ - (s - 1)⁻¹) =ᶠ[𝓝 t] fun s : ℝ ↦ (Real.log s)⁻¹ - (s - 1)⁻¹ := by
        filter_upwards [eventually_ne_nhds ht0, eventually_ne_nhds ht1] with s hs0 hs1
        simp [hs0, hs1]
      have hc : ContinuousAt (fun s : ℝ ↦ (Real.log s)⁻¹ - (s - 1)⁻¹) t :=
        ((Real.continuousAt_log ht_pos.ne').inv₀ hlog_ne).sub
          ((continuousAt_id.sub continuousAt_const).inv₀ hsub_ne)
      exact (hc.congr hev.symm).continuousWithinAt

/-- The function `t ↦ (log t)⁻¹ - (t - 1)⁻¹` has removable singularities at `t = 0` and `t = 1`,
and is therefore interval integrable on `0..x` for every `x > -1`. -/
theorem intervalIntegrable_inv_log_sub_inv_sub_one {x : ℝ} (hx : -1 < x) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) volume 0 x := by
  rcases le_or_gt 0 x with hx0 | hx0
  · have hg_int : IntervalIntegrable (fun t : ℝ ↦ if t = 0 then (1 : ℝ) else if t = 1 then 1 / 2
        else (Real.log t)⁻¹ - (t - 1)⁻¹) volume 0 x :=
      (continuousOn_inv_log_sub_inv_sub_one_ext.mono
        (by rw [uIcc_of_le hx0]; exact fun _ h ↦ h.1)).intervalIntegrable
    refine hg_int.congr_ae ?_
    have hne : ∀ᵐ t ∂volume, t ≠ (0 : ℝ) ∧ t ≠ (1 : ℝ) :=
      (ae_iff.mpr (by simp)).and (ae_iff.mpr (by simp))
    filter_upwards [ae_restrict_of_ae hne] with t ht
    simp [ht.1, ht.2]
  · refine (intervalIntegrable_inv_log_of_mem_Ioo ⟨by norm_num, zero_lt_one⟩
      ⟨hx, hx0.trans zero_lt_one⟩).sub (ContinuousOn.intervalIntegrable fun t ht ↦ ?_)
    rw [uIcc_of_ge hx0.le] at ht
    have hne : t - 1 ≠ 0 := by linarith [ht.2]
    fun_prop (disch := assumption)

/-- Integral of `(t - 1)⁻¹` on an interval avoiding `1`. -/
private theorem integral_inv_sub_one_eq_log {a b : ℝ} (h : ∀ t ∈ uIcc a b, t - 1 ≠ 0) :
    (∫ t in a..b, (t - 1)⁻¹) = Real.log (b - 1) - Real.log (a - 1) := by
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun s : ℝ ↦ Real.log (s - 1)) (t - 1)⁻¹ t := by
    intro t ht
    have h1 := (Real.hasDerivAt_log (h t ht)).comp t ((hasDerivAt_id' t).sub_const 1)
    exact h1.congr_deriv (mul_one _)
  have hi : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦ by
      have := h t ht; fun_prop (disch := assumption)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

/-- Case `0 < x < 1` of `principalLogIntegral_eq_log_add_integral`. -/
private theorem principalLogIntegral_eq_log_add_integral_of_lt_one {x : ℝ}
    (hx0 : 0 < x) (hlt : x < 1) :
    principalLogIntegral x =
      Real.log |x - 1| + ∫ t in (0 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹) := by
  have hne : ∀ t ∈ uIcc (0 : ℝ) x, t - 1 ≠ 0 := fun t ht ↦ by
    rw [uIcc_of_le hx0.le] at ht; linarith [ht.2]
  have h1 : (∫ t in (0 : ℝ)..x, (t - 1)⁻¹) = Real.log |x - 1| := by
    rw [integral_inv_sub_one_eq_log hne, zero_sub, Real.log_neg_eq_log, Real.log_one, sub_zero,
      Real.log_abs]
  have hi : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume 0 x :=
    ContinuousOn.intervalIntegrable fun t ht ↦ by
      have := hne t ht; fun_prop (disch := assumption)
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_inv_log_of_mem_Ioo ⟨by norm_num, zero_lt_one⟩ ⟨by linarith, hlt⟩) hi,
    h1, principalLogIntegral_eq_integral hx0 hlt]
  ring

/-- **Euler–Mascheroni integral on `(0, 1)`**:
`γ = ∫₀¹ ((log t)⁻¹ - (t - 1)⁻¹) dt`. -/
theorem eulerMascheroniConstant_eq_integral_inv_log_sub_inv_sub_one :
    Real.eulerMascheroniConstant = ∫ t in (0 : ℝ)..1, ((Real.log t)⁻¹ - (t - 1)⁻¹) := by
  have hint : IntegrableOn (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one, integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegrable_inv_log_sub_inv_sub_one (by norm_num))
  have hmem : uIcc (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := by
    rw [uIcc_of_le zero_le_one]
    exact mem_nhdsWithin.mpr ⟨Ioi 0, isOpen_Ioi, zero_lt_one, fun t ht ↦ ⟨ht.1.le, ht.2.le⟩⟩
  have hlim_int : Tendsto (fun x : ℝ ↦ ∫ t in (0 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹))
      (𝓝[<] 1) (𝓝 (∫ t in (0 : ℝ)..1, ((Real.log t)⁻¹ - (t - 1)⁻¹))) :=
    ((intervalIntegral.continuousOn_primitive_interval hint) 1
      right_mem_uIcc).tendsto.mono_left (nhdsWithin_le_iff.mpr hmem)
  have hratio : Tendsto (fun x : ℝ ↦ Real.log (Real.log x) - Real.log |x - 1|)
      (𝓝[<] 1) (𝓝 0) := by
    have hd : HasDerivAt Real.log 1 1 := by simpa using Real.hasDerivAt_log one_ne_zero
    have hslope : Tendsto (fun x : ℝ ↦ Real.log x / (x - 1)) (𝓝[<] 1) (𝓝 1) := by
      have h := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
        (nhdsWithin_mono (1 : ℝ) (s := Iio 1) fun _ h ↦ ne_of_lt h)
      exact h.congr fun x ↦ by simp [slope_def_field]
    have hcomp := (Real.continuousAt_log one_ne_zero).tendsto.comp hslope
    rw [Real.log_one] at hcomp
    refine hcomp.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
    have hlog_ne : Real.log x ≠ 0 := (Real.log_neg hx.1 hx.2).ne
    have hx1_ne : x - 1 ≠ 0 := sub_ne_zero.mpr hx.2.ne
    simp only [Function.comp_apply]
    rw [Real.log_div hlog_ne hx1_ne, Real.log_abs]
  have hser : Tendsto (fun x : ℝ ↦
      ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) (𝓝[<] 1) (𝓝 0) := by
    have h0 : (∑' n : ℕ, Real.log (1 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) = 0 := by
      simp
    have hc := (continuous_tsum_pow_div_mul_factorial.continuousAt.comp
      (Real.continuousAt_log one_ne_zero)).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    rw [Function.comp_apply, h0] at hc
    exact hc.congr fun _ ↦ rfl
  have hlim_rhs : Tendsto (fun x : ℝ ↦ principalLogIntegral x - Real.log |x - 1|)
      (𝓝[<] 1) (𝓝 Real.eulerMascheroniConstant) := by
    have h := (tendsto_const_nhds (x := Real.eulerMascheroniConstant).add hratio).add hser
    rw [add_zero, add_zero] at h
    exact h.congr fun x ↦ by simp only [principalLogIntegral_def]; ring
  have hev : ∀ᶠ x in 𝓝[<] (1 : ℝ),
      (∫ t in (0 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹)) =
        principalLogIntegral x - Real.log |x - 1| := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
    linarith [principalLogIntegral_eq_log_add_integral_of_lt_one hx.1 hx.2]
  exact tendsto_nhds_unique hlim_rhs (hlim_int.congr' hev)

/-- Cutoff identity splitting the desingularized integral on `[0, 1 - ε]` and `[1 + ε, x]`. -/
private theorem integral_inv_log_sub_inv_sub_one_pv_eq {x ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hεx : 1 + ε < x) :
    (∫ t in (0 : ℝ)..(1 - ε), ((Real.log t)⁻¹ - (t - 1)⁻¹)) +
        (∫ t in (1 + ε)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹)) =
      ((∫ t in (0 : ℝ)..(1 - ε), (Real.log t)⁻¹) + ∫ t in (1 + ε)..x, (Real.log t)⁻¹) -
        Real.log |x - 1| := by
  have hgt : 1 < x := by linarith
  have hne_l : ∀ t ∈ uIcc (0 : ℝ) (1 - ε), t - 1 ≠ 0 := fun t ht ↦ by
    rw [uIcc_of_le (by linarith)] at ht; linarith [ht.2, hε0]
  have hne_r : ∀ t ∈ uIcc (1 + ε) x, t - 1 ≠ 0 := fun t ht ↦ by
    rw [uIcc_of_le hεx.le] at ht; linarith [ht.1, hε0]
  have hi_l : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume 0 (1 - ε) :=
    ContinuousOn.intervalIntegrable fun t ht ↦ by
      have := hne_l t ht; fun_prop (disch := assumption)
  have hi_r : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume (1 + ε) x :=
    ContinuousOn.intervalIntegrable fun t ht ↦ by
      have := hne_r t ht; fun_prop (disch := assumption)
  have hsub1 := intervalIntegral.integral_sub
    (intervalIntegrable_inv_log_of_mem_Ioo ⟨by norm_num, zero_lt_one⟩
      ⟨by linarith, by linarith⟩) hi_l
  have hsub2 := intervalIntegral.integral_sub
    (by simpa only [pow_one] using intervalIntegrable_inv_log_pow 1 (by linarith) hgt) hi_r
  have hlog_l := integral_inv_sub_one_eq_log hne_l
  have hlog_r := integral_inv_sub_one_eq_log hne_r
  simp only [sub_sub_cancel_left, zero_sub, Real.log_neg_eq_log, Real.log_one, sub_zero,
    add_sub_cancel_left] at hlog_l hlog_r
  rw [abs_of_pos (sub_pos.mpr hgt)]
  linarith

/-- Case `1 < x` of `principalLogIntegral_eq_log_add_integral`. -/
private theorem principalLogIntegral_eq_log_add_integral_of_gt_one {x : ℝ} (hgt : 1 < x) :
    principalLogIntegral x =
      Real.log |x - 1| + ∫ t in (0 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹) := by
  have hx0 : 0 < x := zero_lt_one.trans hgt
  have hint : IntegrableOn (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) (uIcc 0 x) := by
    rw [uIcc_of_le hx0.le, integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx0.le).mp
      (intervalIntegrable_inv_log_sub_inv_sub_one (by linarith))
  have hmem1 : uIcc (0 : ℝ) x ∈ 𝓝 (1 : ℝ) := by
    rw [uIcc_of_le hx0.le]; exact Icc_mem_nhds zero_lt_one hgt
  have h1_mem : (1 : ℝ) ∈ uIcc 0 x := by rw [uIcc_of_le hx0.le]; exact ⟨zero_le_one, hgt.le⟩
  have hlim_l : Tendsto (fun ε : ℝ ↦ ∫ t in (0 : ℝ)..(1 - ε), ((Real.log t)⁻¹ - (t - 1)⁻¹))
      (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..1, ((Real.log t)⁻¹ - (t - 1)⁻¹))) := by
    have hs : Tendsto (fun ε : ℝ ↦ 1 - ε) (𝓝[>] 0) (𝓝 1) := by
      have hc : ContinuousAt (fun ε : ℝ ↦ 1 - ε) 0 := by fun_prop
      simpa only [sub_zero] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    exact (((intervalIntegral.continuousOn_primitive_interval hint) 1
      h1_mem).continuousAt hmem1).tendsto.comp hs
  have hlim_r : Tendsto (fun ε : ℝ ↦ ∫ t in (1 + ε)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹))
      (𝓝[>] 0) (𝓝 (∫ t in (1 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹))) := by
    have hs : Tendsto (fun ε : ℝ ↦ 1 + ε) (𝓝[>] 0) (𝓝 1) := by
      have hc : ContinuousAt (fun ε : ℝ ↦ 1 + ε) 0 := by fun_prop
      simpa only [add_zero] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    exact (((intervalIntegral.continuousOn_primitive_interval_left hint) 1
      h1_mem).continuousAt hmem1).tendsto.comp hs
  have hsplit : (∫ t in (0 : ℝ)..1, ((Real.log t)⁻¹ - (t - 1)⁻¹)) +
      (∫ t in (1 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹)) =
      ∫ t in (0 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹) :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_inv_log_sub_inv_sub_one (by norm_num))
      ((intervalIntegrable_inv_log_sub_inv_sub_one (by linarith)).mono_set
        (uIcc_subset_uIcc h1_mem right_mem_uIcc))
  have hlim_sum : Tendsto (fun ε : ℝ ↦
      (∫ t in (0 : ℝ)..(1 - ε), ((Real.log t)⁻¹ - (t - 1)⁻¹)) +
        ∫ t in (1 + ε)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹))
      (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹))) := by
    rw [← hsplit]; exact hlim_l.add hlim_r
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in (0 : ℝ)..(1 - ε), ((Real.log t)⁻¹ - (t - 1)⁻¹)) +
          (∫ t in (1 + ε)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹)) =
        ((∫ t in (0 : ℝ)..(1 - ε), (Real.log t)⁻¹) + ∫ t in (1 + ε)..x, (Real.log t)⁻¹) -
          Real.log |x - 1| := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one (sub_pos.mpr hgt))] with ε hε
    exact integral_inv_log_sub_inv_sub_one_pv_eq hε.1 (hε.2.trans_le (min_le_left _ _))
      (by linarith [hε.2.trans_le (min_le_right _ _)])
  have hlim_pv := (tendsto_principalLogIntegral_pv hgt).sub
    (tendsto_const_nhds (x := Real.log |x - 1|))
  linarith [tendsto_nhds_unique (hlim_sum.congr' hev) hlim_pv]

/-- **Absolutely convergent integral representation of `li`**: for every `x > 0`,
`li x = log |x - 1| + ∫₀ˣ ((log t)⁻¹ - (t - 1)⁻¹) dt` (at `x = 1`, both sides equal `γ`). -/
theorem principalLogIntegral_eq_log_add_integral {x : ℝ} (hx0 : 0 < x) :
    principalLogIntegral x =
      Real.log |x - 1| + ∫ t in (0 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹) := by
  rcases lt_trichotomy x 1 with hlt | rfl | hgt
  · exact principalLogIntegral_eq_log_add_integral_of_lt_one hx0 hlt
  · rw [sub_self, abs_zero, Real.log_zero, zero_add,
      ← eulerMascheroniConstant_eq_integral_inv_log_sub_inv_sub_one]
    simp [principalLogIntegral_def]
  · exact principalLogIntegral_eq_log_add_integral_of_gt_one hgt

/-- `(log (1 + u))⁻¹ + (log (1 - u))⁻¹ → 1` as `u → 0⁺`. -/
theorem tendsto_inv_log_one_add_add_one_sub_nhdsGT_zero :
    Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) (𝓝[>] 0) (𝓝 1) := by
  have h1 : Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ - u⁻¹) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    have hs0 : Tendsto (fun u : ℝ ↦ 1 + u) (𝓝[>] 0) (𝓝 1) := by
      have hc : ContinuousAt (fun u : ℝ ↦ 1 + u) 0 := by fun_prop
      simpa only [add_zero] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    have hshift : Tendsto (fun u : ℝ ↦ 1 + u) (𝓝[>] 0) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hs0 ?_
      filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
      exact ne_of_gt (by linarith)
    exact (tendsto_inv_log_sub_inv_sub_one_at_one.comp hshift).congr fun u ↦ by simp
  have h2 : Tendsto (fun u : ℝ ↦ (Real.log (1 - u))⁻¹ + u⁻¹) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    have hs0 : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[>] 0) (𝓝 1) := by
      have hc : ContinuousAt (fun u : ℝ ↦ 1 - u) 0 := by fun_prop
      simpa only [sub_zero] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    have hshift : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[>] 0) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hs0 ?_
      filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
      exact ne_of_lt (by linarith)
    exact (tendsto_inv_log_sub_inv_sub_one_at_one.comp hshift).congr fun u ↦ by
      simp [sub_eq_add_neg, neg_inv]
  have hsum := h1.add h2
  norm_num at hsum
  exact hsum.congr fun u ↦ by ring

/-- `(log (1 + u))⁻¹ + (log (1 - u))⁻¹ → (log 2)⁻¹` as `u → 1⁻`. -/
theorem tendsto_inv_log_one_add_add_one_sub_nhdsLT_one :
    Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹)
      (𝓝[<] 1) (𝓝 (Real.log 2)⁻¹) := by
  have h1 : Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹) (𝓝[<] 1) (𝓝 (Real.log 2)⁻¹) := by
    have hlog : ContinuousAt (fun u : ℝ ↦ Real.log (1 + u)) 1 :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ) + 1 ≠ 0)).comp
        (f := fun u : ℝ ↦ 1 + u) (by fun_prop)
    have hc : ContinuousAt (fun u : ℝ ↦ (Real.log (1 + u))⁻¹) 1 :=
      hlog.inv₀ (by norm_num [Real.log_pos one_lt_two |>.ne'])
    simpa only [one_add_one_eq_two] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
  have h2 : Tendsto (fun u : ℝ ↦ (Real.log (1 - u))⁻¹) (𝓝[<] 1) (𝓝 0) := by
    have hs0 : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[<] 1) (𝓝 0) := by
      have hc : ContinuousAt (fun u : ℝ ↦ 1 - u) 1 := by fun_prop
      simpa only [sub_self] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    have hshift : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hs0 ?_
      filter_upwards [self_mem_nhdsWithin] with u (hu : u < 1)
      exact sub_pos.mpr hu
    exact (tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero).comp hshift
  simpa using h1.add h2

/-- Positive-argument case of `abs_inv_log_one_add_add_one_sub_le`. -/
private theorem abs_inv_log_one_add_add_one_sub_le_of_pos {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2) :
    |(Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹| ≤ 16 * Real.log (4 / 3) / 3 := by
  have hlp : 0 < Real.log (1 + u) := Real.log_pos (by linarith)
  have hlm : Real.log (1 - u) < 0 := Real.log_neg (by linarith) (by linarith)
  have h1u2 : 0 < 1 - u ^ 2 := by nlinarith
  have hsum_neg : Real.log (1 + u) + Real.log (1 - u) = Real.log (1 - u ^ 2) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    congr 1; ring
  have hrewrite : (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹ =
      -Real.log (1 - u ^ 2) / (Real.log (1 + u) * (-Real.log (1 - u))) := by
    field_simp [hlp.ne', hlm.ne]
    linarith [hsum_neg]
  have hnonneg : 0 ≤ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹ := by
    rw [hrewrite]
    exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos h1u2.le (by nlinarith)))
      (mul_pos hlp (neg_pos.mpr hlm)).le
  rw [abs_of_nonneg hnonneg, hrewrite]
  have hnum : -Real.log (1 - u ^ 2) ≤ 4 * Real.log (4 / 3) * u ^ 2 := by
    have h4u2 : 4 * u ^ 2 ≤ 1 := by nlinarith
    have hsec := strictConcaveOn_log_Ioi.concaveOn.2
      (by norm_num : (1 : ℝ) ∈ Ioi 0) (by norm_num : (3 / 4 : ℝ) ∈ Ioi 0)
      (by linarith : (0 : ℝ) ≤ 1 - 4 * u ^ 2) (by positivity : (0 : ℝ) ≤ 4 * u ^ 2) (by ring)
    have hcomb : (1 - 4 * u ^ 2) * (1 : ℝ) + (4 * u ^ 2) * (3 / 4 : ℝ) = 1 - u ^ 2 := by ring
    have hlog34 : Real.log (3 / 4 : ℝ) = -Real.log (4 / 3) := by
      rw [← Real.log_inv]; norm_num
    simp only [smul_eq_mul, hcomb, Real.log_one, mul_zero, zero_add, hlog34] at hsec
    linarith
  have hden1 : 3 / 4 * u ≤ Real.log (1 + u) := by
    have hlog32 : (3 / 8 : ℝ) ≤ Real.log (3 / 2) := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have hb := (abs_le.mp (Real.exp_bound (x := (3 / 8 : ℝ)) (by norm_num) (n := 4)
        (by norm_num))).2
      norm_num [Finset.sum_range_succ, Nat.factorial] at hb
      linarith
    have hsec := strictConcaveOn_log_Ioi.concaveOn.2
      (by norm_num : (1 : ℝ) ∈ Ioi 0) (by norm_num : (3 / 2 : ℝ) ∈ Ioi 0)
      (by linarith : (0 : ℝ) ≤ 1 - 2 * u) (by positivity : (0 : ℝ) ≤ 2 * u) (by ring)
    have hcomb : (1 - 2 * u) * (1 : ℝ) + (2 * u) * (3 / 2 : ℝ) = 1 + u := by ring
    simp only [smul_eq_mul, hcomb, Real.log_one, mul_zero, zero_add] at hsec
    nlinarith
  have hden2 : u ≤ -Real.log (1 - u) := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 - u)]
  have hden : 3 / 4 * u ^ 2 ≤ Real.log (1 + u) * (-Real.log (1 - u)) := by
    nlinarith [mul_le_mul hden1 hden2 hu0.le hlp.le]
  calc -Real.log (1 - u ^ 2) / (Real.log (1 + u) * (-Real.log (1 - u)))
      ≤ (4 * Real.log (4 / 3) * u ^ 2) / (3 / 4 * u ^ 2) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 16 * Real.log (4 / 3) / 3 := by field_simp [hu0.ne']; ring

/-- Pointwise bound on the symmetric integrand of `li 2`:
`|(log (1 + u))⁻¹ + (log (1 - u))⁻¹| ≤ (16 / 3) log (4 / 3)` for every `|u| ≤ 1 / 2`. -/
theorem abs_inv_log_one_add_add_one_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |(Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹| ≤ 16 * Real.log (4 / 3) / 3 := by
  rcases lt_trichotomy u 0 with hneg | rfl | hpos
  · have h := abs_inv_log_one_add_add_one_sub_le_of_pos (neg_pos.mpr hneg)
      (by linarith [(abs_le.mp hu).1])
    have heq : (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹ =
        (Real.log (1 + -u))⁻¹ + (Real.log (1 - -u))⁻¹ := by
      rw [add_comm, sub_neg_eq_add, ← sub_eq_add_neg]
    rwa [heq]
  · simp only [add_zero, sub_zero, Real.log_one, inv_zero, abs_zero]
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) (by norm_num)
  · exact abs_inv_log_one_add_add_one_sub_le_of_pos hpos (abs_le.mp hu).2

/-- Continuous extension of `u ↦ (log (1 + u))⁻¹ + (log (1 - u))⁻¹` to `[0, 1]`. -/
private theorem continuousOn_inv_log_one_add_add_one_sub_ext :
    ContinuousOn (fun u : ℝ ↦ if u = 0 then 1 else if u = 1 then (Real.log 2)⁻¹ else
      (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) (Icc 0 1) := by
  intro u hu
  by_cases hu0 : u = 0
  · subst hu0
    rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt]
    simp only [↓reduceIte]
    have hsub : Icc (0 : ℝ) 1 \ {0} ⊆ Ioi 0 := fun s hs ↦
      lt_of_le_of_ne hs.1.1 (Ne.symm hs.2)
    refine (tendsto_inv_log_one_add_add_one_sub_nhdsGT_zero.mono_left
      (nhdsWithin_mono 0 hsub)).congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_ne_nhds (zero_ne_one' ℝ))] with s hs hs1
    have hs0 : s ≠ 0 := hs.2
    simp [hs0, hs1]
  · by_cases hu1 : u = 1
    · subst hu1
      rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt]
      simp only [one_ne_zero, ↓reduceIte]
      have hsub : Icc (0 : ℝ) 1 \ {1} ⊆ Iio 1 := fun s hs ↦ lt_of_le_of_ne hs.1.2 hs.2
      refine (tendsto_inv_log_one_add_add_one_sub_nhdsLT_one.mono_left
        (nhdsWithin_mono 1 hsub)).congr' ?_
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_ne_nhds one_ne_zero)] with s hs hs0
      have hs1 : s ≠ 1 := hs.2
      simp [hs0, hs1]
    · have hu_pos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have hu_lt : u < 1 := lt_of_le_of_ne hu.2 hu1
      have hev : (fun s : ℝ ↦ if s = 0 then 1 else if s = 1 then (Real.log 2)⁻¹ else
          (Real.log (1 + s))⁻¹ + (Real.log (1 - s))⁻¹) =ᶠ[𝓝 u]
          fun s : ℝ ↦ (Real.log (1 + s))⁻¹ + (Real.log (1 - s))⁻¹ := by
        filter_upwards [eventually_ne_nhds hu0, eventually_ne_nhds hu1] with s hs0 hs1
        simp [hs0, hs1]
      have hc1 : ContinuousAt (fun s : ℝ ↦ Real.log (1 + s)) u :=
        (Real.continuousAt_log (by linarith : (1 : ℝ) + u ≠ 0)).comp
          (f := fun s : ℝ ↦ 1 + s) (by fun_prop)
      have hc2 : ContinuousAt (fun s : ℝ ↦ Real.log (1 - s)) u :=
        (Real.continuousAt_log (by linarith : (1 : ℝ) - u ≠ 0)).comp
          (f := fun s : ℝ ↦ 1 - s) (by fun_prop)
      have hc : ContinuousAt (fun s : ℝ ↦ (Real.log (1 + s))⁻¹ + (Real.log (1 - s))⁻¹) u :=
        (hc1.inv₀ (Real.log_pos (by linarith)).ne').add
          (hc2.inv₀ (Real.log_neg (by linarith) (by linarith)).ne)
      exact (hc.congr hev.symm).continuousWithinAt

/-- **Absolutely convergent symmetric integral for `li 2`**:
`li 2 = ∫₀¹ ((log (1 + u))⁻¹ + (log (1 - u))⁻¹) du`. -/
theorem principalLogIntegral_two_eq_integral :
    principalLogIntegral 2 =
      ∫ u in (0 : ℝ)..1, ((Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) := by
  have hint : IntegrableOn (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹)
      (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine continuousOn_inv_log_one_add_add_one_sub_ext.integrableOn_Icc.congr_fun_ae ?_
    have hne : ∀ᵐ u ∂volume, u ≠ (0 : ℝ) ∧ u ≠ (1 : ℝ) :=
      (ae_iff.mpr (by simp)).and (ae_iff.mpr (by simp))
    filter_upwards [ae_restrict_of_ae hne] with u hu
    simp [hu.1, hu.2]
  have hmem : uIcc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [uIcc_of_le zero_le_one]
    exact mem_nhdsWithin.mpr ⟨Iio 1, isOpen_Iio, zero_lt_one, fun t ht ↦ ⟨ht.2.le, ht.1.le⟩⟩
  have hlim_int : Tendsto
      (fun ε : ℝ ↦ ∫ u in ε..1, ((Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹))
      (𝓝[>] 0) (𝓝 (∫ u in (0 : ℝ)..1, ((Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹))) :=
    ((intervalIntegral.continuousOn_primitive_interval_left hint) 0
      left_mem_uIcc).tendsto.mono_left (nhdsWithin_le_iff.mpr hmem)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ u in ε..1, ((Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹)) =
        (∫ t in (0 : ℝ)..(1 - ε), (Real.log t)⁻¹) + ∫ t in (1 + ε)..2, (Real.log t)⁻¹ := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    have h1 : IntervalIntegrable (fun u : ℝ ↦ (Real.log (1 + u))⁻¹) volume ε 1 := by
      have h := (intervalIntegrable_inv_log_pow 1 (by linarith [hε.1] : 1 < 1 + ε)
        one_lt_two).comp_add_left 1
      have heq : (1 + ε - 1 : ℝ) = ε ∧ (2 - 1 : ℝ) = 1 := ⟨by ring, by norm_num⟩
      rw [heq.1, heq.2] at h
      simpa only [pow_one, add_comm] using h
    have h2 : IntervalIntegrable (fun u : ℝ ↦ (Real.log (1 - u))⁻¹) volume ε 1 := by
      have h := (intervalIntegrable_inv_log_of_mem_Ioo (a := 0) (b := 1 - ε)
        ⟨by norm_num, zero_lt_one⟩ ⟨by linarith [hε.2], by linarith [hε.1]⟩).comp_sub_left 1
      have heq : (1 - (1 - ε) : ℝ) = ε ∧ (1 - 0 : ℝ) = 1 := ⟨by ring, by norm_num⟩
      rw [heq.1, heq.2] at h
      exact h.symm
    rw [intervalIntegral.integral_add h1 h2,
      intervalIntegral.integral_comp_add_left (f := fun t : ℝ ↦ (Real.log t)⁻¹) 1,
      intervalIntegral.integral_comp_sub_left (f := fun t : ℝ ↦ (Real.log t)⁻¹) 1]
    norm_num [add_comm]
  exact tendsto_nhds_unique ((tendsto_principalLogIntegral_pv one_lt_two).congr'
    (hev.mono fun _ h ↦ h.symm)) hlim_int

end TauCeti.Real
