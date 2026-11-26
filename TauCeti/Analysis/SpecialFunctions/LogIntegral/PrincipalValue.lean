/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Unoffset
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import TauCeti.Analysis.SpecialFunctions.Exp.Integrals
import TauCeti.Analysis.SpecialFunctions.Exp.Limits
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Log.InvLog
import TauCeti.Analysis.SpecialFunctions.Log.Limits
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.NumberTheory.Harmonic.EulerMascheroni

/-!
# Principal value and integral representations of `li`

This file records the exponential principal value and absolutely convergent integral representations
of the unoffset logarithmic integral `TauCeti.Real.li`:

* `TauCeti.Real.integral_Iic_exp_div`: for `y < 0`, `∫ u in Iic y, exp u / u = li (exp y)`.
* `TauCeti.Real.tendsto_principalValue_exp_div`,
  `TauCeti.Real.tendsto_principalValue_exp_div_log`: for `y > 0`, the Cauchy principal value
  `∫ u in (-1 / ε)..(-ε), exp u / u + ∫ u in ε..y, exp u / u →`
  `γ + log y + ∫ u in 0..y, (exp u - 1) / u`, which equals `li x` at `y = log x` (`x > 1`).
* `TauCeti.Real.li_eq_log_abs_sub_one_add_integral`: for `x > 0`, `x ≠ 1`,
  `li x = log |x - 1| + ∫ t in 0..x, ((log t)⁻¹ - (t - 1)⁻¹)`.
* `TauCeti.Real.li_two_eq_integral`,
  `TauCeti.Real.abs_inv_log_one_add_add_inv_log_one_sub_le`:
  `li 2 = ∫ u in 0..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹)` and the bound
  `|(log (1 + u))⁻¹ + (log (1 - u))⁻¹| ≤ 16 * log (4 / 3) / 3` on `(0, 1 / 2]`.
-/

public section

open Filter MeasureTheory Set
open scoped Interval Topology

namespace TauCeti.Real

/-! ### Exponential form of the principal value -/

/-- For `y < 0`, `∫ u in Iic y, exp u / u = li (exp y)`. -/
theorem integral_Iic_exp_div {y : ℝ} (hy : y < 0) :
    ∫ u in Iic y, Real.exp u / u = li (Real.exp y) := by
  set z : ℝ := -y
  have hz : 0 < z := neg_pos.mpr hy
  -- Step 1: Reflect `u ↦ -t` to write `∫_{Iic y} e^u/u` as `-∫_{Ioi z} e^{-t}/t`.
  have htend_lhs : Tendsto (fun a : ℝ ↦ ∫ u in a..y, Real.exp u / u) atBot
      (𝓝 (∫ u in Iic y, Real.exp u / u)) :=
    intervalIntegral_tendsto_integral_Iic y (Real.integrableOn_Iic_exp_div hy) tendsto_id
  have htend_rhs : Tendsto (fun a : ℝ ↦ -∫ t in z..(-a), Real.exp (-t) / t) atBot
      (𝓝 (-∫ t in Ioi z, Real.exp (-t) / t)) :=
    (intervalIntegral_tendsto_integral_Ioi z (Real.integrableOn_Ioi_exp_neg_div hz)
      tendsto_neg_atBot_atTop).neg
  have heq_Ioi : (∫ u in Iic y, Real.exp u / u) = -∫ t in Ioi z, Real.exp (-t) / t := by
    refine tendsto_nhds_unique htend_lhs (htend_rhs.congr' ?_)
    filter_upwards with a
    simpa [z] using (Real.integral_neg_exp_div z (-a)).symm
  -- Step 2: Combine `γ`, `∫ 1..z, (1 - e^{-t}) / t`, and `∫ 0..z, (1 - e^{-t}) / t`.
  have hsub_Ioi : ∫ t in (1 : ℝ)..z, Real.exp (-t) / t =
      (∫ t in Ioi (1 : ℝ), Real.exp (-t) / t) - ∫ t in Ioi z, Real.exp (-t) / t :=
    (intervalIntegral.integral_Ioi_sub_Ioi'
      (Real.integrableOn_Ioi_exp_neg_div zero_lt_one)
      (Real.integrableOn_Ioi_exp_neg_div hz)).symm
  have h1z_diff := Real.integral_one_sub_exp_neg_div_eq_log_sub zero_lt_one hz
  rw [Real.log_one, sub_zero] at h1z_diff
  have h0z : ∫ t in (0 : ℝ)..z, (1 - Real.exp (-t)) / t =
      (∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) +
        ∫ t in (1 : ℝ)..z, (1 - Real.exp (-t)) / t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (Real.intervalIntegrable_one_sub_exp_neg_div 0 1)
      (Real.intervalIntegrable_one_sub_exp_neg_div 1 z)).symm
  have hgamma := Real.eulerMascheroniConstant_eq_integral_sub_integral
  have h0z_tsum := Real.integral_one_sub_exp_neg_div_eq z
  have hzy : -z = y := by simp [z]
  have hlogabs : Real.log y = Real.log z := by simp [z]
  simp only [hzy] at h0z_tsum
  rw [li_def, Real.log_exp y, hlogabs]
  linarith

/-- **Exponential form of the Cauchy principal value** (`y > 0`):
`lim_{ε → 0⁺} (∫ u in (-1/ε)..(-ε), eᵘ/u du + ∫ u in ε..y, eᵘ/u du) =`
`γ + log y + ∫₀^y (eᵘ - 1)/u du`. -/
theorem tendsto_principalValue_exp_div {y : ℝ} (hy : 0 < y) :
    Tendsto (fun ε : ℝ ↦ (∫ u in (-1 / ε)..(-ε), Real.exp u / u) +
        ∫ u in ε..y, Real.exp u / u)
      (𝓝[>] 0) (𝓝 (Real.eulerMascheroniConstant + Real.log y +
        ∫ u in (0 : ℝ)..y, (Real.exp u - 1) / u)) := by
  -- Step 1: Pass to the limit on the three nonsingular/improper pieces as `ε → 0⁺`.
  have htend₁ : Tendsto (fun ε : ℝ ↦ ∫ t in ε..1, (1 - Real.exp (-t)) / t) (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t)) :=
    TauCeti.intervalIntegral.tendsto_integral_left_nhdsGT zero_lt_one
      Real.continuous_update_one_sub_exp_neg_div_zero.continuousOn
      (Eventually.of_forall fun _ ht ↦ by simp [ht.1.ne'])
  have htend₂ : Tendsto (fun ε : ℝ ↦ ∫ t in (1 : ℝ)..ε⁻¹, Real.exp (-t) / t) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (1 : ℝ), Real.exp (-t) / t)) :=
    (intervalIntegral_tendsto_integral_Ioi 1 (Real.integrableOn_Ioi_exp_neg_div zero_lt_one)
      tendsto_id).comp tendsto_inv_nhdsGT_zero
  have htend₃ : Tendsto (fun ε : ℝ ↦ ∫ u in ε..y, (Real.exp u - 1) / u) (𝓝[>] 0)
      (𝓝 (∫ u in (0 : ℝ)..y, (Real.exp u - 1) / u)) :=
    TauCeti.intervalIntegral.tendsto_integral_left_nhdsGT hy
      Real.continuous_update_exp_sub_one_div_zero.continuousOn
      (Eventually.of_forall fun _ hu ↦ by simp [hu.1.ne'])
  have hlim : Tendsto (fun ε : ℝ ↦
      ((∫ t in ε..1, (1 - Real.exp (-t)) / t) - ∫ t in (1 : ℝ)..ε⁻¹, Real.exp (-t) / t) +
        Real.log y + ∫ u in ε..y, (Real.exp u - 1) / u) (𝓝[>] 0)
      (𝓝 (Real.eulerMascheroniConstant + Real.log y +
        ∫ u in (0 : ℝ)..y, (Real.exp u - 1) / u)) := by
    rw [Real.eulerMascheroniConstant_eq_integral_sub_integral]
    exact ((htend₁.sub htend₂).add tendsto_const_nhds).add htend₃
  -- Step 2: Cancel the logarithmic divergence `log ε` between `(-1/ε, -ε)` and `(ε, y)`.
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one hy)] with ε hε
  have hε0 : 0 < ε := hε.1
  have hinv_pos : 0 < ε⁻¹ := inv_pos.mpr hε0
  have hcomp : ∫ u in (-1 / ε)..(-ε), Real.exp u / u = -∫ t in ε..ε⁻¹, Real.exp (-t) / t := by
    simpa only [show (-1 / ε : ℝ) = -ε⁻¹ by ring] using Real.integral_neg_exp_div ε ε⁻¹
  have hleft_split : ∫ t in ε..ε⁻¹, Real.exp (-t) / t =
      (∫ t in ε..1, Real.exp (-t) / t) + ∫ t in (1 : ℝ)..ε⁻¹, Real.exp (-t) / t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (Real.intervalIntegrable_exp_neg_div hε0 zero_lt_one)
      (Real.intervalIntegrable_exp_neg_div zero_lt_one hinv_pos)).symm
  have hε1_diff := Real.integral_one_sub_exp_neg_div_eq_log_sub hε0 zero_lt_one
  rw [Real.log_one, zero_sub] at hε1_diff
  have hεy_exp := Real.integral_exp_div_eq_log_sub_add hε0 hy
  linarith

/-- For `x > 1`, `lim_{ε → 0⁺} (∫ u in (-1/ε)..(-ε), eᵘ/u du + ∫ u in ε..(log x), eᵘ/u du) =`
`li x`. -/
theorem tendsto_principalValue_exp_div_log {x : ℝ} (hx : 1 < x) :
    Tendsto (fun ε : ℝ ↦ (∫ u in (-1 / ε)..(-ε), Real.exp u / u) +
        ∫ u in ε..(Real.log x), Real.exp u / u)
      (𝓝[>] 0) (𝓝 (li x)) := by
  have h := tendsto_principalValue_exp_div (Real.log_pos hx)
  rw [Real.integral_exp_sub_one_div_eq_tsum (Real.log x), ← liSeries_def,
    ← li_eq_add_liSeries] at h
  exact h

/-! ### Absolutely convergent integral representations -/

/-- As `t → 0⁺`, `(log t)⁻¹ - (t - 1)⁻¹ → 1`. -/
theorem tendsto_inv_log_sub_inv_sub_one_nhdsGT_zero :
    Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) (𝓝[>] 0) (𝓝 1) := by
  have h1 : Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.log_zero] using Real.continuousAt_inv_log_zero.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t : ℝ ↦ (t - 1)⁻¹) (𝓝[>] 0) (𝓝 (-1)) := by
    have hc : ContinuousAt (fun t : ℝ ↦ (t - 1)⁻¹) 0 := by fun_prop (disch := norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa using h1.sub h2

/-- As `t → 1` (`t ≠ 1`), `(log t)⁻¹ - (t - 1)⁻¹ → 1 / 2`. -/
theorem tendsto_inv_log_sub_inv_sub_one_nhdsNE_one :
    Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) (𝓝[≠] 1) (𝓝 (1 / 2 : ℝ)) := by
  have hden : Tendsto (fun h : ℝ ↦ (Real.exp h - 1) / h) (𝓝[≠] 0) (𝓝 1) := by
    simpa using Real.tendsto_exp_mul_sub_one_div 1
  have hq : Tendsto (fun h : ℝ ↦ ((Real.exp h - 1 - h) / h ^ 2) / ((Real.exp h - 1) / h))
      (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) := by
    convert Real.tendsto_exp_sub_one_sub_div_sq.div hden one_ne_zero using 2
    norm_num
  refine (hq.comp Real.tendsto_log_nhdsNE_one_nhdsNE_zero).congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_gt_nhds zero_lt_one)] with t ht1 ht0
  have hlog_ne : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht0 ht1
  have htsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  dsimp only [Function.comp_def]
  rw [Real.exp_log ht0]
  field_simp [hlog_ne, htsub]

private theorem continuousOn_update_two {f : ℝ → ℝ} {s : Set ℝ} {x₀ x₁ v₀ v₁ : ℝ}
    (hne : x₀ ≠ x₁) (hf : ContinuousOn f (s \ {x₀, x₁}))
    (h₀ : x₀ ∈ s → Tendsto f (𝓝[s \ {x₀}] x₀) (𝓝 v₀))
    (h₁ : x₁ ∈ s → Tendsto f (𝓝[s \ {x₁}] x₁) (𝓝 v₁)) :
    ContinuousOn (Function.update (Function.update f x₀ v₀) x₁ v₁) s := by
  rw [continuousOn_update_iff, continuousOn_update_iff]
  refine ⟨⟨?_, fun hx₀ ↦ ?_⟩, fun hx₁ ↦ ?_⟩
  · simpa only [sdiff_sdiff, union_singleton, pair_comm] using hf
  · exact (h₀ hx₀.1).mono_left (nhdsWithin_mono _ fun _ hz ↦ ⟨hz.1.1, hz.2⟩)
  · refine (h₁ hx₁).congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds hne.symm)]
      with u hu
    exact (Function.update_of_ne hu v₀ f).symm

/-- Continuous extension of `(log t)⁻¹ - (t - 1)⁻¹` on `[0, ∞)` with value `1` at `0`
and `1 / 2` at `1`. -/
private noncomputable def invLogSubInvSubOneExt : ℝ → ℝ :=
  Function.update (Function.update (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) 0 1) 1 (1 / 2)

private theorem continuousOn_inv_log_sub_inv_sub_one_ext :
    ContinuousOn invLogSubInvSubOneExt (Ici 0) := by
  refine continuousOn_update_two zero_ne_one (fun t ht ↦ ?_) (fun _ ↦ ?_) (fun _ ↦ ?_)
  · have ht0 : t ≠ 0 := fun h ↦ ht.2 (by simp [h])
    have ht1 : t ≠ 1 := fun h ↦ ht.2 (by simp [h])
    have htpos : 0 < t := lt_of_le_of_ne ht.1 ht0.symm
    have hlog : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one htpos ht1
    have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
    exact (by fun_prop (disch := first | exact ht0 | exact hlog | exact hsub) :
      ContinuousAt (fun u : ℝ ↦ (Real.log u)⁻¹ - (u - 1)⁻¹) t).continuousWithinAt
  · exact tendsto_inv_log_sub_inv_sub_one_nhdsGT_zero.mono_left
      (nhdsWithin_mono _ fun u hu ↦ lt_of_le_of_ne hu.1 (Ne.symm hu.2))
  · exact tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.mono_left
      (nhdsWithin_mono _ fun _ hu ↦ hu.2)

/-- The integrand `(log t)⁻¹ - (t - 1)⁻¹` is interval integrable on `[0, x]` for every `x ≥ 0`. -/
theorem intervalIntegrable_inv_log_sub_inv_sub_one {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹ - (t - 1)⁻¹) volume 0 x := by
  have hg : IntervalIntegrable invLogSubInvSubOneExt volume 0 x :=
    (continuousOn_inv_log_sub_inv_sub_one_ext.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hx
  refine hg.congr_ae ?_
  have hne0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := ae_iff.mpr (by simp)
  have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := ae_iff.mpr (by simp)
  filter_upwards [ae_restrict_of_ae (hne0.and hne1)] with t ⟨ht0, ht1⟩
  simp [invLogSubInvSubOneExt, ht0, ht1]

private theorem integral_invLogSubInvSubOneExt (a b : ℝ) :
    ∫ t in a..b, invLogSubInvSubOneExt t =
      ∫ t in a..b, ((Real.log t)⁻¹ - (t - 1)⁻¹) := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [(ae_iff.mpr (by simp : volume {t : ℝ | ¬t ≠ 0} = 0)).and
    (ae_iff.mpr (by simp : volume {t : ℝ | ¬t ≠ 1} = 0))] with t ⟨ht0, ht1⟩ _
  simp [invLogSubInvSubOneExt, ht0, ht1]

/-- For `x > 1`, `li x = log (x - 1) + ∫ t in 0..x, ((log t)⁻¹ - (t - 1)⁻¹)`. -/
private theorem li_eq_log_sub_one_add_integral_of_one_lt {x : ℝ} (hx : 1 < x) :
    li x =
      Real.log (x - 1) + ∫ t in (0 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹) := by
  -- Step 1: Continuity of the filled-in integrand passes the symmetric limit to
  -- `∫ 0..x, invLogSubInvSubOneExt`.
  have hmid := TauCeti.intervalIntegral.tendsto_principalValue_of_continuousOn (μ := volume)
    zero_lt_one hx (continuousOn_inv_log_sub_inv_sub_one_ext.mono Icc_subset_Ici_self)
  -- Step 2: Subtract `∫ (t - 1)⁻¹` from the principal value on `(0, 1 - ε)` and `(1 + ε, x)`.
  have hrhs : Tendsto (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..(1 - ε), invLogSubInvSubOneExt t) +
      ∫ t in (1 + ε)..x, invLogSubInvSubOneExt t) (𝓝[>] 0)
      (𝓝 (li x - Real.log (x - 1))) := by
    refine ((tendsto_principalValue_inv_log hx).sub
      (tendsto_const_nhds (x := Real.log (x - 1)))).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one (sub_pos.mpr hx))] with ε hε
    have hε1 : ε < 1 := hε.2.trans_le (min_le_left _ _)
    have hεx : 1 + ε < x := by linarith [hε.2.trans_le (min_le_right _ _)]
    have hnot1 : (1 : ℝ) ∉ [[0, 1 - ε]] := fun h ↦ by
      rw [uIcc_of_le (by linarith)] at h; linarith [h.2, hε.1]
    have hnot2 : (1 : ℝ) ∉ [[1 + ε, x]] := fun h ↦ by
      rw [uIcc_of_le hεx.le] at h; linarith [h.1, hε.1]
    have hsub1_val : ∫ t in (0 : ℝ)..(1 - ε), (t - 1)⁻¹ = Real.log ε := by
      rw [Real.integral_sub_inv hnot1, show (1 - ε - 1) / (0 - 1 : ℝ) = ε by ring]
    have hsub2_val : ∫ t in (1 + ε)..x, (t - 1)⁻¹ = Real.log (x - 1) - Real.log ε := by
      rw [Real.integral_sub_inv hnot2, show (1 + ε - 1 : ℝ) = ε by ring,
        Real.log_div (sub_pos.mpr hx).ne' hε.1.ne']
    have hlog1 := Real.intervalIntegrable_inv_log_of_Ico (sub_nonneg.mpr hε1.le)
      (by linarith [hε.1])
    have hlog2 : IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹) volume (1 + ε) x := by
      simpa only [pow_one] using intervalIntegrable_inv_log_pow 1 (by linarith [hε.1]) hx
    rw [integral_invLogSubInvSubOneExt, integral_invLogSubInvSubOneExt,
      intervalIntegral.integral_sub hlog1 (intervalIntegrable_sub_inv_iff.mpr (Or.inr hnot1)),
      intervalIntegral.integral_sub hlog2 (intervalIntegrable_sub_inv_iff.mpr (Or.inr hnot2)),
      hsub1_val, hsub2_val]; ring
  -- Step 3: Equate the two limits and identify `invLogSubInvSubOneExt` with `(log t)⁻¹ - (t - 1)⁻¹`
  -- a.e.
  have heq_g := tendsto_nhds_unique hmid hrhs
  have heq_main := integral_invLogSubInvSubOneExt 0 x
  linarith

/-- **Absolutely convergent integral for `li x`** (`0 < x`, `x ≠ 1`):
`li x = log |x - 1| + ∫ t in 0..x, ((log t)⁻¹ - (t - 1)⁻¹)`. -/
theorem li_eq_log_abs_sub_one_add_integral {x : ℝ} (hx₀ : 0 < x) (hx₁ : x ≠ 1) :
    li x =
      Real.log |x - 1| + ∫ t in (0 : ℝ)..x, ((Real.log t)⁻¹ - (t - 1)⁻¹) := by
  rcases hx₁.lt_or_gt with hx_lt | hx_gt
  · have hlog_abs : Real.log |x - 1| = Real.log (1 - x) := by
      rw [abs_of_neg (sub_neg.mpr hx_lt), neg_sub]
    have hnot : (1 : ℝ) ∉ [[0, x]] := fun h ↦ by
      rw [uIcc_of_le hx₀.le] at h; linarith [h.2]
    have hsub_val : ∫ t in (0 : ℝ)..x, (t - 1)⁻¹ = Real.log (1 - x) := by
      rw [Real.integral_sub_inv hnot, show (x - 1) / (0 - 1 : ℝ) = 1 - x by ring]
    rw [hlog_abs, ← hsub_val, intervalIntegral.integral_sub
      (Real.intervalIntegrable_inv_log_of_Ico hx₀.le hx_lt)
      (intervalIntegrable_sub_inv_iff.mpr (Or.inr hnot)),
      ← li_eq_integral hx₀ hx_lt]
    ring
  · rw [abs_of_pos (sub_pos.mpr hx_gt)]
    exact li_eq_log_sub_one_add_integral_of_one_lt hx_gt

/-- As `u → 0⁺`, `(log (1 + u))⁻¹ + (log (1 - u))⁻¹ → 1`. -/
theorem tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsGT_zero :
    Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) (𝓝[>] 0) (𝓝 1) := by
  have h1 : Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ - u⁻¹) (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
    have hmap : Tendsto (fun u : ℝ ↦ (1 : ℝ) + u) (𝓝[>] 0) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : ContinuousAt (fun u : ℝ ↦ (1 : ℝ) + u) 0 := by fun_prop
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact (by linarith [mem_Ioi.mp hu] : (1 : ℝ) + u ≠ 1)
    refine (tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.comp hmap).congr fun u ↦ by simp
  have h2 : Tendsto (fun u : ℝ ↦ (Real.log (1 - u))⁻¹ + u⁻¹) (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
    have hmap : Tendsto (fun u : ℝ ↦ (1 : ℝ) - u) (𝓝[>] 0) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : ContinuousAt (fun u : ℝ ↦ (1 : ℝ) - u) 0 := by fun_prop
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact (by linarith [mem_Ioi.mp hu] : (1 : ℝ) - u ≠ 1)
    refine (tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.comp hmap).congr fun u ↦ by
      simp only [Function.comp_def]; ring
  have hadd := h1.add h2
  norm_num at hadd
  refine hadd.congr fun u ↦ by ring

/-- As `u → 1⁻`, `(log (1 + u))⁻¹ + (log (1 - u))⁻¹ → (log 2)⁻¹`. -/
theorem tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsLT_one :
    Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹)
      (𝓝[<] 1) (𝓝 (Real.log 2)⁻¹) := by
  have h1 : Tendsto (fun u : ℝ ↦ (Real.log (1 + u))⁻¹) (𝓝[<] 1) (𝓝 (Real.log 2)⁻¹) := by
    have hlog2 : Real.log (1 + (1 : ℝ)) ≠ 0 :=
      (Real.log_pos (by norm_num : (1 : ℝ) < 1 + 1)).ne'
    have hc : ContinuousAt (fun u : ℝ ↦ (Real.log (1 + u))⁻¹) 1 := by
      fun_prop (disch := first | norm_num | exact hlog2)
    simpa [show (1 : ℝ) + 1 = 2 by norm_num] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun u : ℝ ↦ (Real.log (1 - u))⁻¹) (𝓝[<] 1) (𝓝 0) := by
    have hmap : Tendsto (fun u : ℝ ↦ (1 : ℝ) - u) (𝓝[<] 1) (𝓝 0) := by
      have hc : ContinuousAt (fun u : ℝ ↦ (1 : ℝ) - u) 1 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hcomp : Tendsto (fun u : ℝ ↦ (Real.log (1 - u))⁻¹) (𝓝[<] 1) (𝓝 (Real.log 0)⁻¹) :=
      Real.continuousAt_inv_log_zero.tendsto.comp hmap
    simpa [Real.log_zero] using hcomp
  simpa using h1.add h2

/-- Continuous extension of `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` on `[0, 1]`. -/
private noncomputable def invLogOneAddAddInvLogOneSubExt : ℝ → ℝ :=
  Function.update (Function.update (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) 0 1)
    1 (Real.log 2)⁻¹

private theorem continuousOn_inv_log_one_add_add_inv_log_one_sub_ext :
    ContinuousOn invLogOneAddAddInvLogOneSubExt (Icc 0 1) := by
  refine continuousOn_update_two zero_ne_one (fun u hu ↦ ?_) (fun _ ↦ ?_) (fun _ ↦ ?_)
  · have hu0 : u ≠ 0 := fun h ↦ hu.2 (by simp [h])
    have hu1 : u ≠ 1 := fun h ↦ hu.2 (by simp [h])
    have hu_pos : 0 < u := lt_of_le_of_ne hu.1.1 hu0.symm
    have hu_lt : u < 1 := lt_of_le_of_ne hu.1.2 hu1
    have h1p : Real.log (1 + u) ≠ 0 := (Real.log_pos (by linarith)).ne'
    have h1m : Real.log (1 - u) ≠ 0 := (Real.log_neg (by linarith) (by linarith)).ne
    exact (by fun_prop (disch := first | linarith | exact h1p | exact h1m) :
      ContinuousAt (fun v : ℝ ↦ (Real.log (1 + v))⁻¹ + (Real.log (1 - v))⁻¹) u).continuousWithinAt
  · exact tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsGT_zero.mono_left
      (nhdsWithin_mono _ fun v hv ↦ lt_of_le_of_ne hv.1.1 (Ne.symm hv.2))
  · exact tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsLT_one.mono_left
      (nhdsWithin_mono _ fun v hv ↦ lt_of_le_of_ne hv.1.2 hv.2)

/-- `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_inv_log_one_add_add_inv_log_one_sub :
    IntervalIntegrable (fun u : ℝ ↦ (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) volume 0 1 := by
  refine (continuousOn_inv_log_one_add_add_inv_log_one_sub_ext.intervalIntegrable_of_Icc
    zero_le_one).congr_ae ?_
  have hne0 : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := ae_iff.mpr (by simp)
  have hne1 : ∀ᵐ u : ℝ ∂volume, u ≠ 1 := ae_iff.mpr (by simp)
  filter_upwards [ae_restrict_of_ae (hne0.and hne1)] with u ⟨hu0, hu1⟩
  simp [invLogOneAddAddInvLogOneSubExt, hu0, hu1]

/-- Uniform bound on `(0, 1 / 2]` for the symmetric integrand:
`|(log (1 + u))⁻¹ + (log (1 - u))⁻¹| ≤ 16 * log (4 / 3) / 3`. -/
theorem abs_inv_log_one_add_add_inv_log_one_sub_le {u : ℝ} (hu₀ : 0 < u) (hu₂ : u ≤ 1 / 2) :
    |(Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹| ≤ 16 * Real.log (4 / 3) / 3 := by
  have h1pu : 1 < 1 + u := by linarith
  have h1mu_pos : 0 < 1 - u := by linarith
  have hlogp : 0 < Real.log (1 + u) := Real.log_pos h1pu
  have hlogm : 0 < -Real.log (1 - u) := neg_pos.mpr (Real.log_neg h1mu_pos (by linarith))
  have hnum_eq : -Real.log (1 - u) - Real.log (1 + u) = -Real.log (1 - u ^ 2) := by
    have hmul : (1 - u) * (1 + u) = 1 - u ^ 2 := by ring
    rw [← neg_add', ← Real.log_mul h1mu_pos.ne' (zero_lt_one.trans h1pu).ne', hmul]
  have hnum_nn : 0 ≤ -Real.log (1 - u ^ 2) :=
    neg_nonneg.mpr (Real.log_nonpos (by nlinarith) (by nlinarith))
  -- Numerator bound via convexity of `-log (1 - v)` on `[0, 1 / 4]`.
  have hnum_ub : -Real.log (1 - u ^ 2) ≤ 4 * Real.log (4 / 3) * u ^ 2 := by
    have h := Real.neg_log_one_sub_le_div_mul (c := 1 / 4) (v := u ^ 2)
      (by norm_num) (sq_nonneg u) (by nlinarith)
    rwa [show (1 : ℝ) - 1 / 4 = (4 / 3)⁻¹ by norm_num, Real.log_inv, neg_neg,
      show Real.log (4 / 3) / (1 / 4 : ℝ) = 4 * Real.log (4 / 3) by ring] at h
  -- Denominator lower bound: `log (1 + u) ≥ (3 / 4) u` and `-log (1 - u) ≥ u`.
  have hlogp_lb : (3 / 4 : ℝ) * u ≤ Real.log (1 + u) := by
    nlinarith [Real.sub_sq_div_two_le_log_one_add hu₀.le]
  have hlogm_lb : u ≤ -Real.log (1 - u) := by
    linarith [Real.log_le_sub_one_of_pos h1mu_pos]
  have hden_lb : (3 / 4 : ℝ) * u ^ 2 ≤ Real.log (1 + u) * (-Real.log (1 - u)) := by
    calc (3 / 4 : ℝ) * u ^ 2 = ((3 / 4 : ℝ) * u) * u := by ring
      _ ≤ Real.log (1 + u) * (-Real.log (1 - u)) :=
          mul_le_mul hlogp_lb hlogm_lb hu₀.le hlogp.le
  have hden_pos : 0 < Real.log (1 + u) * (-Real.log (1 - u)) := mul_pos hlogp hlogm
  have hid : (Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹ =
      (-Real.log (1 - u ^ 2)) / (Real.log (1 + u) * (-Real.log (1 - u))) := by
    rw [← hnum_eq]
    field_simp [hlogp.ne', neg_ne_zero.mp hlogm.ne']
    ring
  rw [hid, abs_of_nonneg (div_nonneg hnum_nn hden_pos.le)]
  calc (-Real.log (1 - u ^ 2)) / (Real.log (1 + u) * (-Real.log (1 - u)))
      ≤ (4 * Real.log (4 / 3) * u ^ 2) / ((3 / 4 : ℝ) * u ^ 2) := by gcongr
    _ = 16 * Real.log (4 / 3) / 3 := by
        field_simp [pow_ne_zero 2 hu₀.ne']
        norm_num

/-- **Symmetric integral for `li 2`**:
`li 2 = ∫ u in 0..1, ((log (1 + u))⁻¹ + (log (1 - u))⁻¹)`. -/
theorem li_two_eq_integral :
    li 2 =
      ∫ u in (0 : ℝ)..1, ((Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹) := by
  -- Step 1: Pass `∫ u in ε..1` to `∫ u in 0..1` using the continuous extension on `[0, 1]`.
  have hne1 : ∀ᵐ u : ℝ ∂volume, u ≠ 1 := ae_iff.mpr (by simp)
  have htend_rhs : Tendsto
      (fun ε : ℝ ↦ ∫ u in ε..1, ((Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹))
      (𝓝[>] 0) (𝓝 (∫ u in (0 : ℝ)..1, ((Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹))) :=
    TauCeti.intervalIntegral.tendsto_integral_left_nhdsGT zero_lt_one
      continuousOn_inv_log_one_add_add_inv_log_one_sub_ext
      (by filter_upwards [hne1] with u hu1 hu; simp [invLogOneAddAddInvLogOneSubExt, hu.1.ne', hu1])
  -- Step 2: Fold the principal value at `x = 2` via `t = 1 - u` and `t = 1 + u`.
  have heq_pv : Tendsto
      (fun ε : ℝ ↦ ∫ u in ε..1, ((Real.log (1 + u))⁻¹ + (Real.log (1 - u))⁻¹))
      (𝓝[>] 0) (𝓝 (li 2)) := by
    refine (tendsto_principalValue_inv_log one_lt_two).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    have hleft : ∫ t in (0 : ℝ)..(1 - ε), (Real.log t)⁻¹ = ∫ u in ε..1, (Real.log (1 - u))⁻¹ := by
      simpa using (intervalIntegral.integral_comp_sub_left
        (f := fun t : ℝ ↦ (Real.log t)⁻¹) (a := ε) (b := 1) 1).symm
    have hright : ∫ t in (1 + ε)..2, (Real.log t)⁻¹ = ∫ u in ε..1, (Real.log (1 + u))⁻¹ := by
      have hcomp := intervalIntegral.integral_comp_add_left
        (f := fun t : ℝ ↦ (Real.log t)⁻¹) (a := ε) (b := 1) 1
      simp_rw [add_comm _ (1 : ℝ)] at hcomp
      simpa [show (1 : ℝ) + 1 = 2 by norm_num] using hcomp.symm
    have hi1 : IntervalIntegrable (fun u : ℝ ↦ (Real.log (1 + u))⁻¹) volume ε 1 := by
      have h := (intervalIntegrable_inv_log_pow 1 (by linarith [hε.1] : 1 < 1 + ε)
        one_lt_two).comp_add_left 1
      simp only [pow_one, add_sub_cancel_left] at h
      simpa only [add_comm _ (1 : ℝ), show (2 : ℝ) - 1 = 1 by norm_num] using h
    have hi2 : IntervalIntegrable (fun u : ℝ ↦ (Real.log (1 - u))⁻¹) volume ε 1 := by
      have h := (Real.intervalIntegrable_inv_log_of_Ico (sub_nonneg.mpr hε.2.le)
        (by linarith [hε.1] : 1 - ε < 1)).comp_sub_left 1
      simp only [sub_zero, sub_sub_cancel] at h
      exact h.symm
    rw [hleft, hright, intervalIntegral.integral_add hi1 hi2]
    ring
  exact (tendsto_nhds_unique htend_rhs heq_pv).symm

end TauCeti.Real
