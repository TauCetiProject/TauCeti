/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.GeneralizedExtremeValue.Cdf
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of generalized extreme-value laws

For positive scale and an interior level `u`, the generalized extreme-value quantile is

`m + s * ((-log u) ^ (-ξ) - 1) / ξ`

at nonzero shape, with the Gumbel expression `m - s * log (-log u)` at shape zero. The one-sided
limits distinguish the finite endpoint `m - s / ξ` from the unbounded end of the support:
positive shape has a finite lower endpoint, while negative shape has a finite upper endpoint.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 3.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {s ξ u : ℝ}

/-- The quantile of a positive-scale generalized extreme-value law at nonzero shape. -/
theorem quantile_generalizedExtremeValueMeasure_of_shape_ne_zero (hs : 0 < s) (m : ℝ)
    (hξ : ξ ≠ 0) (hu : u ∈ Ioo 0 1) :
    (generalizedExtremeValueMeasure m s ξ).quantile u =
      m + s * ((-log u) ^ (-ξ) - 1) / ξ := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  have hlog : 0 < -log u := neg_pos.mpr (log_neg hu.1 hu.2)
  have hmap : generalizedExtremeValueMap m s ξ (-log u) =
      m + s * ((-log u) ^ (-ξ) - 1) / ξ := by
    rw [generalizedExtremeValueMap_eq_rpow hlog, ite_eq_right hξ]
  rw [← hmap]
  refine eq_of_forall_ge_iff fun x ↦ ?_
  rw [Measure.quantile_le_iff _ hu.1 hu.2,
    cdf_generalizedExtremeValueMeasure_eq hs hξ]
  by_cases hx : 0 < 1 + ξ * ((x - m) / s)
  · rw [ite_eq_left hx, ← log_le_iff_le_exp hu.1]
    have hthreshold :
        log u ≤ -((1 + ξ * ((x - m) / s)) ^ (-1 / ξ)) ↔
          (1 + ξ * ((x - m) / s)) ^ (-1 / ξ) ≤ -log u := by
      constructor <;> intro h <;> linarith
    rw [hthreshold]
    exact (generalizedExtremeValueMap_le_iff hs hξ hlog hx).symm
  · rw [ite_eq_right hx]
    rcases lt_or_gt_of_ne hξ with hξ | hξ
    · rw [ite_eq_right (not_lt.mpr hξ.le)]
      constructor
      · intro _
        exact generalizedExtremeValueMap_le_of_shape_neg_of_nonpos hs hξ hlog hx
      · exact fun _ ↦ hu.2.le
    · rw [ite_eq_left hξ]
      constructor
      · exact fun h ↦ (not_le.mpr hu.1 h).elim
      · intro hle
        exact (not_generalizedExtremeValueMap_le_of_shape_pos_of_nonpos hs hξ hlog hx hle).elim

/-- The generalized extreme-value quantile, including its Gumbel branch at shape zero. -/
theorem quantile_generalizedExtremeValueMeasure (m ξ : ℝ) (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    (generalizedExtremeValueMeasure m s ξ).quantile u =
      if ξ = 0 then m - s * log (-log u)
      else m + s * ((-log u) ^ (-ξ) - 1) / ξ := by
  by_cases hξ : ξ = 0
  · subst ξ
    rw [ite_eq_left rfl, generalizedExtremeValueMeasure_zero,
      quantile_gumbelMeasure hs m hu]
  · rw [ite_eq_right hξ]
    exact quantile_generalizedExtremeValueMeasure_of_shape_ne_zero hs m hξ hu

private theorem tendsto_quantile_generalizedExtremeValueMeasure_finite_endpoint
    (hs : 0 < s) (m : ℝ) (hξ : ξ ≠ 0) {l : Filter ℝ}
    (hu : ∀ᶠ u in l, u ∈ Ioo (0 : ℝ) 1)
    (hrpow : Tendsto (fun u : ℝ ↦ (-log u) ^ (-ξ)) l (𝓝 0)) :
    Tendsto (fun u ↦ ((generalizedExtremeValueMeasure m s ξ).quantile u : EReal)) l
      (𝓝 (m - s / ξ)) := by
  have hlim : Tendsto (fun u : ℝ ↦ m + s * ((-log u) ^ (-ξ) - 1) / ξ) l
      (𝓝 (m - s / ξ)) := by
    have hlim' : Tendsto (fun u : ℝ ↦ m + s * ((-log u) ^ (-ξ) - 1) / ξ) l
        (𝓝 (m + s * (0 - 1) / ξ)) :=
      tendsto_const_nhds.add
        ((tendsto_const_nhds.mul (hrpow.sub tendsto_const_nhds)).div_const ξ)
    convert hlim' using 1
    ring_nf
  apply (EReal.tendsto_coe.mpr hlim).congr'
  filter_upwards [hu] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal))
    (quantile_generalizedExtremeValueMeasure_of_shape_ne_zero hs m hξ hu).symm

/-- For positive shape, generalized extreme-value quantiles tend to the finite lower endpoint
`m - s / ξ` as the level tends to zero from above. -/
theorem tendsto_quantile_generalizedExtremeValueMeasure_nhdsGT_zero_of_shape_pos
    (hs : 0 < s) (m : ℝ) (hξ : 0 < ξ) :
    Tendsto (fun u ↦ ((generalizedExtremeValueMeasure m s ξ).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (m - s / ξ)) := by
  have hlog : Tendsto (fun u : ℝ ↦ -log u) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero
  have hrpow : Tendsto (fun u : ℝ ↦ (-log u) ^ (-ξ)) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_rpow_neg_atTop hξ).comp hlog
  exact tendsto_quantile_generalizedExtremeValueMeasure_finite_endpoint hs m hξ.ne'
    (Ioo_mem_nhdsGT zero_lt_one) hrpow

/-- For negative shape, generalized extreme-value quantiles tend to minus infinity as the level
tends to zero from above. -/
theorem tendsto_quantile_generalizedExtremeValueMeasure_nhdsGT_zero_of_shape_neg
    (hs : 0 < s) (m : ℝ) (hξ : ξ < 0) :
    Tendsto (fun u ↦ ((generalizedExtremeValueMeasure m s ξ).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ⊥) := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  apply EReal.tendsto_coe_nhds_bot_iff.mpr
  refine tendsto_atBot.mpr fun b ↦ ?_
  have hb : 0 < cdf (generalizedExtremeValueMeasure m s ξ) b := by
    rw [cdf_generalizedExtremeValueMeasure_eq hs hξ.ne]
    by_cases hsupport : 0 < 1 + ξ * ((b - m) / s)
    · rw [ite_eq_left hsupport]
      positivity
    · rw [ite_eq_right hsupport, ite_eq_right (not_lt.mpr hξ.le)]
      norm_num
  filter_upwards [Ioo_mem_nhdsGT hb] with u hu
  exact (Measure.quantile_le_iff _ hu.1
    (hu.2.trans_le (cdf_le_one (generalizedExtremeValueMeasure m s ξ) b))).2 hu.2.le

/-- For positive shape, generalized extreme-value quantiles tend to plus infinity as the level
tends to one from below. -/
theorem tendsto_quantile_generalizedExtremeValueMeasure_nhdsLT_one_of_shape_pos
    (hs : 0 < s) (m : ℝ) (hξ : 0 < ξ) :
    Tendsto (fun u ↦ ((generalizedExtremeValueMeasure m s ξ).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  apply EReal.tendsto_coe_nhds_top_iff.mpr
  refine tendsto_atTop.mpr fun b ↦ ?_
  have hb : cdf (generalizedExtremeValueMeasure m s ξ) b < 1 := by
    rw [cdf_generalizedExtremeValueMeasure_eq hs hξ.ne']
    by_cases hsupport : 0 < 1 + ξ * ((b - m) / s)
    · rw [ite_eq_left hsupport, exp_lt_one_iff]
      exact neg_neg_of_pos (rpow_pos_of_pos hsupport _)
    · rw [ite_eq_right hsupport, ite_eq_left hξ]
      norm_num
  filter_upwards [Ioo_mem_nhdsLT hb] with u hu
  exact ((Measure.lt_quantile_iff _
    ((cdf_nonneg (generalizedExtremeValueMeasure m s ξ) b).trans_lt hu.1) hu.2).2 hu.1).le

/-- For negative shape, generalized extreme-value quantiles tend to the finite upper endpoint
`m - s / ξ` as the level tends to one from below. -/
theorem tendsto_quantile_generalizedExtremeValueMeasure_nhdsLT_one_of_shape_neg
    (hs : 0 < s) (m : ℝ) (hξ : ξ < 0) :
    Tendsto (fun u ↦ ((generalizedExtremeValueMeasure m s ξ).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (m - s / ξ)) := by
  have hlog : Tendsto (fun u : ℝ ↦ -log u) (𝓝[<] 1) (𝓝 0) := by
    have hlog' : Tendsto (fun u : ℝ ↦ -log u) (𝓝 1) (𝓝 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto.neg
    exact hlog'.mono_left nhdsWithin_le_nhds
  have hrpow : Tendsto (fun u : ℝ ↦ (-log u) ^ (-ξ)) (𝓝[<] 1) (𝓝 0) :=
    hlog.rpow_const_nhds_zero (neg_pos.mpr hξ)
  exact tendsto_quantile_generalizedExtremeValueMeasure_finite_endpoint hs m hξ.ne
    (Ioo_mem_nhdsLT zero_lt_one) hrpow

/-- At shape zero, generalized extreme-value quantiles tend to minus infinity at the lower
endpoint, as do Gumbel quantiles. -/
theorem tendsto_quantile_generalizedExtremeValueMeasure_zero_nhdsGT_zero (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((generalizedExtremeValueMeasure m s 0).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ⊥) := by
  simpa only [generalizedExtremeValueMeasure_zero] using
    tendsto_quantile_gumbelMeasure_nhdsGT_zero hs m

/-- At shape zero, generalized extreme-value quantiles tend to plus infinity at the upper
endpoint, as do Gumbel quantiles. -/
theorem tendsto_quantile_generalizedExtremeValueMeasure_zero_nhdsLT_one (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((generalizedExtremeValueMeasure m s 0).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  simpa only [generalizedExtremeValueMeasure_zero] using
    tendsto_quantile_gumbelMeasure_nhdsLT_one hs m

/-- Generalized extreme-value quantiles vary continuously with the probability level on the
open unit interval. -/
theorem continuousOn_quantile_generalizedExtremeValueMeasure (hs : 0 < s) (m ξ : ℝ) :
    ContinuousOn (generalizedExtremeValueMeasure m s ξ).quantile (Ioo 0 1) := by
  by_cases hξ : ξ = 0
  · have hcont : ContinuousOn (fun v : ℝ ↦ m - s * log (-log v)) (Ioo 0 1) := by
      apply continuousOn_of_forall_continuousAt
      intro v hv
      have hv0 : v ≠ 0 := hv.1.ne'
      have hlog : -log v ≠ 0 := (neg_pos.mpr (log_neg hv.1 hv.2)).ne'
      fun_prop
    refine hcont.congr fun v hv ↦ ?_
    simpa [hξ] using quantile_gumbelMeasure hs m hv
  · have hcont : ContinuousOn
        (fun v : ℝ ↦ m + s * ((-log v) ^ (-ξ) - 1) / ξ) (Ioo 0 1) := by
      apply continuousOn_of_forall_continuousAt
      intro v hv
      have hv0 : v ≠ 0 := hv.1.ne'
      have hlog : -log v ≠ 0 := (neg_pos.mpr (log_neg hv.1 hv.2)).ne'
      have hbase : ContinuousAt (fun w : ℝ ↦ -log w) v := by fun_prop
      exact continuousAt_const.add
        ((continuousAt_const.mul
          ((hbase.rpow_const (Or.inl hlog)).sub continuousAt_const)).div_const ξ)
    refine hcont.congr fun v hv ↦ ?_
    exact quantile_generalizedExtremeValueMeasure_of_shape_ne_zero hs m hξ hv

end TauCeti.Probability
