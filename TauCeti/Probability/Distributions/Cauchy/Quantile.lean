/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Cauchy.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of Cauchy laws

At every level `0 < u < 1`, the quantile of the Cauchy law with location `m` and
nonnegative scale `γ` is `m + γ * tan (π * (u - 1 / 2))`. This includes scale zero,
where the law is the Dirac mass at `m`.

The one-sided endpoint limits are stated in `EReal`: a positive-scale law has
limits `⊥` and `⊤`, while both limits of the zero-scale law are `m`.
These are limits through interior levels, independently of the totalized values
of the real quantile at `0` and `1`.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped NNReal

namespace TauCeti.Probability

/-- The quantile of a Cauchy law, including its zero-scale Dirac boundary. -/
theorem quantile_cauchyMeasure (m : ℝ) (γ : ℝ≥0) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    (cauchyMeasure m γ).quantile u = m + γ * tan (π * (u - 1 / 2)) := by
  by_cases hγ : γ = 0
  · subst hγ
    simp [cauchyMeasure_zero_scale, Measure.quantile_dirac m hu.1 hu.2.le]
  have hγpos : 0 < (γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  have hangle : π * (u - 1 / 2) ∈ Ioo (-(π / 2)) (π / 2) := by
    constructor <;> nlinarith [pi_pos, mul_pos pi_pos hu.1, mul_pos pi_pos (sub_pos.mpr hu.2)]
  refine eq_of_forall_ge_iff fun x ↦ ?_
  rw [Measure.quantile_le_iff _ hu.1 hu.2, cdf_cauchyMeasure_of_scale_ne_zero m hγ]
  calc
    u ≤ 1 / 2 + arctan ((x - m) / γ) / π ↔
        π * (u - 1 / 2) ≤ arctan ((x - m) / γ) := by
      rw [← sub_le_iff_le_add', le_div_iff₀ pi_pos, mul_comm]
    _ ↔ tan (π * (u - 1 / 2)) ≤ (x - m) / γ := by
      simpa only [arctan_tan hangle.1 hangle.2] using
        (arctan_le_arctan_iff (x := tan (π * (u - 1 / 2))) (y := (x - m) / γ))
    _ ↔ m + γ * tan (π * (u - 1 / 2)) ≤ x := by
      rw [le_div_iff₀ hγpos, mul_comm, le_sub_iff_add_le']

/-- The lower endpoint limit of a Cauchy quantile is minus infinity at positive scale
and the location at zero scale. -/
theorem tendsto_quantile_cauchyMeasure_nhdsGT_zero (m : ℝ) (γ : ℝ≥0) :
    Tendsto (fun u ↦ ((cauchyMeasure m γ).quantile u : EReal)) (𝓝[>] 0)
      (𝓝 (if γ = 0 then (m : EReal) else ⊥)) := by
  by_cases hγ : γ = 0
  · subst hγ
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    simp [Measure.quantile_dirac m hu.1 hu.2.le]
  · rw [ite_eq_right hγ]
    apply EReal.tendsto_coe_nhds_bot_iff.2
    refine tendsto_atBot.2 fun b ↦ ?_
    have hb : 0 < cdf (cauchyMeasure m γ) b := by
      rw [cdf_cauchyMeasure_of_scale_ne_zero m hγ, ← neg_lt_iff_pos_add',
        lt_div_iff₀ pi_pos]
      linarith [neg_pi_div_two_lt_arctan ((b - m) / γ)]
    filter_upwards [Ioo_mem_nhdsGT hb] with u hu
    exact (Measure.quantile_le_iff _ hu.1
      (hu.2.trans_le (cdf_le_one (cauchyMeasure m γ) b))).2 hu.2.le

/-- The upper endpoint limit of a Cauchy quantile is plus infinity at positive scale
and the location at zero scale. -/
theorem tendsto_quantile_cauchyMeasure_nhdsLT_one (m : ℝ) (γ : ℝ≥0) :
    Tendsto (fun u ↦ ((cauchyMeasure m γ).quantile u : EReal)) (𝓝[<] 1)
      (𝓝 (if γ = 0 then (m : EReal) else ⊤)) := by
  by_cases hγ : γ = 0
  · subst hγ
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    simp [Measure.quantile_dirac m hu.1 hu.2.le]
  · rw [ite_eq_right hγ]
    apply EReal.tendsto_coe_nhds_top_iff.2
    refine tendsto_atTop.2 fun b ↦ ?_
    have hb : cdf (cauchyMeasure m γ) b < 1 := by
      rw [cdf_cauchyMeasure_of_scale_ne_zero m hγ, ← lt_sub_iff_add_lt',
        div_lt_iff₀ pi_pos]
      linarith [arctan_lt_pi_div_two ((b - m) / γ)]
    filter_upwards [Ioo_mem_nhdsLT hb] with u hu
    exact ((Measure.lt_quantile_iff _
      ((cdf_nonneg (cauchyMeasure m γ) b).trans_lt hu.1) hu.2).2 hu.1).le

end TauCeti.Probability
