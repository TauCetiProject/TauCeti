/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.InverseGamma.Cdf
public import TauCeti.Probability.Distributions.Gamma.Quantile
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of inverse-gamma laws

For positive shape `a` and scale `r`, the inverse-gamma quantile at an interior level `u` is
`r / inverseRegularizedGamma a (1 - u)`. Here `r` is the rate of the Gamma law whose reciprocal
defines the inverse-gamma law. The quantile tends to `0` and `+∞` at the two endpoints,
respectively; these one-sided limits are stated in `EReal`.

The formula uses the existing inverse regularized Gamma function and the inverse-gamma cdf.
It also supplies the scalar quantile formula for inverse-gamma marginals of matrix laws.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {a r u : ℝ}

/-- The quantile of an inverse-gamma law with positive shape and scale is the scale divided by
the inverse regularized Gamma function at the complementary level. -/
theorem quantile_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (hu : u ∈ Ioo 0 1) :
    (inverseGammaMeasure a r).quantile u = r / inverseRegularizedGamma a (1 - u) := by
  let _ := isProbabilityMeasure_inverseGammaMeasure ha hr
  have hcomp : 1 - u ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hpos := inverseRegularizedGamma_pos ha hcomp
  refine eq_of_forall_lt_iff fun x ↦ ?_
  rw [Measure.lt_quantile_iff _ hu.1 hu.2, cdf_inverseGammaMeasure_eq ha hr]
  by_cases hx : x ≤ 0
  · simp only [ite_eq_left hx]
    exact iff_of_true hu.1 (hx.trans_lt (div_pos hr hpos))
  · rw [ite_eq_right hx]
    calc
      1 - regularizedGamma a (r / x) < u ↔ 1 - u < regularizedGamma a (r / x) := by
        constructor <;> intro h <;> linarith
      _ ↔ inverseRegularizedGamma a (1 - u) < r / x :=
        (inverseRegularizedGamma_lt_iff ha hcomp).symm
      _ ↔ x < r / inverseRegularizedGamma a (1 - u) := by
        rw [lt_div_iff₀ (lt_of_not_ge hx), lt_div_iff₀ hpos, mul_comm]

/-- The inverse-gamma quantile tends to the lower support endpoint `0` as the level tends to
`0` from above. -/
theorem tendsto_quantile_inverseGammaMeasure_nhdsGT_zero (ha : 0 < a) (hr : 0 < r) :
    Tendsto (fun u ↦ ((inverseGammaMeasure a r).quantile u : EReal)) (𝓝[>] 0) (𝓝 0) := by
  have hcomp : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[>] 0) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using ((continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).const_sub 1
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact sub_lt_self _ hu
  have hlim := ((tendsto_inverseRegularizedGamma_nhdsLT_one ha).comp hcomp).const_div_atTop r
  apply EReal.tendsto_coe.mpr
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact (quantile_inverseGammaMeasure ha hr hu).symm

/-- The inverse-gamma quantile tends to infinity as the level tends to `1` from below. -/
theorem tendsto_quantile_inverseGammaMeasure_nhdsLT_one (ha : 0 < a) (hr : 0 < r) :
    Tendsto (fun u ↦ ((inverseGammaMeasure a r).quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) := by
  have hcomp : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using ((continuous_id.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds).const_sub 1
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact sub_pos.mpr hu
  have hlim : Tendsto (fun u ↦ r / inverseRegularizedGamma a (1 - u)) (𝓝[<] 1) atTop := by
    have hinv := tendsto_inv_nhdsGT_zero.comp
      ((tendsto_inverseRegularizedGamma_nhdsGT_zero ha).comp hcomp)
    simpa only [div_eq_mul_inv, Function.comp_apply] using hinv.const_mul_atTop hr
  apply EReal.tendsto_coe_nhds_top_iff.mpr
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_inverseGammaMeasure ha hr hu).symm

end TauCeti.Probability
