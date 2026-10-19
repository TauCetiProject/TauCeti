/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedPareto.Cdf
public import TauCeti.Probability.Distributions.Exponential.Quantile
import TauCeti.Probability.Quantile.Map

/-!
# Quantiles of generalized Pareto laws

For scale `s > 0`, nonzero shape `ξ`, and `0 < u < 1`, the generalized Pareto quantile is
`s * ((1 - u) ^ (-ξ) - 1) / ξ`. At shape zero it is the exponential quantile
`-s * log (1 - u)`. The quantile is continuous and strictly increasing on the open unit
interval. Its lower endpoint limit is zero; its upper endpoint limit is infinite for
nonnegative shape and `-s / ξ` for negative shape.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 4.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {s ξ u : ℝ}

/-- The generalized Pareto quantile at an interior probability level, including the exponential
branch at shape zero. -/
theorem quantile_generalizedParetoMeasure (hs : 0 < s) (ξ : ℝ) (hu : u ∈ Ioo 0 1) :
    (generalizedParetoMeasure s ξ).quantile u =
      if ξ = 0 then -s * Real.log (1 - u) else s * ((1 - u) ^ (-ξ) - 1) / ξ := by
  let _ := isProbabilityMeasure_expMeasure one_pos
  rw [generalizedParetoMeasure_of_pos hs,
    Measure.quantile_map_of_monotone (strictMono_generalizedParetoMap hs ξ).monotone
      (continuous_generalizedParetoMap s ξ) hu.1 hu.2,
    quantile_expMeasure one_pos hu, div_one]
  by_cases hξ : ξ = 0
  · simp [hξ]
  · rw [ite_eq_right hξ, generalizedParetoMap_of_shape_ne_zero hξ,
      Real.rpow_def_of_pos (sub_pos.mpr hu.2)]
    have hexp : ξ * -Real.log (1 - u) = Real.log (1 - u) * -ξ := by ring
    rw [hexp]

/-- Generalized Pareto quantiles are strictly increasing on the open unit interval. -/
theorem strictMonoOn_quantile_generalizedParetoMeasure (hs : 0 < s) (ξ : ℝ) :
    StrictMonoOn (generalizedParetoMeasure s ξ).quantile (Ioo 0 1) :=
  Measure.strictMonoOn_quantile _ (continuous_cdf_generalizedParetoMeasure hs ξ)

/-- Generalized Pareto quantiles are continuous on the open unit interval. -/
theorem continuousOn_quantile_generalizedParetoMeasure (hs : 0 < s) (ξ : ℝ) :
    ContinuousOn (generalizedParetoMeasure s ξ).quantile (Ioo 0 1) := by
  have hc : ContinuousOn (fun u : ℝ =>
      if ξ = 0 then -s * Real.log (1 - u) else s * ((1 - u) ^ (-ξ) - 1) / ξ)
      (Ioo 0 1) := by
    by_cases hξ : ξ = 0
    · simp only [ite_eq_left hξ]
      intro u hu
      have : 1 - u ≠ 0 := (sub_pos.mpr hu.2).ne'
      exact (continuousAt_const.mul
        ((continuousAt_const.sub continuousAt_id).log this)).continuousWithinAt
    · simp only [ite_eq_right hξ]
      intro u hu
      have : 1 - u ≠ 0 := (sub_pos.mpr hu.2).ne'
      exact ((continuousAt_const.mul
        (((continuousAt_const.sub continuousAt_id).rpow_const (Or.inl this)).sub
          continuousAt_const)).div_const ξ).continuousWithinAt
  exact hc.congr (fun u hu => quantile_generalizedParetoMeasure hs ξ hu)

/-- Generalized Pareto quantiles tend to the lower support endpoint zero. -/
theorem tendsto_quantile_generalizedParetoMeasure_nhdsGT_zero (hs : 0 < s) (ξ : ℝ) :
    Tendsto (fun u => ((generalizedParetoMeasure s ξ).quantile u : EReal))
      (𝓝[>] 0) (𝓝 0) := by
  let _ := isProbabilityMeasure_expMeasure one_pos
  apply EReal.tendsto_coe.2
  have hcont := (continuous_generalizedParetoMap s ξ).continuousAt (x := 0)
  have hsource := EReal.tendsto_coe.1 (tendsto_quantile_expMeasure_nhdsGT_zero one_pos)
  have hlim := hcont.tendsto.comp hsource
  rw [generalizedParetoMap_apply_zero] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  rw [generalizedParetoMeasure_of_pos hs,
    Measure.quantile_map_of_monotone (strictMono_generalizedParetoMap hs ξ).monotone
      (continuous_generalizedParetoMap s ξ) hu.1 hu.2, Function.comp_apply]

/-- Negative-shape generalized Pareto quantiles tend to the finite upper support endpoint. -/
theorem tendsto_quantile_generalizedParetoMeasure_nhdsLT_one_of_neg (hs : 0 < s)
    (hξ : ξ < 0) :
    Tendsto (fun u => ((generalizedParetoMeasure s ξ).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ((-s / ξ : ℝ) : EReal)) := by
  rw [EReal.tendsto_coe]
  have hcont : ContinuousAt (fun u : ℝ => s * ((1 - u) ^ (-ξ) - 1) / ξ) 1 := by
    fun_prop (disch := first | exact hξ.ne | right; exact (neg_pos.mpr hξ).le)
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
  simp only [sub_self, Real.zero_rpow (neg_ne_zero.mpr hξ.ne), zero_sub, mul_neg,
    mul_one] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  rw [quantile_generalizedParetoMeasure hs ξ hu, ite_eq_right hξ.ne]

/-- Nonnegative-shape generalized Pareto quantiles tend to positive infinity. -/
theorem tendsto_quantile_generalizedParetoMeasure_nhdsLT_one_of_nonneg (hs : 0 < s)
    (hξ : 0 ≤ ξ) :
    Tendsto (fun u => ((generalizedParetoMeasure s ξ).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  rcases hξ.eq_or_lt with hξ | hξ
  · rw [← hξ, generalizedParetoMeasure_zero hs]
    exact tendsto_quantile_expMeasure_nhdsLT_one (inv_pos.mpr hs)
  rw [EReal.tendsto_coe_nhds_top_iff]
  have hsub : Tendsto (fun u : ℝ => 1 - u) (𝓝[<] 1) (𝓝[>] 0) := by
    simpa only [Tendsto, Filter.map_subLeft_nhdsLT, sub_self] using
      (le_refl (𝓝[>] (0 : ℝ)))
  have hpow := (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hξ)).comp hsub
  have hsubpow : Tendsto (fun u : ℝ => (1 - u) ^ (-ξ) - 1) (𝓝[<] 1) atTop := by
    simpa only [Function.comp_apply, sub_eq_add_neg] using
      hpow.atTop_add (tendsto_const_nhds (x := (-1 : ℝ)))
  have hlim := (hsubpow.const_mul_atTop hs).atTop_div_const hξ
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  rw [quantile_generalizedParetoMeasure hs ξ hu, ite_eq_right hξ.ne']

end TauCeti.Probability
