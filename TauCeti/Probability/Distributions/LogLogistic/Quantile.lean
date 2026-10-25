/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.LogLogistic.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Probability.Quantile.Map

/-!
# Quantiles of log-logistic laws

At every level `0 < u < 1`, the quantile of the log-logistic law with scale `a > 0` and shape
`b > 0` is `a * (u / (1 - u)) ^ b⁻¹`, the exponential of the logistic quantile
`log a + b⁻¹ * log (u / (1 - u))`.

The one-sided endpoint limits are stated in `EReal`: they are `0` at `u → 0⁺` and `⊤` at
`u → 1⁻`, the two ends of the support `Set.Ici 0`. These are limits through interior levels and
do not depend on the totalized quantile values at `0` and `1`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 23.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace TauCeti.Probability

variable {a b : ℝ}

/-- **The quantile function of the log-logistic law** is `u ↦ a * (u / (1 - u)) ^ b⁻¹` at every
level `0 < u < 1`. -/
theorem quantile_logLogisticMeasure (ha : 0 < a) (hb : 0 < b) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    (logLogisticMeasure a b).quantile u = a * (u / (1 - u)) ^ b⁻¹ := by
  have := isProbabilityMeasure_logisticMeasure (inv_pos.mpr hb) (Real.log a)
  rw [logLogisticMeasure_of_pos ha hb, Measure.quantile_map_exp hu.1 hu.2,
    quantile_logisticMeasure (inv_pos.mpr hb) _ hu, Real.exp_add, Real.exp_log ha,
    Real.rpow_def_of_pos (div_pos hu.1 (sub_pos.mpr hu.2)), mul_comm b⁻¹]

/-- The lower endpoint limit of a log-logistic quantile is `0`, the left end of its support. -/
theorem tendsto_quantile_logLogisticMeasure_nhdsGT_zero (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun u ↦ ((logLogisticMeasure a b).quantile u : EReal)) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun u : ℝ ↦ a * (u / (1 - u)) ^ b⁻¹) 0 := by
    refine continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inr (inv_pos.mpr hb).le)
      |>.comp ?_)
    exact continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by norm_num)
  have hlim : Tendsto (fun u : ℝ ↦ a * (u / (1 - u)) ^ b⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [zero_div, Real.zero_rpow (inv_ne_zero hb.ne'), mul_zero] at h
  apply (EReal.tendsto_coe.mpr hlim).congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal)) (quantile_logLogisticMeasure ha hb hu).symm

/-- The upper endpoint limit of a log-logistic quantile is `⊤`: the support is unbounded above. -/
theorem tendsto_quantile_logLogisticMeasure_nhdsLT_one (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun u ↦ ((logLogisticMeasure a b).quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) := by
  -- The odds `u / (1 - u)` tend to `+∞` as `u → 1⁻`, because `1 - u → 0⁺`.
  have hsub : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝 1) (𝓝 (1 - 1)) := tendsto_const_nhds.sub tendsto_id
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact sub_pos.mpr hu
  have hodds : Tendsto (fun u : ℝ ↦ u / (1 - u)) (𝓝[<] 1) atTop := by
    simp only [div_eq_mul_inv]
    exact Tendsto.pos_mul_atTop zero_lt_one (tendsto_id.mono_left nhdsWithin_le_nhds)
      (tendsto_inv_nhdsGT_zero.comp hsub)
  have hlim : Tendsto (fun u : ℝ ↦ a * (u / (1 - u)) ^ b⁻¹) (𝓝[<] 1) atTop :=
    ((tendsto_rpow_atTop (inv_pos.mpr hb)).comp hodds).const_mul_atTop ha
  apply EReal.tendsto_coe_nhds_top_iff.mpr
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_logLogisticMeasure ha hb hu).symm

end TauCeti.Probability
