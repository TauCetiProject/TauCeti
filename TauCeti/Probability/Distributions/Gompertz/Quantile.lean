/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gompertz.Cdf
public import TauCeti.Probability.Distributions.Exponential.Quantile
import TauCeti.Probability.Quantile.Map

/-!
# Gompertz quantiles

At an interior probability level `u`, the Gompertz quantile is
`log (1 - log (1 - u) / η) / b`. It is continuous and strictly increasing, with one-sided
limits zero and positive infinity. The formula follows by applying the increasing logarithmic
transformation to the exponential quantile on its positive full-mass interval.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995).
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {η b u : ℝ}

/-- The interior Gompertz quantile is the logarithmic transform of the exponential quantile. -/
private theorem quantile_gompertzMeasure_eq (hη : 0 < η) (hb : 0 < b) (hu : u ∈ Ioo 0 1) :
    (gompertzMeasure η b).quantile u =
      log (1 + (expMeasure 1).quantile u / η) / b := by
  let _ := isProbabilityMeasure_expMeasure one_pos
  rw [gompertzMeasure_of_pos hη hb]
  apply Measure.quantile_map_of_monotoneOn ordConnected_Ioi (ae_pos_expMeasure 1) _ _ hu.1 hu.2
  · intro e he f hf hef
    apply (div_le_div_iff_of_pos_right hb).2
    exact log_le_log (by have : 0 < e := he; positivity)
      (by linarith [(div_le_div_iff_of_pos_right hη).2 hef])
  · intro e he
    have : 0 < 1 + e / η := by have : 0 < e := he; positivity
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := first | exact hb.ne' | exact hη.ne' | exact this.ne')

/-- The Gompertz quantile formula at every interior probability level. -/
@[simp]
theorem quantile_gompertzMeasure (hη : 0 < η) (hb : 0 < b) (hu : u ∈ Ioo 0 1) :
    (gompertzMeasure η b).quantile u = log (1 - log (1 - u) / η) / b := by
  rw [quantile_gompertzMeasure_eq hη hb hu, quantile_expMeasure one_pos hu, div_one,
    neg_div, ← sub_eq_add_neg]

/-- Gompertz quantiles are strictly increasing at interior probability levels. -/
theorem strictMonoOn_quantile_gompertzMeasure (hη : 0 < η) (hb : 0 < b) :
    StrictMonoOn (gompertzMeasure η b).quantile (Ioo 0 1) := by
  let _ := isProbabilityMeasure_gompertzMeasure hη hb
  exact Measure.strictMonoOn_quantile _ (Measure.continuous_cdf_of_noAtoms _)

/-- Gompertz quantiles are continuous at interior probability levels. -/
theorem continuousOn_quantile_gompertzMeasure (hη : 0 < η) (hb : 0 < b) :
    ContinuousOn (gompertzMeasure η b).quantile (Ioo 0 1) := by
  have hcont : ContinuousOn (fun u : ℝ => log (1 - log (1 - u) / η) / b) (Ioo 0 1) := by
    intro u hu
    have hlog : log (1 - u) < 0 := log_neg (sub_pos.mpr hu.2) (by linarith [hu.1])
    have hbase : 0 < 1 - log (1 - u) / η := by have := div_neg_of_neg_of_pos hlog hη; linarith
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := first | exact (sub_pos.mpr hu.2).ne' | exact hbase.ne')
  exact hcont.congr (fun u hu => quantile_gompertzMeasure hη hb hu)

/-- Gompertz quantiles tend to the lower support endpoint zero. -/
theorem tendsto_quantile_gompertzMeasure_nhdsGT_zero (hη : 0 < η) (hb : 0 < b) :
    Tendsto (fun u => ((gompertzMeasure η b).quantile u : EReal)) (𝓝[>] 0) (𝓝 0) := by
  apply EReal.tendsto_coe.2
  have hc : ContinuousAt (fun e : ℝ => log (1 + e / η) / b) 0 := by
    fun_prop (disch := first | exact hb.ne' | exact hη.ne' | norm_num)
  have hlim := hc.tendsto.comp
    (EReal.tendsto_coe.1 (tendsto_quantile_expMeasure_nhdsGT_zero one_pos))
  simp only [zero_div, add_zero, log_one] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact (quantile_gompertzMeasure_eq hη hb hu).symm

/-- Gompertz quantiles tend to positive infinity at the upper probability endpoint. -/
theorem tendsto_quantile_gompertzMeasure_nhdsLT_one (hη : 0 < η) (hb : 0 < b) :
    Tendsto (fun u => ((gompertzMeasure η b).quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) := by
  rw [EReal.tendsto_coe_nhds_top_iff]
  have he := (EReal.tendsto_coe_nhds_top_iff.1
    (tendsto_quantile_expMeasure_nhdsLT_one one_pos)).atTop_div_const hη
  have hlog := tendsto_log_atTop.comp ((tendsto_const_nhds (x := (1 : ℝ))).add_atTop he)
  apply (hlog.atTop_div_const hb).congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_gompertzMeasure_eq hη hb hu).symm

end TauCeti.Probability
