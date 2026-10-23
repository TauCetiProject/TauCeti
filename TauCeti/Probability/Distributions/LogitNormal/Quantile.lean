/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LogitNormal.Basic
public import TauCeti.Probability.Quantile
import TauCeti.Probability.Distributions.Gaussian.Quantile
import TauCeti.Probability.Quantile.Map

/-!
# Quantiles of logit-normal laws

The interior quantile is the sigmoid of the Gaussian quantile, including at zero variance.
It is continuous in the level. Its one-sided limits are zero and one at positive variance;
at zero variance both are the atom. Endpoint results concern limits through interior levels,
not the totalized quantile values at zero and one.

## References

* J. Aitchison and S. M. Shen, *Logistic-normal distributions: Some properties and uses*,
  Biometrika 67(2), 261–272, 1980.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

/-- The logit-normal quantile is the sigmoid of the Gaussian quantile. -/
theorem quantile_logitNormalMeasure (m : ℝ) (v : ℝ≥0) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    (logitNormalMeasure m v).quantile u =
      Real.sigmoid (m + √(2 * (v : ℝ)) * Real.erfInv (2 * u - 1)) := by
  rw [logitNormalMeasure_def,
    Measure.quantile_map_of_monotone Real.sigmoid_monotone continuous_sigmoid hu.1 hu.2,
    quantile_gaussianReal m v hu]

/-- Interior logit-normal quantiles lie strictly between zero and one even at zero variance. -/
theorem quantile_logitNormalMeasure_mem_Ioo (m : ℝ) (v : ℝ≥0) {u : ℝ}
    (hu : u ∈ Ioo 0 1) : (logitNormalMeasure m v).quantile u ∈ Ioo 0 1 := by
  rw [quantile_logitNormalMeasure m v hu]
  exact ⟨Real.sigmoid_pos _, Real.sigmoid_lt_one _⟩

/-- The quantile is continuous on the interior levels, including at zero variance. -/
theorem continuousOn_quantile_logitNormalMeasure (m : ℝ) (v : ℝ≥0) :
    ContinuousOn (logitNormalMeasure m v).quantile (Ioo 0 1) := by
  refine ContinuousOn.congr ?_ (fun u hu ↦ quantile_logitNormalMeasure m v hu)
  intro u hu
  have hlevel : 2 * u - 1 ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have harg : ContinuousAt
      (fun u : ℝ ↦ m + √(2 * (v : ℝ)) * Real.erfInv (2 * u - 1)) u :=
    continuousAt_const.add (continuousAt_const.mul
      ((Real.continuousAt_erfInv hlevel).comp (f := fun u : ℝ ↦ 2 * u - 1) (by fun_prop)))
  exact (continuous_sigmoid.continuousAt.comp harg).continuousWithinAt

/-- The lower endpoint limit is zero at positive variance and the atom at zero variance. -/
theorem tendsto_quantile_logitNormalMeasure_nhdsGT_zero (m : ℝ) (v : ℝ≥0) :
    Tendsto (fun u ↦ (logitNormalMeasure m v).quantile u) (𝓝[>] 0)
      (𝓝 (if v = 0 then Real.sigmoid m else 0)) := by
  by_cases hv : v = 0
  · subst hv
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    simp [Measure.quantile_dirac (Real.sigmoid m) hu.1 hu.2.le]
  · rw [ite_eq_right hv]
    have h := tendsto_quantile_gaussianReal_nhdsGT_zero m v
    rw [ite_eq_right hv] at h
    apply (Real.tendsto_sigmoid_atBot.comp (EReal.tendsto_coe_nhds_bot_iff.mp h)).congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    simp only [Function.comp_apply, quantile_logitNormalMeasure m v hu,
      quantile_gaussianReal m v hu]

/-- The upper endpoint limit is one at positive variance and the atom at zero variance. -/
theorem tendsto_quantile_logitNormalMeasure_nhdsLT_one (m : ℝ) (v : ℝ≥0) :
    Tendsto (fun u ↦ (logitNormalMeasure m v).quantile u) (𝓝[<] 1)
      (𝓝 (if v = 0 then Real.sigmoid m else 1)) := by
  by_cases hv : v = 0
  · subst hv
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    simp [Measure.quantile_dirac (Real.sigmoid m) hu.1 hu.2.le]
  · rw [ite_eq_right hv]
    have h := tendsto_quantile_gaussianReal_nhdsLT_one m v
    rw [ite_eq_right hv] at h
    apply (Real.tendsto_sigmoid_atTop.comp (EReal.tendsto_coe_nhds_top_iff.mp h)).congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    simp only [Function.comp_apply, quantile_logitNormalMeasure m v hu,
      quantile_gaussianReal m v hu]

end TauCeti.Probability
