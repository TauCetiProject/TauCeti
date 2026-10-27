/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Semicircle.Cdf
public import TauCeti.Probability.Distributions.Beta.Quantile

/-!
# Quantiles of the semicircle law

Interior semicircle quantiles are affine images of inverse regularized incomplete Beta values
with shapes `(3 / 2, 3 / 2)`. They lie in `(-1, 1)`, vary continuously and strictly increasingly
with the level, and tend to the support endpoints as the level tends to zero or one.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, Chapter 25.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

/-- The semicircle quantile is an affine inverse-Beta quantile at every interior level. -/
@[simp]
theorem quantile_semicircleMeasure {u : ℝ} (hu : u ∈ Ioo 0 1) :
    semicircleMeasure.quantile u = 2 * inverseRegularizedIncompleteBeta (3 / 2) (3 / 2) u - 1 := by
  let _ : IsProbabilityMeasure (betaMeasure (3 / 2) (3 / 2)) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  rw [semicircleMeasure_eq_map_betaMeasure, quantile_map_affine_pos (by norm_num) hu.1 hu.2,
    quantile_betaMeasure (by norm_num) (by norm_num) hu]
  ring

/-- Every interior semicircle quantile lies strictly inside the support. -/
theorem quantile_semicircleMeasure_mem_Ioo {u : ℝ} (hu : u ∈ Ioo 0 1) :
    semicircleMeasure.quantile u ∈ Ioo (-1 : ℝ) 1 := by
  rw [quantile_semicircleMeasure hu]
  have h := inverseRegularizedIncompleteBeta_mem_Ioo
    (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (0 : ℝ) < 3 / 2) hu.1 hu.2
  constructor <;> linarith [h.1, h.2]

/-- Semicircle quantiles vary continuously on the interior probability levels. -/
theorem continuousOn_quantile_semicircleMeasure :
    ContinuousOn semicircleMeasure.quantile (Ioo 0 1) := by
  rw [continuousOn_congr (fun u hu ↦ quantile_semicircleMeasure hu)]
  exact (continuousOn_const.mul (continuousOn_inverseRegularizedIncompleteBeta
    (by norm_num) (by norm_num))).sub continuousOn_const

/-- Semicircle quantiles are strictly increasing on the interior probability levels. -/
theorem strictMonoOn_quantile_semicircleMeasure :
    StrictMonoOn semicircleMeasure.quantile (Ioo 0 1) := by
  exact Measure.strictMonoOn_quantile _ (Measure.continuous_cdf_of_noAtoms _)

/-- Semicircle quantiles tend to the lower support endpoint as the level tends to zero. -/
theorem tendsto_quantile_semicircleMeasure_nhdsGT_zero :
    Tendsto (fun u ↦ (semicircleMeasure.quantile u : EReal)) (𝓝[>] 0) (𝓝 (-1)) := by
  have h := ((tendsto_inverseRegularizedIncompleteBeta_zero
    (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (0 : ℝ) < 3 / 2)).const_mul 2).sub_const 1
  norm_num only at h
  apply (EReal.tendsto_coe.2 h).congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal)) (quantile_semicircleMeasure hu).symm

/-- Semicircle quantiles tend to the upper support endpoint as the level tends to one. -/
theorem tendsto_quantile_semicircleMeasure_nhdsLT_one :
    Tendsto (fun u ↦ (semicircleMeasure.quantile u : EReal)) (𝓝[<] 1) (𝓝 1) := by
  have h := ((tendsto_inverseRegularizedIncompleteBeta_one
    (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (0 : ℝ) < 3 / 2)).const_mul 2).sub_const 1
  norm_num only at h
  apply (EReal.tendsto_coe.2 h).congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal)) (quantile_semicircleMeasure hu).symm

end TauCeti.Probability
