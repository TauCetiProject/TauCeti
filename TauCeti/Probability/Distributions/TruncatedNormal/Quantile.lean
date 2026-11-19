/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.TruncatedNormal.Cdf

/-!
# Regularity and endpoints of truncated normal quantiles

For positive variance and truncation to an interval with extended bounds `l < r`,
each interior quantile lies strictly between the bounds and is the unique root of the
truncated cdf at its level. The quantile is continuous and strictly increasing on `(0, 1)`.
Its one-sided limits are `l` and `r` in `EReal`, including infinite bounds.

All endpoint conventions are covered. At zero variance, a truncation retaining the Gaussian
location has constant quantile on `(0, 1]` equal to that location, with the same limit at both
ends. A truncation removing the location has zero mass and is not a probability boundary.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), Chapter 13.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {m : ℝ} {v : ℝ≥0} {s : Set ℝ} {l r : EReal} {u x : ℝ}

/-- Every interior quantile of an interval-truncated positive-variance Gaussian lies strictly
between its extended bounds. -/
theorem quantile_truncatedNormalMeasure_mem_Ioo (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r)
    (hu : u ∈ Ioo 0 1) :
    ((truncatedNormalMeasure m v s).quantile u : EReal) ∈ Ioo l r := by
  have hc := continuous_cdf_truncatedNormalMeasure hv
    ((gaussianReal_preimage_Ioo_pos m hv hlr).trans_le (measure_mono hs₁)).ne'
  have hroot := Measure.cdf_quantile _ hc hu.1 hu.2
  exact ⟨(cdf_truncatedNormalMeasure_pos_iff hv hlr hs₁ hs₂).1 (hroot ▸ hu.1),
    (cdf_truncatedNormalMeasure_lt_one_iff hv hlr hs₁ hs₂).1 (hroot ▸ hu.2)⟩

/-- For an interval-truncated positive-variance Gaussian, an interior quantile is the unique
real root of the truncated cdf at its level. -/
theorem quantile_truncatedNormalMeasure_eq_iff (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r)
    (hu : u ∈ Ioo 0 1) :
    (truncatedNormalMeasure m v s).quantile u = x ↔
      cdf (truncatedNormalMeasure m v s) x = u := by
  have hc := continuous_cdf_truncatedNormalMeasure hv
    ((gaussianReal_preimage_Ioo_pos m hv hlr).trans_le (measure_mono hs₁)).ne'
  have hroot := Measure.cdf_quantile _ hc hu.1 hu.2
  refine ⟨fun h ↦ h ▸ hroot, fun hx ↦ ?_⟩
  exact (strictMonoOn_cdf_truncatedNormalMeasure hv hlr hs₁ hs₂).injOn
    (quantile_truncatedNormalMeasure_mem_Ioo hv hlr hs₁ hs₂ hu)
    ⟨(cdf_truncatedNormalMeasure_pos_iff hv hlr hs₁ hs₂).1 (hx ▸ hu.1),
      (cdf_truncatedNormalMeasure_lt_one_iff hv hlr hs₁ hs₂).1 (hx ▸ hu.2)⟩
    (hroot.trans hx.symm)

/-- Conditioning a positive-variance Gaussian on any set of positive mass gives a strictly
increasing quantile on the interior probability levels. -/
theorem strictMonoOn_quantile_truncatedNormalMeasure (hv : v ≠ 0)
    (hs : gaussianReal m v s ≠ 0) :
    StrictMonoOn (truncatedNormalMeasure m v s).quantile (Ioo 0 1) :=
  Measure.strictMonoOn_quantile _ (continuous_cdf_truncatedNormalMeasure hv hs)

/-- Interval-truncated positive-variance Gaussian quantiles are continuous at every interior
probability level. -/
theorem continuousOn_quantile_truncatedNormalMeasure (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) :
    ContinuousOn (truncatedNormalMeasure m v s).quantile (Ioo 0 1) :=
  Measure.continuousOn_quantile_of_strictMonoOn _
    (ordConnected_Ioo.preimage_mono EReal.coe_strictMono.monotone)
    (strictMonoOn_cdf_truncatedNormalMeasure hv hlr hs₁ hs₂)
    (fun _ hu ↦ quantile_truncatedNormalMeasure_mem_Ioo hv hlr hs₁ hs₂ hu)

/-- As the probability level decreases to zero, an interval-truncated positive-variance
Gaussian quantile tends to the lower extended bound, including minus infinity. -/
theorem tendsto_quantile_truncatedNormalMeasure_nhdsGT_zero (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) :
    Tendsto (fun u ↦ ((truncatedNormalMeasure m v s).quantile u : EReal))
      (𝓝[>] 0) (𝓝 l) := by
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    exact ha.trans (quantile_truncatedNormalMeasure_mem_Ioo hv hlr hs₁ hs₂ hu).1
  · obtain ⟨x, hlx, hxb⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    have hpos := (cdf_truncatedNormalMeasure_pos_iff (m := m) hv hlr hs₁ hs₂).2 hlx
    filter_upwards [Ioo_mem_nhdsGT hpos] with u hu
    have hu1 := hu.2.trans_le (cdf_le_one (truncatedNormalMeasure m v s) x)
    exact (EReal.coe_le_coe_iff.2
      ((Measure.quantile_le_iff _ hu.1 hu1).2 hu.2.le)).trans_lt hxb

/-- As the probability level increases to one, an interval-truncated positive-variance
Gaussian quantile tends to the upper extended bound, including plus infinity. -/
theorem tendsto_quantile_truncatedNormalMeasure_nhdsLT_one (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) :
    Tendsto (fun u ↦ ((truncatedNormalMeasure m v s).quantile u : EReal))
      (𝓝[<] 1) (𝓝 r) := by
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · obtain ⟨x, hax, hxr⟩ := EReal.lt_iff_exists_real_btwn.1 ha
    have hlt := (cdf_truncatedNormalMeasure_lt_one_iff (m := m) hv hlr hs₁ hs₂).2 hxr
    filter_upwards [Ioo_mem_nhdsLT hlt] with u hu
    have hu0 := (cdf_nonneg (truncatedNormalMeasure m v s) x).trans_lt hu.1
    exact hax.trans (EReal.coe_lt_coe_iff.2
      ((Measure.lt_quantile_iff _ hu0 hu.2).2 hu.1))
  · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    exact (quantile_truncatedNormalMeasure_mem_Ioo hv hlr hs₁ hs₂ hu).2.trans hb

/-- At zero variance, truncation retaining the location has constant quantile on `(0, 1]` equal
to that location, including when it is a retained interval endpoint. -/
@[simp]
theorem quantile_truncatedNormalMeasure_zero_var (hm : m ∈ s) (hu : u ∈ Ioc 0 1) :
    (truncatedNormalMeasure m 0 s).quantile u = m := by
  classical
  rw [truncatedNormalMeasure_zero_var, ite_eq_left hm, Measure.quantile_dirac _ hu.1 hu.2]

/-- The lower endpoint limit of a surviving zero-variance truncated normal is its location. -/
theorem tendsto_quantile_truncatedNormalMeasure_zero_var_nhdsGT_zero (hm : m ∈ s) :
    Tendsto (fun u ↦ ((truncatedNormalMeasure m 0 s).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (m : EReal)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal))
    (quantile_truncatedNormalMeasure_zero_var hm ⟨hu.1, hu.2.le⟩).symm

/-- The upper endpoint limit of a surviving zero-variance truncated normal is its location. -/
theorem tendsto_quantile_truncatedNormalMeasure_zero_var_nhdsLT_one (hm : m ∈ s) :
    Tendsto (fun u ↦ ((truncatedNormalMeasure m 0 s).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (m : EReal)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal))
    (quantile_truncatedNormalMeasure_zero_var hm ⟨hu.1, hu.2.le⟩).symm

end TauCeti.Probability
