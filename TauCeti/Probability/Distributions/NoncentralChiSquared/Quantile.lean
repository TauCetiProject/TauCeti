/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralChiSquared.Cdf
public import TauCeti.Probability.Quantile
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of noncentral chi-squared laws

At positive degree every interior quantile is the unique positive root of the Poisson-series
cdf. At degree zero the quantile is zero through the atom of mass `exp (-l / 2)` and is the
unique positive cdf root above that mass. The quantile is continuous even across this transition
and strictly increasing on its positive range.

All valid laws have lower quantile endpoint zero. The upper endpoint is infinite except for
the double-zero Dirac law, whose quantiles are constantly zero.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {k u x : ℝ} {l : ℝ≥0}

/-- Every interior quantile is nonnegative. -/
theorem quantile_noncentralChiSquaredMeasure_nonneg (hk : 0 ≤ k) (l : ℝ≥0)
    (hu : u ∈ Ioo 0 1) : 0 ≤ (noncentralChiSquaredMeasure k l).quantile u := by
  have := isProbabilityMeasure_noncentralChiSquaredMeasure hk l
  exact ordConnected_Ici.quantile_mem (ae_nonneg_noncentralChiSquaredMeasure k l) hu.1 hu.2

/-- An interior quantile is zero exactly through the mass of the atom at zero. At positive
degree that mass is zero, so every interior quantile is positive. -/
@[simp]
theorem quantile_noncentralChiSquaredMeasure_eq_zero_iff (hk : 0 ≤ k) (l : ℝ≥0)
    (hu : u ∈ Ioo 0 1) :
    (noncentralChiSquaredMeasure k l).quantile u = 0 ↔
      u ≤ if k = 0 then exp (-(l : ℝ) / 2) else 0 := by
  have hq := quantile_noncentralChiSquaredMeasure_nonneg hk l hu
  rw [← cdf_noncentralChiSquaredMeasure_zero hk,
    ← Measure.quantile_le_iff _ hu.1 hu.2]
  exact ⟨fun h ↦ h.le, fun h ↦ le_antisymm h hq⟩

/-- Every interior quantile above the mass of the atom at zero is positive. -/
theorem quantile_noncentralChiSquaredMeasure_pos (hk : 0 ≤ k) (hu : u ∈ Ioo 0 1)
    (hcut : (if k = 0 then exp (-(l : ℝ) / 2) else 0) < u) :
    0 < (noncentralChiSquaredMeasure k l).quantile u := by
  rwa [Measure.lt_quantile_iff _ hu.1 hu.2, cdf_noncentralChiSquaredMeasure_zero hk]

/-- A quantile above the atom solves the cdf equation exactly. -/
theorem cdf_quantile_noncentralChiSquaredMeasure (hk : 0 ≤ k) (hu : u ∈ Ioo 0 1)
    (hcut : (if k = 0 then exp (-(l : ℝ) / 2) else 0) < u) :
    cdf (noncentralChiSquaredMeasure k l) ((noncentralChiSquaredMeasure k l).quantile u) = u := by
  have := isProbabilityMeasure_noncentralChiSquaredMeasure hk l
  have hpos := quantile_noncentralChiSquaredMeasure_pos hk hu hcut
  exact Measure.cdf_quantile' _ hu.1 hu.2
    (noncentralChiSquaredMeasure_singleton_of_ne_zero hpos.ne' k l)

/-- Above the atom, the quantile is the unique positive root of the cdf. Together with
`cdf_noncentralChiSquaredMeasure_eq` and `cdf_noncentralChiSquaredMeasure_zero_degree`,
this characterizes it by the explicit Poisson series. -/
theorem quantile_noncentralChiSquaredMeasure_eq_iff (hk : 0 ≤ k) (hu : u ∈ Ioo 0 1)
    (hcut : (if k = 0 then exp (-(l : ℝ) / 2) else 0) < u) :
    (noncentralChiSquaredMeasure k l).quantile u = x ↔
      0 < x ∧ cdf (noncentralChiSquaredMeasure k l) x = u := by
  have hpos := quantile_noncentralChiSquaredMeasure_pos hk hu hcut
  have hroot := cdf_quantile_noncentralChiSquaredMeasure hk hu hcut
  constructor
  · rintro rfl
    exact ⟨hpos, hroot⟩
  · rintro ⟨hx, heq⟩
    have h : k ≠ 0 ∨ l ≠ 0 := by
      by_contra hn
      simp only [not_or, not_not] at hn
      rcases hn with ⟨rfl, rfl⟩
      simp at hcut
      linarith [hu.2]
    exact (strictMonoOn_cdf_noncentralChiSquaredMeasure hk h).injOn hpos.le hx.le
      (hroot.trans heq.symm)

/-- On the levels above its atom, the quantile is strictly increasing. -/
theorem strictMonoOn_quantile_noncentralChiSquaredMeasure (hk : 0 ≤ k) (l : ℝ≥0) :
    StrictMonoOn (noncentralChiSquaredMeasure k l).quantile
      (Ioo (if k = 0 then exp (-(l : ℝ) / 2) else 0) 1) := by
  have hnonneg : 0 ≤ if k = 0 then exp (-(l : ℝ) / 2) else 0 := by split_ifs <;> positivity
  intro s hs t ht hst
  rw [Measure.lt_quantile_iff _ (hnonneg.trans_lt ht.1) ht.2,
    cdf_quantile_noncentralChiSquaredMeasure hk ⟨hnonneg.trans_lt hs.1, hs.2⟩ hs.1]
  exact hst

/-- The quantile is continuous on all interior levels, including the transition out of the
degree-zero atom. -/
theorem continuousOn_quantile_noncentralChiSquaredMeasure (hk : 0 ≤ k) (l : ℝ≥0) :
    ContinuousOn (noncentralChiSquaredMeasure k l).quantile (Ioo 0 1) := by
  by_cases h : k = 0 ∧ l = 0
  · rcases h with ⟨rfl, rfl⟩
    exact continuousOn_const.congr fun u hu ↦ by
      rw [noncentralChiSquaredMeasure_zero_noncentrality, chiSquaredMeasure_zero,
        Measure.quantile_dirac 0 hu.1 hu.2.le]
  exact Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_Ici
    (strictMonoOn_cdf_noncentralChiSquaredMeasure hk (not_and_or.mp h))
    (fun _ hu ↦ quantile_noncentralChiSquaredMeasure_nonneg hk l hu)

/-- At the lower endpoint, every valid noncentral chi-squared quantile tends to zero. -/
theorem tendsto_quantile_noncentralChiSquaredMeasure_nhdsGT_zero (hk : 0 ≤ k) (l : ℝ≥0) :
    Tendsto (fun u ↦ ((noncentralChiSquaredMeasure k l).quantile u : EReal))
      (𝓝[>] 0) (𝓝 0) := by
  apply EReal.tendsto_coe.2
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    exact ha.trans_le (quantile_noncentralChiSquaredMeasure_nonneg hk l hu)
  · have hc := cdf_noncentralChiSquaredMeasure_pos hk l (half_pos hb)
    filter_upwards [Ioo_mem_nhdsGT hc] with u hu
    exact ((Measure.quantile_le_iff _ hu.1 (hu.2.trans_le (cdf_le_one _ _))).2 hu.2.le).trans_lt
      (half_lt_self hb)

/-- The upper endpoint is infinite except for the double-zero Dirac law. -/
theorem tendsto_quantile_noncentralChiSquaredMeasure_nhdsLT_one (hk : 0 ≤ k) (l : ℝ≥0) :
    Tendsto (fun u ↦ ((noncentralChiSquaredMeasure k l).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if k = 0 ∧ l = 0 then 0 else ⊤)) := by
  by_cases h : k = 0 ∧ l = 0
  · rw [ite_eq_left h]
    rcases h with ⟨rfl, rfl⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    rw [noncentralChiSquaredMeasure_zero_noncentrality, chiSquaredMeasure_zero,
      Measure.quantile_dirac 0 hu.1 hu.2.le]
    norm_num
  · rw [ite_eq_right h, EReal.tendsto_coe_nhds_top_iff]
    refine tendsto_atTop.2 fun b ↦ ?_
    have hb := cdf_noncentralChiSquaredMeasure_lt_one hk (not_and_or.mp h) b
    filter_upwards [Ioo_mem_nhdsLT hb] with u hu
    exact ((Measure.lt_quantile_iff _ ((cdf_nonneg _ b).trans_lt hu.1) hu.2).2 hu.1).le

end TauCeti.Probability
