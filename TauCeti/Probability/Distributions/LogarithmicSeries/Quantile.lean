/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LogarithmicSeries.Cdf
public import TauCeti.Probability.Quantile.Discrete
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of logarithmic-series laws

An interior lower quantile of a real-cast logarithmic-series law is the least positive count
whose explicit cumulative sum reaches the requested level. At a cumulative-mass jump it selects
the smaller count. Its one-sided endpoint limits are one and positive infinity.

The crossing characterization uses `MeasureTheory.Measure.quantile_map_natCast_eq_iff`.
The upper endpoint follows from the positive mass left above every finite cutoff.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 7.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {q u : ℝ}

/-- A natural count is the logarithmic-series quantile exactly when it is the least crossing
of the explicit finite cumulative sum. -/
theorem quantile_map_cast_logarithmicSeriesMeasure_eq_iff (hq0 : 0 < q) (hq1 : q < 1)
    (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {i : ℕ | u ≤ ∑ j ∈ Finset.Iic i, q ^ j / j / -Real.log (1 - q)} k := by
  let _ := isProbabilityMeasure_logarithmicSeriesMeasure hq0 hq1
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  simp only [logarithmicSeriesMeasure_real_Iic hq0 hq1]

/-- The quantile equals `k + 1` precisely between the cumulative masses at `k` and `k + 1`.
The lower endpoint is strict, while the upper endpoint is included. -/
theorem quantile_map_cast_logarithmicSeriesMeasure_eq_succ_iff (hq0 : 0 < q) (hq1 : q < 1)
    (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)).quantile u = (k + 1 : ℕ) ↔
      (∑ j ∈ Finset.Iic k, q ^ j / j / -Real.log (1 - q)) < u ∧
        u ≤ ∑ j ∈ Finset.Iic (k + 1), q ^ j / j / -Real.log (1 - q) := by
  let _ := isProbabilityMeasure_logarithmicSeriesMeasure hq0 hq1
  rw [Measure.quantile_map_natCast_eq_succ_iff _ hu]
  simp only [logarithmicSeriesMeasure_real_Iic hq0 hq1]

/-- The logarithmic-series quantile is one exactly through its first atom of mass
`q / (-log (1 - q))`. -/
@[simp]
theorem quantile_map_cast_logarithmicSeriesMeasure_eq_one_iff (hq0 : 0 < q) (hq1 : q < 1)
    (hu : u ∈ Ioo 0 1) :
    ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)).quantile u = 1 ↔
      u ≤ q / -Real.log (1 - q) := by
  simpa [← Nat.range_succ_eq_Iic, Finset.sum_range_succ, hu.1] using
    quantile_map_cast_logarithmicSeriesMeasure_eq_succ_iff hq0 hq1 hu 0

/-- As the level tends to zero from above, logarithmic-series quantiles tend to one. -/
theorem tendsto_quantile_map_cast_logarithmicSeriesMeasure_nhdsGT_zero
    (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun u ↦
      (((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 1) := by
  have hmass : 0 < q / -Real.log (1 - q) :=
    div_pos hq0 (neg_pos.mpr (Real.log_neg (sub_pos.mpr hq1) (sub_lt_self 1 hq0)))
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min hmass zero_lt_one)] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_le (min_le_right _ _)⟩
  rw [(quantile_map_cast_logarithmicSeriesMeasure_eq_one_iff hq0 hq1 hu').2
    (hu.2.le.trans (min_le_left _ _))]
  rfl

/-- As the level tends to one from below, logarithmic-series quantiles tend to positive
infinity: their support has no finite upper endpoint. -/
theorem tendsto_quantile_map_cast_logarithmicSeriesMeasure_nhdsLT_one
    (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun u ↦
      (((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  let _ := isProbabilityMeasure_logarithmicSeriesMeasure hq0 hq1
  apply EReal.tendsto_coe_nhds_top_iff.2
  refine tendsto_atTop.2 fun x ↦ ?_
  have hx := cdf_map_cast_logarithmicSeriesMeasure_lt_one hq0 hq1 x
  filter_upwards [Ioo_mem_nhdsLT hx] with u hu
  exact ((Measure.lt_quantile_iff _
    ((cdf_nonneg _ x).trans_lt hu.1) hu.2).2 hu.1).le

end TauCeti.Probability
