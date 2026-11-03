/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LogarithmicSeries.Basic
public import TauCeti.Probability.Cdf

/-!
# Cumulative probabilities of logarithmic-series laws

The native cumulative mass is the finite sum of the normalized logarithmic-series weights.
The real-cast cdf vanishes below the first supported count, one, and uses the natural floor
at nonnegative cutoffs. Every finite cutoff leaves strictly positive upper-tail mass.
These formulas supply the explicit cumulative crossings for logarithmic-series quantiles.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {q x : ℝ}

/-- A logarithmic-series cumulative mass is the partial sum of its normalized weights.
The term at zero vanishes by real division totalization. -/
theorem logarithmicSeriesMeasure_real_Iic (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    (logarithmicSeriesMeasure q).real (Iic k) =
      ∑ j ∈ Finset.Iic k, q ^ j / j / -Real.log (1 - q) := by
  let _ := isProbabilityMeasure_logarithmicSeriesMeasure hq0 hq1
  simp_rw [← logarithmicSeriesWeightReal_eq_div,
    ← logarithmicSeriesMeasure_real_singleton hq0 hq1]
  simp

/-- The logarithmic-series upper tail is one minus the finite cumulative sum. -/
theorem logarithmicSeriesMeasure_real_Ioi (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    (logarithmicSeriesMeasure q).real (Ioi k) =
      1 - ∑ j ∈ Finset.Iic k, q ^ j / j / -Real.log (1 - q) := by
  let _ := isProbabilityMeasure_logarithmicSeriesMeasure hq0 hq1
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic,
    logarithmicSeriesMeasure_real_Iic hq0 hq1]

/-- No finite initial segment carries all the mass of a valid logarithmic-series law. -/
theorem logarithmicSeriesMeasure_real_Iic_lt_one (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    (logarithmicSeriesMeasure q).real (Iic k) < 1 := by
  let _ := isProbabilityMeasure_logarithmicSeriesMeasure hq0 hq1
  have hpos : 0 < (logarithmicSeriesMeasure q).real {k + 1} := by
    rw [logarithmicSeriesMeasure_real_singleton hq0 hq1]
    exact (logarithmicSeriesWeightReal_pos_iff hq0 hq1 _).2 (by omega)
  have hle : (logarithmicSeriesMeasure q).real (Iic k) ≤
      1 - (logarithmicSeriesMeasure q).real {k + 1} := by
    rw [← probReal_compl_eq_one_sub (μ := logarithmicSeriesMeasure q) .of_discrete]
    exact measureReal_mono (by
      intro j hj
      simp only [mem_compl_iff, mem_singleton_iff]
      exact ne_of_lt (lt_of_le_of_lt hj (Nat.lt_succ_self k)))
  linarith

/-- The real-cast logarithmic-series cdf uses the finite cumulative sum at nonnegative
cutoffs and vanishes below zero. The guard precedes the natural floor. -/
theorem cdf_map_cast_logarithmicSeriesMeasure (hq0 : 0 < q) (hq1 : q < 1) (x : ℝ) :
    cdf ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) x =
      if x < 0 then 0 else
        ∑ j ∈ Finset.Iic ⌊x⌋₊, q ^ j / j / -Real.log (1 - q) := by
  let _ := isProbabilityMeasure_logarithmicSeriesMeasure hq0 hq1
  split_ifs with hx
  · exact Measure.cdf_map_natCast_of_neg _ hx
  · rw [Measure.cdf_map_natCast _ (le_of_not_gt hx),
      logarithmicSeriesMeasure_real_Iic hq0 hq1]

/-- The real-cast logarithmic-series cdf vanishes strictly below its first supported count. -/
theorem cdf_map_cast_logarithmicSeriesMeasure_of_lt_one (hq0 : 0 < q) (hq1 : q < 1)
    (hx : x < 1) :
    cdf ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) x = 0 := by
  rw [cdf_map_cast_logarithmicSeriesMeasure hq0 hq1]
  split_ifs with hx0
  · rfl
  · have hfloor : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx
    simp [hfloor, ← Nat.range_succ_eq_Iic]

/-- At every real cutoff the logarithmic-series cdf is strictly less than one. -/
theorem cdf_map_cast_logarithmicSeriesMeasure_lt_one (hq0 : 0 < q) (hq1 : q < 1) (x : ℝ) :
    cdf ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) x < 1 := by
  let _ := isProbabilityMeasure_logarithmicSeriesMeasure hq0 hq1
  by_cases hx : 0 ≤ x
  · rw [Measure.cdf_map_natCast _ hx]
    exact logarithmicSeriesMeasure_real_Iic_lt_one hq0 hq1 _
  · rw [Measure.cdf_map_natCast_of_neg _ (lt_of_not_ge hx)]
    exact zero_lt_one

end TauCeti.Probability
