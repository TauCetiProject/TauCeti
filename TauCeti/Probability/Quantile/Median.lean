/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Quantile

/-!
# Medians of a real law

A *median* of a probability measure `μ` on `ℝ` is a point `m` such that each of the closed rays
`Iic m` and `Ici m` carries at least half of the mass. Medians always exist, but they need not be
unique: if the cumulative distribution function is constant equal to `1 / 2` on an interval, every
point of the closed interval is a median, as for a fair coin on `{0, 1}`.

More generally, for a level `0 < t < 1`, the points `x` with `t ≤ μ.real (Iic x)` and
`1 - t ≤ μ.real (Ici x)` form exactly the closed interval between the lower quantile
`μ.quantile t` and the upper quantile `μ.upperQuantile t`. At `t = 1 / 2` this identifies the set
of medians: the quantile at level `1 / 2` is the least median and the upper quantile is the
greatest. None of these statements assumes the law to be atomless.

## Main definitions

* `MeasureTheory.Measure.IsMedian` — at least half of the mass lies on each side of a point.

## Main statements

* `MeasureTheory.Measure.mem_Icc_quantile_upperQuantile_iff` — the points between the lower and
  upper quantile at a level `t` are those with mass at least `t` to their left and at least
  `1 - t` to their right;
* `MeasureTheory.Measure.setOf_isMedian_eq_Icc` — the medians form the closed interval between the
  lower and upper quantile at level `1 / 2`;
* `MeasureTheory.Measure.isMedian_quantile_half` — the quantile at level `1 / 2` is a median;
* `MeasureTheory.Measure.isLeast_setOf_isMedian` and
  `MeasureTheory.Measure.isGreatest_setOf_isMedian` — the lower and upper quantile at level
  `1 / 2` are the least and the greatest median.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace MeasureTheory.Measure

variable {μ : Measure ℝ} {t x m : ℝ}

/-- For a level strictly between `0` and `1`, a point lies between the lower and the upper
quantile at that level exactly when the closed ray to its left carries mass at least the level and
the closed ray to its right carries mass at least one minus the level. -/
theorem mem_Icc_quantile_upperQuantile_iff [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1) :
    x ∈ Icc (μ.quantile t) (μ.upperQuantile t) ↔
      t ≤ μ.real (Iic x) ∧ 1 - t ≤ μ.real (Ici x) := by
  rw [mem_Icc, quantile_le_iff μ h0 h1, le_upperQuantile_iff μ h0 h1, cdf_eq_real, ← compl_Iio,
    probReal_compl_eq_one_sub measurableSet_Iio, sub_le_sub_iff_left]

/-- A point `m` is a **median** of a measure `μ` on `ℝ` if each of the closed rays `Iic m` and
`Ici m` carries at least half of the mass. The notion is intended for probability measures, where
medians exist but need not be unique. -/
def IsMedian (μ : Measure ℝ) (m : ℝ) : Prop :=
  2⁻¹ ≤ μ.real (Iic m) ∧ 2⁻¹ ≤ μ.real (Ici m)

/-- Unfolding lemma for `MeasureTheory.Measure.IsMedian`, whose body is not exposed. -/
theorem isMedian_iff : μ.IsMedian m ↔ 2⁻¹ ≤ μ.real (Iic m) ∧ 2⁻¹ ≤ μ.real (Ici m) :=
  Iff.rfl

/-- The medians of a probability measure on `ℝ` are exactly the points between its lower and
upper quantile at level `1 / 2`. -/
theorem isMedian_iff_mem_Icc [IsProbabilityMeasure μ] :
    μ.IsMedian m ↔ m ∈ Icc (μ.quantile 2⁻¹) (μ.upperQuantile 2⁻¹) := by
  rw [mem_Icc_quantile_upperQuantile_iff (by norm_num) (by norm_num), isMedian_iff]
  norm_num

/-- The set of medians of a probability measure on `ℝ` is the closed interval between its lower
and upper quantile at level `1 / 2`. -/
theorem setOf_isMedian_eq_Icc [IsProbabilityMeasure μ] :
    {m | μ.IsMedian m} = Icc (μ.quantile 2⁻¹) (μ.upperQuantile 2⁻¹) :=
  Set.ext fun _ ↦ isMedian_iff_mem_Icc

/-- **The quantile at level `1 / 2` is a median.** This holds for every probability measure on
`ℝ`, including laws with atoms. -/
theorem isMedian_quantile_half (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    μ.IsMedian (μ.quantile 2⁻¹) :=
  isMedian_iff_mem_Icc.2
    ⟨le_rfl, quantile_le_upperQuantile μ (by norm_num) (by norm_num)⟩

/-- The upper quantile at level `1 / 2` is a median. -/
theorem isMedian_upperQuantile_half (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    μ.IsMedian (μ.upperQuantile 2⁻¹) :=
  isMedian_iff_mem_Icc.2
    ⟨quantile_le_upperQuantile μ (by norm_num) (by norm_num), le_rfl⟩

/-- The quantile at level `1 / 2` is the least median of a probability measure on `ℝ`. -/
theorem isLeast_setOf_isMedian (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsLeast {m | μ.IsMedian m} (μ.quantile 2⁻¹) := by
  rw [setOf_isMedian_eq_Icc]
  exact isLeast_Icc (quantile_le_upperQuantile μ (by norm_num) (by norm_num))

/-- The upper quantile at level `1 / 2` is the greatest median of a probability measure on
`ℝ`. -/
theorem isGreatest_setOf_isMedian (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsGreatest {m | μ.IsMedian m} (μ.upperQuantile 2⁻¹) := by
  rw [setOf_isMedian_eq_Icc]
  exact isGreatest_Icc (quantile_le_upperQuantile μ (by norm_num) (by norm_num))

end MeasureTheory.Measure
