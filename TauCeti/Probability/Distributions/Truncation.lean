/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
public import TauCeti.Probability.Quantile
public import TauCeti.MeasureTheory.Measure.LowerSet

/-!
# Interval truncation of real probability laws

Conditioning a real probability law `μ` on an interval retains its mass between the endpoints
and renormalizes it. This file computes the resulting cumulative distribution function and
quantile for all four finite endpoint conventions, retaining endpoint atoms. This distinction
also matters for conditioning degenerate laws, such as a Gaussian with zero variance.

Write `L` for the mass excluded at the lower end and `R` for the mass up to the upper end,
including the upper atom precisely when that endpoint is retained. The conditional cdf is

```text
(min R (max L (cdf μ x)) - L) / (R - L).
```

Consequently, at an interior level `u`, its quantile is the quantile of `μ` at the rescaled level
`L + u * (R - L)`. The strict hypothesis `L < R` says exactly that the conditioning interval has
positive mass. No atomlessness or nondegeneracy assumption on the conditional law is needed.
The underlying statements for differences of measurable lower sets also allow unbounded cuts.

## Main results

* `MeasureTheory.Measure.cdf_cond` — the cdf of a law conditioned on a measurable event;
* `MeasureTheory.Measure.cdf_cond_sdiff`, `MeasureTheory.Measure.quantile_cond_sdiff` —
  truncation between measurable lower cuts;
* `MeasureTheory.Measure.cdf_cond_Ioc`, `MeasureTheory.Measure.cdf_cond_Icc`,
  `MeasureTheory.Measure.cdf_cond_Ioo`, `MeasureTheory.Measure.cdf_cond_Ico` — finite intervals;
* `MeasureTheory.Measure.quantile_cond_Ioc`, `MeasureTheory.Measure.quantile_cond_Icc`,
  `MeasureTheory.Measure.quantile_cond_Ioo`, `MeasureTheory.Measure.quantile_cond_Ico` —
  the corresponding interior quantile formulas.
-/

public section

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable (μ : Measure ℝ)

/-- The cdf of `μ` conditioned on a measurable event is the proportion of that event lying below
the cdf argument. -/
theorem cdf_cond [IsFiniteMeasure μ] {A : Set ℝ} (hA : MeasurableSet A) (hμA : μ A ≠ 0)
    (x : ℝ) :
    cdf (ProbabilityTheory.cond μ A) x = μ.real (A ∩ Iic x) / μ.real A := by
  have := ProbabilityTheory.cond_isProbabilityMeasure hμA
  simp [cdf_eq_real, measureReal_def, ProbabilityTheory.cond_apply hA, div_eq_inv_mul]

variable [IsProbabilityMeasure μ]

/-- Conditioning between two measurable lower cuts clips and rescales the original cdf.
Taking either cut to be an open or closed ray retains its endpoint convention; the empty and
universal cuts also allow unbounded truncations. -/
theorem cdf_cond_sdiff {A B : Set ℝ} (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hmA : MeasurableSet A) (hmB : MeasurableSet B) (hLR : μ.real A < μ.real B) (x : ℝ) :
    cdf (ProbabilityTheory.cond μ (B \ A)) x =
      (min (μ.real B) (max (μ.real A) (cdf μ x)) - μ.real A) /
        (μ.real B - μ.real A) := by
  have hmass : μ.real (B \ A) = μ.real B - μ.real A := by
    rw [μ.measureReal_sdiff_of_isLowerSet hB hA hmA, max_eq_left (sub_nonneg.mpr hLR.le)]
  have hne : μ (B \ A) ≠ 0 := by
    rw [← measureReal_ne_zero_iff, hmass]
    exact (sub_pos.mpr hLR).ne'
  have hinter : (B \ A) ∩ Iic x = (B ∩ Iic x) \ A := inter_sdiff_right_comm.symm
  rw [cdf_cond μ (hmB.diff hmA) hne, hinter, hmass,
    μ.measureReal_sdiff_of_isLowerSet (hB.inter (IsLowerSet.Iic x)) hA hmA,
    μ.measureReal_inter_of_isLowerSet hB (IsLowerSet.Iic x), ← cdf_eq_real]
  congr 1
  rw [min_max_distrib_left, min_eq_right hLR.le, ← max_sub_sub_right, sub_self, max_comm]

/-- At an interior level, conditioning between two measurable lower cuts amounts to an affine
rescaling of the source quantile's probability level. Atoms and flat cdf intervals are allowed. -/
theorem quantile_cond_sdiff {A B : Set ℝ} (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hmA : MeasurableSet A) (hmB : MeasurableSet B) (hLR : μ.real A < μ.real B)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (ProbabilityTheory.cond μ (B \ A)).quantile u =
      μ.quantile (μ.real A + u * (μ.real B - μ.real A)) := by
  let L := μ.real A
  let R := μ.real B
  have hD : 0 < R - L := sub_pos.mpr hLR
  have hqL : L < L + u * (R - L) := by
    nlinarith [mul_pos hu.1 hD]
  have hqR : L + u * (R - L) < R := by
    nlinarith [hu.2]
  -- Compare levels on each side of the clipping thresholds, so that neither continuity nor
  -- strict increase of the source cdf is needed.
  have hlevel (x : ℝ) :
      u ≤ cdf (ProbabilityTheory.cond μ (B \ A)) x ↔
        L + u * (R - L) ≤ cdf μ x := by
    rw [cdf_cond_sdiff μ hA hB hmA hmB hLR]
    by_cases hxL : cdf μ x ≤ L
    · rw [max_eq_left hxL, min_eq_right hLR.le, sub_self, zero_div]
      constructor <;> intro h <;> linarith [hu.1, hqL]
    · have hLx : L ≤ cdf μ x := (not_le.mp hxL).le
      by_cases hRx : R ≤ cdf μ x
      · rw [max_eq_right hLx, min_eq_left hRx, div_self hD.ne']
        constructor
        · intro _
          exact hqR.le.trans hRx
        · intro _
          exact hu.2.le
      · have hxR : cdf μ x ≤ R := (not_le.mp hRx).le
        rw [max_eq_right hLx, min_eq_right hxR, le_div_iff₀ hD]
        constructor <;> intro h <;> linarith
  exact quantile_eq_of_le_cdf_iff _ _ hlevel

/-- The cdf conditioned on `(l, r]` excludes the lower atom and retains the upper atom. -/
theorem cdf_cond_Ioc {l r : ℝ} (hLR : cdf μ l < cdf μ r) (x : ℝ) :
    cdf (ProbabilityTheory.cond μ (Ioc l r)) x =
      (min (cdf μ r) (max (cdf μ l) (cdf μ x)) - cdf μ l) /
        (cdf μ r - cdf μ l) := by
  simpa only [Iic_sdiff_Iic, ← cdf_eq_real] using
    cdf_cond_sdiff μ (IsLowerSet.Iic l) (IsLowerSet.Iic r) measurableSet_Iic measurableSet_Iic
      (by simpa only [← cdf_eq_real] using hLR) x

/-- For `0 < u < 1`, the `u`-quantile conditioned on `(l, r]` is the source quantile at the
rescaled level `cdf μ l + u * (cdf μ r - cdf μ l)`. -/
theorem quantile_cond_Ioc {l r u : ℝ} (hLR : cdf μ l < cdf μ r)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (ProbabilityTheory.cond μ (Ioc l r)).quantile u =
      μ.quantile (cdf μ l + u * (cdf μ r - cdf μ l)) := by
  simpa only [Iic_sdiff_Iic, ← cdf_eq_real] using
    quantile_cond_sdiff μ (IsLowerSet.Iic l) (IsLowerSet.Iic r) measurableSet_Iic measurableSet_Iic
      (by simpa only [← cdf_eq_real] using hLR) hu

/-- The cdf conditioned on `[l, r]` includes both endpoint atoms. The lower cut is the mass
strictly below `l`, allowing even `l = r` when the endpoint has positive mass. -/
theorem cdf_cond_Icc {l r : ℝ} (hLR : μ.real (Iio l) < cdf μ r) (x : ℝ) :
    cdf (ProbabilityTheory.cond μ (Icc l r)) x =
      (min (cdf μ r) (max (μ.real (Iio l)) (cdf μ x)) - μ.real (Iio l)) /
        (cdf μ r - μ.real (Iio l)) := by
  simpa only [Iic_sdiff_Iio, ← cdf_eq_real] using
    cdf_cond_sdiff μ (IsLowerSet.Iio l) (IsLowerSet.Iic r) measurableSet_Iio measurableSet_Iic
      (by simpa only [← cdf_eq_real] using hLR) x

/-- The interior quantile conditioned on `[l, r]`, retaining both endpoint atoms. -/
theorem quantile_cond_Icc {l r u : ℝ} (hLR : μ.real (Iio l) < cdf μ r)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (ProbabilityTheory.cond μ (Icc l r)).quantile u =
      μ.quantile (μ.real (Iio l) + u * (cdf μ r - μ.real (Iio l))) := by
  simpa only [Iic_sdiff_Iio, ← cdf_eq_real] using
    quantile_cond_sdiff μ (IsLowerSet.Iio l) (IsLowerSet.Iic r) measurableSet_Iio measurableSet_Iic
      (by simpa only [← cdf_eq_real] using hLR) hu

/-- The cdf conditioned on `(l, r)` excludes both endpoint atoms. The upper cut is the mass
strictly below `r`. -/
theorem cdf_cond_Ioo {l r : ℝ} (hLR : cdf μ l < μ.real (Iio r)) (x : ℝ) :
    cdf (ProbabilityTheory.cond μ (Ioo l r)) x =
      (min (μ.real (Iio r)) (max (cdf μ l) (cdf μ x)) - cdf μ l) /
        (μ.real (Iio r) - cdf μ l) := by
  simpa only [Iio_sdiff_Iic, ← cdf_eq_real] using
    cdf_cond_sdiff μ (IsLowerSet.Iic l) (IsLowerSet.Iio r) measurableSet_Iic measurableSet_Iio
      (by simpa only [← cdf_eq_real] using hLR) x

/-- The interior quantile conditioned on `(l, r)`, excluding both endpoint atoms. -/
theorem quantile_cond_Ioo {l r u : ℝ} (hLR : cdf μ l < μ.real (Iio r))
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (ProbabilityTheory.cond μ (Ioo l r)).quantile u =
      μ.quantile (cdf μ l + u * (μ.real (Iio r) - cdf μ l)) := by
  simpa only [Iio_sdiff_Iic, ← cdf_eq_real] using
    quantile_cond_sdiff μ (IsLowerSet.Iic l) (IsLowerSet.Iio r) measurableSet_Iic measurableSet_Iio
      (by simpa only [← cdf_eq_real] using hLR) hu

/-- The cdf conditioned on `[l, r)` retains the lower atom and excludes the upper atom. -/
theorem cdf_cond_Ico {l r : ℝ} (hLR : μ.real (Iio l) < μ.real (Iio r)) (x : ℝ) :
    cdf (ProbabilityTheory.cond μ (Ico l r)) x =
      (min (μ.real (Iio r)) (max (μ.real (Iio l)) (cdf μ x)) - μ.real (Iio l)) /
        (μ.real (Iio r) - μ.real (Iio l)) := by
  simpa only [Iio_sdiff_Iio] using
    cdf_cond_sdiff μ (IsLowerSet.Iio l) (IsLowerSet.Iio r) measurableSet_Iio measurableSet_Iio hLR x

/-- The interior quantile conditioned on `[l, r)`, retaining the lower atom and excluding the
upper atom. -/
theorem quantile_cond_Ico {l r u : ℝ} (hLR : μ.real (Iio l) < μ.real (Iio r))
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (ProbabilityTheory.cond μ (Ico l r)).quantile u =
      μ.quantile (μ.real (Iio l) + u * (μ.real (Iio r) - μ.real (Iio l))) := by
  simpa only [Iio_sdiff_Iio] using
    quantile_cond_sdiff μ (IsLowerSet.Iio l) (IsLowerSet.Iio r)
      measurableSet_Iio measurableSet_Iio hLR hu

end MeasureTheory.Measure
