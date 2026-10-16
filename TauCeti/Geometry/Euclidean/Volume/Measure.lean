/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Zero- and one-dimensional Euclidean Hausdorff measure

Mathlib's Euclidean Hausdorff measure `μHE[d]` is the raw Hausdorff measure `μH[d]` rescaled by
the constant that makes it agree with Lebesgue measure on `d`-dimensional Euclidean space. In
dimension zero, Hausdorff measure is counting measure. In dimension one the normalizing constant
is `1`, because `μH[1]` already agrees with Lebesgue measure on `ℝ`. Hence `μHE[1] = μH[1]` on
every extended metric space, so length statements may be proved with either normalization.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- Zero-dimensional Hausdorff measure is counting measure. Thus the normalized Euclidean
Hausdorff measure `μHE[0]` also counts points, by `euclideanHausdorffMeasure_zero`. -/
@[simp]
theorem hausdorffMeasure_zero_eq_count {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] : (μH[0] : Measure X) = count := by
  have hfinite (s : Set X) (hs : s.Finite) : μH[0] s = count s := by
    induction s, hs using Set.Finite.induction_on with
    | empty => simp
    | @insert x s hxs hs ih =>
      rw [insert_eq, measure_union (disjoint_singleton_left.mpr hxs) hs.measurableSet,
        measure_union (disjoint_singleton_left.mpr hxs) hs.measurableSet,
        hausdorffMeasure_zero_singleton, count_singleton, ih]
  ext s hs
  rcases s.finite_or_infinite with hfin | hinf
  · exact hfinite s hfin
  · rw [count_apply_infinite hinf]
    refine top_unique (le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n ↦ ?_)
    obtain ⟨t, ht, htcard⟩ := hinf.exists_subset_card_eq n
    calc
      (n : ℝ≥0∞) = count (t : Set X) := by simp [htcard]
      _ = μH[0] (t : Set X) := (hfinite t t.finite_toSet).symm
      _ ≤ μH[0] s := measure_mono ht

/-- The one-dimensional Euclidean Hausdorff measure is the raw one-dimensional Hausdorff measure,
on every extended metric space. -/
theorem euclideanHausdorffMeasure_one {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] : (μHE[1] : Measure X) = μH[1] := by
  have hℝ : (μHE[1] : Measure ℝ) = μH[1] := by
    rw [hausdorffMeasure_real, ← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      Module.finrank_self]
  have hreal : (μH[((1 : ℕ) : ℝ)] : Measure ℝ) = volume := by
    rw [Nat.cast_one, hausdorffMeasure_real]
  have hc : addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 1)))
      μH[((1 : ℕ) : ℝ)] = 1 := by
    have h := congr($hℝ (Icc (0 : ℝ) 1))
    rw [euclideanHausdorffMeasure_def, smul_apply, hreal, hausdorffMeasure_real] at h
    simpa using h
  rw [euclideanHausdorffMeasure_def, hc, one_smul, Nat.cast_one]

end MeasureTheory.Measure
