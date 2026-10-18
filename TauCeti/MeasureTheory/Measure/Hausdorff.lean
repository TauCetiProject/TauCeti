/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Zero-dimensional Hausdorff measure

Zero-dimensional Hausdorff measure `μH[0]` is counting measure on every extended metric Borel
space: each singleton has measure `1`, so finite sets are counted by finite additivity, and an
infinite set contains finite subsets of every cardinality, so its measure is `∞`.
-/

public section

open Set MeasureTheory Measure
open scoped ENNReal

namespace TauCeti

/-- Zero-dimensional Hausdorff measure is counting measure. Thus the normalized Euclidean
Hausdorff measure `μHE[0]` also counts points, by `euclideanHausdorffMeasure_zero`. -/
@[simp]
theorem hausdorffMeasure_zero_eq_count {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] : (μH[0] : Measure X) = count := by
  have hfinite (s : Set X) (hs : s.Finite) : μH[0] s = count s := by
    simpa [count_apply_finite _ hs] using
      (sum_measure_singleton (μ := μH[0]) (s := hs.toFinset)).symm
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

end TauCeti
