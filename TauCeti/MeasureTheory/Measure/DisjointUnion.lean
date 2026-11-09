/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Partial sums of the measures of a disjoint family

For a family `f` of null-measurable sets that are pairwise almost everywhere disjoint, the mass
of any finite subfamily is bounded by the mass of the union. When the union has finite mass, the
mass of the union not yet covered by the first `n` sets tends to zero.

## Main results

* `MeasureTheory.sum_measure_le_measure_iUnion`: `∑ i ∈ s, μ (f i) ≤ μ (⋃ i, f i)`.
* `MeasureTheory.tendsto_measure_iUnion_sub_sum_range`:
  `μ (⋃ k, f k) - ∑ k ∈ range n, μ (f k) → 0` as `n → ∞`, if `μ (⋃ k, f k) ≠ ∞`.
-/

public section

open Filter Function Set
open scoped Topology ENNReal

namespace MeasureTheory

variable {α ι : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : ι → Set α}

/-- The measures of the sets in a finite subfamily of a pairwise a.e. disjoint family of
null-measurable sets add up to at most the measure of the union of the whole family. -/
theorem sum_measure_le_measure_iUnion (hf : ∀ i, NullMeasurableSet (f i) μ)
    (hdisj : Pairwise (AEDisjoint μ on f)) (s : Finset ι) :
    ∑ i ∈ s, μ (f i) ≤ μ (⋃ i, f i) :=
  (_root_.sum_le_tsum s).trans
    (tsum_meas_le_meas_iUnion_of_disjoint₀ μ hf hdisj)

/-- For a pairwise a.e. disjoint sequence of null-measurable sets whose union has finite measure,
the part of the union's measure not covered by the first `n` sets tends to zero. -/
theorem tendsto_measure_iUnion_sub_sum_range {f : ℕ → Set α}
    (hf : ∀ k, NullMeasurableSet (f k) μ)
    (hdisj : Pairwise (AEDisjoint μ on f))
    (hfin : μ (⋃ k, f k) ≠ ∞) :
    Tendsto (fun n : ℕ => μ (⋃ k, f k) - ∑ k ∈ Finset.range n, μ (f k)) atTop (𝓝 0) := by
  rw [measure_iUnion₀ hdisj hf] at hfin ⊢
  simpa using ENNReal.Tendsto.sub (tendsto_const_nhds (x := ∑' k, μ (f k)))
    (ENNReal.tendsto_nat_tsum fun k => μ (f k)) (Or.inl hfin)

end MeasureTheory
