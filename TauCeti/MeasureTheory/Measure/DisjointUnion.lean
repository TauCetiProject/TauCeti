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

For a pairwise disjoint family `f` of null-measurable sets, the mass of any finite subfamily is
bounded by the mass of the union. When the union has finite mass, the mass of the union not yet
covered by the first `n` sets tends to zero.

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

/-- The measures of the sets in a finite subfamily of a pairwise disjoint family of null-measurable
sets add up to at most the measure of the union of the whole family. -/
theorem sum_measure_le_measure_iUnion (hf : ∀ i, NullMeasurableSet (f i) μ)
    (hdisj : Pairwise (Disjoint on f)) (s : Finset ι) : ∑ i ∈ s, μ (f i) ≤ μ (⋃ i, f i) := by
  rw [← measure_biUnion_finset₀ (fun i _ j _ hij => (hdisj hij).aedisjoint) fun i _ => hf i]
  exact measure_mono (iUnion₂_subset_iUnion _ _)

/-- For a pairwise disjoint sequence of null-measurable sets whose union has finite measure, the
part of the union's measure not covered by the first `n` sets tends to zero. -/
theorem tendsto_measure_iUnion_sub_sum_range {f : ℕ → Set α}
    (hf : ∀ k, NullMeasurableSet (f k) μ) (hdisj : Pairwise (Disjoint on f))
    (hfin : μ (⋃ k, f k) ≠ ∞) :
    Tendsto (fun n : ℕ => μ (⋃ k, f k) - ∑ k ∈ Finset.range n, μ (f k)) atTop (𝓝 0) := by
  rw [measure_iUnion₀ hdisj.aedisjoint hf] at hfin ⊢
  simpa using ENNReal.Tendsto.sub (tendsto_const_nhds (x := ∑' k, μ (f k)))
    (ENNReal.tendsto_nat_tsum fun k => μ (f k)) (Or.inl hfin)

end MeasureTheory
