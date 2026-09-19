/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Splitting a measure along a finite partition

A measure is the sum of its restrictions to the pieces of a finite measurable partition. Scaling
each restriction by a factor `s i ≤ 1` splits it further into a scaled part and a remainder, which
is the form in which mass is matched cell by cell in transport-plan constructions.

## Main statements

* `MeasureTheory.Measure.eq_sum_smul_restrict_add_sum_one_sub_smul_restrict` — for a finite
  measurable partition `A` and factors `s i ≤ 1`,
  `μ = ∑ i, s i • μ.restrict (A i) + ∑ i, (1 - s i) • μ.restrict (A i)`.
-/

public section

open Function Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- Splitting each piece of a finite measurable partition by a factor `s i ≤ 1` splits the measure
into a scaled part and a remainder. -/
theorem eq_sum_smul_restrict_add_sum_one_sub_smul_restrict {Z : Type*} [MeasurableSpace Z]
    {ι : Type*} [Fintype ι] {A : ι → Set Z} (hAm : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (Disjoint on A)) (hAu : (⋃ i, A i) = univ) {s : ι → ℝ≥0∞} (hs : ∀ i, s i ≤ 1)
    (μ : Measure Z) :
    μ = ∑ i, s i • μ.restrict (A i) + ∑ i, (1 - s i) • μ.restrict (A i) := by
  rw [← Finset.sum_add_distrib]
  conv_lhs => rw [← restrict_univ (μ := μ), ← hAu, restrict_iUnion hAd hAm, sum_fintype]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← add_smul, add_tsub_cancel_of_le (hs i), one_smul]

end MeasureTheory.Measure
