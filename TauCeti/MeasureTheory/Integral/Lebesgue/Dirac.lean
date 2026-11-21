/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Integration against finite sums of Dirac measures

A nonnegative measurable function integrates against a finite sum of point masses by
summing its values at the corresponding points, with multiplicities retained.
-/

public section

open scoped ENNReal

namespace MeasureTheory

-- Not a simp lemma: `lintegral_finsetSum_measure` already simplifies its left-hand side.
/-- Integrating against a finite sum of Dirac measures sums the values at their points.
No measurability of singletons or distinctness of the points is required. -/
theorem lintegral_finsetSum_dirac {ι X : Type*} [MeasurableSpace X]
    (s : Finset ι) (x : ι → X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂(∑ i ∈ s, Measure.dirac (x i))) = ∑ i ∈ s, f (x i) := by
  simp [lintegral_finsetSum_measure, lintegral_dirac' _ hf]

end MeasureTheory
