/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Basic

/-!
# Measurable hulls inside a measurable set

A subset `A` of a measurable set `Ω` lies in a measurable subset of `Ω` of the same measure:
intersect Mathlib's measurable hull `toMeasurable μ A` with `Ω`.

## Main results

* `MeasureTheory.exists_measurableSet_subset_measure_eq`: the measurable hull of `A` inside `Ω`.
-/

public section

open Set

namespace MeasureTheory

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {Ω : Set E}

/-- A subset `A` of a measurable set `Ω` lies in a measurable subset of `Ω` of the same measure. -/
theorem exists_measurableSet_subset_measure_eq {A : Set E} (hΩ : MeasurableSet Ω) (hA : A ⊆ Ω) :
    ∃ A', A ⊆ A' ∧ A' ⊆ Ω ∧ MeasurableSet A' ∧ μ A' = μ A :=
  ⟨toMeasurable μ A ∩ Ω, subset_inter (subset_toMeasurable μ A) hA, inter_subset_right,
    (measurableSet_toMeasurable μ A).inter hΩ,
    le_antisymm ((measure_mono inter_subset_left).trans_eq (measure_toMeasurable A))
      (measure_mono (subset_inter (subset_toMeasurable μ A) hA))⟩

end MeasureTheory
