/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CompleteLattice

/-!
# The lattice of measures on singletons

Mathlib computes the infimum of two measures on a measurable set `s` as an infimum over
partitions of `s` into a part measured by `μ` and a part measured by `ν`. On a measurable
singleton this collapses to the smaller of the two masses.

## Main statements

* `MeasureTheory.Measure.inf_apply_singleton`: the infimum of two measures gives a measurable
  singleton the smaller of the two masses.
-/

public section

open Set

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The infimum of two measures gives a measurable singleton the smaller of its two masses. -/
@[simp]
theorem inf_apply_singleton (μ ν : Measure α) (x : α) : (μ ⊓ ν) {x} = min (μ {x}) (ν {x}) := by
  rw [inf_apply (measurableSet_singleton x)]
  refine le_antisymm (le_min (sInf_le ⟨univ, by simp⟩) (sInf_le ⟨∅, by simp⟩)) (le_sInf ?_)
  rintro _ ⟨t, rfl⟩
  by_cases hx : x ∈ t <;> simp [hx]

end MeasureTheory.Measure
