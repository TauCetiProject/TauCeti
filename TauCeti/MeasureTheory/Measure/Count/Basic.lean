/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Count

/-!
# Invariance of counting measure under measurable equivalences

A measurable equivalence `e : α ≃ᵐ β` pushes the counting measure `MeasureTheory.Measure.count` on
`α` forward to the counting measure on `β`, without requiring countability or measurable
singletons on either space.
-/

public section

open MeasureTheory

namespace MeasurableEquiv

/-- Pushing forward the counting measure along a measurable equivalence gives the counting measure,
without any countability or measurable-singleton assumption. -/
@[simp]
theorem map_count {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β) :
    (Measure.count : Measure α).map e = Measure.count := by
  ext s hs
  rw [e.map_apply, Measure.count_apply (e.measurable hs), Measure.count_apply hs,
    Set.encard_preimage_of_bijective e.bijective]

end MeasurableEquiv
