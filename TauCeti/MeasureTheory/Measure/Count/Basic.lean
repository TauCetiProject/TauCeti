/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Counting measure under bijections

A measurable bijection preserves counting measure (`Equiv.measurePreserving_count`).

## References

The statement is adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright
2026 Anthropic PBC), `src/Lib/Adelic/QuotientMeasure/UnfoldingInStages.lean`.
-/

public section

open MeasureTheory Measure

/-- A measurable bijection preserves counting measure. -/
theorem Equiv.measurePreserving_count {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ β) (he : Measurable e) : MeasurePreserving e count count := by
  refine ⟨he, (Measure.map_sum he.aemeasurable).trans ?_⟩
  simp only [Measure.map_dirac' he]
  exact sum_comp_equiv e (fun b ↦ dirac b)
