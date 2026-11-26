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

A bijection of countable types with measurable singletons preserves counting measure
(`Equiv.measurePreserving_count`).

## References

The statement is adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright
2026 Anthropic PBC), `src/Lib/Adelic/QuotientMeasure/UnfoldingInStages.lean`.
-/

public section

open MeasureTheory Measure

/-- A bijection of countable spaces with measurable singletons preserves counting measure. -/
theorem Equiv.measurePreserving_count {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] (e : α ≃ β) : MeasurePreserving e count count := by
  refine ⟨measurable_of_countable _,
    (Measure.map_sum (measurable_of_countable _).aemeasurable).trans ?_⟩
  simp only [Measure.map_dirac' (measurable_of_countable e)]
  exact sum_comp_equiv e (fun b ↦ dirac b)
