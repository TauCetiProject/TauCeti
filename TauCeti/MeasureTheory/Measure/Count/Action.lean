/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Invariance of counting measure under group actions

Counting measure on a measurable space with measurable singletons is invariant under any group
action (multiplicative or additive), since each translation acts injectively.

## Main results

* `MeasureTheory.Measure.smulInvariantMeasure_count`: counting measure is invariant under any
  group action on a space with measurable singletons.
* `MeasureTheory.Measure.vaddInvariantMeasure_count`: additive counterpart of
  `smulInvariantMeasure_count`.
-/

public section

open Set

namespace MeasureTheory.Measure

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]

/-- Counting measure on a space with measurable singletons is invariant under any group action. -/
@[to_additive
/-- Counting measure on a space with measurable singletons is invariant under any additive group
action. -/]
instance smulInvariantMeasure_count [MeasurableSingletonClass X] :
    SMulInvariantMeasure G X count :=
  ⟨fun g s _ ↦ by
    rw [preimage_smul]
    exact count_injective_image (MulAction.injective g⁻¹) s⟩

end MeasureTheory.Measure
