/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable singletons in a disjoint union

If both summands have measurable singletons, so does their disjoint union `α ⊕ β`: the singletons
are images of singletons under the measurable embeddings `Sum.inl` and `Sum.inr`.

## Main results

* `Sum.instMeasurableSingletonClass`: `MeasurableSingletonClass (α ⊕ β)` from
  `MeasurableSingletonClass α` and `MeasurableSingletonClass β`.
-/

public section

namespace Sum

/-- A disjoint union of two spaces with measurable singletons has measurable singletons. -/
instance instMeasurableSingletonClass {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton o := by
    rcases o with a | b
    · simpa using (measurableSet_singleton a).inl_image (β := β)
    · simpa using (measurableSet_singleton b).inr_image (α := α)

end Sum
