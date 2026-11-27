/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable singletons in a disjoint union

The singletons of `α ⊕ β` are measurable when those of `α` and of `β` are: they are the images
of singletons under the measurable embeddings `Sum.inl` and `Sum.inr`.
-/

public section

namespace Sum

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The disjoint union of two spaces with measurable singletons has measurable singletons. -/
instance instMeasurableSingletonClass [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) :=
  ⟨fun o ↦ by
    rcases o with a | b
    · simpa using (measurableSet_singleton a).inl_image (β := β)
    · simpa using (measurableSet_singleton b).inr_image (α := α)⟩

end Sum
