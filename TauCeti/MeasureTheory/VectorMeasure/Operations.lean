/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Operations

/-!
# Operations on vector measures

The evaluation lemma for `MeasureTheory.VectorMeasure.mapRangeL`, the vector measure obtained by
applying a continuous linear map to the values of a vector measure, together with same-set
idempotence of `MeasureTheory.VectorMeasure.restrict`.

## Main declarations

* `MeasureTheory.VectorMeasure.mapRangeL_apply`: `mapRangeL f v s = f (v s)`.
* `MeasureTheory.VectorMeasure.restrict_idem`: `(v.restrict s).restrict s = v.restrict s`.
-/

public section

namespace MeasureTheory.VectorMeasure

section

variable {α M : Type*} [MeasurableSpace α] [AddCommMonoid M] [TopologicalSpace M]

/-- Restricting a vector measure twice to the same set is idempotent. -/
@[simp]
theorem restrict_idem (v : VectorMeasure α M) (s : Set α) :
    (v.restrict s).restrict s = v.restrict s := by
  by_cases hs : MeasurableSet s
  · rw [restrict_restrict v hs hs, Set.inter_self]
  · simp [restrict_not_measurable, hs]

end

variable {α M N R : Type*} [MeasurableSpace α] [Semiring R]
  [TopologicalSpace M] [AddCommMonoid M] [Module R M] [ContinuousAdd M] [ContinuousConstSMul R M]
  [TopologicalSpace N] [AddCommMonoid N] [Module R N] [ContinuousAdd N] [ContinuousConstSMul R N]

@[simp]
theorem mapRangeL_apply (f : M →L[R] N) (v : VectorMeasure α M) (s : Set α) :
    mapRangeL f v s = f (v s) :=
  rfl

end MeasureTheory.VectorMeasure
