/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# Scalar multiplication by a unit is a measurable embedding

If a monoid `M` acts on `α` by measurable maps, scalar multiplication by a unit `c` of `M` is a
measurable embedding of `α` (`IsUnit.measurableEmbedding_const_smul`): its inverse is scalar
multiplication by the inverse of `c`. This is Mathlib's `measurableEmbedding_const_smul` for the
action of the group of units, stated for the element `c` itself; for a group with zero, where
the units are the nonzero elements, it is `measurableEmbedding_const_smul₀`. In a ring that is
not a field, such as `ℤ_p` or a product of fields, it is the form needed for multiplication by a
unit.

## Main declarations

* `IsUnit.measurableEmbedding_const_smul`: `x ↦ c • x` is a measurable embedding when `c` is a
  unit.
-/

public section

variable {M α : Type*} [Monoid M] [MulAction M α] [MeasurableSpace α] [MeasurableConstSMul M α]

/-- Scalar multiplication by a unit of a monoid acting by measurable maps is a measurable
embedding. -/
theorem IsUnit.measurableEmbedding_const_smul {c : M} (hc : IsUnit c) :
    MeasurableEmbedding (c • · : α → α) := by
  simpa only [Units.smul_isUnit] using _root_.measurableEmbedding_const_smul (α := α) hc.unit
