/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Fibres of a subtype inclusion

When singletons of the ambient space are measurable, the fibre `Subtype.val ⁻¹' {z}` of the
inclusion of a subtype over a point `z` is a measurable subset of the subtype. This is the set on
which a point mass at `z` is evaluated, for instance the spectral projection of a single point of
the spectrum of an operator.

## Main results

* `TauCeti.measurableSet_preimage_val_singleton`: the fibre of a subtype inclusion over a point is
  measurable.
-/

public section

namespace TauCeti

/-- The fibre of a subtype inclusion over a point is measurable. -/
theorem measurableSet_preimage_val_singleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {p : α → Prop} (z : α) :
    MeasurableSet (Subtype.val ⁻¹' {z} : Set (Subtype p)) :=
  (measurableSet_singleton z).preimage measurable_subtypeVal

end TauCeti
