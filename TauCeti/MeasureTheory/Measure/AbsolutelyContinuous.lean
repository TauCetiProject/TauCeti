/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
# Almost-everywhere statements along a map with absolutely continuous pushforward

If `f` pushes `μ` forward to a measure absolutely continuous with respect to `ν`, then every
property holding `ν`-almost everywhere holds at `f x` for `μ`-almost every `x`. Mathlib's
`MeasureTheory.ae_eq_comp'` records the special case of an almost-everywhere equality.

## Main declarations

* `MeasureTheory.ae_comp_of_map_absolutelyContinuous`: a `ν`-almost-everywhere property holds
  along `f` `μ`-almost everywhere.
-/

public section

namespace MeasureTheory

/-- If `μ.map f ≪ ν`, a property holding `ν`-almost everywhere holds at `f x` for `μ`-almost
every `x`. This generalizes `MeasureTheory.ae_eq_comp'` from equalities to arbitrary
properties. -/
theorem ae_comp_of_map_absolutelyContinuous {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : AEMeasurable f μ) (hmap : μ.map f ≪ ν)
    {P : β → Prop} (h : ∀ᵐ y ∂ν, P y) : ∀ᵐ x ∂μ, P (f x) :=
  ae_of_ae_map hf (hmap.ae_le h)

end MeasureTheory
