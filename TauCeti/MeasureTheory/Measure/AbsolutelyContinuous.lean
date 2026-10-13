/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
# Absolute continuity: domination by point-charging measures and transfer along maps

If a measure gives positive mass to every singleton, every null set is empty. It
therefore dominates any other measure, without a countability or finiteness
assumption. This is useful when a full-support discrete reference is used for
relative entropy.

If `f` pushes `μ` forward to a measure absolutely continuous with respect to `ν`, then every
property holding `ν`-almost everywhere holds at `f x` for `μ`-almost every `x`. Mathlib's
`MeasureTheory.ae_eq_comp'` records the special case of an almost-everywhere equality.

## Main declarations

* `TauCeti.absolutelyContinuous_of_forall_singleton_ne_zero`: a measure positive on every
  singleton dominates every measure.
* `MeasureTheory.ae_comp_of_map_absolutelyContinuous`: a `ν`-almost-everywhere property holds
  along `f` `μ`-almost everywhere.
-/

public section

open MeasureTheory

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- A measure positive on every singleton dominates every measure: a null set cannot contain
any point. No finiteness or countability assumption is needed. -/
theorem absolutelyContinuous_of_forall_singleton_ne_zero
    (hν : ∀ x : α, ν {x} ≠ 0) : μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun s _ hs ↦ ?_
  have hempty : s = ∅ := by
    apply Set.Subset.antisymm _ (Set.empty_subset s)
    intro y hy
    have hzero : ν {y} = 0 :=
      le_zero_iff.mp ((measure_mono (Set.singleton_subset_iff.mpr hy)).trans_eq hs)
    exact hν y hzero
  simp [hempty]

end TauCeti

namespace MeasureTheory

/-- If `μ.map f ≪ ν`, a property holding `ν`-almost everywhere holds at `f x` for `μ`-almost
every `x`. This generalizes `MeasureTheory.ae_eq_comp'` from equalities to arbitrary
properties. -/
theorem ae_comp_of_map_absolutelyContinuous {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : AEMeasurable f μ) (hmap : μ.map f ≪ ν)
    {P : β → Prop} (h : ∀ᵐ y ∂ν, P y) : ∀ᵐ x ∂μ, P (f x) :=
  ae_of_ae_map hf (hmap.ae_le h)

end MeasureTheory
