/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Order.Disjointed

/-!
# Measurability of disjointed families

Generalizes Mathlib's `MeasurableSet.disjointed` from `ℕ`-indexed families to families indexed by
any locally finite preorder with bottom (`TauCeti.measurableSet_disjointed`), including `Fin n`.
-/

public section

namespace TauCeti

/-- Disjointing a family of measurable sets indexed by a locally finite preorder with bottom
preserves measurability. -/
@[measurability]
theorem measurableSet_disjointed {α ι : Type*} [MeasurableSpace α]
    [Preorder ι] [LocallyFiniteOrderBot ι] {f : ι → Set α}
    (h : ∀ i, MeasurableSet (f i)) (i : ι) : MeasurableSet (disjointed f i) :=
  disjointedRec (fun _ _ ht ↦ ht.diff (h _)) (h i)

end TauCeti
