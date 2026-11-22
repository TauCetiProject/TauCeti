/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Basic

/-!
# Separation properties in `T₁` spaces

In a `T₁` topological space, every specialization `x ⤳ y` is an equality (`specializes_iff_eq`), so
any map into a `T₁` space trivially lifts both generalizations and specializations without any
continuity assumption on the map. Furthermore, the complement of a point is open (`isOpen_ne`),
so the points where a continuous map into a `T₁` space avoids finitely many given values form an
open set.

## Main results

* `TauCeti.generalizingMap_of_t1Space`: any map into a `T₁` space is a `GeneralizingMap`.
* `TauCeti.specializingMap_of_t1Space`: any map into a `T₁` space is a `SpecializingMap`.
* `TauCeti.isOpen_forall_ne`: the points where a continuous map into a `T₁` space avoids finitely
  many values form an open set.
-/

public section

namespace TauCeti

section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y] {f : X → Y}

/-- Any map into a `T₁` space lifts generalizations, since specializations in the target are
equalities. -/
@[simp]
theorem generalizingMap_of_t1Space : GeneralizingMap f :=
  fun x _ hx ↦ ⟨x, specializes_rfl, (specializes_iff_eq.mp hx).symm⟩

/-- Any map into a `T₁` space lifts specializations, since specializations in the target are
equalities. -/
@[simp]
theorem specializingMap_of_t1Space : SpecializingMap f :=
  fun x _ hx ↦ ⟨x, specializes_rfl, specializes_iff_eq.mp hx⟩

end

/-- The points where a continuous map into a `T1Space` avoids finitely many values `c i` form an
open set. -/
theorem isOpen_forall_ne {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    [Finite ι] {f : X → Y} (hf : Continuous f) {c : ι → Y} :
    IsOpen {x : X | ∀ i, f x ≠ c i} := by
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun _ ↦ isOpen_ne.preimage hf

end TauCeti
