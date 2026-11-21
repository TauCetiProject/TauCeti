/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Basic

/-!
# Specializing and generalizing maps into `T₁` spaces

In a `T₁` topological space, every specialization `x ⤳ y` is an equality (`specializes_iff_eq`), so
any map into a `T₁` space trivially lifts both generalizations and specializations without any
continuity assumption on the map.

## Main results

* `TauCeti.generalizingMap_of_t1Space`: any map into a `T₁` space is a `GeneralizingMap`.
* `TauCeti.specializingMap_of_t1Space`: any map into a `T₁` space is a `SpecializingMap`.
-/

public section

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y] {f : X → Y}

/-- Any map into a `T₁` space lifts generalizations, since specializations in the target are
equalities. -/
theorem generalizingMap_of_t1Space : GeneralizingMap f :=
  fun x _ hx ↦ ⟨x, specializes_rfl, (specializes_iff_eq.mp hx).symm⟩

/-- Any map into a `T₁` space lifts specializations, since specializations in the target are
equalities. -/
theorem specializingMap_of_t1Space : SpecializingMap f :=
  fun x _ hx ↦ ⟨x, specializes_rfl, specializes_iff_eq.mp hx⟩

end TauCeti
