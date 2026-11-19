/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Irreducible

/-!
# The irreducible component through a point

Mathlib's `irreducibleComponent x` is a maximal irreducible set containing `x`. We bundle it as
an element `irreducibleComponentOf x` of `irreducibleComponents α`, giving a map from points to
irreducible components. When every point lies on a unique irreducible component, as in a scheme
whose stalks are integral domains, this map sends a point to the component containing it.
-/

public section

namespace TauCeti

variable {α : Type*} [TopologicalSpace α]

/-- An irreducible component containing the point `x`, namely Mathlib's
`irreducibleComponent x`, as an element of `irreducibleComponents α`. -/
noncomputable def irreducibleComponentOf (x : α) : irreducibleComponents α :=
  ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩

/-- A point lies on the irreducible component `irreducibleComponentOf x`. -/
@[simp]
theorem mem_irreducibleComponentOf (x : α) : x ∈ (irreducibleComponentOf x : Set α) :=
  mem_irreducibleComponent

end TauCeti
