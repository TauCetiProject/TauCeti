/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Topology.Sober

/-!
# Separation of generic points

Distinct generic points of irreducible components of a T₀ space do not specialize to one
another. This allows affine neighbourhoods to isolate prescribed generic points.
-/

public section

variable {X : Type*} [TopologicalSpace X]

/-- If `x` and `y` are distinct generic points of irreducible components, then `x` does not lie in
the closure of `y`: otherwise the component of `x` would be contained in the component of `y`,
hence equal to it by maximality. -/
theorem genericPoints.notMem_closure_of_ne [T0Space X] {x y : X} (hx : x ∈ genericPoints X)
    (hy : y ∈ genericPoints X) (hxy : x ≠ y) : x ∉ _root_.closure ({y} : Set X) := by
  intro hmem
  have hle : _root_.closure ({x} : Set X) ⊆ _root_.closure ({y} : Set X) :=
    closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure
  exact hxy (isGenericPoint_closure.eq (hle.antisymm (hx.2 hy.1 hle)).symm)
