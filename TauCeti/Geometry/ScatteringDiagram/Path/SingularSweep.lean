/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Sweep
public import TauCeti.Geometry.ScatteringDiagram.SingularSupport.PolyhedralComplex

/-!
# Avoiding the singular support of a complex's walls

A base point generic for the codimension-two sweep arrangement gives lines
that avoid the wall singular support in every prescribed direction.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/Discriminant.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : Toric.IsIntegralLattice i}

/-- A full line in a prescribed direction avoids the wall singular support when its
base point is outside the codimension-two sweep arrangement for those directions. -/
theorem add_smul_notMem_singularSupport_walls {C : FinitePolyhedralComplex h}
    {vectors : Finset V} {x v : V}
    (hx : (C.codimensionGESweepExceptions (k := 2) le_rfl vectors).IsGeneric x)
    (hv : v ∈ vectors) (t : ℝ) : x + t • v ∉ singularSupport (Subtype.val : C.walls → Set V) :=
  fun hxsing => add_smul_notMem_support_codimensionGE hx hv t
    (C.singularSupport_cellsOfCodimension_subset_support_codimensionGE_succ (k := 1) hxsing)

end TauCeti.FinitePolyhedralComplex
