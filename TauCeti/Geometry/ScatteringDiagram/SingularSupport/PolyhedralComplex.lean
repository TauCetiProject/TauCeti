/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Skeleton
public import TauCeti.Geometry.ScatteringDiagram.SingularSupport.Basic

/-!
# Singular supports of codimension strata

The relative boundaries of the cells of an exact-codimension stratum and the
nonempty intersections of pairs with different supporting directions lie in the
next skeleton.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/Strata.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : Toric.IsIntegralLattice i}

/-- The singular support of the exact-codimension-`k` cells is carried by the next skeleton.
Any set disjoint from the support of the next skeleton is therefore disjoint from this
stratum's singular support. -/
theorem singularSupport_cellsOfCodimension_subset_support_codimensionGE_succ
    (C : FinitePolyhedralComplex h) {k : ℕ} :
    singularSupport (Subtype.val : C.cellsOfCodimension k → Set V) ⊆
      (C.codimensionGE (k + 1)).support := by
  intro x hx
  rcases mem_singularSupport.mp hx with ⟨P, hxP⟩ | ⟨P, Q, hne, hxP, hxQ⟩
  · exact C.intrinsicFrontier_subset_support_codimensionGE_succ
      (C.cellsOfCodimension_subset_cells_codimensionGE k P.property) hxP
  · have hPQ : P.val ≠ Q.val := fun he => hne (congrArg (fun S => (affineSpan ℝ S).direction) he)
    exact mem_support.mpr ⟨P.val ∩ Q.val,
      C.inter_mem_cells_codimensionGE_succ
        (C.cellsOfCodimension_subset_cells_codimensionGE k P.property)
        (C.cellsOfCodimension_subset_cells_codimensionGE k Q.property) hPQ ⟨x, hxP, hxQ⟩, hxP, hxQ⟩

end TauCeti.FinitePolyhedralComplex
