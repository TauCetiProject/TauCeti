/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularSet
public import TauCeti.Geometry.Convex.ConvexSpace.ContractibleSpaceStdSimplex

/-!
# The topological simplices and the singular simplices of a space

The topological `n`-simplex is a standard simplex on a finite nonempty type, up to a universe
lift, hence contractible and in particular simply connected.  This file also names its initial
vertex, and the continuous map on the topological `n`-simplex that underlies a singular
`n`-simplex of a space.

## Main declarations

* `SimplexCategory.toTopInitialVertex`: the initial vertex of the topological `n`-simplex.
* `TauCeti.TopCat.simplexMap`: the continuous map underlying a singular simplex.
-/

public section

open CategoryTheory Convexity

universe u

namespace SimplexCategory

/-- Every topological simplex is contractible, being a universe lift of a standard simplex on a
finite nonempty type. -/
instance contractibleSpace (n : SimplexCategory) : ContractibleSpace (toTop.{u}.obj n) :=
  (Homeomorph.ulift (X := StdSimplex ℝ (Fin (n.len + 1)))).contractibleSpace

/-- The initial vertex of the topological `n`-simplex: the universe lift of the standard-simplex
vertex `StdSimplex.single 0`. -/
noncomputable def toTopInitialVertex (n : SimplexCategory) : toTop.{u}.obj n :=
  ULift.up (StdSimplex.single 0)

/-- The initial vertex of the topological `n`-simplex lifts the standard-simplex vertex
`StdSimplex.single 0`. -/
@[simp]
lemma toTopInitialVertex_down (n : SimplexCategory) :
    (toTopInitialVertex.{u} n).down = StdSimplex.single 0 := (rfl)

end SimplexCategory

namespace TauCeti.TopCat

variable {X Y : TopCat.{u}} {m n : SimplexCategoryᵒᵖ}

/-- The continuous map underlying a singular simplex, defined on the topological simplex
`SimplexCategory.toTop.obj n.unop` rather than on the unlifted model used by
`TopCat.toSSetObjEquiv`, so that it composes directly with the maps `SimplexCategory.toTop.map`. -/
-- The body must stay exposed: the endpoints of a transport inside a simplex, as they appear in
-- `TauCeti.LocalCoefficientSystem.pathTransport_map` and `map_pathTransport`, agree only
-- definitionally, so without it those statements are not type-correct.
@[expose]
noncomputable def simplexMap (σ : (TopCat.toSSet.obj X).obj n) :
    C(SimplexCategory.toTop.{u}.obj n.unop, X) := σ.down.hom

/-- Reindexing a singular simplex precomposes the underlying continuous map with the induced map
of topological simplices. -/
@[simp]
lemma simplexMap_map (α : m ⟶ n) (σ : (TopCat.toSSet.obj X).obj m) :
    simplexMap ((TopCat.toSSet.obj X).map α σ) =
      (simplexMap σ).comp (SimplexCategory.toTop.map α.unop).hom := rfl

/-- Pushing a singular simplex forward along a continuous map postcomposes the underlying
continuous map with that map. -/
@[simp]
lemma simplexMap_app (f : X ⟶ Y) (σ : (TopCat.toSSet.obj X).obj n) :
    simplexMap ((TopCat.toSSet.map f).app n σ) = f.hom.comp (simplexMap σ) := rfl

end TauCeti.TopCat
