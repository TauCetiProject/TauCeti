/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularSet
public import TauCeti.Geometry.Convex.ConvexSpace.ContractibleSpaceStdSimplex
public import TauCeti.Geometry.Convex.ConvexSpace.LocallyPathConnectedSpaceStdSimplex

/-!
# The topological simplices and the singular simplices of a space

The topological `n`-simplex is a standard simplex on a finite nonempty type, up to a universe
lift, hence contractible and in particular simply connected, and locally path connected.  This
file also names its initial vertex, and the continuous map on the topological `n`-simplex that
underlies a singular `n`-simplex of a space.

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

/-- Every topological simplex is locally path connected, being a universe lift of a standard
simplex on a finite type. -/
instance locallyPathConnectedSpace (n : SimplexCategory) :
    LocallyPathConnectedSpace (toTop.{u}.obj n) :=
  (Homeomorph.ulift (X := StdSimplex ℝ (Fin (n.len + 1)))).symm.locallyPathConnectedSpace

/-- The initial vertex of the topological `n`-simplex: the universe lift of the standard-simplex
vertex `StdSimplex.single 0`. -/
noncomputable def toTopInitialVertex (n : SimplexCategory) : toTop.{u}.obj n :=
  ULift.up (StdSimplex.single 0)

/-- The initial vertex of the topological `n`-simplex lifts the standard-simplex vertex
`StdSimplex.single 0`. -/
@[simp]
lemma toTopInitialVertex_down (n : SimplexCategory) :
    (toTopInitialVertex.{u} n).down = StdSimplex.single 0 := (rfl)

/-- A map of topological simplices carries the initial vertex to the vertex indexed by
its value at zero. -/
-- Compute the vertex image before `toTop_map` unfolds the inner map.
@[simp↓]
lemma toTop_map_toTopInitialVertex_down {m n : SimplexCategory} (α : m ⟶ n) :
    (toTop.{u}.map α (toTopInitialVertex m)).down = StdSimplex.single (α.toOrderHom 0) := by
  -- The lifted affine map is read in standard-simplex coordinates.
  rw [toTop_map]
  change StdSimplex.map α.toOrderHom (toTopInitialVertex.{u} m).down = _
  rw [toTopInitialVertex_down, StdSimplex.map_single]

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

/-- A singular simplex is determined by its underlying continuous map. -/
lemma simplexMap_injective :
    Function.Injective (simplexMap : (TopCat.toSSet.obj X).obj n → _) := by
  intro σ τ h
  exact ULift.ext (ConcreteCategory.hom_injective h)

/-- Every continuous map on the topological simplex underlies a singular simplex. -/
lemma simplexMap_surjective :
    Function.Surjective (simplexMap : (TopCat.toSSet.obj X).obj n → _) :=
  fun f ↦ ⟨ULift.up (TopCat.ofHom f), rfl⟩

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

namespace TauCeti

open Simplicial

/-- The topological `n`-simplex, the model of the simplicial singular chains in degree `n`. -/
noncomputable abbrev simplexModel (n : ℕ) : TopCat.{u} := SimplexCategory.toTop.{u}.obj ⦋n⦌

/-- The identity singular simplex of the topological simplex. -/
noncomputable def idSimplex (n : ℕ) : (TopCat.toSSet.obj (simplexModel.{u} n)) _⦋n⦌ :=
  ULift.up (𝟙 _)

/-- A singular simplex is the push-forward of the identity simplex along itself. -/
theorem toSSet_map_down_idSimplex {X : TopCat.{u}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.map σ.down).app _ (idSimplex n) = σ := by
  apply TopCat.simplexMap_injective
  rw [TopCat.simplexMap_app]
  rfl

end TauCeti
