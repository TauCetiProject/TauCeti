/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Naturality of singular simplices

The identification of singular simplices with continuous maps from standard simplices commutes
with continuous maps, which act by postcomposition; in particular, so does the identification of
points with singular zero-simplices.
This transfers naturality of simplicial vertex classes to singular homology, giving naturality
of the basepoint section of the augmentation in `TauCeti.singularHomology₀Section_naturality`.
-/

public section

open CategoryTheory Simplicial Convexity

universe u

namespace TauCeti.TopCat

/-- Mapping the singular vertex of a point gives the singular vertex of its image. -/
@[simp]
lemma toSSet_map_app_toSSetObj₀Equiv_symm {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    (TopCat.toSSet.map f).app (Opposite.op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm (f x) := rfl

/-- The map of singular simplicial sets induced by a continuous map acts on singular simplices
by postcomposition. -/
@[simp]
lemma toSSetObjEquiv_toSSet_map_app {X Y : TopCat.{u}} (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n) :
    Y.toSSetObjEquiv n ((TopCat.toSSet.map f).app n σ) =
      (ConcreteCategory.hom f).comp (X.toSSetObjEquiv n σ) := rfl

/-- The map of singular simplicial sets induced by a continuous map sends the singular simplex
of a continuous map `g` from a standard simplex to that of its composite with the map. -/
@[simp]
lemma toSSet_map_app_toSSetObjEquiv_symm {X Y : TopCat.{u}} (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ}
    (g : C(StdSimplex ℝ (Fin (n.unop.len + 1)), X)) :
    (TopCat.toSSet.map f).app n ((X.toSSetObjEquiv n).symm g) =
      (Y.toSSetObjEquiv n).symm ((ConcreteCategory.hom f).comp g) := rfl

end TauCeti.TopCat
