/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Naturality of the singular simplices of a space

The identification of the `n`-simplices of the singular simplicial set of `X` with the continuous
maps from the topological `n`-simplex to `X` turns the map induced by a continuous map into
postcomposition with it.  In degree zero this identifies points with singular zero-simplices,
which transfers naturality of simplicial vertex classes to singular homology, giving naturality
of the basepoint section of the augmentation in `TauCeti.singularHomology₀Section_naturality`.
-/

public section

open CategoryTheory Simplicial

universe u

namespace TauCeti.TopCat

/-- Mapping the singular vertex of a point gives the singular vertex of its image. -/
@[simp]
lemma toSSet_map_app_toSSetObj₀Equiv_symm {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    (TopCat.toSSet.map f).app (Opposite.op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm (f x) := rfl

/-- The map of singular simplicial sets induced by a continuous map is postcomposition with that
map, read through the identification of singular simplices with continuous maps out of the
topological simplex. -/
@[simp]
lemma toSSetObjEquiv_toSSet_map_app {X Y : TopCat.{u}} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj X).obj n) :
    TopCat.toSSetObjEquiv Y n ((TopCat.toSSet.map f).app n x) =
      f.hom.comp (TopCat.toSSetObjEquiv X n x) := rfl

end TauCeti.TopCat
