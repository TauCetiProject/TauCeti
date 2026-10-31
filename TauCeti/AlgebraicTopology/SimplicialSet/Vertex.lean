/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

/-!
# Vertices of simplices

The `i`-th vertex of an `n`-simplex `s` of a simplicial set `X` is its image
`X.map (SimplexCategory.const ⦋0⦌ n i).op s` under the map `⦋0⦌ ⟶ ⦋n⦌` picking `i`. The vertices of
the image of `s` under a simplicial operator are vertices of `s`, and any two vertices `i ≤ j` of
`s` span an edge of `X`. Consequently a map on vertices that is monotone along the edges of `X` is
monotone along the vertices of every simplex.

## Main results

* `SSet.map_const_map`: the vertices of the image of a simplex under a simplicial operator.
* `SSet.monotone_map_const`: a map on vertices that is monotone along edges is monotone along the
  vertices of each simplex.
-/

public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet

variable {X : SSet.{u}}

/-- The `i`-th vertex of the image of a simplex `s` under `X.map f` is the `f i`-th vertex
of `s`. -/
lemma map_const_map {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (s : X.obj n)
    (i : Fin (m.unop.len + 1)) :
    X.map (SimplexCategory.const ⦋0⦌ m.unop i).op (X.map f s) =
      X.map (SimplexCategory.const ⦋0⦌ n.unop (f.unop.toOrderHom i)).op s := by
  rw [← Functor.map_comp_apply, ← Quiver.Hom.op_unop f, ← op_comp, SimplexCategory.const_comp]
  rfl

/-- A map on vertices that is monotone along edges is monotone along the vertices of each
simplex, since any two vertices of a simplex span an edge. -/
lemma monotone_map_const {P : Type*} [Preorder P] (g : X _⦋0⦌ → P)
    (hg : ∀ ⦃x y⦄, X.Edge x y → g x ≤ g y) {n : SimplexCategoryᵒᵖ} (s : X.obj n) :
    Monotone fun i ↦ g (X.map (SimplexCategory.const ⦋0⦌ n.unop i).op s) := by
  intro i j h
  refine hg (SSet.Edge.mk (X.map (SimplexCategory.mkOfLe i j h).op s) ?_ ?_) <;>
  · rw [SimplicialObject.δ, ← Functor.map_comp_apply, ← op_comp]
    congr 3
    ext a
    fin_cases a
    rfl

end SSet
