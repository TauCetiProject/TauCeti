/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

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
* `SSet.map_const_castSucc_of_δ_last`: the first `n + 1` vertices of an `(n + 1)`-simplex whose
  last face is constant at `x` are `x`.
* `SSet.map_const_succ_of_δ_zero`: the last `n + 1` vertices of an `(n + 1)`-simplex whose
  face opposite to the initial vertex is constant at `y` are `y`.
* `SSet.yonedaEquiv_const_one`, `SSet.const_app_one`: the constant map `Δ[1] ⟶ X` at a vertex
  `x` is the degenerate edge at `x`, and every constant map at `x` sends `1`-simplices to it.
* `SSet.lift_id_const_app_one`: the graph `W ⟶ W ⊗ X` of a constant map at `x` sends a
  `1`-simplex `e` to the pair of `e` and the degenerate edge at `x`.
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

/-- If the face of an `(n + 1)`-simplex `σ` opposite to its last vertex is the constant simplex
at a vertex `x`, then the vertex `j.castSucc` of `σ` is `x`, since it is the vertex `j` of that
face. -/
lemma map_const_castSucc_of_δ_last {n : ℕ} {σ : X _⦋n + 1⦌} {x : X _⦋0⦌}
    (hσ : X.δ (Fin.last (n + 1)) σ = X.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op x)
    (j : Fin (n + 1)) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ j.castSucc).op σ = x := by
  have h := congrArg (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j).op) hσ
  rw [SimplicialObject.δ_def, map_const_map, map_const_map] at h
  simpa [SimplexCategory.δ, Fin.succAbove_last] using h

/-- If the face of an `(n + 1)`-simplex `σ` opposite to its initial vertex is the constant simplex
at a vertex `y`, then the vertex `j.succ` of `σ` is `y`, since it is the vertex `j` of that face. -/
lemma map_const_succ_of_δ_zero {n : ℕ} {σ : X _⦋n + 1⦌} {y : X _⦋0⦌}
    (hσ : X.δ 0 σ = X.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op y) (j : Fin (n + 1)) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ j.succ).op σ = y := by
  have h := congrArg (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j).op) hσ
  rw [SimplicialObject.δ_def, map_const_map, map_const_map] at h
  simpa [SimplexCategory.δ, Fin.succAbove_zero] using h

/-- The constant map `Δ[1] ⟶ X` at a vertex `x` is the degenerate edge at `x`. -/
lemma yonedaEquiv_const_one (x : X _⦋0⦌) :
    yonedaEquiv (const x : Δ[1] ⟶ X) = (Edge.id x).edge := by
  rw [Edge.id_edge, ← comp_const (stdSimplex.σ 0), ← yonedaEquiv_symm_zero,
    stdSimplex.yonedaEquiv_σ_comp, Equiv.apply_symm_apply]

/-- A constant map at a vertex `x` sends every `1`-simplex to the degenerate edge at `x`. -/
lemma const_app_one {W : SSet.{u}} (x : X _⦋0⦌) (e : W _⦋1⦌) :
    (const x : W ⟶ X).app _ e = (Edge.id x).edge := by
  rw [← yonedaEquiv_const_one, ← comp_const (yonedaEquiv.symm e), yonedaEquiv_comp,
    Equiv.apply_symm_apply]

open MonoidalCategory CartesianMonoidalCategory in
/-- The graph `W ⟶ W ⊗ X` of a constant map at a vertex `x` sends a `1`-simplex `e` to the pair
of `e` and the degenerate edge at `x`. -/
lemma lift_id_const_app_one {W : SSet.{u}} (x : X _⦋0⦌) (e : W _⦋1⦌) :
    (lift (𝟙 W) (const x)).app _ e = (e, (Edge.id x).edge) :=
  -- A simplex of `W ⊗ X` is a pair, and the first component of the graph is the identity.
  Prod.ext rfl (const_app_one x e)

end SSet
