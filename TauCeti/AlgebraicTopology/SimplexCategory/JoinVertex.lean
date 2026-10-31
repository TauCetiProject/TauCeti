/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# The join with a final vertex in the simplex category

This file defines the endofunctor `SimplexCategory.joinVertex : ⦋n⦌ ↦ ⦋n⦌ ⋆ ⦋0⦌ = ⦋n + 1⦌` of
`SimplexCategory`, the restriction of the join `- ⊗ ⦋0⦌` of `AugmentedSimplexCategory`. It
extends a monotone map by sending the final vertex to the final vertex, so it sends the coface
and codegeneracy maps `δ i` and `σ i` to `δ i.castSucc` and `σ i.castSucc`. The inclusion
`joinVertexInl m : m ⟶ m ⋆ ⦋0⦌` and the final vertex `joinVertexInr m : ⦋0⦌ ⟶ m ⋆ ⦋0⦌` are
natural in `m`.

For a simplicial object `X`, the simplicial object `joinVertex.op ⋙ X` has as `n`-simplices the
`(n + 1)`-simplices of `X`, with simplicial operators acting on the first `n + 1` vertices and
fixing the last one: its faces and degeneracies are computed by
`SimplicialObject.joinVertex_op_comp_δ` and `SimplicialObject.joinVertex_op_comp_σ`. This is the
simplicial object containing right mapping spaces and slices of simplicial sets.

## Main definitions

* `SimplexCategory.joinVertex`: the endofunctor `⦋n⦌ ↦ ⦋n⦌ ⋆ ⦋0⦌ = ⦋n + 1⦌` of `SimplexCategory`.
* `SimplexCategory.joinVertexInl`, `SimplexCategory.joinVertexInr`: the inclusion of `m` and of
  the final vertex into `m ⋆ ⦋0⦌`.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.8 (joins of simplicial sets).
-/

public section

open CategoryTheory Opposite Simplicial AugmentedSimplexCategory

namespace SimplexCategory

/-- A morphism out of `⦋m.len + 1⦌` is determined by its values on the first `m.len + 1`
vertices and on the last vertex. -/
theorem hom_ext_castSucc_last {m n : SimplexCategory} {f g : ⦋m.len + 1⦌ ⟶ n}
    (h : ∀ i : Fin (m.len + 1), f.toOrderHom i.castSucc = g.toOrderHom i.castSucc)
    (h' : f.toOrderHom (Fin.last _) = g.toOrderHom (Fin.last _)) : f = g := by
  ext i : 3
  cases i using Fin.lastCases
  exacts [h', h _]

/-- The extension of `f` to the joins with a final vertex sends `i` to `f i`. -/
private theorem tensorHomOf_castSucc {m n : SimplexCategory} (f : m ⟶ n) (i : Fin (m.len + 1)) :
    (tensorHomOf f (𝟙 ⦋0⦌)).toOrderHom i.castSucc = (f.toOrderHom i).castSucc := by
  ext
  simp [tensorHomOf, Fin.addCases]

/-- The extension of `f` to the joins with a final vertex fixes the final vertex. -/
private theorem tensorHomOf_last {m n : SimplexCategory} (f : m ⟶ n) :
    (tensorHomOf f (𝟙 ⦋0⦌)).toOrderHom (Fin.last (m.len + 1)) = Fin.last (n.len + 1) := by
  ext
  simp [tensorHomOf, Fin.addCases]

/-- The join `m ⋆ ⦋0⦌` with a final vertex, as an endofunctor of `SimplexCategory`: the
restriction of the join `- ⊗ ⦋0⦌` of `AugmentedSimplexCategory`. It sends `⦋n⦌` to `⦋n + 1⦌` and
extends a monotone map by sending the final vertex to the final vertex. -/
-- The body of `joinVertex` is exposed so that `joinVertex.obj ⦋n⦌` is definitionally `⦋n + 1⦌`
-- downstream: the simplices of `joinVertex.op ⋙ X` are then literally simplices of `X`, so its
-- subcomplexes can be described by face and vertex conditions in `X`. The functor laws are those
-- of the join, which hold here by definitional unfolding of `tensorHom` on `.of` objects.
@[expose]
def joinVertex : SimplexCategory ⥤ SimplexCategory where
  obj m := ⦋m.len + 1⦌
  map f := tensorHomOf f (𝟙 ⦋0⦌)
  map_id m := tensor_id (WithInitial.of m) (WithInitial.of ⦋0⦌)
  map_comp {a b c} f g := (tensorHom_comp_tensorHom (x₁ := WithInitial.of a)
    (y₁ := WithInitial.of b) (z₁ := WithInitial.of c) (x₂ := WithInitial.of ⦋0⦌)
    (y₂ := WithInitial.of ⦋0⦌) (z₂ := WithInitial.of ⦋0⦌) f (𝟙 _) g (𝟙 _)).symm

@[simp]
theorem joinVertex_obj (m : SimplexCategory) : joinVertex.obj m = ⦋m.len + 1⦌ :=
  (rfl)

@[simp]
theorem joinVertex_map_castSucc {m n : SimplexCategory} (f : m ⟶ n) (i : Fin (m.len + 1)) :
    (joinVertex.map f).toOrderHom i.castSucc = (f.toOrderHom i).castSucc :=
  tensorHomOf_castSucc f i

@[simp]
theorem joinVertex_map_last {m n : SimplexCategory} (f : m ⟶ n) :
    (joinVertex.map f).toOrderHom (Fin.last (m.len + 1)) = Fin.last (n.len + 1) :=
  tensorHomOf_last f

/-- The join with a final vertex sends the `i`-th coface map to the `i`-th coface map. -/
@[simp]
theorem joinVertex_map_δ {n : ℕ} (i : Fin (n + 2)) :
    joinVertex.map (δ i) = δ i.castSucc :=
  hom_ext_castSucc_last (m := ⦋n⦌)
    (fun j ↦ (joinVertex_map_castSucc (δ i) j).trans Fin.castSucc_succAbove_castSucc.symm)
    ((joinVertex_map_last (δ i)).trans
      (Fin.succAbove_ne_last_last (Fin.castSucc_lt_last i).ne).symm)

/-- The join with a final vertex sends the `i`-th codegeneracy map to the `i`-th codegeneracy
map. -/
@[simp]
theorem joinVertex_map_σ {n : ℕ} (i : Fin (n + 1)) :
    joinVertex.map (σ i) = σ i.castSucc :=
  hom_ext_castSucc_last (m := ⦋n + 1⦌)
    (fun j ↦ (joinVertex_map_castSucc (σ i) j).trans (Fin.castSucc_predAbove_castSucc i j).symm)
    ((joinVertex_map_last (σ i)).trans Fin.predAbove_right_last.symm)

/-- The inclusion of `m` into `m ⋆ ⦋0⦌` as the face opposite to the final vertex. -/
def joinVertexInl (m : SimplexCategory) : m ⟶ joinVertex.obj m :=
  δ (Fin.last (m.len + 1))

/-- The final vertex of `m ⋆ ⦋0⦌`. -/
def joinVertexInr (m : SimplexCategory) : ⦋0⦌ ⟶ joinVertex.obj m :=
  const ⦋0⦌ ⦋m.len + 1⦌ (Fin.last _)

/-- On `⦋n⦌`, the inclusion into the join with a final vertex is the last coface map. -/
@[simp]
theorem joinVertexInl_mk (n : ℕ) : joinVertexInl ⦋n⦌ = δ (Fin.last (n + 1)) :=
  (rfl)

/-- On `⦋n⦌`, the final vertex of the join is the vertex `n + 1` of `⦋n + 1⦌`. -/
@[simp]
theorem joinVertexInr_mk (n : ℕ) : joinVertexInr ⦋n⦌ = const ⦋0⦌ ⦋n + 1⦌ (Fin.last _) :=
  (rfl)

/-- The inclusion `m ⟶ m ⋆ ⦋0⦌` is natural in `m`. -/
@[reassoc]
theorem joinVertexInl_comp_joinVertex_map {m n : SimplexCategory} (f : m ⟶ n) :
    joinVertexInl m ≫ joinVertex.map f = f ≫ joinVertexInl n := by
  ext i : 3
  exact (congrArg (joinVertex.map f).toOrderHom (Fin.succAbove_last_apply i)).trans
    ((joinVertex_map_castSucc f i).trans (Fin.succAbove_last_apply _).symm)

/-- The join with a final vertex preserves the final vertex. -/
@[reassoc (attr := simp)]
theorem joinVertexInr_comp_joinVertex_map {m n : SimplexCategory} (f : m ⟶ n) :
    joinVertexInr m ≫ joinVertex.map f = joinVertexInr n :=
  Hom.ext_zero_left _ _ (joinVertex_map_last f)

/-- A coface map avoiding the last vertex preserves the final vertex of the join. -/
theorem joinVertexInr_comp_δ_castSucc {n : ℕ} (i : Fin (n + 2)) :
    joinVertexInr ⦋n⦌ ≫ δ i.castSucc = joinVertexInr ⦋n + 1⦌ :=
  (congrArg _ (joinVertex_map_δ i)).symm.trans (joinVertexInr_comp_joinVertex_map (δ i))

end SimplexCategory

namespace CategoryTheory.SimplicialObject

open SimplexCategory

variable {C : Type*} [Category* C] (X : SimplicialObject C)

/-- The faces of `joinVertex.op ⋙ X` are the faces of `X` avoiding the last vertex. -/
theorem joinVertex_op_comp_δ {n : ℕ} (i : Fin (n + 2)) :
    δ (joinVertex.op ⋙ X) i = X.δ i.castSucc :=
  congrArg (fun f ↦ X.map (Quiver.Hom.op f)) (joinVertex_map_δ i)

/-- The degeneracies of `joinVertex.op ⋙ X` are the degeneracies of `X` fixing the last
vertex. -/
theorem joinVertex_op_comp_σ {n : ℕ} (i : Fin (n + 1)) :
    σ (joinVertex.op ⋙ X) i = X.σ i.castSucc :=
  congrArg (fun f ↦ X.map (Quiver.Hom.op f)) (joinVertex_map_σ i)

end CategoryTheory.SimplicialObject
