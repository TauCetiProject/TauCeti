/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
public import Mathlib.AlgebraicTopology.SimplexCategory.Rev
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# The join with a final vertex in the simplex category

This file defines the endofunctor `SimplexCategory.joinVertex : ⦋n⦌ ↦ ⦋n⦌ ⋆ ⦋0⦌ = ⦋n + 1⦌` of
`SimplexCategory`, the restriction of the join `- ⊗ ⦋0⦌` of `AugmentedSimplexCategory`. It
extends a monotone map by sending the final vertex to the final vertex, so it sends the coface
and codegeneracy maps `δ i` and `σ i` to `δ i.castSucc` and `σ i.castSucc`. The inclusion
`joinVertexInl m : m ⟶ m ⋆ ⦋0⦌` and the final vertex `joinVertexInr m : ⦋0⦌ ⟶ m ⋆ ⦋0⦌` are
natural in `m`. Its conjugate `SimplexCategory.vertexJoin : ⦋n⦌ ↦ ⦋0⦌ ⋆ ⦋n⦌ = ⦋n + 1⦌` by the
reversal `SimplexCategory.rev` joins an initial vertex instead, sending `δ i` and `σ i` to
`δ i.succ` and `σ i.succ`; the faces and degeneracies of `vertexJoin.op ⋙ X` are computed by
`SimplicialObject.vertexJoin_op_comp_δ` and `SimplicialObject.vertexJoin_op_comp_σ`.

For a simplicial object `X`, the simplicial object `joinVertex.op ⋙ X` has as `n`-simplices the
`(n + 1)`-simplices of `X`, with simplicial operators acting on the first `n + 1` vertices and
fixing the last one: its faces and degeneracies are computed by
`SimplicialObject.joinVertex_op_comp_δ` and `SimplicialObject.joinVertex_op_comp_σ`. This is the
simplicial object containing right mapping spaces and slices of simplicial sets.

## Main definitions

* `SimplexCategory.joinVertex`: the endofunctor `⦋n⦌ ↦ ⦋n⦌ ⋆ ⦋0⦌ = ⦋n + 1⦌` of `SimplexCategory`.
* `SimplexCategory.joinVertexInl`, `SimplexCategory.joinVertexInr`: the inclusion of `m` and of
  the final vertex into `m ⋆ ⦋0⦌`.
* `SimplexCategory.vertexJoin`: the endofunctor `⦋n⦌ ↦ ⦋0⦌ ⋆ ⦋n⦌ = ⦋n + 1⦌` of `SimplexCategory`.

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

/-- Collapsing `⦋n⦌` to its last vertex fixes the edge of `⦋n⦌ ⋆ ⦋0⦌` from that vertex to the
final vertex. -/
theorem mkOfSucc_last_comp_joinVertex_map {n : ℕ} :
    mkOfSucc (Fin.last n) ≫
        joinVertex.map (const ⦋n⦌ ⦋0⦌ 0 ≫ const ⦋0⦌ ⦋n⦌ (Fin.last n)) =
      mkOfSucc (Fin.last n) := by
  ext k : 3
  fin_cases k
  · exact (joinVertex_map_castSucc (m := ⦋n⦌) (n := ⦋n⦌) _ (Fin.last n) :)
  · exact (joinVertex_map_last (m := ⦋n⦌) (n := ⦋n⦌) _ :)

/-- Collapsing `⦋n⦌` to its last vertex sends an edge between two of the first `n + 1` vertices
of `⦋n⦌ ⋆ ⦋0⦌` to the last of these vertices. -/
theorem mkOfSucc_castSucc_comp_joinVertex_map {n : ℕ} (j : Fin n) :
    mkOfSucc j.castSucc ≫
        joinVertex.map (const ⦋n⦌ ⦋0⦌ 0 ≫ const ⦋0⦌ ⦋n⦌ (Fin.last n)) =
      const ⦋1⦌ ⦋n⦌ (Fin.last n) ≫ δ (Fin.last (n + 1)) := by
  ext k : 3
  fin_cases k
  · exact (joinVertex_map_castSucc (m := ⦋n⦌) (n := ⦋n⦌) _ j.castSucc :).trans (by simp [δ]; rfl)
  · exact (joinVertex_map_castSucc (m := ⦋n⦌) (n := ⦋n⦌) _ j.succ :).trans (by simp [δ]; rfl)

/-- The join `⦋0⦌ ⋆ m` with an initial vertex, as an endofunctor of `SimplexCategory`: the
conjugate of `joinVertex` by the reversal `rev`. It sends `⦋n⦌` to `⦋n + 1⦌` and extends a
monotone map by sending the initial vertex to the initial vertex. -/
-- The body is exposed so that `vertexJoin.obj ⦋n⦌` is definitionally `⦋n + 1⦌` downstream.
@[expose]
def vertexJoin : SimplexCategory ⥤ SimplexCategory :=
  rev ⋙ joinVertex ⋙ rev

@[simp]
theorem vertexJoin_obj (m : SimplexCategory) : vertexJoin.obj m = ⦋m.len + 1⦌ :=
  (rfl)

/-- The extension of `f` by an initial vertex fixes the initial vertex. -/
@[simp]
theorem vertexJoin_map_zero {m n : SimplexCategory} (f : m ⟶ n) :
    (vertexJoin.map f).toOrderHom 0 = 0 :=
  -- Reversal exchanges the initial vertex with the final vertex fixed by `joinVertex`.
  (congrArg Fin.rev (joinVertex_map_last (rev.map f))).trans (Fin.rev_last _)

/-- The extension of `f` by an initial vertex sends `i + 1` to `f i + 1`. -/
@[simp]
theorem vertexJoin_map_succ {m n : SimplexCategory} (f : m ⟶ n) (i : Fin (m.len + 1)) :
    (vertexJoin.map f).toOrderHom i.succ = (f.toOrderHom i).succ := by
  -- Reversal exchanges the shifts `succ` and `castSucc` handled by `joinVertex`.
  refine (congrArg (fun j ↦ ((joinVertex.map (rev.map f)).toOrderHom j).rev)
    (Fin.rev_succ i)).trans
      ((congrArg Fin.rev (joinVertex_map_castSucc (rev.map f) i.rev)).trans ?_)
  rw [rev_map_apply, Fin.rev_rev]
  exact (Fin.rev_castSucc _).trans (congrArg Fin.succ (Fin.rev_rev _))

/-- The join with an initial vertex preserves the initial vertex. -/
@[reassoc]
theorem const_zero_comp_vertexJoin_map {x : SimplexCategory} {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    const x ⦋m + 1⦌ 0 ≫ vertexJoin.map f = const x ⦋n + 1⦌ 0 :=
  (const_comp x (vertexJoin.map f) 0).trans (congrArg (const x ⦋n + 1⦌) (vertexJoin_map_zero f))

/-- The inclusion `δ 0 : m ⟶ ⦋0⦌ ⋆ m` of the face opposite to the initial vertex is natural. -/
@[reassoc]
theorem δ_zero_comp_vertexJoin_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    δ 0 ≫ vertexJoin.map f = f ≫ δ 0 := by
  ext i : 3
  exact vertexJoin_map_succ f i

/-- The join with an initial vertex sends the `i`-th coface map to the `(i + 1)`-th coface map. -/
@[simp]
theorem vertexJoin_map_δ {n : ℕ} (i : Fin (n + 2)) :
    vertexJoin.map (δ i) = δ i.succ := by
  ext j : 3
  cases j using Fin.cases with
  | zero => exact (vertexJoin_map_zero (δ i)).trans (Fin.succ_succAbove_zero i).symm
  | succ j => exact (vertexJoin_map_succ (δ i) j).trans (Fin.succ_succAbove_succ i j).symm

/-- The join with an initial vertex sends the `i`-th codegeneracy map to the `(i + 1)`-th
codegeneracy map. -/
@[simp]
theorem vertexJoin_map_σ {n : ℕ} (i : Fin (n + 1)) :
    vertexJoin.map (σ i) = σ i.succ := by
  ext j : 3
  cases j using Fin.cases with
  | zero => exact (vertexJoin_map_zero (σ i)).trans (Fin.predAbove_right_zero (i := i.succ)).symm
  | succ j => exact (vertexJoin_map_succ (σ i) j).trans (Fin.succ_predAbove_succ i j).symm

end SimplexCategory

namespace CategoryTheory.SimplicialObject

open SimplexCategory

variable {C : Type*} [Category* C] (X : SimplicialObject C)

/-- The faces of `joinVertex.op ⋙ X` are the faces of `X` omitting a vertex other than the last
one, so containing the last vertex. -/
theorem joinVertex_op_comp_δ {n : ℕ} (i : Fin (n + 2)) :
    δ (joinVertex.op ⋙ X) i = X.δ i.castSucc :=
  congrArg (fun f ↦ X.map (Quiver.Hom.op f)) (joinVertex_map_δ i)

/-- The degeneracies of `joinVertex.op ⋙ X` are the degeneracies of `X` repeating a vertex other
than the last one. -/
theorem joinVertex_op_comp_σ {n : ℕ} (i : Fin (n + 1)) :
    σ (joinVertex.op ⋙ X) i = X.σ i.castSucc :=
  congrArg (fun f ↦ X.map (Quiver.Hom.op f)) (joinVertex_map_σ i)

/-- The faces of `vertexJoin.op ⋙ X` are the faces of `X` omitting a vertex after the first one,
so containing the first vertex. -/
theorem vertexJoin_op_comp_δ {n : ℕ} (i : Fin (n + 2)) :
    δ (vertexJoin.op ⋙ X) i = X.δ i.succ :=
  congrArg (fun f ↦ X.map (Quiver.Hom.op f)) (vertexJoin_map_δ i)

/-- The degeneracies of `vertexJoin.op ⋙ X` are the degeneracies of `X` repeating a vertex after
the first one. -/
theorem vertexJoin_op_comp_σ {n : ℕ} (i : Fin (n + 1)) :
    σ (vertexJoin.op ⋙ X) i = X.σ i.succ :=
  congrArg (fun f ↦ X.map (Quiver.Hom.op f)) (vertexJoin_map_σ i)

end CategoryTheory.SimplicialObject
