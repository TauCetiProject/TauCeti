/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplexCategory.JoinVertex
public import TauCeti.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# Contractions of simplicial sets shifted by a joined vertex

The simplicial sets `joinVertex.op ⋙ X` and `vertexJoin.op ⋙ X` contract towards their
last and initial vertices respectively. The cylinder maps restrict simplices along the
ordinal collapse maps and commute with every simplicial restriction.

* `SSet.joinVertexContraction` is the identity at time zero.
* `SSet.vertexJoinContraction` is the identity at time one.
* Their `*_app_apply` lemmas evaluate them without unfolding their definitions.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite Simplicial SimplexCategory

universe u

namespace SSet

variable {X : SSet.{u}}

variable (X) in
/-- The contraction of `joinVertex.op ⋙ X` towards the last vertices: the simplex `(σ, e)` of
`(joinVertex.op ⋙ X) ⊗ Δ[1]` goes to the restriction of `σ` along `joinVertexCollapse e`. -/
noncomputable def joinVertexContraction : (joinVertex.op ⋙ X) ⊗ Δ[1] ⟶ joinVertex.op ⋙ X where
  app m := TypeCat.ofHom fun z ↦
    X.map (joinVertexCollapse (n := m.unop.len) (stdSimplex.objEquiv z.2)).op z.1
  naturality m m' f := by
    obtain ⟨⟨a⟩⟩ := m
    obtain ⟨⟨b⟩⟩ := m'
    ext z
    -- Simplices of `joinVertex.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
    change X.map (joinVertexCollapse (f.unop ≫ stdSimplex.objEquiv z.2)).op
        (X.map (joinVertex.map f.unop).op z.1) =
      X.map (joinVertex.map f.unop).op (X.map (joinVertexCollapse (stdSimplex.objEquiv z.2)).op z.1)
    have h := congrArg (fun g ↦ X.map g.op z.1)
      (joinVertexCollapse_comp_joinVertex_map f.unop (stdSimplex.objEquiv z.2))
    simp only [op_comp, Functor.map_comp_apply] at h
    exact h

/-- Evaluation of the join contraction on a pair of simplices. -/
@[simp]
lemma joinVertexContraction_app_apply {n : ℕ}
    (z : ((joinVertex.op ⋙ X) ⊗ Δ[1]).obj (op ⦋n⦌)) :
    dsimp% (joinVertexContraction X).app _ z =
      X.map (joinVertexCollapse (stdSimplex.objEquiv z.2)).op z.1 :=
  (rfl)

/-- The identity endpoint of the join contraction. -/
@[reassoc]
lemma ι₀_joinVertexContraction : ι₀ ≫ joinVertexContraction X = 𝟙 _ := by
  ext ⟨⟨n⟩⟩ σ
  have he : stdSimplex.objEquiv (ι₀.app _ σ).2 = SimplexCategory.const ⦋n⦌ ⦋1⦌ 0 := by
    ext i : 3
    exact SSet.ι₀_app_snd_apply σ i
  have h := joinVertexContraction_app_apply (X := X) (n := n) (ι₀.app _ σ)
  rw [he, joinVertexCollapse_const_zero, op_id, CategoryTheory.Functor.map_id] at h
  exact h.trans (SSet.ι₀_app_fst σ)

variable (X) in
/-- The contraction of `vertexJoin.op ⋙ X` towards the initial vertices: the simplex `(σ, e)` of
`(vertexJoin.op ⋙ X) ⊗ Δ[1]` goes to the restriction of `σ` along `vertexJoinCollapse e`. -/
noncomputable def vertexJoinContraction : (vertexJoin.op ⋙ X) ⊗ Δ[1] ⟶ vertexJoin.op ⋙ X where
  app m := TypeCat.ofHom fun z ↦
    X.map (vertexJoinCollapse (n := m.unop.len) (stdSimplex.objEquiv z.2)).op z.1
  naturality m m' f := by
    obtain ⟨⟨a⟩⟩ := m
    obtain ⟨⟨b⟩⟩ := m'
    ext z
    -- Simplices of `vertexJoin.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
    change X.map (vertexJoinCollapse (f.unop ≫ stdSimplex.objEquiv z.2)).op
        (X.map (vertexJoin.map f.unop).op z.1) =
      X.map (vertexJoin.map f.unop).op (X.map (vertexJoinCollapse (stdSimplex.objEquiv z.2)).op z.1)
    have h := congrArg (fun g ↦ X.map g.op z.1)
      (vertexJoinCollapse_comp_vertexJoin_map f.unop (stdSimplex.objEquiv z.2))
    simp only [op_comp, Functor.map_comp_apply] at h
    exact h

/-- Evaluation of the join contraction on a pair of simplices. -/
@[simp]
lemma vertexJoinContraction_app_apply {n : ℕ}
    (z : ((vertexJoin.op ⋙ X) ⊗ Δ[1]).obj (op ⦋n⦌)) :
    dsimp% (vertexJoinContraction X).app _ z =
      X.map (vertexJoinCollapse (stdSimplex.objEquiv z.2)).op z.1 :=
  (rfl)

/-- The identity endpoint of the join contraction. -/
@[reassoc]
lemma ι₁_vertexJoinContraction : ι₁ ≫ vertexJoinContraction X = 𝟙 _ := by
  ext ⟨⟨n⟩⟩ σ
  have he : stdSimplex.objEquiv (ι₁.app _ σ).2 = SimplexCategory.const ⦋n⦌ ⦋1⦌ 1 := by
    ext i : 3
    exact SSet.ι₁_app_snd_apply σ i
  have h := vertexJoinContraction_app_apply (X := X) (n := n) (ι₁.app _ σ)
  rw [he, vertexJoinCollapse_const_one, op_id, CategoryTheory.Functor.map_id] at h
  exact h.trans (SSet.ι₁_app_fst σ)

end SSet
