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
* Their other endpoints evaluate the distinguished vertex and take its total degeneracy,
  through `joinVertexEvaluation`/`vertexJoinEvaluation` and
  `joinVertexDegeneracy`/`vertexJoinDegeneracy`.
* Their `*_app_apply` lemmas evaluate them without unfolding their definitions.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite Simplicial SimplexCategory

universe u

namespace SSet

variable {X : SSet.{u}}

/-- Evaluation of a shifted simplex at its distinguished final vertex. -/
def joinVertexEvaluation (X : SSet.{u}) :
    joinVertex.op ⋙ X ⟶ (Functor.const _).obj (X _⦋0⦌) where
  app m := X.map (joinVertexInr m.unop).op
  naturality m m' f := by
    exact (X.map_comp _ _).symm.trans
      (congrArg (fun g ↦ X.map g.op) (joinVertexInr_comp_joinVertex_map f.unop))

/-- The totally degenerate shifted simplex associated to a vertex of `X`. -/
def joinVertexDegeneracy (X : SSet.{u}) :
    (Functor.const _).obj (X _⦋0⦌) ⟶ joinVertex.op ⋙ X where
  app m := X.map (SimplexCategory.const (joinVertex.obj m.unop) ⦋0⦌ 0).op
  naturality m m' f := by
    exact ((X.map_comp _ _).symm.trans
      (congrArg (fun g : joinVertex.obj m'.unop ⟶ ⦋0⦌ ↦ X.map g.op)
        (Subsingleton.elim _ _))).symm

/-- Evaluation at the distinguished initial vertex, obtained by reversing final evaluation. -/
def vertexJoinEvaluation (X : SSet.{u}) :
    vertexJoin.op ⋙ X ⟶ (Functor.const _).obj (X _⦋0⦌) :=
  opFunctor.map (joinVertexEvaluation X.op)

/-- The totally degenerate initial-shifted simplex, obtained by reversing final degeneracy. -/
def vertexJoinDegeneracy (X : SSet.{u}) :
    (Functor.const _).obj (X _⦋0⦌) ⟶ vertexJoin.op ⋙ X :=
  opFunctor.map (joinVertexDegeneracy X.op)

/-- Componentwise evaluation of the final-vertex augmentation. -/
@[simp]
lemma joinVertexEvaluation_app_apply {n : ℕ} (σ : X _⦋n + 1⦌) :
    dsimp% (joinVertexEvaluation X).app (op ⦋n⦌) σ = X.map (joinVertexInr ⦋n⦌).op σ :=
  (rfl)

/-- Componentwise evaluation of total degeneracy in the final shift. -/
@[simp]
lemma joinVertexDegeneracy_app_apply {n : ℕ} (x : X _⦋0⦌) :
    dsimp% (joinVertexDegeneracy X).app (op ⦋n⦌) x =
      X.map (SimplexCategory.const ⦋n + 1⦌ ⦋0⦌ 0).op x :=
  (rfl)

/-- The reversed augmentation evaluates at the initial vertex. -/
@[simp]
lemma vertexJoinEvaluation_app_apply {n : ℕ} (σ : X _⦋n + 1⦌) :
    dsimp% (vertexJoinEvaluation X).app (op ⦋n⦌) σ =
      X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op σ := by
  -- Opposite reverses the final vertex to the initial one.
  change X.map (rev.map (joinVertexInr ⦋n⦌)).op σ = _
  apply congrArg (fun f : ⦋0⦌ ⟶ ⦋n + 1⦌ ↦ X.map f.op σ)
  rw [joinVertexInr_mk]
  -- Normalize the shifted ordinal to expose the constant map to reversal.
  change rev.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1))) = _
  rw [rev_map_const, Fin.rev_last]

/-- The reversed total degeneracy is the same totally degenerate simplex of `X`. -/
@[simp]
lemma vertexJoinDegeneracy_app_apply {n : ℕ} (x : X _⦋0⦌) :
    dsimp% (vertexJoinDegeneracy X).app (op ⦋n⦌) x =
      X.map (SimplexCategory.const ⦋n + 1⦌ ⦋0⦌ 0).op x := by
  -- Opposite preserves the unique map from an ordinal to the singleton ordinal.
  change X.map (rev.map (SimplexCategory.const ⦋n + 1⦌ ⦋0⦌ 0)).op x = _
  rw [rev_map_const]
  rfl

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
@[reassoc (attr := simp)]
lemma ι₀_joinVertexContraction : ι₀ ≫ joinVertexContraction X = 𝟙 _ := by
  ext ⟨⟨n⟩⟩ σ
  have he : stdSimplex.objEquiv (ι₀.app _ σ).2 = SimplexCategory.const ⦋n⦌ ⦋1⦌ 0 := by
    ext i : 3
    exact SSet.ι₀_app_snd_apply σ i
  have h := joinVertexContraction_app_apply (X := X) (n := n) (ι₀.app _ σ)
  rw [he, joinVertexCollapse_const_zero, op_id, CategoryTheory.Functor.map_id] at h
  exact h.trans (SSet.ι₀_app_fst σ)

/-- The collapsing endpoint evaluates the final vertex and then takes its total degeneracy. -/
@[reassoc (attr := simp)]
lemma ι₁_joinVertexContraction :
    ι₁ ≫ joinVertexContraction X = joinVertexEvaluation X ≫ joinVertexDegeneracy X := by
  ext ⟨⟨n⟩⟩ σ
  have he : stdSimplex.objEquiv (ι₁.app _ σ).2 = SimplexCategory.const ⦋n⦌ ⦋1⦌ 1 := by
    ext i : 3
    exact ι₁_app_snd_apply σ i
  have h := joinVertexContraction_app_apply (X := X) (n := n) (ι₁.app _ σ)
  rw [he, joinVertexCollapse_const_one, op_comp, Functor.map_comp_apply] at h
  exact h.trans (congrArg _ (congrArg _ (ι₁_app_fst σ)))

variable (X) in
/-- The contraction of `vertexJoin.op ⋙ X` towards the initial vertices: the simplex `(σ, e)` of
`(vertexJoin.op ⋙ X) ⊗ Δ[1]` goes to the restriction of `σ` along `vertexJoinCollapse e`. -/
noncomputable def vertexJoinContraction : (vertexJoin.op ⋙ X) ⊗ Δ[1] ⟶ vertexJoin.op ⋙ X :=
  -- Opposite turns `joinVertex.op ⋙ X.op` into `vertexJoin.op ⋙ X` by definition.
  (vertexJoin.op ⋙ X) ◁ (stdSimplex.opIso ⦋1⦌).inv ≫
    opFunctor.map (joinVertexContraction X.op)

/-- Evaluation of the join contraction on a pair of simplices. -/
@[simp]
lemma vertexJoinContraction_app_apply {n : ℕ}
    (z : ((vertexJoin.op ⋙ X) ⊗ Δ[1]).obj (op ⦋n⦌)) :
    dsimp% (vertexJoinContraction X).app _ z =
      X.map (vertexJoinCollapse (stdSimplex.objEquiv z.2)).op z.1 :=
by
  have he : stdSimplex.objEquiv (opObjEquiv ((stdSimplex.opIso ⦋1⦌).inv.app _ z.2)) =
      rev.map (stdSimplex.objEquiv z.2) := by
    ext i : 3
    rw [stdSimplex.objEquiv_toOrderHom_apply, stdSimplex.opIso_inv_app_hom_apply,
      stdSimplex.opObjEquiv_opObjEquiv_symm_apply, rev_map_apply,
      stdSimplex.objEquiv_toOrderHom_apply]
  -- Evaluate the opposite cylinder using the right-hand contraction's component law.
  refine (congrArg opObjEquiv (joinVertexContraction_app_apply (X := X.op) (n := n)
    (opObjEquiv.symm z.1, opObjEquiv ((stdSimplex.opIso ⦋1⦌).inv.app _ z.2)))).trans ?_
  exact (congrArg (fun e : ⦋n⦌ ⟶ ⦋1⦌ ↦ X.map (rev.map (joinVertexCollapse e)).op z.1) he).trans
    (congrArg (fun g ↦ X.map g.op z.1) (vertexJoinCollapse_def _).symm)

/-- The identity endpoint of the join contraction. -/
@[reassoc (attr := simp)]
lemma ι₁_vertexJoinContraction : ι₁ ≫ vertexJoinContraction X = 𝟙 _ := by
  have he := lift_const_comp_opIso_inv (joinVertex.op ⋙ X.op) 1
  -- The shifted opposite is `vertexJoin.op ⋙ X`, and interval reversal swaps its endpoints.
  change ι₁ ≫ (vertexJoin.op ⋙ X) ◁ (stdSimplex.opIso ⦋1⦌).inv =
    opFunctor.map (ι₀ : joinVertex.op ⋙ X.op ⟶ _) at he
  exact (Category.assoc ι₁ ((vertexJoin.op ⋙ X) ◁ (stdSimplex.opIso ⦋1⦌).inv)
    (opFunctor.map (joinVertexContraction X.op))).symm.trans
      ((congrArg (· ≫ opFunctor.map (joinVertexContraction X.op)) he).trans
        ((opFunctor.map_comp _ _).symm.trans
          ((congrArg (fun f ↦ opFunctor.map f) (ι₀_joinVertexContraction (X := X.op))).trans
            (opFunctor.map_id _))))

/-- The collapsing endpoint evaluates the initial vertex and takes its total degeneracy. -/
@[reassoc (attr := simp)]
lemma ι₀_vertexJoinContraction :
    ι₀ ≫ vertexJoinContraction X = vertexJoinEvaluation X ≫ vertexJoinDegeneracy X := by
  ext ⟨⟨n⟩⟩ σ
  have he : stdSimplex.objEquiv (ι₀.app _ σ).2 = SimplexCategory.const ⦋n⦌ ⦋1⦌ 0 := by
    ext i : 3
    exact ι₀_app_snd_apply σ i
  have h := vertexJoinContraction_app_apply (X := X) (n := n) (ι₀.app _ σ)
  rw [he, vertexJoinCollapse_const_zero, op_comp, Functor.map_comp_apply] at h
  have hR : (vertexJoinEvaluation X ≫ vertexJoinDegeneracy X).app (op ⦋n⦌) σ =
      X.map (SimplexCategory.const ⦋n + 1⦌ ⦋0⦌ 0).op
        (X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op σ) :=
    (vertexJoinDegeneracy_app_apply (n := n) ((vertexJoinEvaluation X).app (op ⦋n⦌) σ)).trans
      (congrArg _ (vertexJoinEvaluation_app_apply σ))
  exact h.trans ((congrArg (fun τ ↦ X.map (SimplexCategory.const ⦋n + 1⦌ ⦋0⦌ 0).op
    (X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op τ)) (ι₀_app_fst σ)).trans hR.symm)

end SSet
