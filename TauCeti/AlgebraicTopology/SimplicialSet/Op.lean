/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Complements on the opposite of a simplicial set

Mathlib's covariant involution `SSet.opFunctor : SSet ⥤ SSet` reverses the order of the vertices
of every simplex, and `SSet.stdSimplex.opIso n : Δ[n]ᵒᵖ ≅ Δ[n]` identifies the opposite of a
standard simplex with itself. This file records that `SSet.opFunctor` is an equivalence of
categories, and the compatibilities of `SSet.stdSimplex.opIso` with maps of standard simplices,
with the involution, and with the Yoneda bijection. They are what one needs to transport
constructions on simplicial sets, such as joins and slices, along the opposite.

## Main results

* `SSet.stdSimplex.map_comp_opIso_inv`: the isomorphism `Δ[n]ᵒᵖ ≅ Δ[n]` is natural in `n`.
* `SSet.stdSimplex.opFunctor_map_opIso_hom_comp_opIso_hom`,
  `SSet.stdSimplex.opIso_inv_comp_opFunctor_map_opIso_inv`: it is involutive.
* `SSet.stdSimplex.opFunctor_map_const_comp_opIso_hom`: the opposite of a constant map to `Δ[n]` is
  the constant map at the reversed vertex.
* `SSet.stdSimplex.opIso_inv_comp_opFunctor_map_yonedaEquiv_symm`: the map `Δ[n] ⟶ Xᵒᵖ` given by
  an `n`-simplex of `Xᵒᵖ` is the opposite of the map `Δ[n] ⟶ X` given by the same simplex of `X`.
* `SSet.Edge.opEquiv`: the edges of `Xᵒᵖ` are the edges of `X` with source and target exchanged.
* `SSet.Edge.CompStruct.opEquiv`: a `2`-simplex of `X` exhibiting `e₀₂` as a composite of `e₀₁`
  and `e₁₂` is a `2`-simplex of `Xᵒᵖ` exhibiting the opposite of `e₀₂` as a composite of the
  opposites of `e₁₂` and `e₀₁`.
-/

public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet

/-- The involution `SSet.opFunctor` is an equivalence of categories, so that it is full and
faithful. -/
instance : opFunctor.{u}.IsEquivalence :=
  opEquivalence.isEquivalence_functor

namespace stdSimplex

/-- The isomorphism `Δ[n]ᵒᵖ ≅ Δ[n]` reversing the order of the vertices is natural in `n`, where a
map `f` of the simplex category acts on the opposite through its reverse
`SimplexCategory.rev.map f`. -/
@[reassoc]
lemma map_comp_opIso_inv {m n : SimplexCategory} (f : m ⟶ n) :
    stdSimplex.{u}.map f ≫ (opIso n).inv =
      (opIso m).inv ≫ opFunctor.map (stdSimplex.map (SimplexCategory.rev.map f)) := by
  ext ⟨k⟩ x
  induction k using SimplexCategory.rec with | _ k
  induction m using SimplexCategory.rec with | _ m
  induction n using SimplexCategory.rec with | _ n
  apply opObjEquiv.injective
  ext j
  simp only [TypeCat.Fun.toFun_apply, opFunctor_map, Equiv.apply_symm_apply, NatTrans.comp_app,
    ConcreteCategory.comp_apply, opIso_inv_app_hom_apply, opObjEquiv_opObjEquiv_symm_apply,
    SimplexCategory.rev_obj, hom_app_apply, yonedaEquiv_map]
  rw [objEquiv_symm_apply, objEquiv_symm_apply, SimplexCategory.rev_map_apply, Fin.rev_rev]

/-- Reversing the order of the vertices twice is the identity: the isomorphism `Δ[n]ᵒᵖ ≅ Δ[n]`
is compatible with the involution `opFunctorCompOpFunctorIso : Xᵒᵖᵒᵖ ≅ X`. -/
@[reassoc (attr := simp)]
lemma opFunctor_map_opIso_hom_comp_opIso_hom (n : SimplexCategory) :
    opFunctor.map (opIso.{u} n).hom ≫ (opIso n).hom = opFunctorCompOpFunctorIso.hom.app _ := by
  ext ⟨k⟩ x
  induction k using SimplexCategory.rec with | _ k
  induction n using SimplexCategory.rec with | _ n
  ext j
  simp [opFunctor_map, stdSimplex.opObjEquiv_apply]

/-- Reversing the order of the vertices of `Δ[n]` twice is the identity, in the form of the inverse
of `SSet.stdSimplex.opFunctor_map_opIso_hom_comp_opIso_hom`. -/
@[reassoc (attr := simp)]
lemma opIso_inv_comp_opFunctor_map_opIso_inv (n : SimplexCategory) :
    (opIso.{u} n).inv ≫ opFunctor.map (opIso n).inv =
      opFunctorCompOpFunctorIso.inv.app (stdSimplex.obj n) := by
  rw [← cancel_mono (opFunctorCompOpFunctorIso.hom.app (stdSimplex.{u}.obj n)), Category.assoc,
    Iso.inv_hom_id_app, ← opFunctor_map_opIso_hom_comp_opIso_hom, ← Functor.map_comp_assoc]
  simp

/-- The opposite of the constant map at the vertex `e` of `Δ[n]` is, through the isomorphism
`Δ[n]ᵒᵖ ≅ Δ[n]` reversing the vertices, the constant map at the reversed vertex `e.rev`. -/
@[simp]
lemma opFunctor_map_const_comp_opIso_hom {X : SSet.{u}} {n : ℕ} (e : Fin (n + 1)) :
    opFunctor.map (SSet.const (stdSimplex.const n e _) : X ⟶ Δ[n]) ≫ (opIso ⦋n⦌).hom =
      SSet.const (stdSimplex.const n e.rev _) := by
  ext ⟨k⟩ x
  induction k using SimplexCategory.rec with | _ k
  ext j
  simp only [TypeCat.Fun.toFun_apply, NatTrans.comp_app, ConcreteCategory.comp_apply,
    opFunctor_map, opIso_hom_app_hom_apply, stdSimplex.opObjEquiv_apply, Equiv.apply_symm_apply,
    const_app_apply]

/-- The map `Δ[n] ⟶ Xᵒᵖ` given by an `n`-simplex `x` of `Xᵒᵖ` is, through the isomorphism
`Δ[n] ≅ Δ[n]ᵒᵖ` reversing the vertices, the opposite of the map `Δ[n] ⟶ X` given by `x`. -/
lemma opIso_inv_comp_opFunctor_map_yonedaEquiv_symm {X : SSet.{u}} {n : SimplexCategory}
    (x : X.obj (op n)) :
    (opIso n).inv ≫ opFunctor.map (yonedaEquiv.symm x) = yonedaEquiv.symm (opObjEquiv.symm x) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  induction n using SimplexCategory.rec with | _ n
  -- The top simplex of `Δ[n]` corresponds to the top simplex of `Δ[n]ᵒᵖ`.
  have h : opObjEquiv (yonedaEquiv (opIso.{u} ⦋n⦌).inv) = yonedaEquiv (𝟙 Δ[n]) := by
    rw [← Category.id_comp (opIso.{u} ⦋n⦌).inv, yonedaEquiv_comp]
    ext j
    rw [opIso_inv_app_hom_apply, opObjEquiv_opObjEquiv_symm_apply]
    rw [← objEquiv_toOrderHom_apply, ← objEquiv_toOrderHom_apply, objEquiv_yonedaEquiv_id]
    simp
  rw [opFunctor_map, h]
  simp

end stdSimplex

namespace Edge

variable {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}

/-- The edges of `Xᵒᵖ` are the edges of `X` with source and target exchanged: the same
`1`-simplex, read with its vertices in the reverse order. -/
def opEquiv : X.Edge x₀ x₁ ≃ X.op.Edge (X.opObjEquiv.symm x₁) (X.opObjEquiv.symm x₀) where
  toFun e := mk (X.opObjEquiv.symm e.edge) (by simp) (by simp)
  invFun e := mk (X.opObjEquiv e.edge)
    (X.opObjEquiv.symm.injective ((X.op_δ 0 e.edge).symm.trans e.tgt_eq))
    (X.opObjEquiv.symm.injective ((X.op_δ 1 e.edge).symm.trans e.src_eq))
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma opEquiv_edge (e : X.Edge x₀ x₁) : (opEquiv e).edge = X.opObjEquiv.symm e.edge :=
  (rfl)

@[simp]
lemma opEquiv_symm_edge (e : X.op.Edge (X.opObjEquiv.symm x₁) (X.opObjEquiv.symm x₀)) :
    (opEquiv.symm e).edge = X.opObjEquiv e.edge :=
  (rfl)

/-- The opposite of an identity edge is an identity edge. -/
@[simp]
lemma opEquiv_id (x : X _⦋0⦌) : opEquiv (id x) = id (X.opObjEquiv.symm x) := by
  ext
  simp

namespace CompStruct

variable {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂} {e₀₂ : X.Edge x₀ x₂}

/-- A `2`-simplex of `X` exhibiting `e₀₂` as a composite of `e₀₁` and `e₁₂` is a `2`-simplex of
`Xᵒᵖ` exhibiting the opposite of `e₀₂` as a composite of the opposites of `e₁₂` and `e₀₁`. -/
def opEquiv : CompStruct e₀₁ e₁₂ e₀₂ ≃
    CompStruct (Edge.opEquiv e₁₂) (Edge.opEquiv e₀₁) (Edge.opEquiv e₀₂) where
  toFun h := mk (X.opObjEquiv.symm h.simplex) (by simp) (by simp) (by simp)
  invFun h := mk (X.opObjEquiv h.simplex)
    (X.opObjEquiv.symm.injective (((X.op_δ 0 h.simplex).symm.trans h.d₀).trans (opEquiv_edge _)))
    (X.opObjEquiv.symm.injective (((X.op_δ 2 h.simplex).symm.trans h.d₂).trans (opEquiv_edge _)))
    (X.opObjEquiv.symm.injective (((X.op_δ 1 h.simplex).symm.trans h.d₁).trans (opEquiv_edge _)))
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma opEquiv_simplex (h : CompStruct e₀₁ e₁₂ e₀₂) :
    (opEquiv h).simplex = X.opObjEquiv.symm h.simplex :=
  (rfl)

@[simp]
lemma opEquiv_symm_simplex
    (h : CompStruct (Edge.opEquiv e₁₂) (Edge.opEquiv e₀₁) (Edge.opEquiv e₀₂)) :
    (opEquiv.symm h).simplex = X.opObjEquiv h.simplex :=
  (rfl)

end CompStruct

end Edge

end SSet
