/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.StdSimplex
public import TauCeti.AlgebraicTopology.SimplicialSet.BoundaryColimits

/-!
# Complements on the opposite of a simplicial set

Mathlib's covariant involution `SSet.opFunctor : SSet ⥤ SSet` reverses the order of the vertices
of every simplex, and `SSet.stdSimplex.opIso n : Δ[n]ᵒᵖ ≅ Δ[n]` identifies the opposite of a
standard simplex with itself. This file records that `SSet.opFunctor` is an equivalence of
categories, and the compatibilities of `SSet.stdSimplex.opIso` with maps of standard simplices,
with the involution, and with the Yoneda bijection. Reversal also restricts to an isomorphism
on simplex boundaries (`SSet.boundary.opIso`) and on horns (`SSet.horn.opIso`), showing in
particular that the opposite of a quasicategory is a quasicategory (`SSet.Quasicategory.op`).
They are what one needs to transport constructions on simplicial sets, such as joins, slices, and
outer-horn filling, along the opposite.

## Main results

* `SSet.stdSimplex.map_comp_opIso_inv`: the isomorphism `Δ[n]ᵒᵖ ≅ Δ[n]` is natural in `n`.
* `SSet.stdSimplex.opFunctor_map_opIso_hom_comp_opIso_hom`,
  `SSet.stdSimplex.opIso_inv_comp_opFunctor_map_opIso_inv`: it is involutive.
* `SSet.stdSimplex.opFunctor_map_const_comp_opIso_hom`: the opposite of a constant map to `Δ[n]` is
  the constant map at the reversed vertex.
* `SSet.stdSimplex.opIso_inv_comp_opFunctor_map_yonedaEquiv_symm`: the map `Δ[n] ⟶ Xᵒᵖ` given by
  an `n`-simplex of `Xᵒᵖ` is the opposite of the map `Δ[n] ⟶ X` given by the same simplex of `X`.
* `SSet.boundary.opIso`: boundary reversal, compatible with the boundary inclusions and vertices.
* `SSet.boundary.exists_extension_iff_op`: boundary extension is invariant under reversal.
* `SSet.horn.opIso`: horn reversal `Λ[n, i]ᵒᵖ ≅ Λ[n, i.rev]`, compatible with horn inclusions and
  edges.
* `SSet.horn.exists_extension_iff_op`: horn extension is invariant under reversal.
* `SSet.Quasicategory.op`, `SSet.quasicategory_op_iff`: a simplicial set is a quasicategory
  exactly when its opposite is.
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

namespace boundary

/-- Restriction of standard-simplex reversal to boundary simplices. -/
private def opObjEquiv' (n : ℕ) (d : SimplexCategoryᵒᵖ) :
    (opFunctor.obj (∂Δ[n] : SSet.{u})).obj d ≃ (∂Δ[n] : SSet.{u}).obj d :=
  opObjEquiv.trans (Equiv.subtypeEquiv
    (opObjEquiv.symm.trans ((stdSimplex.opIso ⦋n⦌).app d).toEquiv) (fun x ↦ by
      have h := Set.ext_iff.mp (congrArg (fun A ↦ A.obj d) (op_boundary.{u} n))
        ((stdSimplex.opIso ⦋n⦌).hom.app d (opObjEquiv.symm x))
      simpa only [Subcomplex.preimage_obj, Set.mem_preimage, Subcomplex.mem_op_obj_iff,
        Iso.hom_inv_id_app_apply, Equiv.apply_symm_apply, Equiv.trans_apply,
        Iso.toEquiv_fun, Iso.app_hom] using h))

/-- Reversing the vertices identifies the opposite of a simplex boundary with that boundary. -/
def opIso (n : ℕ) : opFunctor.obj (∂Δ[n] : SSet.{u}) ≅ (∂Δ[n] : SSet.{u}) :=
  NatIso.ofComponents (fun d ↦ (opObjEquiv' n d).toIso) (by
    intro d e f
    ext x
    apply Subtype.ext
    exact NatTrans.naturality_apply (stdSimplex.opIso ⦋n⦌).hom f
      (opObjEquiv.symm (opObjEquiv x).1))

/-- Boundary reversal is the restriction of standard-simplex reversal. -/
@[reassoc (attr := simp)]
lemma opIso_hom_ι (n : ℕ) :
    (opIso.{u} n).hom ≫ ∂Δ[n].ι =
      opFunctor.map ∂Δ[n].ι ≫ (stdSimplex.opIso ⦋n⦌).hom :=
  (rfl)

/-- The inverse boundary reversal is the restriction of the inverse simplex reversal. -/
@[reassoc (attr := simp)]
lemma opIso_inv_opFunctor_map_ι (n : ℕ) :
    (opIso.{u} n).inv ≫ opFunctor.map ∂Δ[n].ι =
      ∂Δ[n].ι ≫ (stdSimplex.opIso ⦋n⦌).inv :=
  (rfl)

/-- Boundary reversal sends a vertex to the oppositely numbered vertex. -/
@[simp]
lemma opIso_inv_app_vertex (n : ℕ) (i : Fin (n + 2)) :
    (dsimp% only [Subfunctor.toFunctor_obj]
      (opIso.{u} (n + 1)).inv.app _ (vertex n i)) = opObjEquiv.symm (vertex n i.rev) := by
  apply opObjEquiv.injective
  apply Subtype.ext
  ext j
  simp [opIso, opObjEquiv', stdSimplex.opObjEquiv_opObjEquiv_symm_apply]

/-- A boundary map extends to a simplex if and only if its reversal does. -/
lemma exists_extension_iff_op {X : SSet.{u}} {n : ℕ} (σ₀ : (∂Δ[n] : SSet) ⟶ X) :
    (∃ σ : Δ[n] ⟶ X, σ₀ = ∂Δ[n].ι ≫ σ) ↔
      ∃ τ : Δ[n] ⟶ X.op, (opIso n).inv ≫ opFunctor.map σ₀ = ∂Δ[n].ι ≫ τ := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨(stdSimplex.opIso ⦋n⦌).inv ≫ opFunctor.map σ, by
      simp [opFunctor.map_comp, ← Category.assoc]⟩
  · rintro ⟨τ, hτ⟩
    refine ⟨opFunctor.preimage ((stdSimplex.opIso ⦋n⦌).hom ≫ τ), ?_⟩
    apply opFunctor.map_injective
    rw [opFunctor.map_comp, Functor.map_preimage, ← Category.assoc,
      ← opIso_hom_ι, Category.assoc, ← hτ]
    simp

end boundary

namespace horn

/-- Restriction of standard-simplex reversal to horn simplices. -/
private def opObjEquiv' (n : ℕ) (i : Fin (n + 1)) (d : SimplexCategoryᵒᵖ) :
    (opFunctor.obj (Λ[n, i] : SSet.{u})).obj d ≃ (Λ[n, i.rev] : SSet.{u}).obj d :=
  opObjEquiv.trans (Equiv.subtypeEquiv
    (opObjEquiv.symm.trans ((stdSimplex.opIso ⦋n⦌).app d).toEquiv) (fun x ↦ by
      have h := Set.ext_iff.mp (congrArg (fun A ↦ A.obj d) (op_horn.{u} i))
        ((stdSimplex.opIso ⦋n⦌).hom.app d (opObjEquiv.symm x))
      simpa only [Subcomplex.preimage_obj, Set.mem_preimage, Subcomplex.mem_op_obj_iff,
        Iso.hom_inv_id_app_apply, Equiv.apply_symm_apply, Equiv.trans_apply,
        Iso.toEquiv_fun, Iso.app_hom] using h))

/-- Reversing the vertices identifies the opposite of the horn `Λ[n, i]` with the horn
`Λ[n, i.rev]`. -/
def opIso (n : ℕ) (i : Fin (n + 1)) :
    opFunctor.obj (Λ[n, i] : SSet.{u}) ≅ (Λ[n, i.rev] : SSet.{u}) :=
  NatIso.ofComponents (fun d ↦ (opObjEquiv' n i d).toIso) (by
    intro d e f
    ext x
    apply Subtype.ext
    exact NatTrans.naturality_apply (stdSimplex.opIso ⦋n⦌).hom f
      (opObjEquiv.symm (opObjEquiv x).1))

/-- Horn reversal is the restriction of standard-simplex reversal. -/
@[reassoc (attr := simp)]
lemma opIso_hom_ι (n : ℕ) (i : Fin (n + 1)) :
    (opIso.{u} n i).hom ≫ Λ[n, i.rev].ι =
      opFunctor.map Λ[n, i].ι ≫ (stdSimplex.opIso ⦋n⦌).hom :=
  (rfl)

/-- The inverse horn reversal is the restriction of the inverse simplex reversal. -/
@[reassoc (attr := simp)]
lemma opIso_inv_opFunctor_map_ι (n : ℕ) (i : Fin (n + 1)) :
    (opIso.{u} n i).inv ≫ opFunctor.map Λ[n, i].ι =
      Λ[n, i.rev].ι ≫ (stdSimplex.opIso ⦋n⦌).inv :=
  (rfl)

/-- Horn reversal sends an edge from `a` to `b` of `Λ[n, i.rev]` to the reversed edge from `b.rev`
to `a.rev` of `Λ[n, i]`. -/
lemma opIso_inv_app_edge {n : ℕ} (i a b : Fin (n + 1)) (hab : a ≤ b)
    (H : Finset.card {i.rev, a, b} ≤ n) (H' : Finset.card {i, b.rev, a.rev} ≤ n) :
    (dsimp% only [Subfunctor.toFunctor_obj]
      (opIso.{u} n i).inv.app _ (edge n i.rev a b hab H)) =
      opObjEquiv.symm (edge n i b.rev a.rev (Fin.rev_le_rev.2 hab) H') := by
  apply opObjEquiv.injective
  apply Subtype.ext
  ext j
  fin_cases j <;>
    simp [opIso, opObjEquiv', stdSimplex.opObjEquiv_opObjEquiv_symm_apply]

/-- A horn map extends to a simplex if and only if its reversal does. -/
lemma exists_extension_iff_op {X : SSet.{u}} {n : ℕ} {i : Fin (n + 1)}
    (σ₀ : (Λ[n, i] : SSet) ⟶ X) :
    (∃ σ : Δ[n] ⟶ X, σ₀ = Λ[n, i].ι ≫ σ) ↔
      ∃ τ : Δ[n] ⟶ X.op, (opIso n i).inv ≫ opFunctor.map σ₀ = Λ[n, i.rev].ι ≫ τ := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨(stdSimplex.opIso ⦋n⦌).inv ≫ opFunctor.map σ, by
      simp [opFunctor.map_comp, ← Category.assoc]⟩
  · rintro ⟨τ, hτ⟩
    refine ⟨opFunctor.preimage ((stdSimplex.opIso ⦋n⦌).hom ≫ τ), ?_⟩
    apply opFunctor.map_injective
    rw [opFunctor.map_comp, Functor.map_preimage, ← Category.assoc,
      ← opIso_hom_ι, Category.assoc, ← hτ]
    simp

end horn

/-- The opposite of a quasicategory is a quasicategory. -/
instance Quasicategory.op {X : SSet.{u}} [Quasicategory X] : Quasicategory X.op where
  hornFilling' n i σ₀ h0 hn := by
    have h0' : 0 < i.rev := by
      rw [← Fin.rev_last]
      exact Fin.rev_lt_rev.2 hn
    have hn' : i.rev < Fin.last (n + 2) := by
      rw [← Fin.rev_zero]
      exact Fin.rev_lt_rev.2 h0
    obtain ⟨τ, hτ⟩ := Quasicategory.hornFilling (S := X) h0' hn'
      ((horn.opIso (n + 2) i).inv ≫ opFunctor.map σ₀ ≫ opFunctorCompOpFunctorIso.hom.app X)
    refine (horn.exists_extension_iff_op σ₀).2 ⟨τ ≫ opFunctorCompOpFunctorIso.inv.app X, ?_⟩
    have h := hτ =≫ opFunctorCompOpFunctorIso.inv.app X
    simpa [Category.assoc] using h

/-- A simplicial set is a quasicategory exactly when its opposite is. -/
lemma quasicategory_op_iff {X : SSet.{u}} : Quasicategory X.op ↔ Quasicategory X := by
  refine ⟨fun _ ↦ ⟨fun n i σ₀ h0 hn ↦ ?_⟩, fun _ ↦ inferInstance⟩
  have h0' : 0 < i.rev := by
    rw [← Fin.rev_last]
    exact Fin.rev_lt_rev.2 hn
  have hn' : i.rev < Fin.last (n + 2) := by
    rw [← Fin.rev_zero]
    exact Fin.rev_lt_rev.2 h0
  exact (horn.exists_extension_iff_op σ₀).2 (Quasicategory.hornFilling h0' hn' _)

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
