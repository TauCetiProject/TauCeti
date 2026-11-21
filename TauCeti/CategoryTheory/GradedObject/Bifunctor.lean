/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Antidiag.Prod
public import Mathlib.CategoryTheory.GradedObject.Bifunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Coproducts of graded objects as biproducts

Given a graded object `X : GradedObject I C` and a map `p : I → J`, the object `X.mapObj p n` is
the coproduct of the `X i` with `p i = n`. Given an equivalence `e` of the fibre `p ⁻¹' {n}` with
a type `A` such that the objects `X (e.symm a)` have a biproduct, for instance a finite type when
`C` has finite biproducts, `X.mapObj p n` is this biproduct
(`CategoryTheory.GradedObject.mapObjIsoBiproductOfEquiv`), with the expected inclusions.

For graded objects indexed by a type with an addition and antidiagonals, such as `ℕ`, the fibre of
the addition map over `n` is `Finset.antidiagonal n` (`Finset.fiberEquivAntidiagonal`), so the
coproduct over `i + j = n` defining `CategoryTheory.GradedObject.mapBifunctorMapObj` is the
biproduct indexed by `Finset.antidiagonal n`
(`CategoryTheory.GradedObject.mapBifunctorMapObjIsoBiproduct`). The tensor product of graded
objects is a special case (`CategoryTheory.GradedObject.Monoidal.tensorObjIsoBiproduct`).
-/

public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.GradedObject

section MapObj

variable {I J A C : Type*} [Category* C] [HasZeroMorphisms C] (X : GradedObject I C) (p : I → J)
  [X.HasMap p] {n : J} (e : p ⁻¹' {n} ≃ A) [HasBiproduct fun a ↦ X (e.symm a).val]

/-- The biproduct of the `X i` with `p i = n`, reindexed along `e`, as a cofan over the fibre. -/
private abbrev cofanOfEquiv : X.CofanMapObjFun p n :=
  Cofan.mk (⨁ fun a ↦ X (e.symm a).val) fun i ↦
    eqToHom (by rw [e.symm_apply_apply]) ≫ biproduct.ι (fun a ↦ X (e.symm a).val) (e i)

omit [HasZeroMorphisms C] [X.HasMap p] [HasBiproduct fun a ↦ X (e.symm a).val] in
/-- The inclusion of a summand of a cofan over the fibre, transported along an equality of
indices. -/
private lemma eqToHom_comp_inj (s : Cofan (X.mapObjFun p n)) {i i' : p ⁻¹' {n}} (h : i' = i)
    (h' : X i.val = X i'.val) : eqToHom h' ≫ s.inj i' = s.inj i := by
  subst h
  exact Category.id_comp _

/-- The cofan `cofanOfEquiv` is a colimit: maps out of it are maps out of the biproduct. -/
private def isColimitCofanOfEquiv : IsColimit (cofanOfEquiv X p e) :=
  Cofan.IsColimit.mk _ (fun s ↦ biproduct.desc fun a ↦ s.inj (e.symm a))
    (fun s i ↦ by
      rw [cofan_mk_inj, Category.assoc, biproduct.ι_desc]
      exact eqToHom_comp_inj X p s (e.symm_apply_apply i) _)
    (fun s m hm ↦ biproduct.hom_ext' _ _ fun a ↦ by
      rw [biproduct.ι_desc, ← hm (e.symm a), cofan_mk_inj]
      exact congrArg (· ≫ m) (biproduct.eqToHom_comp_ι _ (e.apply_symm_apply a).symm).symm)

/-- The coproduct `X.mapObj p n` of the `X i` with `p i = n` is the biproduct of these objects,
indexed through an equivalence `e` of the fibre `p ⁻¹' {n}` with a type `A`. -/
def mapObjIsoBiproductOfEquiv : X.mapObj p n ≅ ⨁ fun a ↦ X (e.symm a).val :=
  (CofanMapObjFun.iso (isColimitCofanOfEquiv X p e)).symm

/-- `mapObjIsoBiproductOfEquiv` sends the summand `X (e.symm a)` to the summand of index `a`. -/
@[reassoc (attr := simp)]
lemma ιMapObj_mapObjIsoBiproductOfEquiv_hom (a : A) :
    X.ιMapObj p (e.symm a).val n (Set.mem_singleton_iff.1 (e.symm a).property) ≫
        (X.mapObjIsoBiproductOfEquiv p e).hom = biproduct.ι (fun a ↦ X (e.symm a).val) a := by
  rw [mapObjIsoBiproductOfEquiv, Iso.symm_hom]
  refine (CofanMapObjFun.ιMapObj_iso_inv (isColimitCofanOfEquiv X p e) _ _).trans ?_
  rw [cofan_mk_inj]
  exact biproduct.eqToHom_comp_ι (fun a ↦ X (e.symm a).val) (e.apply_symm_apply a).symm

/-- The inverse of `mapObjIsoBiproductOfEquiv` sends the summand of index `a` to the summand
`X (e.symm a)` of `X.mapObj p n`. -/
@[reassoc (attr := simp)]
lemma ι_mapObjIsoBiproductOfEquiv_inv (a : A) :
    biproduct.ι (fun a ↦ X (e.symm a).val) a ≫ (X.mapObjIsoBiproductOfEquiv p e).inv =
      X.ιMapObj p (e.symm a).val n (Set.mem_singleton_iff.1 (e.symm a).property) := by
  rw [← ιMapObj_mapObjIsoBiproductOfEquiv_hom X p e a, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end MapObj

section Antidiagonal

variable {I : Type*} [Add I] [Finset.HasAntidiagonal I]
  {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [HasZeroMorphisms C₃]
  (X : GradedObject I C₁) (Y : GradedObject I C₂) (F : C₁ ⥤ C₂ ⥤ C₃)
  [HasMap (((mapBifunctor F I I).obj X).obj Y) (fun x ↦ x.1 + x.2)] (n : I)
  [HasBiproduct fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2)]

-- The summands of the reindexed biproduct are by definition the `(F.obj (X i)).obj (Y j)`, since
-- `Finset.fiberEquivAntidiagonal` does not change the underlying pairs.
private instance : HasBiproduct fun a : Finset.antidiagonal n ↦
    (((mapBifunctor F I I).obj X).obj Y) ((Finset.fiberEquivAntidiagonal n).symm a).val :=
  ‹HasBiproduct fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2)›

/-- For graded objects indexed by a type with an addition and antidiagonals, such as `ℕ`, the
coproduct of the `(F.obj (X i)).obj (Y j)` with `i + j = n` is the biproduct of these objects
indexed by `Finset.antidiagonal n`: this is `CategoryTheory.GradedObject.mapObjIsoBiproductOfEquiv`
for the equivalence `Finset.fiberEquivAntidiagonal` of the fibre of the addition map with
`Finset.antidiagonal n`. -/
def mapBifunctorMapObjIsoBiproduct :
    mapBifunctorMapObj F (fun x ↦ x.1 + x.2) X Y n ≅
      ⨁ fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2) :=
  -- `mapBifunctorMapObj` is by definition `mapObj` of the graded object of the summands
  mapObjIsoBiproductOfEquiv (((mapBifunctor F I I).obj X).obj Y) _ (Finset.fiberEquivAntidiagonal n)

/-- `mapBifunctorMapObjIsoBiproduct` sends the summand `(F.obj (X i)).obj (Y j)` to the
corresponding summand of the biproduct. -/
@[reassoc (attr := simp)]
lemma ι_mapBifunctorMapObjIsoBiproduct_hom (i j : I) (h : i + j = n) :
    ιMapBifunctorMapObj F (fun x ↦ x.1 + x.2) X Y i j n h ≫
        (mapBifunctorMapObjIsoBiproduct X Y F n).hom =
      biproduct.ι (fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2))
        ⟨(i, j), Finset.mem_antidiagonal.2 h⟩ :=
  -- `ιMapBifunctorMapObj` is by definition `ιMapObj`, and the pair `(i, j)` is by definition the
  -- image of `⟨(i, j), _⟩` under `(Finset.fiberEquivAntidiagonal n).symm`
  ιMapObj_mapObjIsoBiproductOfEquiv_hom (((mapBifunctor F I I).obj X).obj Y) _
    (Finset.fiberEquivAntidiagonal n) ⟨(i, j), Finset.mem_antidiagonal.2 h⟩

/-- The inverse of `mapBifunctorMapObjIsoBiproduct` sends each summand of the biproduct to the
corresponding summand of `mapBifunctorMapObj`. -/
@[reassoc (attr := simp)]
lemma ι_mapBifunctorMapObjIsoBiproduct_inv (x : Finset.antidiagonal n) :
    biproduct.ι (fun x : Finset.antidiagonal n ↦ (F.obj (X x.val.1)).obj (Y x.val.2)) x ≫
        (mapBifunctorMapObjIsoBiproduct X Y F n).inv =
      ιMapBifunctorMapObj F _ X Y x.val.1 x.val.2 n (Finset.mem_antidiagonal.1 x.property) :=
  -- as for `ι_mapBifunctorMapObjIsoBiproduct_hom`
  ι_mapObjIsoBiproductOfEquiv_inv (((mapBifunctor F I I).obj X).obj Y) _
    (Finset.fiberEquivAntidiagonal n) x

end Antidiagonal

end CategoryTheory.GradedObject
