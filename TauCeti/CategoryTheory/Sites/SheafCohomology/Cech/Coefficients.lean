/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic

/-!
# Čech complexes under a change of coefficients

Let `F : A ⥤ B` be an additive functor between preadditive categories with products, and let
`U : ι → C` be a family in a category with finite products. The degree `n` term of the Čech
complex `Č(U, P)` of a presheaf `P : Cᵒᵖ ⥤ A` is a product indexed by `Fin (n + 1) → ι`. If `F`
preserves these products, then applying `F` termwise to `Č(U, P)` gives the Čech complex
`Č(U, P ⋙ F)`, naturally in `P` (`TauCeti.CategoryTheory.cechComplexFunctorMapIso`).

Typical uses are the forgetful functor from modules over a ring to abelian groups, which preserves
all products, and an additive functor such as extension of scalars, which preserves finite products,
for a finite family `U`. For instance, the Čech complex of a presheaf of modules is a complex of
modules whose underlying complex of abelian groups is the Čech complex of the underlying presheaf
of abelian groups.

When `A` is linear over a ring `R`, the Čech complex functor is `R`-linear
(`TauCeti.CategoryTheory.cechComplexFunctor_linear`): multiplying a morphism of presheaves by a
scalar multiplies the induced map of Čech complexes by that scalar.

## Main definitions

* `TauCeti.CategoryTheory.cechComplexFunctorMapIso`: the natural isomorphism between `F` applied
  to the Čech complex of `P` and the Čech complex of `P ⋙ F`.

## Main results

* `TauCeti.CategoryTheory.cechComplexFunctorMapIso_hom_app_f_π`: its factors are the images
  under `F` of the projections of the products.
* `TauCeti.CategoryTheory.cechComplexFunctor_linear`: the Čech complex functor is linear.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v v' v'' u u' u''

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  {B : Type u''} [Category.{v''} B] [Preadditive B] [HasProducts.{w} B]
  {ι : Type w} (U : ι → C) (F : A ⥤ B)
  [∀ n : ℕ, PreservesLimitsOfShape (Discrete (Fin (n + 1) → ι)) F]

/-- The degree `n` term of a Čech complex is, up to unfolding, the product of the values of `P`
on the `(n + 1)`-fold products of members. -/
private def cechXIso (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    ((cechComplexFunctor U).obj P).X n ≅
      ∏ᶜ fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j))) :=
  Iso.refl _

/-- `cechComplexFunctor_obj_d_comp_π`, stated through `cechXIso`. -/
@[reassoc]
private lemma cechComplexFunctor_obj_d_comp_cechXIso_hom_π (P : Cᵒᵖ ⥤ A) (n : ℕ)
    (k : Fin (n + 2) → ι) :
    ((cechComplexFunctor U).obj P).d n (n + 1) ≫ (cechXIso U P (n + 1)).hom ≫ Pi.π _ k =
      ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) • ((cechXIso U P n).hom ≫ Pi.π _ (k ∘ m.succAbove) ≫
        P.map (Pi.lift fun x ↦ Pi.π (fun j ↦ U (k j)) (m.succAbove x)).op) :=
  -- `cechXIso` is the identity
  (_ ≫= Category.id_comp _).trans <| (cechComplexFunctor_obj_d_comp_π U P n k).trans <|
    Finset.sum_congr rfl fun _ _ ↦ congrArg _ (Category.id_comp _).symm

/-- The degree `n` component of `cechComplexFunctorMapIso`: `F` preserves the product indexed by
`Fin (n + 1) → ι` which is the degree `n` term of the Čech complex. -/
private def cechComplexFunctorMapXIso (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    F.obj (((cechComplexFunctor U).obj P).X n) ≅ ((cechComplexFunctor U).obj (P ⋙ F)).X n :=
  F.mapIso (cechXIso U P n) ≪≫
    PreservesProduct.iso F (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) ≪≫
    (cechXIso U (P ⋙ F) n).symm

/-- The factors of `cechComplexFunctorMapXIso` are the images of the projections. -/
@[reassoc]
private lemma cechComplexFunctorMapXIso_hom_π (P : Cᵒᵖ ⥤ A) (n : ℕ) (a : Fin (n + 1) → ι) :
    (cechComplexFunctorMapXIso U F P n).hom ≫ (cechXIso U (P ⋙ F) n).hom ≫ Pi.π _ a =
      F.map ((cechXIso U P n).hom ≫ Pi.π _ a) := by
  simp [cechComplexFunctorMapXIso]

/-- `cechComplexFunctor_map_f_π`, stated through `cechXIso`. -/
@[reassoc]
private lemma cechComplexFunctor_map_f_cechXIso_hom_π {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ)
    (a : Fin (n + 1) → ι) :
    ((cechComplexFunctor U).map α).f n ≫ (cechXIso U Q n).hom ≫ Pi.π _ a =
      (cechXIso U P n).hom ≫ Pi.π _ a ≫ α.app (op (∏ᶜ fun j ↦ U (a j))) :=
  -- `cechXIso` is the identity
  (_ ≫= Category.id_comp _).trans <| (cechComplexFunctor_map_f_π U P α n a).trans
    (Category.id_comp _).symm

/-- The components `cechComplexFunctorMapXIso` are natural in the presheaf. -/
private lemma cechComplexFunctorMapXIso_hom_naturality {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    F.map (((cechComplexFunctor U).map α).f n) ≫ (cechComplexFunctorMapXIso U F Q n).hom =
      (cechComplexFunctorMapXIso U F P n).hom ≫
        ((cechComplexFunctor U).map (Functor.whiskerRight α F)).f n := by
  rw [← cancel_mono (cechXIso U (Q ⋙ F) n).hom]
  refine Pi.hom_ext _ _ fun a ↦ ?_
  simp only [Category.assoc]
  rw [cechComplexFunctorMapXIso_hom_π, ← F.map_comp, cechComplexFunctor_map_f_cechXIso_hom_π,
    cechComplexFunctor_map_f_cechXIso_hom_π]
  dsimp only [Functor.comp_obj, Functor.whiskerRight_app]
  rw [cechComplexFunctorMapXIso_hom_π_assoc]
  simp only [Functor.map_comp, Category.assoc]

variable [F.Additive]

/-- The components `cechComplexFunctorMapXIso` commute with the differentials. -/
private lemma cechComplexFunctorMapXIso_hom_comp_d (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (cechComplexFunctorMapXIso U F P n).hom ≫ ((cechComplexFunctor U).obj (P ⋙ F)).d n (n + 1) =
      F.map (((cechComplexFunctor U).obj P).d n (n + 1)) ≫
        (cechComplexFunctorMapXIso U F P (n + 1)).hom := by
  rw [← cancel_mono (cechXIso U (P ⋙ F) (n + 1)).hom]
  refine Pi.hom_ext _ _ fun k ↦ ?_
  simp only [Category.assoc]
  rw [cechComplexFunctor_obj_d_comp_cechXIso_hom_π, cechComplexFunctorMapXIso_hom_π,
    ← F.map_comp, cechComplexFunctor_obj_d_comp_cechXIso_hom_π, F.map_sum, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Preadditive.comp_zsmul, F.map_zsmul]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  rw [cechComplexFunctorMapXIso_hom_π_assoc]
  simp only [Functor.map_comp, Category.assoc]

/-- **Čech complexes under a change of coefficients.** For an additive functor `F : A ⥤ B`
preserving the products indexed by `Fin (n + 1) → ι` for every `n`, applying `F` to the Čech
complex of a presheaf `P` for the family `U` gives the Čech complex of `P ⋙ F`, naturally in `P`.
Its factors are the images under `F` of the projections of the products
(`cechComplexFunctorMapIso_hom_app_f_π`). -/
def cechComplexFunctorMapIso :
    cechComplexFunctor U ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ) ≅
      (Functor.whiskeringRight Cᵒᵖ A B).obj F ⋙ cechComplexFunctor U :=
  NatIso.ofComponents
    (fun P ↦ HomologicalComplex.Hom.isoOfComponents (cechComplexFunctorMapXIso U F P)
      fun n _ h ↦ by
        obtain rfl : n + 1 = _ := h
        exact cechComplexFunctorMapXIso_hom_comp_d U F P n)
    fun α ↦ by
      ext n : 2
      exact cechComplexFunctorMapXIso_hom_naturality U F α n

/-- The factor indexed by `a` of the degree `n` component of `cechComplexFunctorMapIso` is the
image under `F` of the projection onto the factor indexed by `a`. -/
@[reassoc]
theorem cechComplexFunctorMapIso_hom_app_f_π (P : Cᵒᵖ ⥤ A) (n : ℕ) (a : Fin (n + 1) → ι) :
    ((cechComplexFunctorMapIso U F).hom.app P).f n ≫ Pi.π _ a =
      F.map (Pi.π (fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) a) :=
  -- `cechXIso` is the identity
  (_ ≫= (Category.id_comp _).symm).trans <| (cechComplexFunctorMapXIso_hom_π U F P n a).trans
    (congrArg F.map (Category.id_comp _))

omit [HasProducts.{w} B] in
/-- The Čech complex functor of a family is linear when the coefficient category is. -/
instance cechComplexFunctor_linear (R : Type*) [Semiring R] [Linear R A] :
    (cechComplexFunctor (A := A) U).Linear R where
  map_smul {P Q} α r := by
    ext n : 1
    refine Pi.hom_ext _ _ fun a ↦ ?_
    rw [HomologicalComplex.smul_f_apply]
    erw [cechComplexFunctor_map_f_π]
    rw [NatTrans.app_smul]
    exact (Linear.comp_smul _ _ _ _ _ _).trans <| (congrArg (r • ·)
      (cechComplexFunctor_map_f_π U P α n a).symm).trans (Linear.smul_comp _ _ _ _ _ _).symm

end TauCeti.CategoryTheory
