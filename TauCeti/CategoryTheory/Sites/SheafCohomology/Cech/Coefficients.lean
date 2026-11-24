/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic
import TauCeti.CategoryTheory.Limits.Shapes.ZeroMorphisms

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

If `F` also preserves homology, then `F` applied to the cohomology of `Č(U, P)` is the cohomology
of `Č(U, P ⋙ F)` (`TauCeti.CategoryTheory.cechComplexFunctorMapHomologyIso`), naturally in `P`
and compatibly with the maps induced by morphisms of families. For a faithful `F`, the cohomology
of `Č(U, P)` vanishes exactly when that of `Č(U, P ⋙ F)` does.

When `A` is linear over a ring `R`, the Čech complex functor is `R`-linear
(`TauCeti.CategoryTheory.cechComplexFunctor_linear`): multiplying a morphism of presheaves by a
scalar multiplies the induced map of Čech complexes by that scalar.

## Main definitions

* `TauCeti.CategoryTheory.cechComplexFunctorMapIso`: the natural isomorphism between `F` applied
  to the Čech complex of `P` and the Čech complex of `P ⋙ F`.
* `TauCeti.CategoryTheory.cechComplexFunctorMapHomologyIso`: the isomorphism between `F` applied
  to the cohomology of the Čech complex of `P` and the cohomology of the Čech complex of `P ⋙ F`.

## Main results

* `TauCeti.CategoryTheory.cechComplexFunctorMapIso_hom_app_f_π`: its factors are the images
  under `F` of the projections of the products.
* `TauCeti.CategoryTheory.cechComplexFunctorMapIso_hom_app_comp_cechComplexMap`: it commutes
  with the maps induced by morphisms of families.
* `TauCeti.CategoryTheory.cechComplexFunctorMapHomologyIso_hom_comp_homologyMap_cechComplexMap`:
  the isomorphism on cohomology commutes with the maps induced by morphisms of families.
* `TauCeti.CategoryTheory.cechComplexFunctorMapHomologyIso_hom_naturality`: it is natural in the
  presheaf.
* `TauCeti.CategoryTheory.isZero_homology_cechComplex_comp_iff`: for a faithful `F`, the cohomology
  of `Č(U, P ⋙ F)` vanishes exactly when that of `Č(U, P)` does.
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

/-- The components `cechComplexFunctorMapXIso` are natural in the presheaf. -/
private lemma cechComplexFunctorMapXIso_hom_naturality {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    F.map (((cechComplexFunctor U).map α).f n) ≫ (cechComplexFunctorMapXIso U F Q n).hom =
      (cechComplexFunctorMapXIso U F P n).hom ≫
        ((cechComplexFunctor U).map (Functor.whiskerRight α F)).f n := by
  rw [← cancel_mono (cechXIso U (Q ⋙ F) n).hom]
  refine Pi.hom_ext _ _ fun a ↦ ?_
  simp only [Category.assoc]
  rw [cechComplexFunctorMapXIso_hom_π, ← F.map_comp, cechComplexFunctor_map_f_comp_cechXIso_hom_π,
    cechComplexFunctor_map_f_comp_cechXIso_hom_π]
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
  (_ ≫= (cechXIso_hom_π U (P ⋙ F) n a).symm).trans <|
    (cechComplexFunctorMapXIso_hom_π U F P n a).trans
      (congrArg F.map (cechXIso_hom_π U P n a))

/-- **`cechComplexFunctorMapIso` commutes with refinement maps.** For a morphism `φ` from the
family `U` to a family `V`, applying `F` to the map `Č(V, P) ⟶ Č(U, P)` induced by `φ` and then
identifying with `Č(U, P ⋙ F)` is identifying with `Č(V, P ⋙ F)` and then applying the map
induced by `φ`. -/
@[reassoc]
theorem cechComplexFunctorMapIso_hom_app_comp_cechComplexMap {κ : Type w} {V : κ → C}
    [∀ n : ℕ, PreservesLimitsOfShape (Discrete (Fin (n + 1) → κ)) F] (P : Cᵒᵖ ⥤ A)
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (F.mapHomologicalComplex _).map (cechComplexMap P φ) ≫
        (cechComplexFunctorMapIso U F).hom.app P =
      (cechComplexFunctorMapIso V F).hom.app P ≫ cechComplexMap (P ⋙ F) φ := by
  ext n : 1
  refine Pi.hom_ext _ _ fun a ↦ ?_
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  have h₁ := cechComplexFunctorMapIso_hom_app_f_π U F P n a
  have h₂ := cechComplexMap_f_π (P ⋙ F) φ n a
  have h₃ := cechComplexFunctorMapIso_hom_app_f_π V F P n (φ.f ∘ a)
  have h₄ := (F.map_comp _ _).symm.trans
    ((congrArg F.map (cechComplexMap_f_π P φ n a)).trans (F.map_comp _ _))
  -- the factors of the Čech terms are only defeq to the products they are projected from, so the
  -- steps are composed as terms rather than rewrites
  exact ((Category.assoc _ _ _).trans ((F.map _ ≫= h₁).trans h₄)).trans
    ((h₃ =≫ _).symm.trans ((Category.assoc _ _ _).trans
      ((_ ≫= h₂.symm).trans (Category.assoc _ _ _).symm)))

section Homology

variable [CategoryWithHomology A] [CategoryWithHomology B] [F.PreservesHomology]

/-- **Čech cohomology under a change of coefficients.** For an additive functor `F : A ⥤ B`
preserving homology and the products indexed by `Fin (n + 1) → ι` for every `n`, applying `F` to
the degree `n` cohomology of the Čech complex of a presheaf `P` for the family `U` gives the degree
`n` cohomology of the Čech complex of `P ⋙ F`: homology commutes with `F`
(`CategoryTheory.Functor.mapHomologicalComplexCompHomologyFunctorIso`), and `F` applied to the
Čech complex of `P` is the Čech complex of `P ⋙ F` (`cechComplexFunctorMapIso`). -/
def cechComplexFunctorMapHomologyIso (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    F.obj (((cechComplexFunctor U).obj P).homology n) ≅
      ((cechComplexFunctor U).obj (P ⋙ F)).homology n :=
  ((F.mapHomologicalComplexCompHomologyFunctorIso _ n).app _).symm ≪≫
    HomologicalComplex.homologyMapIso ((cechComplexFunctorMapIso U F).app P) n

/-- The forward map of `cechComplexFunctorMapHomologyIso`: the comparison map of `F` with the
cohomology of the Čech complex, followed by the map on cohomology induced by
`cechComplexFunctorMapIso`. -/
theorem cechComplexFunctorMapHomologyIso_hom (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (cechComplexFunctorMapHomologyIso U F P n).hom =
      (F.mapHomologicalComplexCompHomologyFunctorIso _ n).inv.app ((cechComplexFunctor U).obj P) ≫
        HomologicalComplex.homologyMap ((cechComplexFunctorMapIso U F).hom.app P) n :=
  (rfl)

/-- **`cechComplexFunctorMapHomologyIso` commutes with refinement maps.** For a morphism `φ` from
the family `U` to a family `V`, applying `F` to the map `Hⁿ(Č(V, P)) ⟶ Hⁿ(Č(U, P))` induced by `φ`
and then identifying with `Hⁿ(Č(U, P ⋙ F))` is identifying with `Hⁿ(Č(V, P ⋙ F))` and then
applying the map induced by `φ`. -/
@[reassoc]
theorem cechComplexFunctorMapHomologyIso_hom_comp_homologyMap_cechComplexMap {κ : Type w}
    {V : κ → C} [∀ n : ℕ, PreservesLimitsOfShape (Discrete (Fin (n + 1) → κ)) F] (P : Cᵒᵖ ⥤ A)
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (n : ℕ) :
    F.map (HomologicalComplex.homologyMap (cechComplexMap P φ) n) ≫
        (cechComplexFunctorMapHomologyIso U F P n).hom =
      (cechComplexFunctorMapHomologyIso V F P n).hom ≫
        HomologicalComplex.homologyMap (cechComplexMap (P ⋙ F) φ) n := by
  have ha := (F.mapHomologicalComplexCompHomologyFunctorIso _ n).inv.naturality
    (cechComplexMap P φ)
  have h := congrArg (HomologicalComplex.homologyMap · n)
    (cechComplexFunctorMapIso_hom_app_comp_cechComplexMap U F P φ)
  simp only [HomologicalComplex.homologyMap_comp] at h
  rw [cechComplexFunctorMapHomologyIso_hom, cechComplexFunctorMapHomologyIso_hom]
  -- `ha` is stated for the composite functors, whose objects and maps unfold to the ones in the
  -- goal, so the steps are combined as terms
  exact ((reassoc_of% ha) _).trans ((congrArg (_ ≫ ·) h).trans (Category.assoc _ _ _).symm)

/-- **`cechComplexFunctorMapHomologyIso` is natural in the presheaf.** For a morphism of
presheaves `f : P ⟶ Q`, applying `F` to the map `Hⁿ(Č(U, P)) ⟶ Hⁿ(Č(U, Q))` induced by `f` and
then identifying with `Hⁿ(Č(U, Q ⋙ F))` is identifying with `Hⁿ(Č(U, P ⋙ F))` and then applying
the map induced by `whiskerRight f F`. -/
@[reassoc]
theorem cechComplexFunctorMapHomologyIso_hom_naturality {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) (n : ℕ) :
    F.map (HomologicalComplex.homologyMap ((cechComplexFunctor U).map f) n) ≫
        (cechComplexFunctorMapHomologyIso U F Q n).hom =
      (cechComplexFunctorMapHomologyIso U F P n).hom ≫
        HomologicalComplex.homologyMap
          ((cechComplexFunctor U).map (Functor.whiskerRight f F)) n := by
  have ha := (F.mapHomologicalComplexCompHomologyFunctorIso _ n).inv.naturality
    ((cechComplexFunctor U).map f)
  have h := congrArg (HomologicalComplex.homologyMap · n)
    ((cechComplexFunctorMapIso U F).hom.naturality f)
  simp only [HomologicalComplex.homologyMap_comp] at h
  rw [cechComplexFunctorMapHomologyIso_hom, cechComplexFunctorMapHomologyIso_hom]
  exact ((reassoc_of% ha) _).trans ((congrArg (_ ≫ ·) h).trans (Category.assoc _ _ _).symm)

/-- **Vanishing of Čech cohomology under a faithful change of coefficients.** For a faithful
functor `F`, the degree `n` cohomology of the Čech complex of `P ⋙ F` for the family `U` vanishes
if and only if that of the Čech complex of `P` does. -/
theorem isZero_homology_cechComplex_comp_iff [F.Faithful] (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    IsZero (((cechComplexFunctor U).obj (P ⋙ F)).homology n) ↔
      IsZero (((cechComplexFunctor U).obj P).homology n) := by
  rw [← (cechComplexFunctorMapHomologyIso U F P n).isZero_iff]
  exact ⟨F.isZero_of_isZero_obj, F.map_isZero⟩

end Homology

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
