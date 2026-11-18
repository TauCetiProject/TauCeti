/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Functor
public import TauCeti.CategoryTheory.Exact.DerivedCategory.Conflation

/-!
# Conflation-exact functors preserve connecting morphisms

Let `F : C ⥤ D` be a conflation-exact functor between exact categories `E` and `E'`. The induced
triangle functor `Dᵇ(E) ⥤ Dᵇ(E')` sends the connecting morphism `Z ⟶ X⟦1⟧` of a conflation
`X ↣ Y ↠ Z` to the connecting morphism of the image conflation `F X ↣ F Y ↠ F Z`, up to the
identifications of the functor with the shift and with objects placed in degree zero.

The connecting morphism is determined in `Kᵇ(C)` by the resolution `X ⟶ (Y ⟶ Z)` of the first
term (`TauCeti.ExactStructure.BoundedDerivedCategory.conflationδ_comp_shift_map_doubleι`). Applying
`F` termwise to the complexes and chain maps of that description gives the description for the
image conflation.

## Main results

* `TauCeti.ExactStructure.IsConflationExact.mapBoundedDerivedCategory_map_conflationδ`: the
  functor `Dᵇ(E) ⥤ Dᵇ(E')` preserves connecting morphisms of conflations.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
open HomotopyCategory.Bounded (mkMap mkMap_comp_assoc ι_map_mkMap singleFunctorObjIsoMk
  mkSingleIsoShift)

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Preadditive C] [Category.{v₂} D]
  [Preadditive D]

namespace IsConflationExact

section Description

variable {A : Type*} [Category A] [Preadditive A] [HasZeroObject A]

/-- The resolution `X ⟶ (Y ⟶ Z)` of the first term of a short complex, in `Kᵇ(A)`. -/
private noncomputable abbrev resolution (S : ShortComplex A) :
    (HomotopyCategory.Bounded.singleFunctor A 0).obj S.X₁ ⟶
      HomotopyCategory.Bounded.mk _
        (CochainComplex.bounded_double S.g ComplexShape.up_rel_zero_one) :=
  (singleFunctorObjIsoMk 0 S.X₁).hom ≫ mkMap S.doubleι

/-- The identification `Z[0] ≅ Z[-1]⟦1⟧`, in `Kᵇ(A)`. -/
private noncomputable abbrev singleShift (Z : A) :
    (HomotopyCategory.Bounded.singleFunctor A 0).obj Z ⟶
      (HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single 1 Z))⟦(1 : ℤ)⟧ :=
  (singleFunctorObjIsoMk 0 Z).hom ≫ (mkSingleIsoShift 1 0 1 (by simp) Z).hom

/-- The inclusion `Z[-1] ⟶ (Y ⟶ Z)`, in `Kᵇ(A)`. -/
private noncomputable abbrev doubleInclusion {Y Z : A} (g : Y ⟶ Z) :
    HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single 1 Z) ⟶
      HomotopyCategory.Bounded.mk _
        (CochainComplex.bounded_double g ComplexShape.up_rel_zero_one) :=
  mkMap (HomologicalComplex.doubleι₁ g ComplexShape.up_rel_zero_one zero_ne_one)

end Description

section Complexes

variable (F : C ⥤ D) [F.Additive]

/-- The image in `Kᵇ(D)` of the class of a bounded complex is the class of its termwise image. -/
private noncomputable def mapMkIso (K : CochainComplex C ℤ) (hK : CochainComplex.bounded C K) :
    F.mapHomotopyCategoryBounded.obj (HomotopyCategory.Bounded.mk K hK) ≅
      HomotopyCategory.Bounded.mk _ (F.bounded_mapHomologicalComplex hK) :=
  (HomotopyCategory.Bounded.fullyFaithfulι D).preimageIso
    (F.mapHomotopyCategoryBoundedCompι.app (HomotopyCategory.Bounded.mk K hK))

private theorem ι_map_mapMkIso_inv (K : CochainComplex C ℤ) (hK : CochainComplex.bounded C K) :
    (HomotopyCategory.Bounded.ι D).map (mapMkIso F K hK).inv =
      F.mapHomotopyCategoryBoundedCompι.inv.app (HomotopyCategory.Bounded.mk K hK) :=
  (HomotopyCategory.Bounded.fullyFaithfulι D).map_preimage _

private theorem mkMap_comp_mapMkIso_inv {K L : CochainComplex C ℤ}
    {hK : CochainComplex.bounded C K} {hL : CochainComplex.bounded C L} (φ : K ⟶ L) :
    mkMap ((F.mapHomologicalComplex (.up ℤ)).map φ) ≫ (mapMkIso F L hL).inv =
      (mapMkIso F K hK).inv ≫ F.mapHomotopyCategoryBounded.map (mkMap φ) := by
  apply (HomotopyCategory.Bounded.ι D).map_injective
  rw [Functor.map_comp, Functor.map_comp, ι_map_mapMkIso_inv, ι_map_mapMkIso_inv]
  exact F.mapHomotopyCategoryBoundedCompι.inv.naturality
    (mkMap φ : HomotopyCategory.Bounded.mk K hK ⟶ HomotopyCategory.Bounded.mk L hL)

variable [HasZeroObject C] [HasZeroObject D]

/-- The comparison `(F X₀ ⟶ F X₁) ⟶ F (X₀ ⟶ X₁)` of two-term complexes. -/
private noncomputable def doubleComparison {X₀ X₁ : C} (g : X₀ ⟶ X₁) :
    HomologicalComplex.double (F.map g) ComplexShape.up_rel_zero_one ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.double g ComplexShape.up_rel_zero_one) :=
  HomologicalComplex.mkHomFromDouble _ zero_ne_one
    (F.map (HomologicalComplex.doubleXIso₀ g ComplexShape.up_rel_zero_one).inv)
    (F.map (HomologicalComplex.doubleXIso₁ g ComplexShape.up_rel_zero_one zero_ne_one).inv)
    (by
      rw [Functor.mapHomologicalComplex_obj_d, HomologicalComplex.double_d g _ zero_ne_one,
        ← F.map_comp, ← F.map_comp, Iso.inv_hom_id_assoc])
    (fun k _ ↦ by
      rw [Functor.mapHomologicalComplex_obj_d,
        HomologicalComplex.double_d_eq_zero₀ g _ _ _ one_ne_zero, F.map_zero, comp_zero])

private theorem doubleι_comp_doubleComparison (S : ShortComplex C) :
    (S.map F).doubleι ≫ doubleComparison F S.g =
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app S.X₁ ≫
        (F.mapHomologicalComplex (.up ℤ)).map S.doubleι := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ShortComplex.doubleι_f_zero,
    doubleComparison, HomologicalComplex.mkHomFromDouble_f₀,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f, ShortComplex.doubleι_f_zero]
  simp only [ShortComplex.map_f, ShortComplex.map_g, ShortComplex.map_X₁, Category.assoc,
    Iso.inv_hom_id_assoc,
    ← CategoryTheory.Functor.map_comp]

private theorem doubleι₁_comp_doubleComparison {X₀ X₁ : C} (g : X₀ ⟶ X₁) :
    HomologicalComplex.doubleι₁ (F.map g) ComplexShape.up_rel_zero_one zero_ne_one ≫
        doubleComparison F g =
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 1).inv.app X₁ ≫
        (F.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.doubleι₁ g ComplexShape.up_rel_zero_one zero_ne_one) := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.doubleι₁_f₁,
    doubleComparison, HomologicalComplex.mkHomFromDouble_f₁,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f, HomologicalComplex.doubleι₁_f₁]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp]

private theorem singleMapHomologicalComplex_inv_app_comp_shiftIso (X : C) :
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app X ≫
        (F.mapHomologicalComplex (.up ℤ)).map
          (((CochainComplex.singleFunctors C).shiftIso 1 0 1 (by simp)).inv.app X) ≫
        ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app _ =
      ((CochainComplex.singleFunctors D).shiftIso 1 0 1 (by simp)).inv.app (F.obj X) ≫
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 1).inv.app X)⟦(1 : ℤ)⟧' := by
  apply HomologicalComplex.from_single_hom_ext
  simp [CochainComplex.singleFunctors, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq, eqToHom_map]

/-- The comparison `X[n] ⟶ F (X[n])` of single complexes, in `Kᵇ(D)`. -/
private noncomputable def singleComparison (n : ℤ) (X : C) :
    HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single n (F.obj X)) ⟶
      F.mapHomotopyCategoryBounded.obj
        (HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single n X)) :=
  mkMap ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).inv.app X) ≫
    (mapMkIso F _ _).inv

private theorem ι_map_singleComparison_comp (n : ℤ) (X : C) :
    (HomotopyCategory.Bounded.ι D).map (singleComparison F n X) ≫
        F.mapHomotopyCategoryBoundedCompι.hom.app _ =
      (HomotopyCategory.quotient D (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).inv.app X) := by
  rw [singleComparison, Functor.map_comp, ι_map_mkMap, ι_map_mapMkIso_inv, Category.assoc,
    Iso.inv_hom_id_app]
  exact Category.comp_id _

private theorem singleFunctorIso_hom_app_comp (X : C) :
    (F.mapHomotopyCategoryBoundedSingleFunctorIso 0).hom.app X ≫
        (singleFunctorObjIsoMk 0 (F.obj X)).hom ≫ singleComparison F 0 X =
      F.mapHomotopyCategoryBounded.map (singleFunctorObjIsoMk 0 X).hom := by
  apply (HomotopyCategory.Bounded.ι D).map_injective
  rw [← cancel_mono (F.mapHomotopyCategoryBoundedCompι.hom.app _)]
  have h := F.mapHomotopyCategoryBoundedCompι.hom.naturality (singleFunctorObjIsoMk 0 X).hom
  simp only [Functor.comp_map, HomotopyCategory.Bounded.ι_map_singleFunctorObjIsoMk_hom] at h
  rw [h, Functor.map_comp, Functor.map_comp, singleComparison, Functor.map_comp,
    Functor.ι_map_mapHomotopyCategoryBoundedSingleFunctorIso_hom_app,
    HomotopyCategory.Bounded.ι_map_singleFunctorObjIsoMk_hom, ι_map_mkMap, ι_map_mapMkIso_inv]
  simp only [Category.assoc]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc, Category.assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  rfl

private theorem ι_map_mkSingleIsoShift_hom_comp_shift_singleComparison (X : C) :
    (HomotopyCategory.Bounded.ι D).map
        ((mkSingleIsoShift 1 0 1 (by simp) (F.obj X)).hom ≫ (singleComparison F 1 X)⟦(1 : ℤ)⟧') ≫
        ((HomotopyCategory.Bounded.ι D).commShiftIso (1 : ℤ)).hom.app _ ≫
        (F.mapHomotopyCategoryBoundedCompι.hom.app
          (HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single 1 X)))⟦(1 : ℤ)⟧' =
      (HomotopyCategory.quotient D (.up ℤ)).map
        (((CochainComplex.singleFunctors D).shiftIso 1 0 1 (by simp)).inv.app (F.obj X) ≫
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 1).inv.app X)⟦(1 : ℤ)⟧') ≫
        ((HomotopyCategory.quotient D (.up ℤ)).commShiftIso (1 : ℤ)).hom.app _ := by
  rw [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality_assoc,
    HomotopyCategory.Bounded.ι_map_mkSingleIsoShift_hom]
  -- `erw`: the objects of the composites agree only up to unfolding the composite functors.
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    ι_map_singleComparison_comp, ← Functor.commShiftIso_hom_naturality, ← Functor.map_comp_assoc]
  rfl

private theorem ι_map_singleComparison_comp_map_mkSingleIsoShift_hom (X : C) :
    (HomotopyCategory.Bounded.ι D).map (singleComparison F 0 X ≫
        F.mapHomotopyCategoryBounded.map (mkSingleIsoShift 1 0 1 (by simp) X).hom ≫
        (F.mapHomotopyCategoryBounded.commShiftIso (1 : ℤ)).hom.app _) ≫
        ((HomotopyCategory.Bounded.ι D).commShiftIso (1 : ℤ)).hom.app _ ≫
        (F.mapHomotopyCategoryBoundedCompι.hom.app
          (HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single 1 X)))⟦(1 : ℤ)⟧' =
      (HomotopyCategory.quotient D (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app X ≫
          (F.mapHomologicalComplex (.up ℤ)).map
            (((CochainComplex.singleFunctors C).shiftIso 1 0 1 (by simp)).inv.app X) ≫
          ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app _) ≫
        ((HomotopyCategory.quotient D (.up ℤ)).commShiftIso (1 : ℤ)).hom.app _ := by
  have h₂ := NatTrans.shift_app_comm (F.mapHomotopyCategoryFactors (.up ℤ)).hom (1 : ℤ)
    ((HomologicalComplex.single C (.up ℤ) 1).obj X)
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app,
    Functor.mapHomotopyCategoryFactors_hom_app, Functor.mapHomotopyCategoryFactors_hom_app] at h₂
  -- `erw`: the identities sit on objects which agree with their neighbours only up to unfolding.
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at h₂
  have h₃ := F.mapHomotopyCategoryBoundedCompι.hom.naturality
    (mkSingleIsoShift 1 0 1 (by simp) X).hom
  rw [Functor.comp_map, Functor.comp_map] at h₃
  rw [Functor.map_comp (HomotopyCategory.Bounded.ι D) (singleComparison F 0 X),
    Functor.map_comp (HomotopyCategory.Bounded.ι D)
      (F.mapHomotopyCategoryBounded.map (mkSingleIsoShift 1 0 1 (by simp) X).hom),
    Category.assoc, Category.assoc,
    ← Category.assoc ((HomotopyCategory.Bounded.ι D).map
      ((F.mapHomotopyCategoryBounded.commShiftIso (1 : ℤ)).hom.app _)),
    ← Functor.commShiftIso_comp_hom_app, NatTrans.shift_app_comm, reassoc_of% h₃,
    reassoc_of% ι_map_singleComparison_comp, Functor.commShiftIso_comp_hom_app,
    HomotopyCategory.Bounded.ι_map_mkSingleIsoShift_hom]
  erw [← Functor.map_comp_assoc, Category.assoc, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, Functor.map_comp, Category.assoc, h₂, Functor.mapHomotopyCategory_map,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc]
  rfl

private theorem mkSingleIsoShift_hom_comp_shift_singleComparison (X : C) :
    (mkSingleIsoShift 1 0 1 (by simp) (F.obj X)).hom ≫ (singleComparison F 1 X)⟦(1 : ℤ)⟧' =
      singleComparison F 0 X ≫
        F.mapHomotopyCategoryBounded.map (mkSingleIsoShift 1 0 1 (by simp) X).hom ≫
        (F.mapHomotopyCategoryBounded.commShiftIso (1 : ℤ)).hom.app _ := by
  apply (HomotopyCategory.Bounded.ι D).map_injective
  rw [← cancel_mono (((HomotopyCategory.Bounded.ι D).commShiftIso (1 : ℤ)).hom.app _ ≫
    (F.mapHomotopyCategoryBoundedCompι.hom.app
      (HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single 1 X)))⟦(1 : ℤ)⟧')]
  refine (ι_map_mkSingleIsoShift_hom_comp_shift_singleComparison F X).trans
    (Eq.trans ?_ (ι_map_singleComparison_comp_map_mkSingleIsoShift_hom F X).symm)
  rw [singleMapHomologicalComplex_inv_app_comp_shiftIso]
  rfl

/-- The comparison `(F X₀ ⟶ F X₁) ⟶ F (X₀ ⟶ X₁)` of two-term complexes, in `Kᵇ(D)`. -/
private noncomputable def doubleComparisonMk {X₀ X₁ : C} (g : X₀ ⟶ X₁) :
    HomotopyCategory.Bounded.mk _
        (CochainComplex.bounded_double (F.map g) ComplexShape.up_rel_zero_one) ⟶
      F.mapHomotopyCategoryBounded.obj (HomotopyCategory.Bounded.mk _
        (CochainComplex.bounded_double g ComplexShape.up_rel_zero_one)) :=
  mkMap (doubleComparison F g) ≫ (mapMkIso F _ _).inv

private theorem singleFunctorIso_hom_app_comp_resolution (S : ShortComplex C) :
    (F.mapHomotopyCategoryBoundedSingleFunctorIso 0).hom.app S.X₁ ≫ resolution (S.map F) ≫
        doubleComparisonMk F S.g =
      F.mapHomotopyCategoryBounded.map (resolution S) := by
  have h : mkMap (S.map F).doubleι ≫ doubleComparisonMk F S.g =
      singleComparison F 0 S.X₁ ≫ F.mapHomotopyCategoryBounded.map (mkMap S.doubleι) := by
    rw [doubleComparisonMk, singleComparison, Category.assoc, ← mkMap_comp_mapMkIso_inv,
      ← mkMap_comp_assoc, ← mkMap_comp_assoc, doubleι_comp_doubleComparison]
  rw [resolution, resolution, Category.assoc, h, Functor.map_comp,
    ← singleFunctorIso_hom_app_comp F S.X₁, Category.assoc, Category.assoc]
  rfl

private theorem doubleInclusion_comp_doubleComparisonMk {X₀ X₁ : C} (g : X₀ ⟶ X₁) :
    doubleInclusion (F.map g) ≫ doubleComparisonMk F g =
      singleComparison F 1 X₁ ≫ F.mapHomotopyCategoryBounded.map (doubleInclusion g) := by
  rw [doubleComparisonMk, singleComparison, Category.assoc, ← mkMap_comp_mapMkIso_inv,
    ← mkMap_comp_assoc, ← mkMap_comp_assoc, doubleι₁_comp_doubleComparison]

private theorem singleFunctorIso_hom_app_comp_singleShift (Z : C) :
    (F.mapHomotopyCategoryBoundedSingleFunctorIso 0).hom.app Z ≫ singleShift (F.obj Z) ≫
        (singleComparison F 1 Z)⟦(1 : ℤ)⟧' =
      F.mapHomotopyCategoryBounded.map (singleShift Z) ≫
        (F.mapHomotopyCategoryBounded.commShiftIso (1 : ℤ)).hom.app _ := by
  rw [singleShift, singleShift, Category.assoc, mkSingleIsoShift_hom_comp_shift_singleComparison,
    reassoc_of% singleFunctorIso_hom_app_comp, Functor.map_comp, Category.assoc]

end Complexes

variable [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]
  (hF : E.IsConflationExact E' F)

/-- The image of a morphism `δ : A ⟶ P⟦1⟧` of `Dᵇ(E)` described in `Kᵇ(C)`: if `δ` followed by
the shift of `y : P ⟶ M` is the shift of `-v` for `v : B ⟶ M`, after `u : A ⟶ B⟦1⟧`, then the same
holds for its image under `hF.mapBoundedDerivedCategory`, with the images of `u`, `v` and `y`. -/
private theorem map_comp_shift_map {A B M P : HomotopyCategory.Bounded C}
    (δ : (BoundedDerivedCategory.Q E).obj A ⟶ ((BoundedDerivedCategory.Q E).obj P)⟦(1 : ℤ)⟧)
    (u : A ⟶ B⟦(1 : ℤ)⟧) (v : B ⟶ M) (y : P ⟶ M)
    (h : δ ≫ ((BoundedDerivedCategory.Q E).map y)⟦(1 : ℤ)⟧' =
      (BoundedDerivedCategory.Q E).map u ≫
        ((BoundedDerivedCategory.Q E).commShiftIso (1 : ℤ)).hom.app B ≫
        (-((BoundedDerivedCategory.Q E).map v)⟦(1 : ℤ)⟧')) :
    hF.mapBoundedDerivedCategory.map δ ≫
        (hF.mapBoundedDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
        (hF.mapBoundedDerivedCategoryFactors.hom.app P ≫
          (BoundedDerivedCategory.Q E').map (F.mapHomotopyCategoryBounded.map y))⟦(1 : ℤ)⟧' =
      hF.mapBoundedDerivedCategoryFactors.hom.app A ≫
        (BoundedDerivedCategory.Q E').map (F.mapHomotopyCategoryBounded.map u ≫
          (F.mapHomotopyCategoryBounded.commShiftIso (1 : ℤ)).hom.app B) ≫
        ((BoundedDerivedCategory.Q E').commShiftIso (1 : ℤ)).hom.app _ ≫
        (-((BoundedDerivedCategory.Q E').map (F.mapHomotopyCategoryBounded.map v))⟦(1 : ℤ)⟧') := by
  have e₁ : (hF.mapBoundedDerivedCategory.map ((BoundedDerivedCategory.Q E).map v))⟦(1 : ℤ)⟧' ≫
      (hF.mapBoundedDerivedCategoryFactors.hom.app M)⟦(1 : ℤ)⟧' =
      (hF.mapBoundedDerivedCategoryFactors.hom.app B)⟦(1 : ℤ)⟧' ≫
        ((BoundedDerivedCategory.Q E').map (F.mapHomotopyCategoryBounded.map v))⟦(1 : ℤ)⟧' := by
    rw [← Functor.map_comp, hF.mapBoundedDerivedCategoryFactors_hom_naturality, Functor.map_comp]
  have e₂ := NatTrans.shift_app_comm hF.mapBoundedDerivedCategoryFactors.hom (1 : ℤ) B
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app, Category.assoc] at e₂
  rw [← hF.mapBoundedDerivedCategoryFactors_hom_naturality y, Functor.map_comp,
    ← Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp_assoc, h]
  simp only [Functor.map_comp, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg,
    Category.assoc, Functor.commShiftIso_hom_naturality_assoc]
  rw [e₁, reassoc_of% e₂, hF.mapBoundedDerivedCategoryFactors_hom_naturality_assoc]

omit [HasBinaryBiproducts C] in
private theorem doubleInclusion_comp_doubleComparisonMk_shift {X₀ X₁ : C} (g : X₀ ⟶ X₁) :
    (-((BoundedDerivedCategory.Q E').map (doubleInclusion (F.map g)))⟦(1 : ℤ)⟧') ≫
      ((BoundedDerivedCategory.Q E').map (doubleComparisonMk F g))⟦(1 : ℤ)⟧' =
      ((BoundedDerivedCategory.Q E').map (singleComparison F 1 X₁))⟦(1 : ℤ)⟧' ≫
        (-((BoundedDerivedCategory.Q E').map
          (F.mapHomotopyCategoryBounded.map (doubleInclusion g)))⟦(1 : ℤ)⟧') := by
  rw [Preadditive.neg_comp, Preadditive.comp_neg, ← Functor.map_comp, ← Functor.map_comp,
    doubleInclusion_comp_doubleComparisonMk, Functor.map_comp, Functor.map_comp]

/-- The connecting morphism of the image conflation, followed by the shifted resolution of its
first term, in terms of the images under `F` of the complexes and chain maps describing it. -/
private theorem singleFunctorIso_hom_app_comp_conflationδ_comp {S : ShortComplex C}
    (hS : E.Conflation S) :
    ((hF.mapBoundedDerivedCategorySingleFunctorIso 0).hom.app S.X₃ ≫
      BoundedDerivedCategory.conflationδ (hF.map_conflation hS)) ≫
      ((BoundedDerivedCategory.Q E').map
        (resolution (S.map F) ≫ doubleComparisonMk F S.g))⟦(1 : ℤ)⟧' =
      hF.mapBoundedDerivedCategoryFactors.hom.app _ ≫
        (BoundedDerivedCategory.Q E').map (F.mapHomotopyCategoryBounded.map (singleShift S.X₃) ≫
          (F.mapHomotopyCategoryBounded.commShiftIso (1 : ℤ)).hom.app _) ≫
        ((BoundedDerivedCategory.Q E').commShiftIso (1 : ℤ)).hom.app _ ≫
        (-((BoundedDerivedCategory.Q E').map
          (F.mapHomotopyCategoryBounded.map (doubleInclusion S.g)))⟦(1 : ℤ)⟧') := by
  rw [Category.assoc, Functor.map_comp (BoundedDerivedCategory.Q E') (resolution (S.map F)),
    Functor.map_comp (shiftFunctor _ (1 : ℤ)),
    reassoc_of% (BoundedDerivedCategory.conflationδ_comp_shift_map_doubleι
      (hF.map_conflation hS))]
  dsimp only [ShortComplex.map_X₃, ShortComplex.map_g]
  rw [doubleInclusion_comp_doubleComparisonMk_shift, ← Functor.commShiftIso_hom_naturality_assoc,
    mapBoundedDerivedCategorySingleFunctorIso_hom_app, Category.assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    singleFunctorIso_hom_app_comp_singleShift]

/-- **A conflation-exact functor preserves connecting morphisms of conflations**: the image under
`Dᵇ(E) ⥤ Dᵇ(E')` of the connecting morphism `Z ⟶ X⟦1⟧` of a conflation `X ↣ Y ↠ Z` is the
connecting morphism of the image conflation, up to the identifications of the functor with the
shift and with objects placed in degree zero. -/
theorem mapBoundedDerivedCategory_map_conflationδ {S : ShortComplex C} (hS : E.Conflation S) :
    hF.mapBoundedDerivedCategory.map (BoundedDerivedCategory.conflationδ hS) ≫
        (hF.mapBoundedDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
        ((hF.mapBoundedDerivedCategorySingleFunctorIso 0).hom.app S.X₁)⟦(1 : ℤ)⟧' =
      (hF.mapBoundedDerivedCategorySingleFunctorIso 0).hom.app S.X₃ ≫
        BoundedDerivedCategory.conflationδ (hF.map_conflation hS) := by
  have k₁ := singleFunctorIso_hom_app_comp_resolution F S
  have hy : IsIso ((BoundedDerivedCategory.Q E).map (resolution S)) := by
    have := BoundedDerivedCategory.isIso_Q_map_mkMap_doubleι hS
    rw [resolution, Functor.map_comp]
    infer_instance
  have hy' : IsIso ((BoundedDerivedCategory.Q E').map
      (F.mapHomotopyCategoryBounded.map (resolution S))) :=
    (NatIso.isIso_map_iff hF.mapBoundedDerivedCategoryFactors (resolution S)).1
      (inferInstanceAs (IsIso (hF.mapBoundedDerivedCategory.map _)))
  have : IsIso ((BoundedDerivedCategory.Q E').map
      (resolution (S.map F) ≫ doubleComparisonMk F S.g)) := by
    rw [← k₁, Functor.map_comp] at hy'
    exact IsIso.of_isIso_comp_left ((BoundedDerivedCategory.Q E').map
      ((F.mapHomotopyCategoryBoundedSingleFunctorIso 0).hom.app S.X₁)) _
  rw [← cancel_mono (((BoundedDerivedCategory.Q E').map
    (resolution (S.map F) ≫ doubleComparisonMk F S.g))⟦(1 : ℤ)⟧'),
    singleFunctorIso_hom_app_comp_conflationδ_comp hF hS, Category.assoc,
    Category.assoc, ← Functor.map_comp, mapBoundedDerivedCategorySingleFunctorIso_hom_app,
    Category.assoc, ← Functor.map_comp, k₁]
  exact map_comp_shift_map hF _ _ _ _
    (BoundedDerivedCategory.conflationδ_comp_shift_map_doubleι hS)

end IsConflationExact

end TauCeti.ExactStructure
