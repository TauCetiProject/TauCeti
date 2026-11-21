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
open HomotopyCategory.Bounded (mkMap mkMap_comp_assoc singleFunctorObjIsoMk mkSingleIsoShift)

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

variable (F : C ⥤ D) [F.Additive] [HasZeroObject C] [HasZeroObject D]

/-- The comparison `(F X₀ ⟶ F X₁) ⟶ F (X₀ ⟶ X₁)` of two-term complexes, in `Kᵇ(D)`. -/
private noncomputable abbrev doubleComparisonMk {X₀ X₁ : C} (g : X₀ ⟶ X₁) :
    HomotopyCategory.Bounded.mk _
        (CochainComplex.bounded_double (F.map g) ComplexShape.up_rel_zero_one) ⟶
      F.mapHomotopyCategoryBounded.obj (HomotopyCategory.Bounded.mk _
        (CochainComplex.bounded_double g ComplexShape.up_rel_zero_one)) :=
  mkMap (HomologicalComplex.doubleToMapHomologicalComplex F g ComplexShape.up_rel_zero_one
    zero_ne_one) ≫ (F.mapHomotopyCategoryBoundedMkIso _ _).inv

private theorem singleFunctorIso_hom_app_comp_resolution (S : ShortComplex C) :
    (F.mapHomotopyCategoryBoundedSingleFunctorIso 0).hom.app S.X₁ ≫ resolution (S.map F) ≫
        doubleComparisonMk F S.g =
      F.mapHomotopyCategoryBounded.map (resolution S) := by
  have h : mkMap (S.map F).doubleι ≫ doubleComparisonMk F S.g =
      (F.mapHomotopyCategoryBoundedMkSingleIso 0 S.X₁).inv ≫
        F.mapHomotopyCategoryBounded.map (mkMap S.doubleι) := by
    rw [Functor.mapHomotopyCategoryBoundedMkSingleIso_inv, Category.assoc,
      ← Functor.mkMap_comp_mapHomotopyCategoryBoundedMkIso_inv, ← mkMap_comp_assoc,
      ← mkMap_comp_assoc, ShortComplex.map_doubleι_comp_doubleToMapHomologicalComplex]
  rw [resolution, resolution, Category.assoc, h, Functor.map_comp,
    ← Functor.mapHomotopyCategoryBoundedSingleFunctorIso_hom_app_comp F 0 S.X₁, Category.assoc,
    Category.assoc]
  -- `(S.map F).X₁` is `F.obj S.X₁` by definition.
  rfl

private theorem doubleInclusion_comp_doubleComparisonMk {X₀ X₁ : C} (g : X₀ ⟶ X₁) :
    doubleInclusion (F.map g) ≫ doubleComparisonMk F g =
      (F.mapHomotopyCategoryBoundedMkSingleIso 1 X₁).inv ≫
        F.mapHomotopyCategoryBounded.map (doubleInclusion g) := by
  rw [Functor.mapHomotopyCategoryBoundedMkSingleIso_inv, Category.assoc,
    ← Functor.mkMap_comp_mapHomotopyCategoryBoundedMkIso_inv, ← mkMap_comp_assoc,
    ← mkMap_comp_assoc, HomologicalComplex.doubleι₁_comp_doubleToMapHomologicalComplex]

private theorem singleFunctorIso_hom_app_comp_singleShift (Z : C) :
    (F.mapHomotopyCategoryBoundedSingleFunctorIso 0).hom.app Z ≫ singleShift (F.obj Z) ≫
        (F.mapHomotopyCategoryBoundedMkSingleIso 1 Z).inv⟦(1 : ℤ)⟧' =
      F.mapHomotopyCategoryBounded.map (singleShift Z) ≫
        (F.mapHomotopyCategoryBounded.commShiftIso (1 : ℤ)).hom.app _ := by
  rw [singleShift, singleShift, Category.assoc,
    Functor.mkSingleIsoShift_hom_comp_shift_mapHomotopyCategoryBoundedMkSingleIso_inv,
    Functor.mapHomotopyCategoryBoundedSingleFunctorIso_hom_app_comp_assoc, Functor.map_comp,
    Category.assoc]

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
      ((BoundedDerivedCategory.Q E').map
        (F.mapHomotopyCategoryBoundedMkSingleIso 1 X₁).inv)⟦(1 : ℤ)⟧' ≫
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
