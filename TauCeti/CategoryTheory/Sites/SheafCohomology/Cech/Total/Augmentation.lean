/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Total.Basic

import TauCeti.Algebra.Homology.TotalComplex.UpInt

/-!
# Augmentation of the total Čech complex

Sections of an integer-graded presheaf of complexes map canonically to its total Čech complex.
This construction needs neither boundedness nor a covering condition. Its component in degree
`n` is the restriction to Čech degree zero followed by the native total inclusion at `(0,n)`.

## References

* The Stacks Project, Cohomology of Sheaves, §20.25, equation (20.25.0.1): the augmentation
  from sections to the total Čech complex.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex₂

universe w v u v' u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasZeroObject A]
  [HasProducts.{w} A] [HasCoproducts.{0} A]
  {ι κ : Type w} (U : ι → C) {V : κ → C}
  {T : C} (hT : IsTerminal T) (P : Cᵒᵖ ⥤ CochainComplex A ℤ)

/-- Restriction of sections to the zero Čech column, transported along zero extension. -/
def cechTotalComplexAugmentationColumn : P.obj (op T) ⟶
    (((cechComplexFunctor U).obj P).extend ComplexShape.embeddingUpNat).X 0 :=
  (HomologicalComplex.singleObjXSelf _ 0 _).inv ≫ (cechAugmentation U hT P).f 0 ≫
    (((cechComplexFunctor U).obj P).extendXIso ComplexShape.embeddingUpNat
      (i := 0) rfl).inv

omit [HasCoproducts.{0} A] in
/-- The zero-column map is the ordinary Čech augmentation, transported to the extended column. -/
lemma cechTotalComplexAugmentationColumn_def :
    cechTotalComplexAugmentationColumn U hT P =
      (HomologicalComplex.singleObjXSelf _ 0 _).inv ≫ (cechAugmentation U hT P).f 0 ≫
        (((cechComplexFunctor U).obj P).extendXIso ComplexShape.embeddingUpNat
          (i := 0) rfl).inv := (rfl)

omit [HasCoproducts.{0} A] in
/-- Restriction to the zero Čech column is killed by the Čech differential. -/
lemma cechTotalComplexAugmentationColumn_comp_d :
    cechTotalComplexAugmentationColumn U hT P ≫
      (((cechComplexFunctor U).obj P).extend ComplexShape.embeddingUpNat).d 0 1 = 0 := by
  rw [cechTotalComplexAugmentationColumn,
    HomologicalComplex.extend_d_eq _ ComplexShape.embeddingUpNat
    (i := 0) (j := 1) (i' := (0 : ℤ)) (j' := (1 : ℤ)) rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [(cechAugmentation U hT P).comm_assoc,
    HomologicalComplex.single_obj_d, zero_comp, comp_zero]

/-- The canonical map from sections over a terminal object to the total Čech complex of an
arbitrary integer-graded presheaf of complexes. -/
def cechTotalComplexAugmentation : P.obj (op T) ⟶ (cechTotalComplexFunctor U).obj P :=
  totalCoaugmentationUpInt _ (cechTotalComplexAugmentationColumn U hT P)
    (cechTotalComplexAugmentationColumn_comp_d U hT P)

/-- In degree `n`, the augmentation restricts to Čech degree zero and includes bidegree `(0,n)`
in the native direct-sum total. -/
@[simp]
lemma cechTotalComplexAugmentation_f (n : ℤ) :
    (cechTotalComplexAugmentation U hT P).f n =
      ((HomologicalComplex.singleObjXSelf _ 0 _).inv ≫
        (cechAugmentation U hT P).f 0 ≫
          (((cechComplexFunctor U).obj P).extendXIso ComplexShape.embeddingUpNat
            (i := 0) rfl).inv).f n ≫
      ιTotal _ (ComplexShape.up ℤ) 0 n n (zero_add n) := by
  unfold cechTotalComplexAugmentation
  rw [totalCoaugmentationUpInt_f, cechTotalComplexAugmentationColumn_def]

omit [HasCoproducts.{0} A] in
private lemma cechTotalComplexAugmentationColumn_naturality
    {Q : Cᵒᵖ ⥤ CochainComplex A ℤ} (α : P ⟶ Q) :
    cechTotalComplexAugmentationColumn U hT P ≫
      (HomologicalComplex.extendMap ((cechComplexFunctor U).map α)
        ComplexShape.embeddingUpNat).f 0 =
      α.app (op T) ≫ cechTotalComplexAugmentationColumn U hT Q := by
  rw [cechTotalComplexAugmentationColumn, cechTotalComplexAugmentationColumn,
    HomologicalComplex.extendMap_f _
    ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h := congrArg (fun f ↦ f.f 0) (cechAugmentation_naturality U hT P α)
  simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] at h
  simp [reassoc_of% h]

/-- The total Čech augmentation is natural in the coefficient presheaf of complexes. -/
@[reassoc]
lemma cechTotalComplexAugmentation_naturality {Q : Cᵒᵖ ⥤ CochainComplex A ℤ}
    (α : P ⟶ Q) :
    cechTotalComplexAugmentation U hT P ≫ (cechTotalComplexFunctor U).map α =
      α.app (op T) ≫ cechTotalComplexAugmentation U hT Q := by
  ext n
  simp only [HomologicalComplex.comp_f, cechTotalComplexAugmentation_f,
    ← cechTotalComplexAugmentationColumn_def]
  rw [cechTotalComplexFunctor_map, Category.assoc, ιTotal_map,
    ← Category.assoc, ← HomologicalComplex.comp_f, cechTotalComplexAugmentationColumn_naturality]
  simp

omit [HasCoproducts.{0} A] in
private lemma cechTotalComplexAugmentationColumn_refinement
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    cechTotalComplexAugmentationColumn V hT P ≫
      (HomologicalComplex.extendMap (cechComplexMap P φ)
        ComplexShape.embeddingUpNat).f 0 = cechTotalComplexAugmentationColumn U hT P := by
  rw [cechTotalComplexAugmentationColumn, cechTotalComplexAugmentationColumn,
    HomologicalComplex.extendMap_f _
    ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h := congrArg (fun f ↦ f.f 0) (cechAugmentation_comp_cechComplexMap hT P φ)
  simp only [HomologicalComplex.comp_f] at h
  rw [reassoc_of% h]

/-- Restricting sections and then applying any raw refinement gives the same augmentation. -/
@[reassoc (attr := simp)]
lemma cechTotalComplexAugmentation_refinement
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    cechTotalComplexAugmentation V hT P ≫ cechTotalComplexMap P φ =
      cechTotalComplexAugmentation U hT P := by
  ext n
  simp only [HomologicalComplex.comp_f, cechTotalComplexAugmentation_f,
    ← cechTotalComplexAugmentationColumn_def]
  rw [Category.assoc, ι_cechTotalComplexMap,
    ← Category.assoc, ← HomologicalComplex.comp_f, cechTotalComplexAugmentationColumn_refinement]

/-- The total Čech augmentation, as a natural transformation in the coefficient presheaf. -/
def cechTotalComplexAugmentationNatTrans :
    (evaluation Cᵒᵖ (CochainComplex A ℤ)).obj (op T) ⟶ cechTotalComplexFunctor U where
  app P := cechTotalComplexAugmentation U hT P
  naturality _ _ α := (cechTotalComplexAugmentation_naturality U hT _ α).symm

@[simp]
lemma cechTotalComplexAugmentationNatTrans_app (Q : Cᵒᵖ ⥤ CochainComplex A ℤ) :
    (cechTotalComplexAugmentationNatTrans U hT).app Q =
      cechTotalComplexAugmentation U hT Q := (rfl)

end TauCeti.CategoryTheory
