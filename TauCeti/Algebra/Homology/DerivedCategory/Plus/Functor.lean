/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Triangulated.Functor
public import TauCeti.Algebra.Homology.DerivedCategory.ExactFunctor
public import TauCeti.Algebra.Homology.DerivedCategory.Plus.Basic

/-!
# Exact functors on bounded-below derived categories

An exact functor `F : C₁ ⥤ C₂` between abelian categories preserves cohomological boundedness
below and therefore restricts from Mathlib's `F.mapDerivedCategory` to a triangulated functor
`F.mapDerivedCategoryPlus : DerivedCategory.Plus C₁ ⥤ DerivedCategory.Plus C₂` commuting with
shifts, with the localization functor `DerivedCategory.Plus.Q`, with single-object embeddings, and
with cohomology functors.

## Main definitions and results

* `CategoryTheory.Functor.mapDerivedCategoryPlus`: the triangulated functor
  `DerivedCategory.Plus C₁ ⥤ DerivedCategory.Plus C₂` induced by an exact functor `F`.
* `CategoryTheory.Functor.mapDerivedCategoryPlusCompιIso`: inclusion into the unbounded derived
  category identifies `F.mapDerivedCategoryPlus` with `F.mapDerivedCategory`.
* `CategoryTheory.Functor.mapDerivedCategoryPlusFactors`: `Q ⋙ F.mapDerivedCategoryPlus ≅
  F.mapCochainComplexPlus ⋙ Q`, compatible with shifts.
* `CategoryTheory.Functor.mapDerivedCategoryPlusSingleFunctor`: compatibility with single-object
  embeddings in every degree.
* `CategoryTheory.Functor.mapDerivedCategoryPlusCompHomologyFunctorIso`: compatibility with
  cohomology functors in every degree.
* `CategoryTheory.NatTrans.mapDerivedCategoryPlus`: naturality in morphisms of exact functors.

## References

* `TauCeti/Algebra/Homology/DerivedCategory/Bounded/Functor.lean`, whose `DerivedCategory.Bounded`
  exact-functor construction (`bounded_mapDerivedCategory`, `mapBoundedDerivedCategory`,
  `mapBoundedDerivedCategoryCompιIso`, and `mapBoundedDerivedCategorySingleFunctor`) is adapted
  here to `DerivedCategory.Plus`.
* Mathlib's `Mathlib/Algebra/Homology/HomotopyCategory/Plus.lean` (specifically
  `Functor.mapHomotopyCategoryPlus` and
  `whiskerRight_quotientCompMapHomotopyCategoryPlusIso_hom_ι`), whose factorization pattern is
  followed for `mapDerivedCategoryPlusFactors` and
  `whiskerRight_mapDerivedCategoryPlusFactors_hom_ι`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor preserves cohomological boundedness below in the derived category. -/
lemma plus_mapDerivedCategory (X : DerivedCategory C₁)
    (hX : (DerivedCategory.TStructure.t (C := C₁)).plus X) :
    (DerivedCategory.TStructure.t (C := C₂)).plus (F.mapDerivedCategory.obj X) := by
  obtain ⟨a, ha⟩ := hX
  obtain ⟨K, _, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE a
  let L : CochainComplex C₂ ℤ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have : L.IsGE a := by
    rw [CochainComplex.isGE_iff]
    exact fun i hi ↦ (K.exactAt_of_isGE a i hi).map F
  exact (DerivedCategory.TStructure.t (C := C₂)).plus.prop_of_iso
    (F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K).symm
    ⟨a, by
      simpa only [Functor.comp_obj] using (DerivedCategory.isGE_Q_obj_iff L a).2 ‹L.IsGE a›⟩

/-- The triangulated functor `DerivedCategory.Plus C₁ ⥤ DerivedCategory.Plus C₂` induced by an
exact functor `F : C₁ ⥤ C₂` between abelian categories. -/
def mapDerivedCategoryPlus : DerivedCategory.Plus C₁ ⥤ DerivedCategory.Plus C₂ :=
  (DerivedCategory.TStructure.t (C := C₂)).plus.lift
    (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory)
    (fun X ↦ F.plus_mapDerivedCategory X.obj X.property)

/-- Inclusion into the unbounded derived category identifies `F.mapDerivedCategoryPlus` with
`F.mapDerivedCategory`. -/
def mapDerivedCategoryPlusCompιIso :
    F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory :=
  (DerivedCategory.TStructure.t (C := C₂)).plus.liftCompιIso _ _

instance : F.mapDerivedCategoryPlus.CommShift ℤ :=
  Functor.CommShift.ofComp F.mapDerivedCategoryPlusCompιIso ℤ

instance : NatTrans.CommShift F.mapDerivedCategoryPlusCompιIso.hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

instance : F.mapDerivedCategoryPlus.IsTriangulated := by
  rw [Functor.isTriangulated_iff_comp_right F.mapDerivedCategoryPlusCompιIso]
  infer_instance

/-- The functor `F.mapDerivedCategoryPlus` is induced by `F.mapCochainComplexPlus`. -/
def mapDerivedCategoryPlusFactors :
    DerivedCategory.Plus.Q ⋙ F.mapDerivedCategoryPlus ≅
      F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q :=
  ((DerivedCategory.TStructure.t (C := C₂)).plus.fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft DerivedCategory.Plus.Q F.mapDerivedCategoryPlusCompιIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (DerivedCategory.Plus.QCompιIso C₁) F.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (CochainComplex.Plus.ι C₁) F.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight F.mapCochainComplexPlusCompι.symm DerivedCategory.Q ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft F.mapCochainComplexPlus (DerivedCategory.Plus.QCompιIso C₂).symm ≪≫
      (Functor.associator _ _ _).symm)

@[reassoc]
lemma whiskerRight_mapDerivedCategoryPlusFactors_hom_ι :
    whiskerRight F.mapDerivedCategoryPlusFactors.hom DerivedCategory.Plus.ι =
      (Functor.associator _ _ _).hom ≫
        whiskerLeft DerivedCategory.Plus.Q F.mapDerivedCategoryPlusCompιIso.hom ≫
        (Functor.associator _ _ _).inv ≫
        whiskerRight (DerivedCategory.Plus.QCompιIso C₁).hom F.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom ≫
        whiskerLeft (CochainComplex.Plus.ι C₁) F.mapDerivedCategoryFactors.hom ≫
        (Functor.associator _ _ _).inv ≫
        whiskerRight F.mapCochainComplexPlusCompι.inv DerivedCategory.Q ≫
        (Functor.associator _ _ _).hom ≫
        whiskerLeft F.mapCochainComplexPlus (DerivedCategory.Plus.QCompιIso C₂).inv ≫
        (Functor.associator _ _ _).inv :=
  ((DerivedCategory.TStructure.t (C := C₂)).plus.fullyFaithfulι.whiskeringRight _).map_preimage _

instance : NatTrans.CommShift F.mapDerivedCategoryPlusFactors.hom ℤ :=
  NatTrans.CommShift.of_comp_faithful DerivedCategory.Plus.ι <| by
    rw [whiskerRight_mapDerivedCategoryPlusFactors_hom_ι]
    infer_instance

/-- `F.mapDerivedCategoryPlus` commutes with `DerivedCategory.Plus.singleFunctor` in every
degree. -/
def mapDerivedCategoryPlusSingleFunctor (n : ℤ) :
    DerivedCategory.Plus.singleFunctor C₁ n ⋙ F.mapDerivedCategoryPlus ≅
      F ⋙ DerivedCategory.Plus.singleFunctor C₂ n :=
  ((DerivedCategory.TStructure.t (C := C₂)).plus.fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ F.mapDerivedCategoryPlusCompιIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso C₁ n) F.mapDerivedCategory ≪≫
      F.mapDerivedCategorySingleFunctor n ≪≫
      isoWhiskerLeft F (DerivedCategory.Plus.singleFunctorιIso C₂ n).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- Characterizing identity for `F.mapDerivedCategoryPlusSingleFunctor` after whiskering with
`DerivedCategory.Plus.ι`. -/
@[reassoc]
lemma whiskerRight_mapDerivedCategoryPlusSingleFunctor_hom_ι (n : ℤ) :
    whiskerRight (F.mapDerivedCategoryPlusSingleFunctor n).hom DerivedCategory.Plus.ι =
      (Functor.associator _ _ _).hom ≫
        whiskerLeft (DerivedCategory.Plus.singleFunctor C₁ n)
          F.mapDerivedCategoryPlusCompιIso.hom ≫
        (Functor.associator _ _ _).inv ≫
        whiskerRight (DerivedCategory.Plus.singleFunctorιIso C₁ n).hom F.mapDerivedCategory ≫
        (F.mapDerivedCategorySingleFunctor n).hom ≫
        whiskerLeft F (DerivedCategory.Plus.singleFunctorιIso C₂ n).inv ≫
        (Functor.associator _ _ _).inv :=
  ((DerivedCategory.TStructure.t (C := C₂)).plus.fullyFaithfulι.whiskeringRight _).map_preimage _

/-- `F.mapDerivedCategoryPlus` commutes with `DerivedCategory.Plus.homologyFunctor` in every
degree. -/
def mapDerivedCategoryPlusCompHomologyFunctorIso (n : ℤ) :
    F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.homologyFunctor C₂ n ≅
      DerivedCategory.Plus.homologyFunctor C₁ n ⋙ F :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight F.mapDerivedCategoryPlusCompιIso
      (DerivedCategory.homologyFunctor C₂ n) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft DerivedCategory.Plus.ι (F.mapDerivedCategoryCompHomologyFunctorIso n) ≪≫
    (Functor.associator _ _ _).symm

/-- Component formula for `F.mapDerivedCategoryPlusCompHomologyFunctorIso`. -/
@[reassoc]
lemma mapDerivedCategoryPlusCompHomologyFunctorIso_hom_app (n : ℤ)
    (X : DerivedCategory.Plus C₁) :
    (F.mapDerivedCategoryPlusCompHomologyFunctorIso n).hom.app X =
      (DerivedCategory.homologyFunctor C₂ n).map
          (F.mapDerivedCategoryPlusCompιIso.hom.app X) ≫
        (F.mapDerivedCategoryCompHomologyFunctorIso n).hom.app (DerivedCategory.Plus.ι.obj X) := by
  dsimp only [mapDerivedCategoryPlusCompHomologyFunctorIso, DerivedCategory.Plus.homologyFunctor]
  simp

/-- On `DerivedCategory.Plus.Q.obj K`, `F.mapDerivedCategoryPlusCompHomologyFunctorIso` agrees
with `F.mapDerivedCategoryPlusFactors`, `TauCeti.DerivedCategory.Plus.homologyFunctorFactors`, and
`F.mapHomologicalComplexCompHomologyFunctorIso`. -/
@[reassoc]
lemma mapDerivedCategoryPlusCompHomologyFunctorIso_hom_app_Q_obj
    (K : CochainComplex.Plus C₁) (n : ℤ) :
    (F.mapDerivedCategoryPlusCompHomologyFunctorIso n).hom.app (DerivedCategory.Plus.Q.obj K) =
      (DerivedCategory.Plus.homologyFunctor C₂ n).map
          (F.mapDerivedCategoryPlusFactors.hom.app K) ≫
        (TauCeti.DerivedCategory.Plus.homologyFunctorFactors C₂ n).hom.app
          (F.mapCochainComplexPlus.obj K) ≫
        (F.mapHomologicalComplexCompHomologyFunctorIso (ComplexShape.up ℤ) n).hom.app K.obj ≫
        F.map ((TauCeti.DerivedCategory.Plus.homologyFunctorFactors C₁ n).inv.app K) := by
  have hfac : DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlusFactors.hom.app K) =
      F.mapDerivedCategoryPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj K) ≫
        F.mapDerivedCategoryFactors.hom.app K.obj := by
    have h := NatTrans.congr_app F.whiskerRight_mapDerivedCategoryPlusFactors_hom_ι K
    simp only [Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerLeft_app, Category.comp_id, Category.id_comp] at h
    have h2 : F.mapDerivedCategoryFactors.hom.app ((CochainComplex.Plus.ι C₁).obj K) ≫
        DerivedCategory.Q.map (F.mapCochainComplexPlusCompι.inv.app K) ≫
        (DerivedCategory.Plus.QCompιIso C₂).inv.app (F.mapCochainComplexPlus.obj K) =
        F.mapDerivedCategoryFactors.hom.app K.obj := by
      have h2a : DerivedCategory.Q.map (F.mapCochainComplexPlusCompι.inv.app K) ≫
          (DerivedCategory.Plus.QCompιIso C₂).inv.app (F.mapCochainComplexPlus.obj K) = 𝟙 _ := by
        dsimp [Functor.mapCochainComplexPlus]
        rw [Functor.mapCochainComplexPlusCompι_inv_app, DerivedCategory.Plus.QCompιIso_inv_app,
          DerivedCategory.Q.map_id, Category.id_comp]
        rfl
      rw [h2a]
      exact Category.comp_id _
    have h1 : F.mapDerivedCategory.map ((DerivedCategory.Plus.QCompιIso C₁).hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app K.obj =
        F.mapDerivedCategoryFactors.hom.app K.obj := by
      dsimp [DerivedCategory.Plus.Q]
      rw [DerivedCategory.Plus.QCompιIso_hom_app, F.mapDerivedCategory.map_id, Category.id_comp]
    rw [h2, h1] at h
    exact h
  have hH : (DerivedCategory.Plus.homologyFunctor C₂ n).map
        (F.mapDerivedCategoryPlusFactors.hom.app K) =
      (DerivedCategory.homologyFunctor C₂ n).map
          (F.mapDerivedCategoryPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj K)) ≫
        (DerivedCategory.homologyFunctor C₂ n).map
          (F.mapDerivedCategoryFactors.hom.app K.obj) := by
    rw [← Functor.map_comp]
    exact congrArg (DerivedCategory.homologyFunctor C₂ n).map hfac
  have hQ : (F.mapDerivedCategoryCompHomologyFunctorIso n).hom.app
        (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj K)) =
      (DerivedCategory.homologyFunctor C₂ n).map (F.mapDerivedCategoryFactors.hom.app K.obj) ≫
        (TauCeti.DerivedCategory.Plus.homologyFunctorFactors C₂ n).hom.app
          (F.mapCochainComplexPlus.obj K) ≫
        (F.mapHomologicalComplexCompHomologyFunctorIso (ComplexShape.up ℤ) n).hom.app K.obj ≫
        F.map ((TauCeti.DerivedCategory.Plus.homologyFunctorFactors C₁ n).inv.app K) := by
    rw [TauCeti.DerivedCategory.Plus.homologyFunctorFactors_hom_app,
      TauCeti.DerivedCategory.Plus.homologyFunctorFactors_inv_app]
    exact F.mapDerivedCategoryCompHomologyFunctorIso_hom_app_Q_obj K.obj n
  exact (F.mapDerivedCategoryPlusCompHomologyFunctorIso_hom_app n _).trans
    ((congrArg (_ ≫ ·) hQ).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hH.symm)))

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {F G : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- A natural transformation between exact functors induces a natural transformation between their
actions on bounded-below derived categories. -/
def mapDerivedCategoryPlus (τ : F ⟶ G) :
    F.mapDerivedCategoryPlus ⟶ G.mapDerivedCategoryPlus :=
  ((DerivedCategory.TStructure.t (C := C₂)).plus.fullyFaithfulι.whiskeringRight _).preimage
    (F.mapDerivedCategoryPlusCompιIso.hom ≫
      whiskerLeft DerivedCategory.Plus.ι τ.mapDerivedCategory ≫
      G.mapDerivedCategoryPlusCompιIso.inv)

@[reassoc]
lemma whiskerRight_mapDerivedCategoryPlus_ι (τ : F ⟶ G) :
    whiskerRight τ.mapDerivedCategoryPlus DerivedCategory.Plus.ι =
      F.mapDerivedCategoryPlusCompιIso.hom ≫
        whiskerLeft DerivedCategory.Plus.ι τ.mapDerivedCategory ≫
        G.mapDerivedCategoryPlusCompιIso.inv :=
  ((DerivedCategory.TStructure.t (C := C₂)).plus.fullyFaithfulι.whiskeringRight _).map_preimage _

instance (τ : F ⟶ G) : NatTrans.CommShift τ.mapDerivedCategoryPlus ℤ :=
  NatTrans.CommShift.of_comp_faithful DerivedCategory.Plus.ι <| by
    rw [whiskerRight_mapDerivedCategoryPlus_ι]
    infer_instance

end CategoryTheory.NatTrans
