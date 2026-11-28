/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.ExactFunctor
public import TauCeti.Algebra.Homology.DerivedCategory.Plus.Basic

import TauCeti.Algebra.Homology.DerivedCategory.Functoriality

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
* `CategoryTheory.NatTrans.mapDerivedCategoryPlus`: naturality in morphisms of exact functors,
  with component formula `CategoryTheory.NatTrans.mapDerivedCategoryPlus_app_Q_obj`.

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
  obtain ⟨a, _⟩ := hX
  exact ⟨a, F.isGE_mapDerivedCategory_obj X a⟩

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

/-- Component characterization of `F.mapDerivedCategoryPlusFactors` after applying
`DerivedCategory.Plus.ι`. -/
@[reassoc]
lemma ι_map_mapDerivedCategoryPlusFactors_hom_app (K : CochainComplex.Plus C₁) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlusFactors.hom.app K) =
      F.mapDerivedCategoryPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj K) ≫
        F.mapDerivedCategory.map ((DerivedCategory.Plus.QCompιIso C₁).hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app K.obj ≫
        DerivedCategory.Q.map (F.mapCochainComplexPlusCompι.inv.app K) ≫
        (DerivedCategory.Plus.QCompιIso C₂).inv.app (F.mapCochainComplexPlus.obj K) := by
  simpa only [Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, ObjectProperty.ι_obj, Functor.comp_obj,
    Category.comp_id, Category.id_comp, Category.assoc] using
    NatTrans.congr_app F.whiskerRight_mapDerivedCategoryPlusFactors_hom_ι K

/-- Component characterization of `F.mapDerivedCategoryPlusFactors.inv` after applying
`DerivedCategory.Plus.ι`. -/
@[reassoc]
lemma ι_map_mapDerivedCategoryPlusFactors_inv_app (K : CochainComplex.Plus C₁) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlusFactors.inv.app K) =
      (DerivedCategory.Plus.QCompιIso C₂).hom.app (F.mapCochainComplexPlus.obj K) ≫
        DerivedCategory.Q.map (F.mapCochainComplexPlusCompι.hom.app K) ≫
        F.mapDerivedCategoryFactors.inv.app K.obj ≫
        F.mapDerivedCategory.map ((DerivedCategory.Plus.QCompιIso C₁).inv.app K) ≫
        F.mapDerivedCategoryPlusCompιIso.inv.app (DerivedCategory.Plus.Q.obj K) := by
  rw [← cancel_epi (DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlusFactors.hom.app K)),
    ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id,
    F.ι_map_mapDerivedCategoryPlusFactors_hom_app K]
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp]

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

/-- Evaluate the unbounded homology compatibility `F.mapDerivedCategoryCompHomologyFunctorIso`
at `DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj K)` via naturality along `QCompιIso`. -/
private lemma mapDerivedCategoryCompHomologyFunctorIso_hom_app_ι_Q_obj
    (K : CochainComplex.Plus C₁) (n : ℤ) :
    (F.mapDerivedCategoryCompHomologyFunctorIso n).hom.app
        (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj K)) =
      (DerivedCategory.homologyFunctor C₂ n).map
          (F.mapDerivedCategory.map ((DerivedCategory.Plus.QCompιIso C₁).hom.app K)) ≫
        (DerivedCategory.homologyFunctor C₂ n).map
          (F.mapDerivedCategoryFactors.hom.app K.obj) ≫
        (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj) ≫
        ((K.obj.sc n).mapHomologyIso F).hom ≫
        F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app K.obj) ≫
        F.map ((DerivedCategory.homologyFunctor C₁ n).map
          ((DerivedCategory.Plus.QCompιIso C₁).inv.app K)) := by
  have hnat := (F.mapDerivedCategoryCompHomologyFunctorIso n).hom.naturality
    ((DerivedCategory.Plus.QCompιIso C₁).hom.app K)
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.comp_map] at hnat
  rw [← cancel_mono (F.map ((DerivedCategory.homologyFunctor C₁ n).map
    ((DerivedCategory.Plus.QCompιIso C₁).hom.app K)))]
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Category.assoc, ← F.map_comp,
    ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, Category.comp_id]
  rw [← hnat, F.mapDerivedCategoryCompHomologyFunctorIso_hom_app_Q_obj n K.obj]

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
  -- Transport the `mapDerivedCategoryFactors` prefix through `F.mapDerivedCategoryPlusFactors`.
  have hfac_mor :
      F.mapDerivedCategoryPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj K) ≫
        F.mapDerivedCategory.map ((DerivedCategory.Plus.QCompιIso C₁).hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app K.obj =
      DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlusFactors.hom.app K) ≫
        (DerivedCategory.Plus.QCompιIso C₂).hom.app (F.mapCochainComplexPlus.obj K) ≫
        DerivedCategory.Q.map (F.mapCochainComplexPlusCompι.hom.app K) := by
    rw [F.ι_map_mapDerivedCategoryPlusFactors_hom_app K]
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Category.assoc, Iso.inv_hom_id_app_assoc,
      ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, Category.comp_id]
  have hfac := congrArg (DerivedCategory.homologyFunctor C₂ n).map hfac_mor
  simp only [Functor.map_comp, ← Category.assoc] at hfac
  -- Simplify the `QCompιIso` and `mapCochainComplexPlusCompι` identity factors on each side.
  have hQ₁ :
      F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app K.obj) ≫
        F.map ((DerivedCategory.homologyFunctor C₁ n).map
          ((DerivedCategory.Plus.QCompιIso C₁).inv.app K)) =
      F.map ((TauCeti.DerivedCategory.Plus.homologyFunctorFactors C₁ n).inv.app K) := by
    simp [TauCeti.DerivedCategory.Plus.homologyFunctorFactors_inv_app,
      DerivedCategory.Plus.QCompιIso_inv_app]
    -- `DerivedCategory.Plus.ι.obj (Q.obj K)` is defeq to `DerivedCategory.Q.obj K.obj`.
    rfl
  have hQ₂ :
      (DerivedCategory.homologyFunctor C₂ n).map
          ((DerivedCategory.Plus.QCompιIso C₂).hom.app (F.mapCochainComplexPlus.obj K)) ≫
        (DerivedCategory.homologyFunctor C₂ n).map
          (DerivedCategory.Q.map (F.mapCochainComplexPlusCompι.hom.app K)) ≫
        (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj) =
      (TauCeti.DerivedCategory.Plus.homologyFunctorFactors C₂ n).hom.app
        (F.mapCochainComplexPlus.obj K) := by
    rw [TauCeti.DerivedCategory.Plus.homologyFunctorFactors_hom_app,
      DerivedCategory.Plus.QCompιIso_hom_app, Functor.mapCochainComplexPlusCompι_hom_app]
    dsimp only [DerivedCategory.Plus.Q, Functor.comp_obj, ObjectProperty.ι_obj]
    simp [Functor.mapCochainComplexPlus_obj_obj]
  -- Assemble from the unbounded formula at `ι (Q K)`.
  rw [F.mapDerivedCategoryPlusCompHomologyFunctorIso_hom_app,
    F.mapDerivedCategoryCompHomologyFunctorIso_hom_app_ι_Q_obj]
  simp only [← Category.assoc]
  rw [hfac]
  simp only [Category.assoc, hQ₁,
    ← Functor.mapHomologicalComplexCompHomologyFunctorIso_hom_app F (ComplexShape.up ℤ) n K.obj]
  rw [← Category.assoc _ ((DerivedCategory.homologyFunctorFactors C₂ n).hom.app _),
    ← Category.assoc _ (_ ≫ _), hQ₂]
  dsimp only [DerivedCategory.Plus.homologyFunctor, Functor.comp_map]

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {F G H : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

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

/-- Component formula for `τ.mapDerivedCategoryPlus` on `DerivedCategory.Plus.Q.obj K`. -/
@[reassoc]
lemma mapDerivedCategoryPlus_app_Q_obj (τ : F ⟶ G) (K : CochainComplex.Plus C₁) :
    τ.mapDerivedCategoryPlus.app (DerivedCategory.Plus.Q.obj K) =
      F.mapDerivedCategoryPlusFactors.hom.app K ≫
        DerivedCategory.Plus.Q.map (τ.mapCochainComplexPlus.app K) ≫
        G.mapDerivedCategoryPlusFactors.inv.app K := by
  apply DerivedCategory.Plus.ι.map_injective
  have hτ : DerivedCategory.Plus.ι.map (τ.mapDerivedCategoryPlus.app
      (DerivedCategory.Plus.Q.obj K)) =
      F.mapDerivedCategoryPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj K) ≫
        τ.mapDerivedCategory.app (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj K)) ≫
        G.mapDerivedCategoryPlusCompιIso.inv.app (DerivedCategory.Plus.Q.obj K) := by
    simpa [Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app] using
      NatTrans.congr_app (whiskerRight_mapDerivedCategoryPlus_ι τ)
        (DerivedCategory.Plus.Q.obj K)
  have hQ : DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map (τ.mapCochainComplexPlus.app K)) =
      (DerivedCategory.Plus.QCompιIso C₂).hom.app (F.mapCochainComplexPlus.obj K) ≫
        DerivedCategory.Q.map (F.mapCochainComplexPlusCompι.hom.app K) ≫
        DerivedCategory.Q.map ((τ.mapHomologicalComplex _).app K.obj) ≫
        DerivedCategory.Q.map (G.mapCochainComplexPlusCompι.inv.app K) ≫
        (DerivedCategory.Plus.QCompιIso C₂).inv.app (G.mapCochainComplexPlus.obj K) := by
    have hnat := (DerivedCategory.Plus.QCompιIso C₂).hom.naturality (τ.mapCochainComplexPlus.app K)
    simp only [Functor.comp_obj, Functor.comp_map] at hnat
    rw [← cancel_mono ((DerivedCategory.Plus.QCompιIso C₂).hom.app (G.mapCochainComplexPlus.obj K))]
    simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app, Category.comp_id, hnat]
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    congr 2
    simp [NatTrans.mapCochainComplexPlus_app_hom]
  have happ : τ.mapDerivedCategory.app
      (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj K)) =
      F.mapDerivedCategory.map ((DerivedCategory.Plus.QCompιIso C₁).hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app K.obj ≫
        DerivedCategory.Q.map ((τ.mapHomologicalComplex _).app K.obj) ≫
        G.mapDerivedCategoryFactors.inv.app K.obj ≫
        G.mapDerivedCategory.map ((DerivedCategory.Plus.QCompιIso C₁).inv.app K) := by
    have hnat := τ.mapDerivedCategory.naturality ((DerivedCategory.Plus.QCompιIso C₁).hom.app K)
    simp only [Functor.comp_obj, ObjectProperty.ι_obj] at hnat
    rw [← cancel_mono (G.mapDerivedCategory.map ((DerivedCategory.Plus.QCompιIso C₁).hom.app K))]
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, Functor.map_id, Category.comp_id]
    rw [← hnat, τ.mapDerivedCategory_app_Q_obj K.obj]
  rw [hτ, Functor.map_comp, Functor.map_comp, F.ι_map_mapDerivedCategoryPlusFactors_hom_app K,
    hQ, G.ι_map_mapDerivedCategoryPlusFactors_inv_app K, happ]
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]

instance (τ : F ⟶ G) : NatTrans.CommShift τ.mapDerivedCategoryPlus ℤ :=
  NatTrans.CommShift.of_comp_faithful DerivedCategory.Plus.ι <| by
    rw [whiskerRight_mapDerivedCategoryPlus_ι]
    infer_instance

/-- `NatTrans.mapDerivedCategoryPlus` sends the identity natural transformation to the
identity. -/
@[simp]
lemma mapDerivedCategoryPlus_id (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    mapDerivedCategoryPlus (𝟙 F) = 𝟙 F.mapDerivedCategoryPlus := by
  apply ((DerivedCategory.TStructure.t (C := C₂)).plus.fullyFaithfulι.whiskeringRight
    _).map_injective
  simp only [Functor.whiskeringRight_obj_map, whiskerRight_mapDerivedCategoryPlus_ι,
    mapDerivedCategory_id, Functor.whiskerRight_id']
  ext X
  simp

/-- `NatTrans.mapDerivedCategoryPlus` preserves composition of natural transformations. -/
@[simp]
lemma mapDerivedCategoryPlus_comp (τ₁ : F ⟶ G) (τ₂ : G ⟶ H) :
    (τ₁ ≫ τ₂).mapDerivedCategoryPlus =
      τ₁.mapDerivedCategoryPlus ≫ τ₂.mapDerivedCategoryPlus := by
  apply ((DerivedCategory.TStructure.t (C := C₂)).plus.fullyFaithfulι.whiskeringRight
    _).map_injective
  simp only [Functor.whiskeringRight_obj_map, Functor.whiskerRight_comp,
    whiskerRight_mapDerivedCategoryPlus_ι, mapDerivedCategory_comp]
  ext X
  simp

end CategoryTheory.NatTrans
