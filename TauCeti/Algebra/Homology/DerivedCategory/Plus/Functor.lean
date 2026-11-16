/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Exact functors and homology on bounded-below derived categories

An exact functor `F : C₁ ⥤ C₂` between abelian categories preserves cohomological boundedness
below and therefore restricts from Mathlib's `F.mapDerivedCategory` to a triangulated functor
`F.mapDerivedCategoryPlus : DerivedCategory.Plus C₁ ⥤ DerivedCategory.Plus C₂` commuting with
shifts, with the localization functor `DerivedCategory.Plus.Q`, with single-object embeddings, and
with cohomology functors.

We also record basic conveniences for `DerivedCategory.Plus`: factorization of
`DerivedCategory.Plus.homologyFunctor` through `DerivedCategory.Plus.Q`, homotopy invariance of
`DerivedCategory.Plus.Q`, and the commutation of `F.mapDerivedCategory` with
`DerivedCategory.homologyFunctor`.

## Main definitions and results

* `DerivedCategory.Plus.homologyFunctorFactors`: `Q ⋙ homologyFunctor C n` identifies with
  termwise homology `HomologicalComplex.homologyFunctor`.
* `DerivedCategory.Plus.Q_map_eq_of_homotopy`: homotopic morphisms of bounded-below cochain
  complexes induce the same morphism in `DerivedCategory.Plus C`.
* `CategoryTheory.Functor.mapDerivedCategoryCompHomologyFunctorIso`: exact functors commute with
  `DerivedCategory.homologyFunctor`.
* `CategoryTheory.Functor.mapDerivedCategoryPlus`: the triangulated functor
  `DerivedCategory.Plus C₁ ⥤ DerivedCategory.Plus C₂` induced by an exact functor `F`.
* `CategoryTheory.Functor.mapDerivedCategoryPlusFactors`: `Q ⋙ F.mapDerivedCategoryPlus ≅
  F.mapCochainComplexPlus ⋙ Q`, compatible with shifts.
* `CategoryTheory.Functor.mapDerivedCategoryPlusSingleFunctor`: compatibility with single-object
  embeddings in every degree.
* `CategoryTheory.Functor.mapDerivedCategoryPlusCompHomologyFunctorIso`: compatibility with
  cohomology functors in every degree.
* `CategoryTheory.NatTrans.mapDerivedCategoryPlus`: naturality in morphisms of exact functors.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace DerivedCategory.Plus

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]

variable (C) in
/-- The cohomology of `DerivedCategory.Plus.Q.obj K` is naturally isomorphic to the cohomology of
the underlying bounded-below cochain complex `K.obj`. -/
def homologyFunctorFactors (n : ℤ) :
    DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor C n ≅
      CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n :=
  NatIso.ofComponents
    (fun K ↦ (DerivedCategory.homologyFunctorFactors C n).app K.obj)
    (fun f ↦ (DerivedCategory.homologyFunctorFactors C n).hom.naturality f.hom)

@[reassoc]
lemma homologyFunctorFactors_hom_naturality {K L : CochainComplex.Plus C} (f : K ⟶ L) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor C n).map (DerivedCategory.Plus.Q.map f) ≫
        (homologyFunctorFactors C n).hom.app L =
      (homologyFunctorFactors C n).hom.app K ≫ HomologicalComplex.homologyMap f.hom n :=
  (homologyFunctorFactors C n).hom.naturality f

@[simp]
lemma homologyFunctorFactors_hom_app (K : CochainComplex.Plus C) (n : ℤ) :
    (homologyFunctorFactors C n).hom.app K =
      (DerivedCategory.homologyFunctorFactors C n).hom.app K.obj := by
  dsimp only [homologyFunctorFactors]
  rfl

/-- Homotopic morphisms of bounded-below cochain complexes induce the same morphism in
`DerivedCategory.Plus C`. -/
lemma Q_map_eq_of_homotopy {K L : CochainComplex.Plus C} {f g : K ⟶ L}
    (h : Homotopy f.hom g.hom) :
    DerivedCategory.Plus.Q.map f = DerivedCategory.Plus.Q.map g := by
  apply DerivedCategory.Plus.ι.map_injective
  rw [← cancel_mono ((QCompιIso C).hom.app L)]
  have hf := (QCompιIso C).hom.naturality f
  have hg := (QCompιIso C).hom.naturality g
  dsimp at hf hg ⊢
  rw [hf, hg, DerivedCategory.Q_map_eq_of_homotopy C h]

/-- A quasi-isomorphism in `CochainComplex.Plus C` becomes an isomorphism in
`DerivedCategory.Plus C`. -/
lemma isIso_Q_map_of_quasiIso {K L : CochainComplex.Plus C} (f : K ⟶ L) [QuasiIso f.hom] :
    IsIso (DerivedCategory.Plus.Q.map f) :=
  Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C) f
    (show QuasiIso f.hom from inferInstance)

end DerivedCategory.Plus

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor commutes with `DerivedCategory.homologyFunctor` in every degree. -/
def mapDerivedCategoryCompHomologyFunctorIso (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n ≅
      DerivedCategory.homologyFunctor C₁ n ⋙ F :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n)
    (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor C₁ n ⋙ F)
    (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n)
    (DerivedCategory.homologyFunctor C₁ n ⋙ F)
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight F.mapDerivedCategoryFactors (DerivedCategory.homologyFunctor C₂ n) ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (F.mapHomologicalComplex _)
        (DerivedCategory.homologyFunctorFactors C₂ n) ≪≫
      F.mapHomologicalComplexCompHomologyFunctorIso (ComplexShape.up ℤ) n ≪≫
      isoWhiskerRight (DerivedCategory.homologyFunctorFactors C₁ n).symm F ≪≫
      Functor.associator _ _ _)

@[reassoc]
lemma mapDerivedCategoryCompHomologyFunctorIso_hom_app_Q_obj
    (K : CochainComplex C₁ ℤ) (n : ℤ) :
    (F.mapDerivedCategoryCompHomologyFunctorIso n).hom.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.homologyFunctor C₂ n).map (F.mapDerivedCategoryFactors.hom.app K) ≫
        (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
          ((F.mapHomologicalComplex _).obj K) ≫
        (F.mapHomologicalComplexCompHomologyFunctorIso (ComplexShape.up ℤ) n).hom.app K ≫
        F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app K) := by
  simp [mapDerivedCategoryCompHomologyFunctorIso]

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
