/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import TauCeti.Algebra.Homology.Embedding.Extend.Basic

/-!
# Single complexes, mapping cones, truncations, and composition on `CochainComplex.Plus`

This file provides general constructions on Mathlib's category `CochainComplex.Plus C` of
bounded-below `ℤ`-indexed cochain complexes under minimal categorical hypotheses:

* `TauCeti.CochainComplex.Plus.singleFunctor` and `singleFunctorCompιIso`: the single-object
  embedding `C ⥤ CochainComplex.Plus C` in degree `n : ℤ` (for `[HasZeroMorphisms C]` and
  `[HasZeroObject C]`).
* `CategoryTheory.InjectiveResolution.extendResolution` and `extendResolution_naturality`:
  the bounded-below resolution `X[0] ⟶ extend I.cocomplex` induced by an injective resolution
  `I` of `X`, together with its `QuasiIso` instance and naturality.
* `CochainComplex.Plus.mappingCone`, `mappingConeTriangle`, and
  `mappingConeTriangleιIso`: mapping cones and mapping cone triangles in `CochainComplex.Plus C`
  (for `[Preadditive C]` and `[HasBinaryBiproducts C]`).
* `CochainComplex.Plus.truncLE`, `truncGE`, `ιTruncLE`, and `πTruncGE`: canonical truncations on
  `CochainComplex.Plus C` together with their `QuasiIso` instances under `IsLE`/`IsGE` (for
  `[HasZeroMorphisms C]`, `[HasZeroObject C]`, and `[∀ i, K.obj.HasHomology i]`).
* `CategoryTheory.Functor.mapCochainComplexPlusCompIso` (with its `NatTrans.CommShift` instance)
  and `CategoryTheory.NatTrans.isIso_mapCochainComplexPlus`: functoriality of
  `Functor.mapCochainComplexPlus` with respect to composition and natural isomorphisms.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace TauCeti.CochainComplex.Plus

section Single

variable (C : Type u₁) [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The functor `C ⥤ CochainComplex.Plus C` sending `X` to the cochain complex concentrated in
degree `n : ℤ`. -/
@[expose, implicit_reducible]
def singleFunctor (n : ℤ) : C ⥤ _root_.CochainComplex.Plus C :=
  ObjectProperty.lift _ (HomologicalComplex.single C (.up ℤ) n)
    (fun _ ↦ ⟨n, inferInstance⟩)

/-- Inclusion into `CochainComplex C ℤ` identifies `singleFunctor C n` with
`HomologicalComplex.single C (.up ℤ) n`. -/
def singleFunctorCompιIso (n : ℤ) :
    singleFunctor C n ⋙ _root_.CochainComplex.Plus.ι C ≅
      HomologicalComplex.single C (.up ℤ) n :=
  ObjectProperty.liftCompιIso _ _ _

variable {C}

@[simp]
lemma singleFunctor_obj_obj (n : ℤ) (X : C) :
    ((singleFunctor C n).obj X).obj = (HomologicalComplex.single C (.up ℤ) n).obj X :=
  rfl

@[simp]
lemma singleFunctor_map_hom (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    ((singleFunctor C n).map f).hom = (HomologicalComplex.single C (.up ℤ) n).map f :=
  rfl

instance hasHomology_singleFunctor_obj (n : ℤ) (X : C) (i : ℤ) :
    ((singleFunctor C n).obj X).obj.HasHomology i :=
  inferInstanceAs (((HomologicalComplex.single C (.up ℤ) n).obj X).HasHomology i)

@[simp]
lemma singleFunctorCompιIso_hom_app (n : ℤ) (X : C) :
    (singleFunctorCompιIso C n).hom.app X = 𝟙 _ :=
  (rfl)

@[simp]
lemma singleFunctorCompιIso_inv_app (n : ℤ) (X : C) :
    (singleFunctorCompιIso C n).inv.app X = 𝟙 _ :=
  (rfl)

end Single

end TauCeti.CochainComplex.Plus

namespace CategoryTheory.InjectiveResolution

section BoundedBelow

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The bounded-below resolution `X[0] ⟶ extend I.cocomplex` in `CochainComplex.Plus C`
induced by an injective resolution `I` of `X`. -/
def extendResolution {X : C} (I : InjectiveResolution X) :
    (TauCeti.CochainComplex.Plus.singleFunctor C 0).obj X ⟶
      ⟨I.cocomplex.extend ComplexShape.embeddingUpNat,
        (_root_.CochainComplex.plus_iff C _).2 ⟨0, inferInstance⟩⟩ :=
  ObjectProperty.homMk
    ((TauCeti.CochainComplex.Plus.singleFunctorCompιIso C 0).hom.app X ≫
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0
        (ComplexShape.embeddingUpNat_f 0)).inv ≫
      HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)

/-- Underlying cochain-complex morphism of `I.extendResolution`. -/
@[simp]
lemma extendResolution_hom {X : C} (I : InjectiveResolution X) :
    I.extendResolution.hom =
      (TauCeti.CochainComplex.Plus.singleFunctorCompιIso C 0).hom.app X ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0
          (ComplexShape.embeddingUpNat_f 0)).inv ≫
        HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat :=
  (rfl)

instance quasiIso_extendResolution_hom {X : C} (I : InjectiveResolution X) :
    QuasiIso I.extendResolution.hom := by
  rw [extendResolution_hom]
  infer_instance

/-- Naturality of `extendResolution` with respect to a lifting morphism `φ` of injective
resolutions. -/
lemma extendResolution_naturality {X Y : C} (f : X ⟶ Y)
    (IX : InjectiveResolution X) (IY : InjectiveResolution Y)
    (φ : IX.cocomplex ⟶ IY.cocomplex)
    (hφ : IX.ι ≫ φ = (_root_.CochainComplex.single₀ C).map f ≫ IY.ι) :
    IX.extendResolution ≫
        (ObjectProperty.homMk (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) :
          (⟨IX.cocomplex.extend ComplexShape.embeddingUpNat,
            (_root_.CochainComplex.plus_iff C _).2 ⟨0, inferInstance⟩⟩ :
              _root_.CochainComplex.Plus C) ⟶
          ⟨IY.cocomplex.extend ComplexShape.embeddingUpNat,
            (_root_.CochainComplex.plus_iff C _).2 ⟨0, inferInstance⟩⟩) =
      (TauCeti.CochainComplex.Plus.singleFunctor C 0).map f ≫ IY.extendResolution := by
  apply (_root_.CochainComplex.Plus.ι C).map_injective
  change IX.extendResolution.hom ≫ HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat =
    ((TauCeti.CochainComplex.Plus.singleFunctor C 0).map f).hom ≫ IY.extendResolution.hom
  simp only [extendResolution_hom, TauCeti.CochainComplex.Plus.singleFunctorCompιIso_hom_app,
    TauCeti.CochainComplex.Plus.singleFunctor_map_hom, Category.id_comp, Category.assoc]
  rw [← HomologicalComplex.extendMap_comp, hφ, HomologicalComplex.extendMap_comp]
  dsimp only [_root_.CochainComplex.single₀]
  rw [← ComplexShape.embeddingUpNat.extendSingleIso_inv_naturality_assoc f (i := 0) (i' := 0)
    (by simp)]

end BoundedBelow

end CategoryTheory.InjectiveResolution

namespace CochainComplex.Plus

section MappingCone

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The mapping cone of a morphism `f : K ⟶ L` in `CochainComplex.Plus C`, as a bounded-below
cochain complex. -/
@[expose]
def mappingCone {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    CochainComplex.Plus C :=
  ⟨_root_.CochainComplex.mappingCone f.hom, by
    obtain ⟨n₁, _⟩ := K.property
    obtain ⟨n₂, _⟩ := L.property
    exact ⟨min (n₁ - 1) n₂, _root_.CochainComplex.isStrictlyGE_mappingCone f.hom n₁ n₂
      (min (n₁ - 1) n₂) (by omega) (by omega)⟩⟩

@[simp]
lemma mappingCone_obj {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingCone f).obj = _root_.CochainComplex.mappingCone f.hom :=
  rfl

/-- The mapping cone triangle `K ⟶ L ⟶ cone(f) ⟶ K⟦1⟧` in `CochainComplex.Plus C`. -/
@[expose]
def mappingConeTriangle {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    Triangle (CochainComplex.Plus C) :=
  Triangle.mk f
    (ObjectProperty.homMk (_root_.CochainComplex.mappingCone.inr f.hom) :
      L ⟶ mappingCone f)
    ((CochainComplex.Plus.fullyFaithfulι C).preimage
      ((_root_.CochainComplex.mappingCone.triangle f.hom).mor₃ ≫
        ((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).inv.app K))

@[simp]
lemma mappingConeTriangle_obj₁ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangle f).obj₁ = K :=
  rfl

@[simp]
lemma mappingConeTriangle_obj₂ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangle f).obj₂ = L :=
  rfl

@[simp]
lemma mappingConeTriangle_obj₃ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangle f).obj₃ = mappingCone f :=
  rfl

@[simp]
lemma mappingConeTriangle_mor₁ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangle f).mor₁ = f :=
  rfl

@[simp]
lemma mappingConeTriangle_mor₂_hom {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangle f).mor₂.hom = _root_.CochainComplex.mappingCone.inr f.hom :=
  rfl

/-- Characterizing equation for the connecting morphism of `mappingConeTriangle f` after inclusion
into `CochainComplex C ℤ`. -/
@[reassoc (attr := simp)]
lemma mappingConeTriangle_mor₃_hom_comp {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangle f).mor₃.hom ≫
        ((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).hom.app K =
      (_root_.CochainComplex.mappingCone.triangle f.hom).mor₃ := by
  have h := (CochainComplex.Plus.fullyFaithfulι C).map_preimage
    (X := mappingCone f) (Y := K⟦(1 : ℤ)⟧)
    ((_root_.CochainComplex.mappingCone.triangle f.hom).mor₃ ≫
      ((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).inv.app K)
  simpa [mappingConeTriangle] using
    congrArg (· ≫ ((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).hom.app K) h

/-- Inclusion into `CochainComplex C ℤ` identifies `mappingConeTriangle f` with
`CochainComplex.mappingCone.triangle f.hom`. -/
def mappingConeTriangleιIso {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (CochainComplex.Plus.ι C).mapTriangle.obj (mappingConeTriangle f) ≅
      _root_.CochainComplex.mappingCone.triangle f.hom :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [Triangle.mk])
    (by dsimp [Triangle.mk]; exact (Category.comp_id _).trans (Category.id_comp _).symm)
    (by
      dsimp
      rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
      exact mappingConeTriangle_mor₃_hom_comp f)

@[simp]
lemma mappingConeTriangleιIso_hom_hom₁ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).hom.hom₁ = 𝟙 K.obj :=
  (rfl)

@[simp]
lemma mappingConeTriangleιIso_hom_hom₂ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).hom.hom₂ = 𝟙 L.obj :=
  (rfl)

@[simp]
lemma mappingConeTriangleιIso_hom_hom₃ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).hom.hom₃ = 𝟙 (_root_.CochainComplex.mappingCone f.hom) :=
  (rfl)

@[simp]
lemma mappingConeTriangleιIso_inv_hom₁ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).inv.hom₁ = 𝟙 K.obj :=
  (rfl)

@[simp]
lemma mappingConeTriangleιIso_inv_hom₂ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).inv.hom₂ = 𝟙 L.obj :=
  (rfl)

@[simp]
lemma mappingConeTriangleιIso_inv_hom₃ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).inv.hom₃ = 𝟙 (_root_.CochainComplex.mappingCone f.hom) :=
  (rfl)

end MappingCone

section Trunc

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The canonical `≤ n` truncation of a bounded-below cochain complex stays bounded below. -/
@[expose]
def truncLE (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    CochainComplex.Plus C :=
  ⟨K.obj.truncLE n, by
    obtain ⟨b, _⟩ := K.property
    exact ⟨b, inferInstance⟩⟩

/-- The canonical `≥ n` truncation of a bounded-below cochain complex stays bounded below. -/
@[expose]
def truncGE (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    CochainComplex.Plus C :=
  ⟨K.obj.truncGE n, by
    obtain ⟨b, _⟩ := K.property
    exact ⟨b, inferInstance⟩⟩

@[simp]
lemma truncLE_obj (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    (K.truncLE n).obj = K.obj.truncLE n :=
  rfl

@[simp]
lemma truncGE_obj (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    (K.truncGE n).obj = K.obj.truncGE n :=
  rfl

instance hasHomology_truncLE (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i]
    (n i : ℤ) : (K.truncLE n).obj.HasHomology i :=
  inferInstanceAs ((K.obj.truncLE n).HasHomology i)

instance hasHomology_truncGE (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i]
    (n i : ℤ) : (K.truncGE n).obj.HasHomology i :=
  inferInstanceAs ((K.obj.truncGE n).HasHomology i)

instance isStrictlyLE_truncLE_obj (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i]
    (n : ℤ) : (K.truncLE n).obj.IsStrictlyLE n :=
  inferInstanceAs ((K.obj.truncLE n).IsStrictlyLE n)

instance isStrictlyGE_truncGE_obj (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i]
    (n : ℤ) : (K.truncGE n).obj.IsStrictlyGE n :=
  inferInstanceAs ((K.obj.truncGE n).IsStrictlyGE n)

/-- The canonical morphism `τ_{≤ n} K ⟶ K` in `CochainComplex.Plus C`. -/
def ιTruncLE (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    K.truncLE n ⟶ K :=
  ObjectProperty.homMk (K.obj.ιTruncLE n)

/-- The canonical morphism `K ⟶ τ_{≥ n} K` in `CochainComplex.Plus C`. -/
def πTruncGE (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    K ⟶ K.truncGE n :=
  ObjectProperty.homMk (K.obj.πTruncGE n)

@[simp]
lemma ιTruncLE_hom (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    (K.ιTruncLE n).hom = K.obj.ιTruncLE n :=
  (rfl)

@[simp]
lemma πTruncGE_hom (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    (K.πTruncGE n).hom = K.obj.πTruncGE n :=
  (rfl)

instance quasiIso_ιTruncLE_hom (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i]
    (n : ℤ) [K.obj.IsLE n] : QuasiIso (K.ιTruncLE n).hom :=
  inferInstanceAs (QuasiIso (K.obj.ιTruncLE n))

instance quasiIso_πTruncGE_hom (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i]
    (n : ℤ) [K.obj.IsGE n] : QuasiIso (K.πTruncGE n).hom :=
  inferInstanceAs (QuasiIso (K.obj.πTruncGE n))

end Trunc

end CochainComplex.Plus

namespace CategoryTheory.Functor

section Comp

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {E : Type u₃} [Category.{v₃} E]

/-- Natural isomorphism `F.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus ≅
(F ⋙ G).mapCochainComplexPlus` for functors preserving zero morphisms. -/
def mapCochainComplexPlusCompIso [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms E]
    (F : A ⥤ B) (G : B ⥤ E) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] :
    F.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus ≅ (F ⋙ G).mapCochainComplexPlus :=
  NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _ (Iso.refl _)) (fun _ ↦ by ext; simp)

@[simp]
lemma mapCochainComplexPlusCompIso_hom_app_hom [HasZeroMorphisms A] [HasZeroMorphisms B]
    [HasZeroMorphisms E] (F : A ⥤ B) (G : B ⥤ E) [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (K : CochainComplex.Plus A) :
    ((F.mapCochainComplexPlusCompIso G).hom.app K).hom = 𝟙 _ :=
  (rfl)

@[simp]
lemma mapCochainComplexPlusCompIso_inv_app_hom [HasZeroMorphisms A] [HasZeroMorphisms B]
    [HasZeroMorphisms E] (F : A ⥤ B) (G : B ⥤ E) [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (K : CochainComplex.Plus A) :
    ((F.mapCochainComplexPlusCompIso G).inv.app K).hom = 𝟙 _ :=
  (rfl)

instance [Preadditive A] [Preadditive B] [Preadditive E]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive] :
    NatTrans.CommShift (F.mapCochainComplexPlusCompIso G).hom ℤ :=
  NatTrans.CommShift.of_comp_faithful (CochainComplex.Plus.ι E) (by
    have h : Functor.whiskerRight (F.mapCochainComplexPlusCompIso G).hom
          (CochainComplex.Plus.ι E) =
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft F.mapCochainComplexPlus G.mapCochainComplexPlusCompι.hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight F.mapCochainComplexPlusCompι.hom (G.mapHomologicalComplex _) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (CochainComplex.Plus.ι A)
            (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom ≫
          (F ⋙ G).mapCochainComplexPlusCompι.inv := by
      ext K n
      simp [mapCochainComplexPlusCompIso]
    rw [h]
    infer_instance)

end Comp

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

/-- If `τ : F₁ ⟶ F₂` is a natural isomorphism between additive functors, then
`τ.mapCochainComplexPlus` is also an isomorphism. -/
instance isIso_mapCochainComplexPlus {A : Type u₁} [Category.{v₁} A] [Preadditive A]
    {B : Type u₂} [Category.{v₂} B] [Preadditive B]
    {F₁ F₂ : A ⥤ B} [F₁.Additive] [F₂.Additive] (τ : F₁ ⟶ F₂) [IsIso τ] :
    IsIso τ.mapCochainComplexPlus :=
  ⟨(inv τ).mapCochainComplexPlus,
    by rw [← mapCochainComplexPlus_comp, IsIso.hom_inv_id, mapCochainComplexPlus_id],
    by rw [← mapCochainComplexPlus_comp, IsIso.inv_hom_id, mapCochainComplexPlus_id]⟩

end CategoryTheory.NatTrans
