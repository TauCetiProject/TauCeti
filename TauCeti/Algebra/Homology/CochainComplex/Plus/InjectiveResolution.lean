/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Preadditive.Injective.InjectiveObject
public import TauCeti.Algebra.Homology.CochainComplex.Plus.Basic
public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Basic

import Mathlib.Algebra.Homology.FullSubcategory

/-!
# Bounded-below injective resolutions in `CochainComplex.Plus`

This file embeds `ℕ`-indexed injective resolutions `I : InjectiveResolution X` into Mathlib's
category `CochainComplex.Plus C` of bounded-below `ℤ`-indexed cochain complexes, and provides
lifting of bounded-below complexes of injective objects into
`CochainComplex.Plus (InjectiveObject C)`:

* `CochainComplex.Plus.liftInjective` and `CochainComplex.Plus.liftInjectiveIso`: lift a
  bounded-below cochain complex of injective objects in `C` to
  `CochainComplex.Plus (InjectiveObject C)`.
* `CategoryTheory.InjectiveResolution.cochainComplexPlus`: the bounded-below `ℤ`-indexed complex
  `I.cochainComplex` viewed in `CochainComplex.Plus C`, with characterizing lemma
  `cochainComplexPlus_obj` and termwise `Injective` instance.
* `CategoryTheory.InjectiveResolution.cochainComplexPlusMap`: functoriality in
  `InjectiveResolution.Hom` via `InjectiveResolution.Hom.hom'`, with characterizing lemma
  `cochainComplexPlusMap_hom`.
* `CategoryTheory.InjectiveResolution.cochainComplexPlusHomologyIso`: natural identification of the
  cohomology of `F(I.cochainComplexPlus.obj)` in degree `n : ℤ` with the cohomology of
  `F(I.cocomplex)` in degree `n : ℕ`.
* `CategoryTheory.InjectiveResolution.ιPlus`: the bounded-below resolution morphism
  `(TauCeti.CochainComplex.Plus.singleFunctor C 0).obj X ⟶ I.cochainComplexPlus` built from
  `I.ι'`, with characterizing lemma `ιPlus_hom`, `QuasiIso` instance, and naturality lemma
  `ιPlus_naturality` via `Hom.ι'_comp_hom'`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁

namespace CochainComplex.Plus

section Injective

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]

/-- Lift a bounded-below cochain complex of injective objects in `C` to
`CochainComplex.Plus (InjectiveObject C)`. -/
def liftInjective (K : CochainComplex.Plus C) (hK : ∀ n, Injective (K.obj.X n)) :
    CochainComplex.Plus (InjectiveObject C) :=
  ⟨HomologicalComplex.liftObjectProperty _ K.obj hK, by
    obtain ⟨b, _⟩ := K.property
    refine ⟨b, ?_⟩
    rwa [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι C)]⟩

/-- Inclusion of `InjectiveObject C` identifies `liftInjective K hK` with `K` in
`CochainComplex.Plus C`. -/
def liftInjectiveIso (K : CochainComplex.Plus C) (hK : ∀ n, Injective (K.obj.X n)) :
    (InjectiveObject.ι C).mapCochainComplexPlus.obj (liftInjective K hK) ≅ K :=
  ObjectProperty.isoMk _
    (HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
      simp [liftInjective]))

end Injective

end CochainComplex.Plus

namespace CategoryTheory.InjectiveResolution

section BoundedBelow

section Preadditive

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [Preadditive C]

/-- Mathlib's extended `ℤ`-indexed injective resolution `I.cochainComplex` viewed in
`CochainComplex.Plus C`. -/
def cochainComplexPlus {X : C} (I : InjectiveResolution X) : _root_.CochainComplex.Plus C :=
  ⟨I.cochainComplex, (_root_.CochainComplex.plus_iff C _).2 ⟨0, inferInstance⟩⟩

/-- The underlying `ℤ`-indexed cochain complex of `I.cochainComplexPlus` is
`I.cochainComplex`. -/
@[simp]
lemma cochainComplexPlus_obj {X : C} (I : InjectiveResolution X) :
    I.cochainComplexPlus.obj = I.cochainComplex :=
  (rfl)

instance {X : C} (I : InjectiveResolution X) (n : ℤ) :
    Injective (I.cochainComplexPlus.obj.X n) := by
  rw [cochainComplexPlus_obj]
  infer_instance

/-- The bounded-below resolution `X[0] ⟶ I.cochainComplexPlus` in `CochainComplex.Plus C`
induced by `I.ι'`. -/
def ιPlus {X : C} (I : InjectiveResolution X) :
    (TauCeti.CochainComplex.Plus.singleFunctor C 0).obj X ⟶ I.cochainComplexPlus :=
  ObjectProperty.homMk
    (eqToHom (TauCeti.CochainComplex.Plus.singleFunctor_obj_obj 0 X) ≫ I.ι' ≫
      eqToHom I.cochainComplexPlus_obj.symm)

/-- The underlying chain map of `I.ιPlus`. -/
@[simp]
lemma ιPlus_hom {X : C} (I : InjectiveResolution X) :
    I.ιPlus.hom =
      eqToHom (TauCeti.CochainComplex.Plus.singleFunctor_obj_obj 0 X) ≫ I.ι' ≫
        eqToHom I.cochainComplexPlus_obj.symm :=
  (rfl)

section Homology

variable {D : Type*} [Category* D] [HasZeroMorphisms D] [HasZeroObject D]
  [CategoryWithHomology D]

/-- Transport from the cohomology of `F(I.cochainComplexPlus.obj)` in degree `n : ℤ` to the
cohomology of `F(I.cocomplex)` in degree `n : ℕ`. -/
def cochainComplexPlusHomologyIso {X : C} (I : InjectiveResolution X)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (n : ℕ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplexPlus.obj).homology (n : ℤ) ≅
      ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology n :=
  (HomologicalComplex.homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
      ((F.mapHomologicalComplex (.up ℤ)).mapIso (eqToIso I.cochainComplexPlus_obj)) ≪≫
    ((ComplexShape.embeddingUpNat.extendFunctorCompMapHomologyFunctorIso F
      (ComplexShape.embeddingUpNat_f n)).app I.cocomplex :
      ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homology (n : ℤ) ≅ _)

/-- Characterizing formula for `(I.cochainComplexPlusHomologyIso F n).hom`. -/
@[reassoc]
lemma cochainComplexPlusHomologyIso_hom {X : C} (I : InjectiveResolution X)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (n : ℕ) :
    (I.cochainComplexPlusHomologyIso F n).hom =
      HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (.up ℤ)).map (eqToHom I.cochainComplexPlus_obj)) (n : ℤ) ≫
        (HomologicalComplex.homologyMap
            (F.mapHomologicalComplexExtendObjIso ComplexShape.embeddingUpNat I.cocomplex).hom
            (n : ℤ) ≫
          (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n)).hom :
          ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homology (n : ℤ) ⟶ _) :=
  congrArg (_ ≫ ·)
    (ComplexShape.Embedding.extendFunctorCompMapHomologyFunctorIso_hom_app
      ComplexShape.embeddingUpNat F (ComplexShape.embeddingUpNat_f n) I.cocomplex)

end Homology

end Preadditive

section Abelian

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

instance {X : C} (I : InjectiveResolution X) : QuasiIso I.ιPlus.hom := by
  rw [ιPlus_hom]
  infer_instance

/-- The morphism `IX.cochainComplexPlus ⟶ IY.cochainComplexPlus` induced by a morphism
`φ : IX.Hom IY f` of injective resolutions, wrapping `Hom.hom'`. -/
def cochainComplexPlusMap {X Y : C} {IX : InjectiveResolution X} {IY : InjectiveResolution Y}
    {f : X ⟶ Y} (φ : IX.Hom IY f) :
    IX.cochainComplexPlus ⟶ IY.cochainComplexPlus :=
  ObjectProperty.homMk
    (eqToHom IX.cochainComplexPlus_obj ≫ φ.hom' ≫ eqToHom IY.cochainComplexPlus_obj.symm)

/-- The underlying chain map of `cochainComplexPlusMap φ` is `φ.hom'` up to
`cochainComplexPlus_obj`. -/
@[simp]
lemma cochainComplexPlusMap_hom {X Y : C}
    {IX : InjectiveResolution X} {IY : InjectiveResolution Y}
    {f : X ⟶ Y} (φ : IX.Hom IY f) :
    (cochainComplexPlusMap φ).hom =
      eqToHom IX.cochainComplexPlus_obj ≫ φ.hom' ≫ eqToHom IY.cochainComplexPlus_obj.symm :=
  (rfl)

/-- Naturality of `cochainComplexPlusHomologyIso` in morphisms of injective resolutions. -/
@[reassoc]
lemma cochainComplexPlusHomologyIso_hom_naturality {X Y : C}
    {IX : InjectiveResolution X} {IY : InjectiveResolution Y} {f : X ⟶ Y}
    (φ : IX.Hom IY f)
    {D : Type*} [Category* D] [HasZeroMorphisms D] [HasZeroObject D]
    [CategoryWithHomology D] (F : C ⥤ D) [F.PreservesZeroMorphisms] (n : ℕ) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (.up ℤ)).map (cochainComplexPlusMap φ).hom) (n : ℤ) ≫
        (IY.cochainComplexPlusHomologyIso F n).hom =
      (IX.cochainComplexPlusHomologyIso F n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ.hom) n := by
  rw [cochainComplexPlusHomologyIso_hom, cochainComplexPlusHomologyIso_hom,
    cochainComplexPlusMap_hom]
  have h :
      HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (.up ℤ)).map
            (eqToHom IX.cochainComplexPlus_obj ≫ φ.hom' ≫
              eqToHom IY.cochainComplexPlus_obj.symm)) (n : ℤ) ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (.up ℤ)).map (eqToHom IY.cochainComplexPlus_obj)) (n : ℤ) =
      HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (.up ℤ)).map (eqToHom IX.cochainComplexPlus_obj)) (n : ℤ) ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ) := by
    simp only [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp,
      Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [← Category.assoc, h, Category.assoc, Category.assoc]
  congr 1
  dsimp only [InjectiveResolution.cochainComplex]
  simpa [InjectiveResolution.Hom.hom', Category.assoc] using
    (ComplexShape.embeddingUpNat.extendFunctorCompMapHomologyFunctorIso F
      (ComplexShape.embeddingUpNat_f n)).hom.naturality φ.hom

/-- Naturality of `ιPlus` with respect to a morphism `φ : IX.Hom IY f` of injective
resolutions, derived from `Hom.ι'_comp_hom'`. -/
lemma ιPlus_naturality {X Y : C} {f : X ⟶ Y}
    {IX : InjectiveResolution X} {IY : InjectiveResolution Y}
    (φ : IX.Hom IY f) :
    IX.ιPlus ≫ cochainComplexPlusMap φ =
      (TauCeti.CochainComplex.Plus.singleFunctor C 0).map f ≫ IY.ιPlus := by
  apply (_root_.CochainComplex.Plus.ι C).map_injective
  simp only [ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
    ιPlus_hom, cochainComplexPlusMap_hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, InjectiveResolution.Hom.ι'_comp_hom'_assoc,
    TauCeti.CochainComplex.Plus.singleFunctor_map_hom]

end Abelian

end BoundedBelow

end CategoryTheory.InjectiveResolution
