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
* `CategoryTheory.InjectiveResolution.cocomplexPlus`: the bounded-below `ℤ`-indexed complex
  `I.cochainComplex` viewed in `CochainComplex.Plus C`.
* `CategoryTheory.InjectiveResolution.cocomplexPlusMap`: functoriality in `InjectiveResolution.Hom`
  via `InjectiveResolution.Hom.hom'`.
* `CategoryTheory.InjectiveResolution.cocomplexPlusHomologyIso`: natural identification of the
  cohomology of `F(I.cocomplexPlus.obj)` in degree `n : ℤ` with the cohomology of
  `F(I.cocomplex)` in degree `n : ℕ`.
* `CategoryTheory.InjectiveResolution.ιPlus`: the bounded-below resolution morphism
  `(TauCeti.CochainComplex.Plus.singleFunctor C 0).obj X ⟶ I.cocomplexPlus` built from
  `I.ι'`, together with its naturality lemma `ιPlus_naturality` via `Hom.ι'_comp_hom'`.
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
abbrev cocomplexPlus {X : C} (I : InjectiveResolution X) : _root_.CochainComplex.Plus C :=
  ⟨I.cochainComplex, (_root_.CochainComplex.plus_iff C _).2 ⟨0, inferInstance⟩⟩

/-- The bounded-below resolution `X[0] ⟶ I.cocomplexPlus` in `CochainComplex.Plus C` induced by
`I.ι'`. -/
abbrev ιPlus {X : C} (I : InjectiveResolution X) :
    (TauCeti.CochainComplex.Plus.singleFunctor C 0).obj X ⟶ I.cocomplexPlus :=
  { hom := (TauCeti.CochainComplex.Plus.singleFunctorCompιIso C 0).hom.app X ≫ I.ι' }

section Homology

variable {D : Type*} [Category* D] [HasZeroMorphisms D] [HasZeroObject D]
  [CategoryWithHomology D]

/-- Transport from the cohomology of `F(I.cocomplexPlus.obj)` in degree `n : ℤ` to the cohomology
of `F(I.cocomplex)` in degree `n : ℕ`. -/
def cocomplexPlusHomologyIso {X : C} (I : InjectiveResolution X)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (n : ℕ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj I.cocomplexPlus.obj).homology (n : ℤ) ≅
      ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology n :=
  (ComplexShape.embeddingUpNat.extendFunctorCompMapHomologyFunctorIso F
    (ComplexShape.embeddingUpNat_f n)).app I.cocomplex

/-- Characterizing formula for `(I.cocomplexPlusHomologyIso F n).hom`. -/
@[reassoc]
lemma cocomplexPlusHomologyIso_hom {X : C} (I : InjectiveResolution X)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (n : ℕ) :
    (I.cocomplexPlusHomologyIso F n).hom =
      HomologicalComplex.homologyMap
          (F.mapHomologicalComplexExtendObjIso ComplexShape.embeddingUpNat I.cocomplex).hom
          (n : ℤ) ≫
        (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n)).hom :=
  ComplexShape.Embedding.extendFunctorCompMapHomologyFunctorIso_hom_app
    ComplexShape.embeddingUpNat F (ComplexShape.embeddingUpNat_f n) I.cocomplex

end Homology

end Preadditive

section Abelian

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-- The morphism `IX.cocomplexPlus ⟶ IY.cocomplexPlus` induced by a morphism
`φ : IX.Hom IY f` of injective resolutions, wrapping `Hom.hom'`. -/
abbrev cocomplexPlusMap {X Y : C} {IX : InjectiveResolution X} {IY : InjectiveResolution Y}
    {f : X ⟶ Y} (φ : IX.Hom IY f) :
    IX.cocomplexPlus ⟶ IY.cocomplexPlus :=
  { hom := φ.hom' }

/-- Naturality of `cocomplexPlusHomologyIso` in morphisms of injective resolutions. -/
@[reassoc]
lemma cocomplexPlusHomologyIso_hom_naturality {X Y : C}
    {IX : InjectiveResolution X} {IY : InjectiveResolution Y} {f : X ⟶ Y}
    (φ : IX.Hom IY f)
    {D : Type*} [Category* D] [HasZeroMorphisms D] [HasZeroObject D]
    [CategoryWithHomology D] (F : C ⥤ D) [F.PreservesZeroMorphisms] (n : ℕ) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (.up ℤ)).map (cocomplexPlusMap φ).hom) (n : ℤ) ≫
        (IY.cocomplexPlusHomologyIso F n).hom =
      (IX.cocomplexPlusHomologyIso F n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ.hom) n := by
  dsimp only [InjectiveResolution.cochainComplex]
  rw [cocomplexPlusHomologyIso_hom, cocomplexPlusHomologyIso_hom, Category.assoc]
  simpa [InjectiveResolution.Hom.hom', Category.assoc] using
    (ComplexShape.embeddingUpNat.extendFunctorCompMapHomologyFunctorIso F
      (ComplexShape.embeddingUpNat_f n)).hom.naturality φ.hom

/-- Naturality of `ιPlus` with respect to a morphism `φ : IX.Hom IY f` of injective
resolutions, derived from `Hom.ι'_comp_hom'`. -/
lemma ιPlus_naturality {X Y : C} {f : X ⟶ Y}
    {IX : InjectiveResolution X} {IY : InjectiveResolution Y}
    (φ : IX.Hom IY f) :
    IX.ιPlus ≫ cocomplexPlusMap φ =
      (TauCeti.CochainComplex.Plus.singleFunctor C 0).map f ≫ IY.ιPlus := by
  apply (_root_.CochainComplex.Plus.ι C).map_injective
  have hnat := (TauCeti.CochainComplex.Plus.singleFunctorCompιIso C 0).hom.naturality f
  dsimp at hnat
  simp only [ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    φ.ι'_comp_hom']
  rw [← Category.assoc, ← hnat, Category.assoc]

end Abelian

end BoundedBelow

end CategoryTheory.InjectiveResolution
