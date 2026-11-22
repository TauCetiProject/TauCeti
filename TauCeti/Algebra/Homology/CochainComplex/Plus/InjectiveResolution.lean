/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import TauCeti.Algebra.Homology.CochainComplex.Plus.Basic
public import TauCeti.Algebra.Homology.Embedding.Extend.Basic

/-!
# Bounded-below injective resolutions in `CochainComplex.Plus`

This file embeds `ℕ`-indexed injective resolutions `I : InjectiveResolution X` into Mathlib's
category `CochainComplex.Plus C` of bounded-below `ℤ`-indexed cochain complexes:

* `CategoryTheory.InjectiveResolution.cocomplexPlus`: the bounded-below `ℤ`-indexed extension of
  `I.cocomplex`.
* `CategoryTheory.InjectiveResolution.cocomplexPlusMap`: functoriality in morphisms of injective
  resolutions.
* `CategoryTheory.InjectiveResolution.ιPlus`: the bounded-below resolution morphism
  `(TauCeti.CochainComplex.Plus.singleFunctor C 0).obj X ⟶ I.cocomplexPlus`, together with its
  `QuasiIso` instance and naturality lemma `ιPlus_naturality`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁

namespace CategoryTheory.InjectiveResolution

section BoundedBelow

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The bounded-below `ℤ`-indexed cochain complex obtained by extending `I.cocomplex` along
`ComplexShape.embeddingUpNat`. -/
def cocomplexPlus {X : C} (I : InjectiveResolution X) : _root_.CochainComplex.Plus C :=
  ⟨I.cocomplex.extend ComplexShape.embeddingUpNat,
    (_root_.CochainComplex.plus_iff C _).2 ⟨0, inferInstance⟩⟩

/-- The underlying cochain complex of `I.cocomplexPlus` is
`I.cocomplex.extend ComplexShape.embeddingUpNat`. -/
@[simp]
lemma cocomplexPlus_obj {X : C} (I : InjectiveResolution X) :
    I.cocomplexPlus.obj = I.cocomplex.extend ComplexShape.embeddingUpNat :=
  (rfl)

/-- The morphism `IX.cocomplexPlus ⟶ IY.cocomplexPlus` induced by a morphism
`φ : IX.cocomplex ⟶ IY.cocomplex` of injective resolutions. -/
def cocomplexPlusMap {X Y : C} {IX : InjectiveResolution X} {IY : InjectiveResolution Y}
    (φ : IX.cocomplex ⟶ IY.cocomplex) :
    IX.cocomplexPlus ⟶ IY.cocomplexPlus :=
  ObjectProperty.homMk
    (eqToHom IX.cocomplexPlus_obj ≫
      HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat ≫
      eqToHom IY.cocomplexPlus_obj.symm)

/-- Underlying cochain-complex morphism of `cocomplexPlusMap φ`. -/
@[simp]
lemma cocomplexPlusMap_hom {X Y : C} {IX : InjectiveResolution X} {IY : InjectiveResolution Y}
    (φ : IX.cocomplex ⟶ IY.cocomplex) :
    (cocomplexPlusMap φ).hom =
      eqToHom IX.cocomplexPlus_obj ≫
        HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat ≫
        eqToHom IY.cocomplexPlus_obj.symm := by
  simp [cocomplexPlusMap]

/-- The bounded-below resolution `X[0] ⟶ I.cocomplexPlus` in `CochainComplex.Plus C` induced by
an injective resolution `I` of `X`. -/
def ιPlus {X : C} (I : InjectiveResolution X) :
    (TauCeti.CochainComplex.Plus.singleFunctor C 0).obj X ⟶ I.cocomplexPlus :=
  ObjectProperty.homMk
    ((TauCeti.CochainComplex.Plus.singleFunctorCompιIso C 0).hom.app X ≫
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0
        (ComplexShape.embeddingUpNat_f 0)).inv ≫
      HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat ≫
      eqToHom I.cocomplexPlus_obj.symm)

/-- Underlying cochain-complex morphism of `I.ιPlus`. -/
@[simp]
lemma ιPlus_hom {X : C} (I : InjectiveResolution X) :
    I.ιPlus.hom =
      (TauCeti.CochainComplex.Plus.singleFunctorCompιIso C 0).hom.app X ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0
          (ComplexShape.embeddingUpNat_f 0)).inv ≫
        HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat ≫
        eqToHom I.cocomplexPlus_obj.symm := by
  simp [ιPlus]

instance hasHomology_cocomplexPlus {X : C} (I : InjectiveResolution X) (i : ℤ) :
    I.cocomplexPlus.obj.HasHomology i :=
  HomologicalComplex.hasHomology_of_iso (eqToIso I.cocomplexPlus_obj).symm i

instance injective_cocomplexPlus_X {X : C} (I : InjectiveResolution X) (n : ℤ) :
    Injective (I.cocomplexPlus.obj.X n) := by
  rw [cocomplexPlus_obj]
  infer_instance

instance quasiIso_ιPlus_hom {X : C} (I : InjectiveResolution X) :
    QuasiIso I.ιPlus.hom := by
  rw [ιPlus_hom]
  infer_instance

/-- Naturality of `ιPlus` with respect to a lifting morphism `φ` of injective resolutions. -/
lemma ιPlus_naturality {X Y : C} (f : X ⟶ Y)
    (IX : InjectiveResolution X) (IY : InjectiveResolution Y)
    (φ : IX.cocomplex ⟶ IY.cocomplex)
    (hφ : IX.ι ≫ φ = (_root_.CochainComplex.single₀ C).map f ≫ IY.ι) :
    IX.ιPlus ≫ cocomplexPlusMap φ =
      (TauCeti.CochainComplex.Plus.singleFunctor C 0).map f ≫ IY.ιPlus := by
  apply (_root_.CochainComplex.Plus.ι C).map_injective
  simp only [ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom, ιPlus_hom,
    cocomplexPlusMap_hom, TauCeti.CochainComplex.Plus.singleFunctorCompιIso_hom_app,
    TauCeti.CochainComplex.Plus.singleFunctor_map_hom, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  rw [← HomologicalComplex.extendMap_comp_assoc, hφ, HomologicalComplex.extendMap_comp_assoc]
  dsimp only [_root_.CochainComplex.single₀]
  rw [← ComplexShape.embeddingUpNat.extendSingleIso_inv_naturality_assoc f (i := 0) (i' := 0)
    (by simp)]

end BoundedBelow

end CategoryTheory.InjectiveResolution
