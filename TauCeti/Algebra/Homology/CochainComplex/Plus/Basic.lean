/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.SingleHomology

/-!
# Single complexes and composition on `CochainComplex.Plus`

This file provides general constructions on Mathlib's category `CochainComplex.Plus C` of
bounded-below `ℤ`-indexed cochain complexes under minimal categorical hypotheses:

* `TauCeti.CochainComplex.Plus.singleFunctor` and `singleFunctorCompιIso`: the single-object
  embedding `C ⥤ CochainComplex.Plus C` in degree `n : ℤ` (for `[HasZeroMorphisms C]` and
  `[HasZeroObject C]`).
* `CategoryTheory.Functor.mapCochainComplexPlusCompIso` (with its `NatTrans.CommShift` instance)
  and `CategoryTheory.NatTrans.isIso_mapCochainComplexPlus`: functoriality of
  `Functor.mapCochainComplexPlus` with respect to composition and natural isomorphisms.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace TauCeti.CochainComplex.Plus

section Single

variable (C : Type u₁) [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The functor `C ⥤ CochainComplex.Plus C` sending `X` to the cochain complex concentrated in
degree `n : ℤ`. -/
@[implicit_reducible]
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

/-- The underlying cochain complex of `(singleFunctor C n).obj X` is
`(HomologicalComplex.single C (.up ℤ) n).obj X`. -/
@[simp]
lemma singleFunctor_obj_obj (n : ℤ) (X : C) :
    ((singleFunctor C n).obj X).obj = (HomologicalComplex.single C (.up ℤ) n).obj X :=
  (rfl)

/-- Component formula for `(singleFunctorCompιIso C n).hom` at `X`. -/
@[simp]
lemma singleFunctorCompιIso_hom_app (n : ℤ) (X : C) :
    (singleFunctorCompιIso C n).hom.app X = eqToHom (singleFunctor_obj_obj n X) :=
  (rfl)

/-- Component formula for `(singleFunctorCompιIso C n).inv` at `X`. -/
@[simp]
lemma singleFunctorCompιIso_inv_app (n : ℤ) (X : C) :
    (singleFunctorCompιIso C n).inv.app X = eqToHom (singleFunctor_obj_obj n X).symm :=
  (rfl)

/-- Component formula for `(singleFunctor C n).map f`. -/
@[simp]
lemma singleFunctor_map_hom (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    ((singleFunctor C n).map f).hom =
      eqToHom (singleFunctor_obj_obj n X) ≫
        (HomologicalComplex.single C (.up ℤ) n).map f ≫
        eqToHom (singleFunctor_obj_obj n Y).symm := by
  have h := (singleFunctorCompιIso C n).hom.naturality f
  simp only [Functor.comp_map, ObjectProperty.ι_map, singleFunctorCompιIso_hom_app] at h
  simpa [Category.assoc] using congrArg (· ≫ eqToHom (singleFunctor_obj_obj n Y).symm) h

instance hasHomology_singleFunctor_obj (n : ℤ) (X : C) (i : ℤ) :
    ((singleFunctor C n).obj X).obj.HasHomology i :=
  HomologicalComplex.hasHomology_of_iso (eqToIso (singleFunctor_obj_obj n X)).symm i

end Single

end TauCeti.CochainComplex.Plus

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

/-- The inverse of `τ.mapCochainComplexPlus` for a natural isomorphism `τ` is
`(inv τ).mapCochainComplexPlus`. -/
@[simp]
lemma inv_mapCochainComplexPlus {A : Type u₁} [Category.{v₁} A] [Preadditive A]
    {B : Type u₂} [Category.{v₂} B] [Preadditive B]
    {F₁ F₂ : A ⥤ B} [F₁.Additive] [F₂.Additive] (τ : F₁ ⟶ F₂) [IsIso τ] :
    inv τ.mapCochainComplexPlus = (inv τ).mapCochainComplexPlus :=
  IsIso.inv_eq_of_hom_inv_id
    (by rw [← mapCochainComplexPlus_comp, IsIso.hom_inv_id, mapCochainComplexPlus_id])

end CategoryTheory.NatTrans
