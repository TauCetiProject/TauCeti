/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Equivalences of full subcategories

This file supplements Mathlib's `Mathlib.CategoryTheory.ObjectProperty.Equivalence` with the API
of `CategoryTheory.Equivalence.congrFullSubcategory`, the equivalence between full subcategories
of corresponding properties induced by an equivalence of ambient categories.

## Main declarations

* `CategoryTheory.ObjectProperty.inverseImage_functor_inverseImage_inverse`: pulling an
  isomorphism-invariant property backward along both functors of an equivalence recovers it, as
  `congrFullSubcategory` asks of the transported property `P.inverseImage e.inverse`.
* `CategoryTheory.Equivalence.congrFullSubcategory_functor_comp_ι` and
  `CategoryTheory.Equivalence.congrFullSubcategory_inverse_comp_ι`: the restricted functors,
  followed by the inclusions, are the inclusions followed by the original functors.
* `CategoryTheory.Equivalence.congrFullSubcategory_functor_obj_obj`,
  `CategoryTheory.Equivalence.congrFullSubcategory_functor_map_hom` and their `inverse`
  counterparts: the restricted functors evaluated on objects and morphisms, for deriving the
  evaluation lemmas of any equivalence defined as a `congrFullSubcategory`.
* `CategoryTheory.Equivalence.congrFullSubcategory_functor_additive` and
  `CategoryTheory.Equivalence.congrFullSubcategory_inverse_additive`: an additive equivalence
  restricts to an additive equivalence between corresponding full subcategories.
-/

public section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory

namespace ObjectProperty

/-- Pulling an isomorphism-invariant object property backward along both functors of an
equivalence recovers the original property. -/
theorem inverseImage_functor_inverseImage_inverse
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (e : C ≌ D) :
    (P.inverseImage e.inverse).inverseImage e.functor = P := by
  ext X
  exact (P.prop_iff_of_iso (e.unitIso.app X)).symm

end ObjectProperty

namespace Equivalence

/-- The forward functor on corresponding full subcategories, followed by the inclusion, is the
inclusion followed by the original functor. -/
theorem congrFullSubcategory_functor_comp_ι
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).functor ⋙ Q.ι = P.ι ⋙ e.functor := by
  rw [congrFullSubcategory_functor]
  exact ObjectProperty.lift_comp_ι ..

/-- The inverse functor on corresponding full subcategories, followed by the inclusion, is the
inclusion followed by the original inverse. -/
theorem congrFullSubcategory_inverse_comp_ι
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).inverse ⋙ P.ι = Q.ι ⋙ e.inverse := by
  rw [congrFullSubcategory_inverse]
  exact ObjectProperty.lift_comp_ι ..

section Evaluation

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
  (e : C ≌ D) (h : Q.inverseImage e.functor = P)

/-- The forward functor on corresponding full subcategories acts on objects as the original
functor. Not a simp lemma: `congrFullSubcategory_functor` already unfolds the left-hand side. -/
theorem congrFullSubcategory_functor_obj_obj (X : P.FullSubcategory) :
    ((e.congrFullSubcategory h).functor.obj X).obj = e.functor.obj X.obj := by simp

/-- The forward functor on corresponding full subcategories acts on morphisms as the original
functor, up to the identifications of `congrFullSubcategory_functor_obj_obj`. -/
theorem congrFullSubcategory_functor_map_hom {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((e.congrFullSubcategory h).functor.map f).hom =
      eqToHom (e.congrFullSubcategory_functor_obj_obj h X) ≫ e.functor.map f.hom ≫
        eqToHom (e.congrFullSubcategory_functor_obj_obj h Y).symm := by
  simpa only [Functor.comp_map, ObjectProperty.ι_map] using
    ObjectProperty.map_hom_of_comp_ι_eq (e.congrFullSubcategory_functor_comp_ι h) f
      (e.congrFullSubcategory_functor_obj_obj h X) (e.congrFullSubcategory_functor_obj_obj h Y)

/-- The inverse functor on corresponding full subcategories acts on objects as the original
inverse. Not a simp lemma: `congrFullSubcategory_inverse` already unfolds the left-hand side. -/
theorem congrFullSubcategory_inverse_obj_obj (Y : Q.FullSubcategory) :
    ((e.congrFullSubcategory h).inverse.obj Y).obj = e.inverse.obj Y.obj := by simp

/-- The inverse functor on corresponding full subcategories acts on morphisms as the original
inverse, up to the identifications of `congrFullSubcategory_inverse_obj_obj`. -/
theorem congrFullSubcategory_inverse_map_hom {X Y : Q.FullSubcategory} (f : X ⟶ Y) :
    ((e.congrFullSubcategory h).inverse.map f).hom =
      eqToHom (e.congrFullSubcategory_inverse_obj_obj h X) ≫ e.inverse.map f.hom ≫
        eqToHom (e.congrFullSubcategory_inverse_obj_obj h Y).symm := by
  simpa only [Functor.comp_map, ObjectProperty.ι_map] using
    ObjectProperty.map_hom_of_comp_ι_eq (e.congrFullSubcategory_inverse_comp_ι h) f
      (e.congrFullSubcategory_inverse_obj_obj h X) (e.congrFullSubcategory_inverse_obj_obj h Y)

end Evaluation

/-- The functor of an equivalence restricted to corresponding full subcategories is additive. -/
instance congrFullSubcategory_functor_additive
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) [e.functor.Additive] (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).functor.Additive := by
  rw [congrFullSubcategory_functor]
  infer_instance

/-- The inverse of an equivalence restricted to corresponding full subcategories is additive. -/
instance congrFullSubcategory_inverse_additive
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) [e.inverse.Additive] (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).inverse.Additive := by
  rw [congrFullSubcategory_inverse]
  infer_instance

end Equivalence

end CategoryTheory
