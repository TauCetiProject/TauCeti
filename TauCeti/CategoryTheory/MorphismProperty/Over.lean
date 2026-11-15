/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Restricted over categories: object properties, identity base change, and slices

Let `P` be a morphism property on a category `C`. This file collects categorical constructions on
the restricted over categories `P.Over Q X`:

* `CategoryTheory.MorphismProperty.overEquivFullSubcategory`: equivalence between `P.Over ⊤ X` and
  any full subcategory of `Over X` characterized by `P` on structure morphisms;
* `CategoryTheory.MorphismProperty.Over.pullbackId`: base change `Over.pullback P ⊤ (𝟙 X)` along
  the identity morphism identifies with the identity functor, adapting
  `CategoryTheory.Over.pullbackId` from `Mathlib.CategoryTheory.Comma.Over.Pullback`;
* `CategoryTheory.MorphismProperty.Over.iteratedSliceEquiv`: for `U : P.Over ⊤ X`, when `P` is
  stable under composition and satisfies `P.HasOfPostcompProperty P`, the slice category
  `CategoryTheory.Over U` is equivalent to `P.Over ⊤ U.left`, adapting
  `CategoryTheory.Over.iteratedSliceEquiv`, `CategoryTheory.Over.iteratedSliceForward`, and
  `CategoryTheory.Over.iteratedSliceBackward` from `Mathlib.CategoryTheory.Comma.Over.Basic`.
-/

public section

namespace CategoryTheory.MorphismProperty

open Limits

section FullSubcategory

variable {C : Type*} [Category* C] (P : MorphismProperty C) (X : C)
  (Q : ObjectProperty (CategoryTheory.Over X)) (hQ : ∀ Y, Q Y ↔ P Y.hom)

/-- The morphism-property over category with unrestricted morphisms is equivalent to any full
subcategory of the ordinary over category characterized by the same structure morphisms.
Taking `Q = P.overObj` gives the canonical object-property presentation. -/
def overEquivFullSubcategory : P.Over ⊤ X ≌ Q.FullSubcategory where
  functor := Q.lift (Over.forget P ⊤ X) fun Y ↦ (hQ _).mpr Y.prop
  inverse := Comma.lift Q.ι (fun Y ↦ (hQ _).mp Y.property)
    (fun _ ↦ trivial) (fun _ ↦ trivial)
  unitIso := NatIso.ofComponents (fun Y ↦ Iso.refl Y) (by
    intros
    ext
    simp [Comma.lift, ObjectProperty.lift, Over.forget, Comma.forget])
  counitIso := NatIso.ofComponents (fun Y ↦ Iso.refl Y) (by
    intros
    ext
    simp [Comma.lift, ObjectProperty.lift, Over.forget, Comma.forget])
  functor_unitIso_comp Y := by
    ext
    simp [NatIso.ofComponents, Comma.lift, ObjectProperty.lift, Over.forget, Comma.forget]

/-- The comparison does not change the underlying object over the base. -/
@[simp]
theorem overEquivFullSubcategory_functor_obj_obj (Y : P.Over ⊤ X) :
    ((P.overEquivFullSubcategory X Q hQ).functor.obj Y).obj = (Over.forget P ⊤ X).obj Y :=
  (rfl)

/-- The inverse comparison does not change the underlying object over the base. -/
@[simp]
theorem overEquivFullSubcategory_inverse_obj_toComma (Y : Q.FullSubcategory) :
    ((P.overEquivFullSubcategory X Q hQ).inverse.obj Y).toComma = Y.obj :=
  (rfl)

/-- Forgetting the comparison recovers the usual forgetful functor to `Over X`. -/
@[simp]
theorem overEquivFullSubcategory_functor_comp_ι :
    (P.overEquivFullSubcategory X Q hQ).functor ⋙ Q.ι =
      Over.forget P ⊤ X :=
  (rfl)

/-- Forgetting the inverse comparison recovers the full-subcategory inclusion. -/
@[simp]
theorem overEquivFullSubcategory_inverse_comp_forget :
    (P.overEquivFullSubcategory X Q hQ).inverse ⋙ Over.forget P ⊤ X = Q.ι :=
  (rfl)

end FullSubcategory

namespace Over

section PullbackId

variable {C : Type*} [Category* C] (P : MorphismProperty C) [P.IsMultiplicative]
  (X : C) [P.HasPullbacksAlong (𝟙 X)] [P.IsStableUnderBaseChangeAlong (𝟙 X)]

/-- Base change in `P.Over ⊤ X` along `𝟙 X` identifies naturally with the identity functor,
conjugate to `Over.mapId ⊤ X`. -/
noncomputable def pullbackId :
    Over.pullback P ⊤ (𝟙 X) ≅ 𝟭 (P.Over ⊤ X) :=
  conjugateIsoEquiv (Over.mapPullbackAdj P ⊤ (𝟙 X) (P.id_mem X) trivial)
    Adjunction.id (Over.mapId ⊤ X).symm

@[simp]
lemma conjugateEquiv_symm_pullbackId_hom :
    (conjugateEquiv (Over.mapPullbackAdj P ⊤ (𝟙 X) (P.id_mem X) trivial) Adjunction.id).symm
      (pullbackId P X).hom = (Over.mapId ⊤ X).inv := by
  simp [pullbackId]

@[simp]
lemma conjugateEquiv_symm_pullbackId_inv :
    (conjugateEquiv Adjunction.id (Over.mapPullbackAdj P ⊤ (𝟙 X) (P.id_mem X) trivial)).symm
      (pullbackId P X).inv = (Over.mapId ⊤ X).hom := by
  simp [pullbackId]

@[simp]
lemma pullbackId_hom_app_left (Y : P.Over ⊤ X) :
    ((pullbackId P X).hom.app Y).left = Limits.pullback.fst Y.hom (𝟙 X) := by
  simp only [pullbackId, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app, Adjunction.id_unit,
    NatTrans.id_app, Functor.id_obj, Functor.id_map, Over.mapPullbackAdj_counit_app,
    Category.id_comp]
  exact Category.id_comp _

@[simp]
lemma pullbackId_inv_app_left_fst (Y : P.Over ⊤ X) :
    ((pullbackId P X).inv.app Y).left ≫ Limits.pullback.fst Y.hom (𝟙 X) = 𝟙 Y.left := by
  rw [← pullbackId_hom_app_left]
  exact congrArg (fun g : Y ⟶ Y ↦ g.left) ((pullbackId P X).inv_hom_id_app Y)

@[simp]
lemma pullbackId_inv_app_left_fst_assoc (Y : P.Over ⊤ X) {Z : C} (h : Y.left ⟶ Z) :
    ((pullbackId P X).inv.app Y).left ≫ Limits.pullback.fst Y.hom (𝟙 X) ≫ h = h :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ h) (pullbackId_inv_app_left_fst P X Y)).trans (Category.id_comp h))

@[simp]
lemma pullbackId_inv_app_left_snd (Y : P.Over ⊤ X) :
    ((pullbackId P X).inv.app Y).left ≫ Limits.pullback.snd Y.hom (𝟙 X) = Y.hom := by
  simpa using Over.w ((pullbackId P X).inv.app Y)

@[simp]
lemma pullbackId_inv_app_left_snd_assoc (Y : P.Over ⊤ X) {Z : C} (h : X ⟶ Z) :
    ((pullbackId P X).inv.app Y).left ≫ Limits.pullback.snd Y.hom (𝟙 X) ≫ h = Y.hom ≫ h :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ h) (pullbackId_inv_app_left_snd P X Y))

end PullbackId

section IteratedSlice

variable {C : Type*} [Category* C] {P : MorphismProperty C} {X : C}

/-- Given `U : P.Over ⊤ X`, when `P` has the `of_postcomp` property with respect to itself, any
morphism `α : V ⟶ U` in `P.Over ⊤ X` has underlying morphism `α.left : V.left ⟶ U.left` satisfying
`P`. This defines the forward functor `(P.Over ⊤ X)/U ⥤ P.Over ⊤ U.left`. -/
def iteratedSliceForward [P.HasOfPostcompProperty P] (U : P.Over ⊤ X) :
    CategoryTheory.Over U ⥤ P.Over ⊤ U.left where
  obj α := Over.mk ⊤ α.hom.left
    (P.of_postcomp (W' := P) α.hom.left U.hom U.prop ((Over.w α.hom).symm ▸ α.left.prop))
  map κ := Over.homMk κ.left.left
    (congrArg (fun g ↦ g.hom.left) (CategoryTheory.Over.w κ))

@[simp]
lemma iteratedSliceForward_obj_left [P.HasOfPostcompProperty P] (U : P.Over ⊤ X)
    (α : CategoryTheory.Over U) :
    ((iteratedSliceForward U).obj α).left = α.left.left :=
  (rfl)

@[simp]
lemma iteratedSliceForward_obj_hom [P.HasOfPostcompProperty P] (U : P.Over ⊤ X)
    (α : CategoryTheory.Over U) :
    ((iteratedSliceForward U).obj α).hom = eqToHom (by simp) ≫ α.hom.left :=
  (Category.id_comp _).symm

@[simp]
lemma iteratedSliceForward_map_left [P.HasOfPostcompProperty P] (U : P.Over ⊤ X)
    {α β : CategoryTheory.Over U} (κ : α ⟶ β) :
    ((iteratedSliceForward U).map κ).left =
      eqToHom (by simp) ≫ κ.left.left ≫ eqToHom (by simp) :=
  ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- Composing `iteratedSliceForward U` with the forgetful functor to `C` recovers the composite
forgetful functor on `CategoryTheory.Over U`. -/
theorem iteratedSliceForward_forget [P.HasOfPostcompProperty P] (U : P.Over ⊤ X) :
    iteratedSliceForward U ⋙ Over.forget P ⊤ U.left ⋙ CategoryTheory.Over.forget U.left =
      CategoryTheory.Over.forget U ⋙ Over.forget P ⊤ X ⋙ CategoryTheory.Over.forget X :=
  (rfl)

/-- Given `U : P.Over ⊤ X`, post-composition with `U.hom` sends an object `V : P.Over ⊤ U.left` to
an object over `U` in `P.Over ⊤ X`. -/
def iteratedSliceBackward [P.IsStableUnderComposition] (U : P.Over ⊤ X) :
    P.Over ⊤ U.left ⥤ CategoryTheory.Over U where
  obj V := CategoryTheory.Over.mk
    (Over.homMk V.hom (w := rfl) : (Over.map (X := U.left) (Y := X) ⊤ U.prop).obj V ⟶ U)
  map f := CategoryTheory.Over.homMk
    ((Over.map (X := U.left) (Y := X) ⊤ U.prop).map f) (by ext; exact Over.w f)

@[simp]
lemma iteratedSliceBackward_obj_left [P.IsStableUnderComposition] (U : P.Over ⊤ X)
    (V : P.Over ⊤ U.left) :
    ((iteratedSliceBackward U).obj V).left =
      (Over.map (X := U.left) (Y := X) ⊤ U.prop).obj V :=
  (rfl)

@[simp]
lemma iteratedSliceBackward_obj_hom_left [P.IsStableUnderComposition] (U : P.Over ⊤ X)
    (V : P.Over ⊤ U.left) :
    ((iteratedSliceBackward U).obj V).hom.left = eqToHom (by simp) ≫ V.hom :=
  (Category.id_comp _).symm

@[simp]
lemma iteratedSliceBackward_map_left [P.IsStableUnderComposition] (U : P.Over ⊤ X)
    {V W : P.Over ⊤ U.left} (f : V ⟶ W) :
    ((iteratedSliceBackward U).map f).left =
      eqToHom (by simp) ≫
        (Over.map (X := U.left) (Y := X) ⊤ U.prop).map f ≫ eqToHom (by simp) :=
  ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- Composing `iteratedSliceBackward U` with the forgetful functor from `CategoryTheory.Over U`
recovers `Over.map ⊤ U.prop`. -/
@[simp]
theorem iteratedSliceBackward_forget [P.IsStableUnderComposition] (U : P.Over ⊤ X) :
    iteratedSliceBackward U ⋙ CategoryTheory.Over.forget U =
      Over.map (X := U.left) (Y := X) ⊤ U.prop :=
  (rfl)

/-- Composing `Over.map ⊤ hf` with the forgetful functor to `C` recovers the forgetful functor on
the source. -/
theorem map_forget_forget [P.IsStableUnderComposition] {Y : C} {f : Y ⟶ X} (hf : P f) :
    Over.map (P := P) ⊤ hf ⋙ Over.forget P ⊤ X ⋙ CategoryTheory.Over.forget X =
      Over.forget P ⊤ Y ⋙ CategoryTheory.Over.forget Y :=
  (rfl)

/-- Composing `iteratedSliceBackward U` with the forgetful functors to `C` recovers the forgetful
functor on `P.Over ⊤ U.left`. -/
theorem iteratedSliceBackward_forget_forget [P.IsStableUnderComposition] (U : P.Over ⊤ X) :
    iteratedSliceBackward U ⋙ CategoryTheory.Over.forget U ⋙
      Over.forget P ⊤ X ⋙ CategoryTheory.Over.forget X =
      Over.forget P ⊤ U.left ⋙ CategoryTheory.Over.forget U.left :=
  (rfl)

/-- For `U : P.Over ⊤ X`, the slice category `CategoryTheory.Over U` is equivalent to
`P.Over ⊤ U.left` whenever `P` is stable under composition and satisfies `P.HasOfPostcompProperty P`
(for example when `P` is étale, weakly étale, or open immersions). -/
def iteratedSliceEquiv [P.IsStableUnderComposition] [P.HasOfPostcompProperty P] (U : P.Over ⊤ X) :
    CategoryTheory.Over U ≌ P.Over ⊤ U.left where
  functor := iteratedSliceForward U
  inverse := iteratedSliceBackward U
  unitIso := NatIso.ofComponents
    (fun α ↦
      (CategoryTheory.Over.isoMk
        (Over.isoMk (Iso.refl α.left.left) ((Category.id_comp _).trans (Over.w α.hom)))
        (by ext; exact Category.id_comp α.hom.left) :
        α ≅ (iteratedSliceBackward U).obj ((iteratedSliceForward U).obj α)))
    (fun κ ↦ by ext; exact (Category.comp_id κ.left.left).trans (Category.id_comp κ.left.left).symm)
  counitIso := NatIso.ofComponents
    (fun V ↦
      (Over.isoMk (Iso.refl V.left) (Category.id_comp V.hom) :
        (iteratedSliceForward U).obj ((iteratedSliceBackward U).obj V) ≅ V))
    (fun f ↦ by ext; exact (Category.comp_id f.left).trans (Category.id_comp f.left).symm)
  functor_unitIso_comp α := by ext; exact Category.id_comp _

@[simp]
lemma iteratedSliceEquiv_functor [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]
    (U : P.Over ⊤ X) :
    (iteratedSliceEquiv U).functor = iteratedSliceForward U :=
  (rfl)

@[simp]
lemma iteratedSliceEquiv_inverse [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]
    (U : P.Over ⊤ X) :
    (iteratedSliceEquiv U).inverse = iteratedSliceBackward U :=
  (rfl)

@[simp]
lemma iteratedSliceEquiv_unitIso_hom_app_left_left [P.IsStableUnderComposition]
    [P.HasOfPostcompProperty P] (U : P.Over ⊤ X) (α : CategoryTheory.Over U) :
    (((iteratedSliceEquiv U).unitIso.hom.app α).left).left = eqToHom (by simp) :=
  (eqToHom_refl _ _).symm

@[simp]
lemma iteratedSliceEquiv_unitIso_inv_app_left_left [P.IsStableUnderComposition]
    [P.HasOfPostcompProperty P] (U : P.Over ⊤ X) (α : CategoryTheory.Over U) :
    (((iteratedSliceEquiv U).unitIso.inv.app α).left).left = eqToHom (by simp) :=
  (eqToHom_refl _ _).symm

@[simp]
lemma iteratedSliceEquiv_counitIso_hom_app_left [P.IsStableUnderComposition]
    [P.HasOfPostcompProperty P] (U : P.Over ⊤ X) (V : P.Over ⊤ U.left) :
    ((iteratedSliceEquiv U).counitIso.hom.app V).left = eqToHom (by simp) :=
  (eqToHom_refl _ _).symm

@[simp]
lemma iteratedSliceEquiv_counitIso_inv_app_left [P.IsStableUnderComposition]
    [P.HasOfPostcompProperty P] (U : P.Over ⊤ X) (V : P.Over ⊤ U.left) :
    ((iteratedSliceEquiv U).counitIso.inv.app V).left = eqToHom (by simp) :=
  (eqToHom_refl _ _).symm

end IteratedSlice

end Over

end CategoryTheory.MorphismProperty
