/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Presentations and iterated slices of a restricted over category

For a morphism property `P`, the category `P.Over ⊤ X` and the full subcategory of `Over X`
on `P.overObj` have the same objects and all morphisms over `X`. The equivalence
`overEquivFullSubcategory` keeps the underlying object and morphism of `Over X` unchanged,
allowing constructions stated for morphism-property over categories to be used with
object-property full subcategories.

When `P` is stable under composition and has right cancellation (`P.HasOfPostcompProperty P`),
a morphism `V ⟶ U` in `P.Over ⊤ X` automatically has its underlying morphism `V.left ⟶ U.left`
in `P`, and conversely any `W : P.Over ⊤ U.left` composes with `U.hom` to an object of
`P.Over ⊤ X` over `U`. Thus the slice category `CategoryTheory.Over U` is equivalent to
`P.Over ⊤ U.left` (`CategoryTheory.MorphismProperty.Over.iteratedSliceEquiv`), matching
`CategoryTheory.Over.iteratedSliceEquiv` on unrestricted slice categories.
-/

public section

namespace CategoryTheory.MorphismProperty

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

section Backward

variable {C : Type*} [Category* C] {P : MorphismProperty C} [P.IsStableUnderComposition]
  {X : C} (U : P.Over ⊤ X)

/-- The inverse functor of `CategoryTheory.Over U ≌ P.Over ⊤ U.left`, sending `W : P.Over ⊤ U.left`
to `(Over.map ⊤ U.prop).obj W` equipped with the structure morphism `W.hom` over `U`. -/
-- The body is exposed so dependent `.left` and `.hom` types of mapped morphisms compute.
@[expose]
def iteratedSliceBackward : P.Over ⊤ U.left ⥤ CategoryTheory.Over U where
  obj W := CategoryTheory.Over.mk (Over.homMk W.hom rfl : (Over.map ⊤ U.prop).obj W ⟶ U)
  map g := CategoryTheory.Over.homMk ((Over.map ⊤ U.prop).map g)
    (Over.Hom.ext (Over.w g))

@[simp]
lemma iteratedSliceBackward_obj_left (W : P.Over ⊤ U.left) :
    ((iteratedSliceBackward U).obj W).left = (Over.map ⊤ U.prop).obj W :=
  (rfl)

@[simp]
lemma iteratedSliceBackward_obj_hom_left (W : P.Over ⊤ U.left) :
    (((iteratedSliceBackward U).obj W).hom).left = W.hom :=
  (rfl)

@[simp]
lemma iteratedSliceBackward_map_left_left {V W : P.Over ⊤ U.left} (g : V ⟶ W) :
    (((iteratedSliceBackward U).map g).left).left = g.left :=
  (rfl)

/-- Postcomposing `iteratedSliceBackward U` with `CategoryTheory.Over.forget U` recovers
`MorphismProperty.Over.map ⊤ U.prop : P.Over ⊤ U.left ⥤ P.Over ⊤ X`. -/
def iteratedSliceBackwardCompForgetIso :
    iteratedSliceBackward U ⋙ CategoryTheory.Over.forget U ≅ Over.map ⊤ U.prop :=
  NatIso.ofComponents
    (fun _ ↦ Over.isoMk (Iso.refl _) (Category.id_comp _))
    (fun _ ↦ Over.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm))

@[simp]
lemma iteratedSliceBackwardCompForgetIso_hom_app_left (W : P.Over ⊤ U.left) :
    ((iteratedSliceBackwardCompForgetIso U).hom.app W).left = 𝟙 W.left :=
  (rfl)

@[simp]
lemma iteratedSliceBackwardCompForgetIso_inv_app_left (W : P.Over ⊤ U.left) :
    ((iteratedSliceBackwardCompForgetIso U).inv.app W).left = 𝟙 W.left :=
  (rfl)

end Backward

section Forward

variable {C : Type*} [Category* C] {P : MorphismProperty C} [P.HasOfPostcompProperty P]
  {X : C} (U : P.Over ⊤ X)

/-- The forward functor of `CategoryTheory.Over U ≌ P.Over ⊤ U.left`, sending an object `V` of
`CategoryTheory.Over U` to `V.left.left ⟶ U.left` in `P.Over ⊤ U.left`. -/
-- The body is exposed so dependent `.left` and `.hom` types of mapped morphisms compute.
@[expose]
def iteratedSliceForward : CategoryTheory.Over U ⥤ P.Over ⊤ U.left where
  obj V := Over.mk ⊤ V.hom.left
    (P.of_postcomp V.hom.left U.hom U.prop ((Over.w V.hom).symm ▸ V.left.prop))
  map f := Over.homMk f.left.left (by rw [← CategoryTheory.Over.w f]; rfl)

@[simp]
lemma iteratedSliceForward_obj_left (V : CategoryTheory.Over U) :
    ((iteratedSliceForward U).obj V).left = V.left.left :=
  (rfl)

@[simp]
lemma iteratedSliceForward_obj_hom (V : CategoryTheory.Over U) :
    ((iteratedSliceForward U).obj V).hom = V.hom.left :=
  (rfl)

@[simp]
lemma iteratedSliceForward_map_left {V W : CategoryTheory.Over U} (f : V ⟶ W) :
    ((iteratedSliceForward U).map f).left = f.left.left :=
  (rfl)

end Forward

section Equiv

variable {C : Type*} [Category* C] {P : MorphismProperty C}
  [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]
  {X : C} (U : P.Over ⊤ X)

/-- When `P` is stable under composition and satisfies right cancellation, the slice category
`CategoryTheory.Over U` over `U : P.Over ⊤ X` is equivalent to `P.Over ⊤ U.left`. -/
-- The body is exposed so `functor` and `inverse` reduce to `iteratedSliceForward` and
-- `iteratedSliceBackward` in dependent `.left` and `.hom` types.
@[expose]
def iteratedSliceEquiv : CategoryTheory.Over U ≌ P.Over ⊤ U.left where
  functor := iteratedSliceForward U
  inverse := iteratedSliceBackward U
  unitIso := NatIso.ofComponents
    (fun V ↦ CategoryTheory.Over.isoMk
      (Over.isoMk (Iso.refl _) ((Category.id_comp _).trans (Over.w V.hom)))
      (Over.Hom.ext (Category.id_comp _)))
    (fun _ ↦ CategoryTheory.Over.OverMorphism.ext
      (Over.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm)))
  counitIso := NatIso.ofComponents
    (fun _ ↦ Over.isoMk (Iso.refl _) (Category.id_comp _))
    (fun _ ↦ Over.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm))
  functor_unitIso_comp _ := Over.Hom.ext (Category.id_comp _)

@[simp]
lemma iteratedSliceEquiv_functor :
    (iteratedSliceEquiv U).functor = iteratedSliceForward U :=
  (rfl)

@[simp]
lemma iteratedSliceEquiv_inverse :
    (iteratedSliceEquiv U).inverse = iteratedSliceBackward U :=
  (rfl)

/-- Postcomposing `iteratedSliceForward U` with `MorphismProperty.Over.map ⊤ U.prop` recovers
`CategoryTheory.Over.forget U : CategoryTheory.Over U ⥤ P.Over ⊤ X`. -/
def iteratedSliceForwardCompMapIso :
    iteratedSliceForward U ⋙ Over.map ⊤ U.prop ≅ CategoryTheory.Over.forget U :=
  NatIso.ofComponents
    (fun V ↦ Over.isoMk (Iso.refl _) ((Category.id_comp _).trans (Over.w V.hom).symm))
    (fun _ ↦ Over.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm))

@[simp]
lemma iteratedSliceForwardCompMapIso_hom_app_left (V : CategoryTheory.Over U) :
    ((iteratedSliceForwardCompMapIso U).hom.app V).left = 𝟙 V.left.left :=
  (rfl)

@[simp]
lemma iteratedSliceForwardCompMapIso_inv_app_left (V : CategoryTheory.Over U) :
    ((iteratedSliceForwardCompMapIso U).inv.app V).left = 𝟙 V.left.left :=
  (rfl)

end Equiv

end Over

end CategoryTheory.MorphismProperty
