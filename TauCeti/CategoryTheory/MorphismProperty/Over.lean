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
  the identity morphism identifies with the identity functor;
* `CategoryTheory.MorphismProperty.Over.iteratedSliceEquiv`: for `U : P.Over ⊤ X`, when `P` is
  stable under composition and satisfies `P.HasOfPostcompProperty P`, the slice category
  `CategoryTheory.Over U` is equivalent to `P.Over ⊤ U.left`.
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

end PullbackId

section IteratedSlice

variable {C : Type*} [Category* C] {P : MorphismProperty C} {X : C}

/-- Given `U : P.Over ⊤ X`, when `P` has the `of_postcomp` property with respect to itself, any
morphism `α : V ⟶ U` in `P.Over ⊤ X` has underlying morphism `α.left : V.left ⟶ U.left` satisfying
`P`. This defines the forward functor `(P.Over ⊤ X)/U ⥤ P.Over ⊤ U.left`. -/
@[expose]
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
    ((iteratedSliceForward U).obj α).hom = α.hom.left :=
  (rfl)

@[simp]
lemma iteratedSliceForward_map_left [P.HasOfPostcompProperty P] (U : P.Over ⊤ X)
    {α β : CategoryTheory.Over U} (κ : α ⟶ β) :
    ((iteratedSliceForward U).map κ).left = κ.left.left :=
  (rfl)

/-- Given `U : P.Over ⊤ X`, post-composition with `U.hom` sends an object `V : P.Over ⊤ U.left` to
an object over `U` in `P.Over ⊤ X`. -/
@[expose]
def iteratedSliceBackward [P.IsStableUnderComposition] (U : P.Over ⊤ X) :
    P.Over ⊤ U.left ⥤ CategoryTheory.Over U where
  obj V := CategoryTheory.Over.mk (Over.homMk V.hom (w := rfl) : (Over.map ⊤ U.prop).obj V ⟶ U)
  map f := CategoryTheory.Over.homMk ((Over.map ⊤ U.prop).map f) (by ext; exact Over.w f)

@[simp]
lemma iteratedSliceBackward_obj_left [P.IsStableUnderComposition] (U : P.Over ⊤ X)
    (V : P.Over ⊤ U.left) :
    ((iteratedSliceBackward U).obj V).left = (Over.map ⊤ U.prop).obj V :=
  (rfl)

@[simp]
lemma iteratedSliceBackward_obj_hom_left [P.IsStableUnderComposition] (U : P.Over ⊤ X)
    (V : P.Over ⊤ U.left) :
    ((iteratedSliceBackward U).obj V).hom.left = V.hom :=
  (rfl)

@[simp]
lemma iteratedSliceBackward_map_left [P.IsStableUnderComposition] (U : P.Over ⊤ X)
    {V W : P.Over ⊤ U.left} (f : V ⟶ W) :
    ((iteratedSliceBackward U).map f).left = (Over.map ⊤ U.prop).map f :=
  (rfl)

/-- Composing `iteratedSliceBackward U` with the forgetful functor from `CategoryTheory.Over U`
recovers `Over.map ⊤ U.prop`. -/
@[simp]
theorem iteratedSliceBackward_forget [P.IsStableUnderComposition] (U : P.Over ⊤ X) :
    iteratedSliceBackward U ⋙ CategoryTheory.Over.forget U = Over.map ⊤ U.prop :=
  (rfl)

/-- Composing `Over.map ⊤ hf` with the forgetful functor to `C` recovers the forgetful functor on
the source. -/
theorem map_forget_forget [P.IsStableUnderComposition] {Y : C} {f : Y ⟶ X} (hf : P f) :
    Over.map (P := P) ⊤ hf ⋙ Over.forget P ⊤ X ⋙ CategoryTheory.Over.forget X =
      Over.forget P ⊤ Y ⋙ CategoryTheory.Over.forget Y :=
  (rfl)

/-- For `U : P.Over ⊤ X`, the slice category `CategoryTheory.Over U` is equivalent to
`P.Over ⊤ U.left` whenever `P` is stable under composition and satisfies `P.HasOfPostcompProperty P`
(for example when `P` is étale, smooth, or open immersions). -/
@[expose]
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

end IteratedSlice

end Over

end CategoryTheory.MorphismProperty
