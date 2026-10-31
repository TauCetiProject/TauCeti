/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Two presentations of a restricted over category

For a morphism property `P`, the category `P.Over ⊤ X` and the full subcategory of `Over X`
on `P.overObj` have the same objects and all morphisms over `X`. The equivalence below keeps
the underlying object and morphism of `Over X` unchanged. It allows constructions stated for
morphism-property over categories to be used with object-property full subcategories.
-/

public section

namespace CategoryTheory.MorphismProperty

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

end CategoryTheory.MorphismProperty
