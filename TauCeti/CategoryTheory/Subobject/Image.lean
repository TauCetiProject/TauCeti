/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Balanced
public import Mathlib.CategoryTheory.Subobject.Limits
import TauCeti.CategoryTheory.Subobject.Limits

/-!
# Image subobjects in balanced categories

In a balanced category with images, precomposing with an epimorphism does not change an image
subobject (`imageSubobject_comp_eq_of_epi`). Hence precomposing with an epimorphism does not change
whether a morphism factors through a subobject (`Subobject.factors_comp_iff_of_epi`), and the direct
image of the image subobject of `f` along `g` is the image subobject of `f ≫ g`
(`Subobject.exists_obj_imageSubobject`).
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {X Y : C}
  [Balanced C] [HasImages C] [HasEqualizers C]

/-- Precomposing with an epimorphism does not change the image subobject. -/
lemma imageSubobject_comp_eq_of_epi {X' : C} (h : X' ⟶ X) [Epi h] (f : X ⟶ Y) :
    imageSubobject (h ≫ f) = imageSubobject f := by
  have := isIso_of_mono_of_epi (Subobject.ofLE _ _ (imageSubobject_comp_le h f))
  exact le_antisymm (imageSubobject_comp_le h f)
    (Subobject.le_of_comm (inv (Subobject.ofLE _ _ (imageSubobject_comp_le h f))) (by simp))

/-- Precomposing with an epimorphism does not change whether a morphism factors through a
subobject. -/
lemma Subobject.factors_comp_iff_of_epi {Z : C} (S : Subobject Z) {X' : C} (h : X' ⟶ X) [Epi h]
    (f : X ⟶ Z) : S.Factors (h ≫ f) ↔ S.Factors f := by
  rw [← imageSubobject_le_iff_factors, ← imageSubobject_le_iff_factors,
    imageSubobject_comp_eq_of_epi]

/-- The direct image of the image subobject of `f` along `g` is the image subobject of `f ≫ g`. -/
lemma Subobject.exists_obj_imageSubobject (f : X ⟶ Y) {Z : C} (g : Y ⟶ Z) :
    (Subobject.exists g).obj (imageSubobject f) = imageSubobject (f ≫ g) := by
  rw [Subobject.exists_eq_imageSubobject,
    ← imageSubobject_comp_eq_of_epi (factorThruImageSubobject f), imageSubobject_arrow_comp_assoc]

end CategoryTheory
