/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Image subobjects in abelian categories

In a balanced category with images, precomposing with an epimorphism does not change an image
subobject (`imageSubobject_comp_eq_of_epi`). Hence the direct image of the image subobject of `f`
along `g` is the image subobject of `f ≫ g` (`Subobject.exists_obj_imageSubobject`).

In an abelian category, a morphism `a : A ⟶ Y` factors through the image subobject of
`f : X ⟶ Y` exactly when, after precomposition with an epimorphism, it lifts along `f`
(`imageSubobject_factors_iff_up_to_refinements`). This is the subobject form of the
characterization of epimorphisms in `Mathlib.CategoryTheory.Abelian.Refinements`. As a
consequence, the restriction of `f` to the preimage of a subobject of its image is an
epimorphism onto that subobject (`Subobject.epi_pullbackπ_of_le_imageSubobject`).
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {X Y : C}

section Balanced

variable [Balanced C] [HasImages C] [HasEqualizers C]

/-- Precomposing with an epimorphism does not change the image subobject. -/
lemma imageSubobject_comp_eq_of_epi {X' : C} (h : X' ⟶ X) [Epi h] (f : X ⟶ Y) :
    imageSubobject (h ≫ f) = imageSubobject f := by
  have := isIso_of_mono_of_epi (Subobject.ofLE _ _ (imageSubobject_comp_le h f))
  exact le_antisymm (imageSubobject_comp_le h f)
    (Subobject.le_of_comm (inv (Subobject.ofLE _ _ (imageSubobject_comp_le h f))) (by simp))

/-- The direct image of the image subobject of `f` along `g` is the image subobject of `f ≫ g`. -/
lemma Subobject.exists_obj_imageSubobject (f : X ⟶ Y) {Z : C} (g : Y ⟶ Z) :
    (Subobject.exists g).obj (imageSubobject f) = imageSubobject (f ≫ g) := by
  rw [Subobject.exists_eq_imageSubobject,
    ← imageSubobject_comp_eq_of_epi (factorThruImageSubobject f), imageSubobject_arrow_comp_assoc]

end Balanced

variable [Abelian C]

/-- A morphism factors through the image subobject of `f` if and only if it lifts along `f`
up to refinements. -/
lemma imageSubobject_factors_iff_up_to_refinements (f : X ⟶ Y) {A : C} (a : A ⟶ Y) :
    (imageSubobject f).Factors a ↔
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ a = x ≫ f := by
  constructor
  · intro h
    obtain ⟨A', π, hπ, x, hx⟩ := surjective_up_to_refinements_of_epi
      (factorThruImageSubobject f) ((imageSubobject f).factorThru a h)
    exact ⟨A', π, hπ, x, by
      rw [← Subobject.factorThru_arrow _ a h, reassoc_of% hx, imageSubobject_arrow_comp]⟩
  · rintro ⟨A', π, hπ, x, hx⟩
    have hf : f ≫ cokernel.π (imageSubobject f).arrow = 0 := by
      calc f ≫ cokernel.π (imageSubobject f).arrow =
          factorThruImageSubobject f ≫ (imageSubobject f).arrow ≫
            cokernel.π (imageSubobject f).arrow := by rw [imageSubobject_arrow_comp_assoc]
        _ = 0 := by rw [cokernel.condition, comp_zero]
    have ha : a ≫ cokernel.π (imageSubobject f).arrow = 0 := by
      rw [← cancel_epi π, reassoc_of% hx, hf, comp_zero, comp_zero]
    obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift'
      (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel (imageSubobject f).arrow)) a ha
    exact hl ▸ Subobject.factors_comp_arrow (P := imageSubobject f) l

/-- The restriction of `f : X ⟶ Y` to the preimage of a subobject `y` of the image of `f` is an
epimorphism onto `y`. -/
lemma Subobject.epi_pullbackπ_of_le_imageSubobject (f : X ⟶ Y) {y : Subobject Y}
    (hy : y ≤ imageSubobject f) : Epi (Subobject.pullbackπ f y) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro A b
  obtain ⟨A', π, hπ, x, hx⟩ := (imageSubobject_factors_iff_up_to_refinements f (b ≫ y.arrow)).1
    (Subobject.factors_of_le _ hy (Subobject.factors_comp_arrow b))
  exact ⟨A', π, hπ, (Subobject.isPullback f y).lift (π ≫ b) x (by simpa using hx),
    by simp⟩

end CategoryTheory
