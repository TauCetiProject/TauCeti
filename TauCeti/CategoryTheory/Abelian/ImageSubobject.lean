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

In an abelian category, a morphism `a : A ⟶ Y` factors through the image subobject of
`f : X ⟶ Y` exactly when, after precomposition with an epimorphism, it lifts along `f`
(`imageSubobject_factors_iff_up_to_refinements`). This is the subobject form of the
characterization of epimorphisms in `Mathlib.CategoryTheory.Abelian.Refinements`. As a
consequence, the restriction of `f` to the preimage of a subobject of its image is an
epimorphism onto that subobject (`Subobject.epi_pullbackπ_of_le_imageSubobject`), and a morphism
factors through a subobject as soon as its precomposition with an epimorphism does
(`Subobject.factors_epi_comp_iff`). Factorizations through image subobjects lift along a
commutative square whose map on the sources is an epimorphism, provided the kernel of the target
map lies in the image of the source map (`imageSubobject_factors_of_comm`).

## Main results

* `CategoryTheory.imageSubobject_factors_iff_up_to_refinements`: a morphism factors through the
  image subobject of `f` exactly when it lifts along `f` up to refinements.
* `CategoryTheory.Subobject.epi_pullbackπ_of_le_imageSubobject`: the restriction of `f` to the
  preimage of a subobject of its image is an epimorphism onto that subobject.
* `CategoryTheory.Subobject.factors_epi_comp_iff`: a morphism factors through a subobject exactly
  when its precomposition with an epimorphism does.
* `CategoryTheory.imageSubobject_factors_of_comm`: lifting factorizations through image
  subobjects along a commutative square.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {X Y : C}

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

/-- A morphism factors through a subobject exactly when its precomposition with an epimorphism
does. -/
lemma Subobject.factors_epi_comp_iff (P : Subobject X) {A A' : C} (π : A' ⟶ A) [Epi π]
    (a : A ⟶ X) :
    P.Factors (π ≫ a) ↔ P.Factors a := by
  refine ⟨fun h ↦ ?_, Subobject.factors_of_factors_right π⟩
  have hP : P = imageSubobject P.arrow := by rw [imageSubobject_mono, Subobject.mk_arrow]
  rw [hP] at h ⊢
  obtain ⟨A'', π', _, x, hx⟩ := (imageSubobject_factors_iff_up_to_refinements _ _).1 h
  exact (imageSubobject_factors_iff_up_to_refinements _ _).2
    ⟨A'', π' ≫ π, inferInstance, x, by rw [Category.assoc, hx]⟩

/-- **Lifting factorizations along a commutative square.** Let `α ≫ p = p' ≫ α'` with `p'` an
epimorphism, and suppose that the kernel of `p` lies in the image of `α`. If `y ≫ p` factors
through the image of `α'`, then `y` factors through the image of `α`. -/
lemma imageSubobject_factors_of_comm {E F E' F' W : C} (p : E ⟶ F)
    (α : E' ⟶ E) (α' : F' ⟶ F) (p' : E' ⟶ F') [Epi p'] (w : α ≫ p = p' ≫ α')
    (h : kernelSubobject p ≤ imageSubobject α) (y : W ⟶ E)
    (hy : (imageSubobject α').Factors (y ≫ p)) : (imageSubobject α).Factors y := by
  obtain ⟨A₁, π₁, _, x, hx⟩ := (imageSubobject_factors_iff_up_to_refinements α' _).1 hy
  obtain ⟨A₂, π₂, _, z, hz⟩ := surjective_up_to_refinements_of_epi p' x
  rw [← Subobject.factors_epi_comp_iff _ (π₂ ≫ π₁)]
  have hk : (kernelSubobject p).Factors ((π₂ ≫ π₁) ≫ y - z ≫ α) :=
    kernelSubobject_factors _ _ (by
      rw [Preadditive.sub_comp, Category.assoc, Category.assoc, hx, Category.assoc, w,
        ← Category.assoc z, ← hz, Category.assoc, sub_self])
  have := Subobject.factors_add _ _ (Subobject.factors_of_le _ h hk)
    (imageSubobject_factors_comp_self α z)
  rwa [sub_add_cancel] at this

end CategoryTheory
