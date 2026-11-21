/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Universal injectivity of affine morphisms

For a ring map `φ : R ⟶ S`, the morphism `Spec S ⟶ Spec R` is universally injective iff any two
ring maps from `S` into a field that agree on `R` are equal. This is Mathlib's field-valued
criterion for universal injectivity (Stacks, Lemma 29.10.2 (01S4)) with arrows reversed under
`Spec`.

## Main results

* `AlgebraicGeometry.UniversallyInjective.SpecMap_iff`: the field-valued criterion for
  `Spec.map φ`.

## References

* [Stacks Project, Lemma 29.10.2](https://stacks.math.columbia.edu/tag/01S4), the field-valued
  criterion for universal injectivity.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Field-valued criterion for universal injectivity of affine morphisms.** The morphism
`Spec S ⟶ Spec R` induced by `φ : R ⟶ S` is universally injective iff any two ring maps from `S`
into a field that agree on `R` are equal. -/
@[stacks 01S4]
theorem UniversallyInjective.SpecMap_iff {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    UniversallyInjective (Spec.map φ) ↔
      ∀ (K : Type u) [Field K], Function.Injective fun g : S →+* K ↦ g.comp φ.hom := by
  have := (tfae_universallyInjective (Spec.map φ)).out 1 2
  rw [this]
  refine forall_congr' fun K ↦ forall_congr' fun _ ↦ ⟨fun h g₁ g₂ hg ↦ ?_, fun h g₁ g₂ hg ↦ ?_⟩
  · have := h (a₁ := Spec.map (CommRingCat.ofHom g₁)) (a₂ := Spec.map (CommRingCat.ofHom g₂))
      (by simp only [← Spec.map_comp]; congr 1; ext1; exact hg)
    simpa using congr(($(Spec.map_injective this)).hom)
  · obtain ⟨g₁, rfl⟩ := Spec.map_surjective g₁
    obtain ⟨g₂, rfl⟩ := Spec.map_surjective g₂
    simp only [← Spec.map_comp] at hg
    have := congr(($(Spec.map_injective hg)).hom)
    rw [CommRingCat.hom_ext (h (a₁ := g₁.hom) (a₂ := g₂.hom) (by simpa using this))]

end AlgebraicGeometry
