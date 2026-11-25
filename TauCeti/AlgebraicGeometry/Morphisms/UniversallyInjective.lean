/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Universal injectivity

Universal injectivity descends along surjections: if `f ≫ g` is universally injective and `f` is
surjective, then `g` is universally injective. An injective morphism inducing isomorphisms of
residue fields is universally injective.

For a ring map `φ : R ⟶ S`, the morphism `Spec S ⟶ Spec R` is universally injective iff any two
ring maps from `S` into a field that agree on `R` are equal. This is Mathlib's field-valued
criterion for universal injectivity (Stacks, Lemma 29.10.2 (01S4)) with arrows reversed under
`Spec`.

## Main results

* `AlgebraicGeometry.UniversallyInjective.of_comp_surjective`: universal injectivity descends
  along a surjection.
* `AlgebraicGeometry.UniversallyInjective.of_injective_of_isIso_residueFieldMap`: an injective
  morphism with trivial residue field extensions is universally injective.
* `AlgebraicGeometry.UniversallyInjective.SpecMap_iff`: the field-valued criterion for
  `Spec.map φ`.

## References

* [Stacks Project, Lemma 29.10.2](https://stacks.math.columbia.edu/tag/01S4), the field-valued
  criterion for universal injectivity.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- If `f ≫ g` is universally injective and `f` is surjective, then `g` is universally
injective. -/
theorem UniversallyInjective.of_comp_surjective {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [UniversallyInjective (f ≫ g)] [Surjective f] : UniversallyInjective g := by
  constructor
  intro X' Y' i₁ i₂ g' H
  have := UniversallyInjective.universally_injective _ _ _
    ((IsPullback.of_hasPullback i₁ f).paste_horiz H)
  have hs : Surjective (pullback.fst i₁ f) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback i₁ f).flip ‹_›
  exact Function.Injective.of_comp_right (f := g'.base) this hs.surj

/-- An injective morphism inducing isomorphisms of residue fields is universally injective. -/
theorem UniversallyInjective.of_injective_of_isIso_residueFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Function.Injective f.base) (hres : ∀ x, IsIso (f.residueFieldMap x)) :
    UniversallyInjective f := by
  -- The diagonal is surjective: a point of `X ×_Y X` lies over a pair `(x, x)`, and it is the
  -- unique point over that pair because `f` preserves the residue field at `x`.
  rw [UniversallyInjective.iff_diagonal]
  refine ⟨fun t ↦ ⟨pullback.fst f f t, ?_⟩⟩
  have h : pullback.fst f f t = pullback.snd f f t := hf <| by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have := hres (pullback.snd f f t)
  apply Scheme.Pullback.eq_of_fst_eq_snd_eq_of_isIso
  · rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]
    simp
  · rw [← Scheme.Hom.comp_apply, pullback.diagonal_snd]
    exact h

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
