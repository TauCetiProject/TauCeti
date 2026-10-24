/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Universal homeomorphisms of schemes

A universal homeomorphism is a scheme morphism whose every base change is a homeomorphism on
underlying spaces. Such maps are surjective, universally injective and universally closed.
Conversely, these three properties suffice. Equivalently, a universal homeomorphism is an
integral, universally injective, surjective morphism.

This criterion applies to Frobenius without imposing finiteness or reducedness assumptions.

## References

* The Stacks Project, [Tag 04DD](https://stacks.math.columbia.edu/tag/04DD), universal
  homeomorphisms.
* The Stacks Project, [Tag 04DF](https://stacks.math.columbia.edu/tag/04DF), the integral
  characterization of universal homeomorphisms.
-/

public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- A universal homeomorphism is surjective. -/
theorem Surjective.of_universally_isHomeomorph (hf : (topologically @IsHomeomorph).universally f) :
    Surjective f :=
  ⟨(universally_le _ _ hf).surjective⟩

/-- A universal homeomorphism is universally injective. -/
theorem UniversallyInjective.of_universally_isHomeomorph
    (hf : (topologically @IsHomeomorph).universally f) : UniversallyInjective f :=
  ⟨universally_mono (fun _ _ _ ↦ IsHomeomorph.injective) _ hf⟩

/-- A universal homeomorphism is universally closed. -/
theorem UniversallyClosed.of_universally_isHomeomorph
    (hf : (topologically @IsHomeomorph).universally f) : UniversallyClosed f :=
  ⟨universally_mono (fun _ _ _ ↦ IsHomeomorph.isClosedMap) _ hf⟩

end AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

variable {X Y Z S : Scheme.{u}}

/-- Every base change of a universal homeomorphism is a homeomorphism on underlying spaces. -/
@[mk_iff]
class IsUniversalHomeomorphism (f : X ⟶ Y) : Prop where
  universally_isHomeomorph : (topologically IsHomeomorph).universally f

/-- Universal homeomorphisms are the universal closure of the homeomorphism property. -/
theorem isUniversalHomeomorphism_eq :
    @IsUniversalHomeomorphism.{u} =
      (topologically IsHomeomorph : MorphismProperty Scheme.{u}).universally := by
  ext X Y f
  exact isUniversalHomeomorphism_iff f

instance isUniversalHomeomorphism_respectsIso :
    MorphismProperty.RespectsIso @IsUniversalHomeomorphism.{u} := by
  rw [isUniversalHomeomorphism_eq]
  infer_instance

instance isUniversalHomeomorphism_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsUniversalHomeomorphism.{u} := by
  rw [isUniversalHomeomorphism_eq]
  infer_instance

/-- A universal homeomorphism induces a homeomorphism before any base change. -/
theorem Scheme.Hom.isHomeomorph_of_isUniversalHomeomorphism
    (f : X ⟶ Y) [IsUniversalHomeomorphism f] : IsHomeomorph f :=
  MorphismProperty.universally_le _ _ IsUniversalHomeomorphism.universally_isHomeomorph

/-- Universal homeomorphisms are surjective on points. -/
instance (f : X ⟶ Y) [IsUniversalHomeomorphism f] : Surjective f :=
  Surjective.of_universally_isHomeomorph IsUniversalHomeomorphism.universally_isHomeomorph

/-- Universal homeomorphisms are universally closed. -/
instance (f : X ⟶ Y) [IsUniversalHomeomorphism f] : UniversallyClosed f :=
  UniversallyClosed.of_universally_isHomeomorph
    IsUniversalHomeomorphism.universally_isHomeomorph

/-- Universal homeomorphisms are universally injective. -/
instance (f : X ⟶ Y) [IsUniversalHomeomorphism f] : UniversallyInjective f :=
  UniversallyInjective.of_universally_isHomeomorph
    IsUniversalHomeomorphism.universally_isHomeomorph

/-- An explicit universal-homeomorphism hypothesis implies surjectivity on points. -/
theorem IsUniversalHomeomorphism.surjective {f : X ⟶ Y}
    (h : IsUniversalHomeomorphism f) : Surjective f := by
  let := h
  infer_instance

/-- An explicit universal-homeomorphism hypothesis implies universal closedness. -/
theorem IsUniversalHomeomorphism.universallyClosed {f : X ⟶ Y}
    (h : IsUniversalHomeomorphism f) : UniversallyClosed f := by
  let := h
  infer_instance

/-- An explicit universal-homeomorphism hypothesis implies universal injectivity. -/
theorem IsUniversalHomeomorphism.universallyInjective {f : X ⟶ Y}
    (h : IsUniversalHomeomorphism f) : UniversallyInjective f := by
  let := h
  infer_instance

/-- The second pullback projection is a universal homeomorphism when the first input map is. -/
instance (f : X ⟶ S) (g : Y ⟶ S) [IsUniversalHomeomorphism f] :
    IsUniversalHomeomorphism (pullback.snd f g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsUniversalHomeomorphism.{u}) (IsPullback.of_hasPullback f g) inferInstance

/-- The first pullback projection is a universal homeomorphism when the second input map is. -/
instance (f : X ⟶ S) (g : Y ⟶ S) [IsUniversalHomeomorphism g] :
    IsUniversalHomeomorphism (pullback.fst f g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsUniversalHomeomorphism.{u}) (IsPullback.of_hasPullback f g).flip inferInstance

/-- Universally closed, universally injective, surjective scheme maps are precisely the
universal homeomorphisms. -/
theorem isUniversalHomeomorphism_iff_universallyClosed_universallyInjective_surjective
    (f : X ⟶ Y) :
    IsUniversalHomeomorphism f ↔
      UniversallyClosed f ∧ UniversallyInjective f ∧ Surjective f := by
  constructor
  · intro h
    let := h
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · rintro ⟨hclosed, hinj, hsurj⟩
    let := hclosed
    let := hinj
    let := hsurj
    constructor
    intro X' Y' i₁ i₂ f' H
    have : UniversallyClosed f' := MorphismProperty.of_isPullback H.flip hclosed
    have : UniversallyInjective f' := MorphismProperty.of_isPullback H.flip hinj
    have : Surjective f' := MorphismProperty.of_isPullback H.flip hsurj
    exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
      ⟨f'.continuous, f'.isClosedMap, f'.injective, f'.surjective⟩

/-- Universal homeomorphisms are integral. -/
instance (f : X ⟶ Y) [IsUniversalHomeomorphism f] : IsIntegralHom f := by
  have : IsAffineHom f := isAffineHom_of_isInducing f
    (Scheme.Hom.isHomeomorph_of_isUniversalHomeomorphism f).isInducing
    (Scheme.Hom.isHomeomorph_of_isUniversalHomeomorphism f).isClosedEmbedding.isClosed_range
  exact IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr
    ⟨inferInstance, inferInstance⟩

/-- Integral, universally injective, surjective scheme maps are precisely the universal
homeomorphisms. -/
theorem isUniversalHomeomorphism_iff_isIntegralHom_universallyInjective_surjective
    (f : X ⟶ Y) :
    IsUniversalHomeomorphism f ↔
      IsIntegralHom f ∧ UniversallyInjective f ∧ Surjective f := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance, inferInstance⟩, ?_⟩
  rintro ⟨hint, hinj, hsurj⟩
  let := hint
  exact (isUniversalHomeomorphism_iff_universallyClosed_universallyInjective_surjective f).mpr
    ⟨inferInstance, hinj, hsurj⟩

/-- The affine universal-homeomorphism criterion: a ring map is integral, induces an injection
on maps into every field, and is surjective on prime spectra. Under `Spec`, precomposition by
the ring map corresponds to postcomposition by the scheme map. -/
theorem universalHomeomorphism_affineComparison {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    IsUniversalHomeomorphism (Spec.map φ) ↔
      φ.hom.IsIntegral ∧
        (∀ (K : Type u) [Field K],
          Function.Injective (fun g : S ⟶ CommRingCat.of K ↦ φ ≫ g)) ∧
        Function.Surjective (PrimeSpectrum.comap φ.hom) := by
  have hfield : UniversallyInjective (Spec.map φ) ↔
      ∀ (K : Type u) [Field K],
        Function.Injective (fun g : Spec (CommRingCat.of K) ⟶ Spec S ↦ g ≫ Spec.map φ) :=
    (tfae_universallyInjective (Spec.map φ)).out 1 2
  rw [isUniversalHomeomorphism_iff_isIntegralHom_universallyInjective_surjective,
    IsIntegralHom.SpecMap_iff, hfield]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · constructor
    · intro h K _ g₁ g₂ hg
      apply Spec.map_injective
      apply h K
      simpa only [← Spec.map_comp] using congrArg Spec.map hg
    · intro h K _ g₁ g₂ hg
      obtain ⟨f₁, rfl⟩ := Spec.map_surjective g₁
      obtain ⟨f₂, rfl⟩ := Spec.map_surjective g₂
      apply congrArg Spec.map
      apply h K
      exact Spec.map_injective (by simpa only [Spec.map_comp] using hg)
  · simp only [surjective_iff, Function.Surjective, Spec.map_apply]
    -- Points of Spec are definitionally prime ideals; Spec.map_apply identifies the point map
    -- with PrimeSpectrum.comap, so the two surjectivity statements are definitionally equal.
    rfl

/-- Composites of universal homeomorphisms are universal homeomorphisms. -/
instance isUniversalHomeomorphism_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @IsUniversalHomeomorphism.{u} where
  comp_mem f g hf hg := by
    let := hf
    let := hg
    apply (isUniversalHomeomorphism_iff_universallyClosed_universallyInjective_surjective _).mpr
    exact ⟨inferInstance,
      MorphismProperty.comp_mem @UniversallyInjective f g inferInstance inferInstance,
      inferInstance⟩

/-- Typeclass inference recognizes composites of universal homeomorphisms. -/
instance (f : X ⟶ Y) (g : Y ⟶ Z) [IsUniversalHomeomorphism f]
    [IsUniversalHomeomorphism g] : IsUniversalHomeomorphism (f ≫ g) :=
  MorphismProperty.comp_mem @IsUniversalHomeomorphism f g inferInstance inferInstance

/-- Every isomorphism of schemes is a universal homeomorphism. -/
instance IsUniversalHomeomorphism.of_isIso (f : X ⟶ Y) [IsIso f] :
    IsUniversalHomeomorphism f :=
  (isUniversalHomeomorphism_iff_universallyClosed_universallyInjective_surjective f).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- The homeomorphism of underlying spaces induced by a universal homeomorphism of schemes. -/
noncomputable def Scheme.Hom.homeomorphOfIsUniversalHomeomorphism
    (f : X ⟶ Y) [IsUniversalHomeomorphism f] : X ≃ₜ Y :=
  (Scheme.Hom.isHomeomorph_of_isUniversalHomeomorphism f).homeomorph f

@[simp]
theorem Scheme.Hom.homeomorphOfIsUniversalHomeomorphism_apply
    (f : X ⟶ Y) [IsUniversalHomeomorphism f] (x : X) :
    (Scheme.Hom.homeomorphOfIsUniversalHomeomorphism f) x = f x :=
  (rfl)

/-- The inverse underlying homeomorphism sends the image of a point back to that point. -/
@[simp]
theorem Scheme.Hom.homeomorphOfIsUniversalHomeomorphism_symm_apply_apply
    (f : X ⟶ Y) [IsUniversalHomeomorphism f] (x : X) :
    (Scheme.Hom.homeomorphOfIsUniversalHomeomorphism f).symm (f x) = x := by
  simpa only [Scheme.Hom.homeomorphOfIsUniversalHomeomorphism_apply] using
    (Scheme.Hom.homeomorphOfIsUniversalHomeomorphism f).symm_apply_apply x

/-- Mapping the point supplied by the inverse homeomorphism recovers the original point. -/
@[simp]
theorem Scheme.Hom.homeomorphOfIsUniversalHomeomorphism_apply_symm_apply
    (f : X ⟶ Y) [IsUniversalHomeomorphism f] (y : Y) :
    f ((Scheme.Hom.homeomorphOfIsUniversalHomeomorphism f).symm y) = y := by
  simpa only [Scheme.Hom.homeomorphOfIsUniversalHomeomorphism_apply] using
    (Scheme.Hom.homeomorphOfIsUniversalHomeomorphism f).apply_symm_apply y

end TauCeti.AlgebraicGeometry
