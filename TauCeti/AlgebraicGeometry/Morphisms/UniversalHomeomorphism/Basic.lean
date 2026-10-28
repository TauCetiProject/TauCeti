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

A morphism of schemes `f : X ⟶ Y` is a *universal homeomorphism* when every base change
`X ×_Y Y' ⟶ Y'` of `f` is a homeomorphism of underlying spaces (Stacks, Definition 29.46.1
(04DD)). No finiteness hypothesis is imposed. Typical examples are surjective closed immersions
(thickenings), the absolute and relative Frobenius, and the normalization of a cusp.

The main result is the criterion of Stacks, Lemma 29.46.5 (04DF): a morphism is a universal
homeomorphism if and only if it is integral, universally injective and surjective. One direction
uses that a morphism whose underlying map is a closed embedding is affine (Stacks 04DE, Mathlib's
`AlgebraicGeometry.isAffineHom_of_isInducing`), so that a universal homeomorphism is affine and
universally closed, hence integral. Over affine schemes, the criterion
becomes a statement about ring maps: `Spec S ⟶ Spec R` is a universal homeomorphism iff `R → S`
is integral, surjective on prime spectra, and any two ring maps from `S` to a field agreeing on
`R` are equal.

## Main definitions

* `TauCeti.AlgebraicGeometry.IsUniversalHomeomorphism f`: every base change of `f` is a
  homeomorphism on underlying spaces.
* `AlgebraicGeometry.Scheme.Hom.homeomorphOfIsUniversalHomeomorphism f`: the homeomorphism of
  underlying spaces induced by a universal homeomorphism `f`.

## Main results

* `TauCeti.AlgebraicGeometry.isUniversalHomeomorphism_eq`: the class is Mathlib's
  `(topologically IsHomeomorph).universally`.
* `IsUniversalHomeomorphism.iff_universallyClosed_and_universallyInjective_and_surjective` and
  `IsUniversalHomeomorphism.iff_isIntegralHom_and_universallyInjective_and_surjective`: the two
  criteria for universal homeomorphisms.
* `TauCeti.AlgebraicGeometry.IsUniversalHomeomorphism.SpecMap_iff`: the affine criterion in terms
  of ring maps.
* Instances: universal homeomorphisms are stable under base change and composition, contain the
  isomorphisms and the surjective closed immersions, and are surjective, universally closed,
  universally injective and integral.

## References

* [Stacks Project, Section 29.46](https://stacks.math.columbia.edu/tag/04DC), universal
  homeomorphisms.
-/

public section

open CategoryTheory Limits MorphismProperty

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

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

/-- A morphism of schemes `f : X ⟶ Y` is a *universal homeomorphism* if for every morphism
`Y' ⟶ Y` the base change `X ×_Y Y' ⟶ Y'` is a homeomorphism of underlying spaces. -/
@[mk_iff, stacks 04DD]
class IsUniversalHomeomorphism (f : X ⟶ Y) : Prop where
  universally_isHomeomorph : (topologically @IsHomeomorph).universally f

/-- Universal homeomorphisms are the universal closure of the homeomorphism property. -/
theorem isUniversalHomeomorphism_eq :
    @IsUniversalHomeomorphism.{u} = (topologically @IsHomeomorph).universally := by
  ext X Y f
  rw [isUniversalHomeomorphism_iff]

/-- Being a universal homeomorphism is invariant under composing with isomorphisms. -/
instance isUniversalHomeomorphism_respectsIso :
    MorphismProperty.RespectsIso @IsUniversalHomeomorphism.{u} := by
  rw [isUniversalHomeomorphism_eq]
  infer_instance

/-- Every base change of a universal homeomorphism is a universal homeomorphism. -/
instance isUniversalHomeomorphism_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsUniversalHomeomorphism.{u} := by
  rw [isUniversalHomeomorphism_eq]
  infer_instance

namespace IsUniversalHomeomorphism

variable (f : X ⟶ Y)

/-- The underlying map of a universal homeomorphism is a homeomorphism. -/
theorem isHomeomorph [IsUniversalHomeomorphism f] : IsHomeomorph f :=
  universally_le _ _ (universally_isHomeomorph (f := f))

/-- A universal homeomorphism is surjective. -/
instance (priority := 900) surjective [IsUniversalHomeomorphism f] : Surjective f :=
  .of_universally_isHomeomorph universally_isHomeomorph

/-- A universal homeomorphism is universally closed. -/
instance (priority := 900) universallyClosed [IsUniversalHomeomorphism f] : UniversallyClosed f :=
  .of_universally_isHomeomorph universally_isHomeomorph

/-- A universal homeomorphism is universally injective. -/
instance (priority := 900) universallyInjective [IsUniversalHomeomorphism f] :
    UniversallyInjective f :=
  .of_universally_isHomeomorph universally_isHomeomorph

/-- A universal homeomorphism is affine: its underlying map is a closed embedding. -/
instance (priority := 900) isAffineHom [IsUniversalHomeomorphism f] : IsAffineHom f :=
  isAffineHom_of_isInducing f (isHomeomorph f).isInducing
    (isHomeomorph f).isClosedEmbedding.isClosed_range

/-- A universal homeomorphism is integral, being affine and universally closed. -/
instance (priority := 900) isIntegralHom [IsUniversalHomeomorphism f] : IsIntegralHom f :=
  IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

variable {f} in
/-- A morphism is a universal homeomorphism iff it is universally closed, universally injective
and surjective. -/
theorem iff_universallyClosed_and_universallyInjective_and_surjective :
    IsUniversalHomeomorphism f ↔
      UniversallyClosed f ∧ UniversallyInjective f ∧ Surjective f := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance, inferInstance⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨?_⟩⟩
  intro X' Y' i₁ i₂ f' H
  have : UniversallyClosed f' := of_isPullback H.flip h₁
  have : UniversallyInjective f' := of_isPullback H.flip h₂
  have : Surjective f' := of_isPullback H.flip h₃
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨f'.continuous, f'.isClosedMap, f'.injective, f'.surjective⟩

variable {f} in
/-- **Criterion for universal homeomorphisms.** A morphism is a universal homeomorphism iff it is
integral, universally injective and surjective. -/
@[stacks 04DF]
theorem iff_isIntegralHom_and_universallyInjective_and_surjective :
    IsUniversalHomeomorphism f ↔
      IsIntegralHom f ∧ UniversallyInjective f ∧ Surjective f := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance, inferInstance⟩, fun ⟨_, h₂, h₃⟩ ↦ ?_⟩
  exact iff_universallyClosed_and_universallyInjective_and_surjective.mpr ⟨inferInstance, h₂, h₃⟩

/-- The `MorphismProperty` form of the criterion for universal homeomorphisms. -/
theorem eq_isIntegralHom_inf_universallyInjective_inf_surjective :
    @IsUniversalHomeomorphism.{u} =
      (@IsIntegralHom ⊓ (@UniversallyInjective ⊓ @Surjective) : MorphismProperty Scheme.{u}) := by
  ext X Y f
  exact iff_isIntegralHom_and_universallyInjective_and_surjective

/-- Isomorphisms are universal homeomorphisms. -/
instance (priority := 900) of_isIso [IsIso f] : IsUniversalHomeomorphism f :=
  iff_isIntegralHom_and_universallyInjective_and_surjective.mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- A surjective closed immersion (a thickening) is a universal homeomorphism. -/
instance (priority := 900) of_isClosedImmersion_of_surjective [IsClosedImmersion f]
    [Surjective f] : IsUniversalHomeomorphism f :=
  iff_isIntegralHom_and_universallyInjective_and_surjective.mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- The composite of two universal homeomorphisms is a universal homeomorphism. -/
instance comp (g : Y ⟶ Z) [IsUniversalHomeomorphism f] [IsUniversalHomeomorphism g] :
    IsUniversalHomeomorphism (f ≫ g) :=
  iff_isIntegralHom_and_universallyInjective_and_surjective.mpr
    ⟨inferInstance, comp_mem _ _ _ inferInstance inferInstance, inferInstance⟩

/-- The first projection of a pullback along a universal homeomorphism is a universal
homeomorphism. -/
instance pullback_fst {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsUniversalHomeomorphism g] :
    IsUniversalHomeomorphism (pullback.fst f g) :=
  of_isPullback (IsPullback.of_hasPullback f g).flip ‹_›

/-- The second projection of a pullback along a universal homeomorphism is a universal
homeomorphism. -/
instance pullback_snd {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsUniversalHomeomorphism f] :
    IsUniversalHomeomorphism (pullback.snd f g) :=
  of_isPullback (IsPullback.of_hasPullback f g) ‹_›

/-- **Affine criterion for universal homeomorphisms.** The morphism `Spec S ⟶ Spec R` induced
by `φ : R ⟶ S` is a universal homeomorphism iff `φ` is integral, any two ring maps from `S` into
a field agreeing on `R` are equal, and `φ` is surjective on prime spectra. -/
theorem SpecMap_iff {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    IsUniversalHomeomorphism (Spec.map φ) ↔
      φ.hom.IsIntegral ∧
        (∀ (K : Type u) [Field K], Function.Injective fun g : S →+* K ↦ g.comp φ.hom) ∧
        Function.Surjective (PrimeSpectrum.comap φ.hom) := by
  rw [iff_isIntegralHom_and_universallyInjective_and_surjective, IsIntegralHom.SpecMap_iff,
    UniversallyInjective.SpecMap_iff, surjective_iff]
  -- the underlying map of `Spec.map φ` is `PrimeSpectrum.comap φ.hom` by definition
  rfl

end IsUniversalHomeomorphism

/-- Universal homeomorphisms are stable under composition. -/
instance isUniversalHomeomorphism_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @IsUniversalHomeomorphism.{u} where
  comp_mem _ _ _ _ := inferInstance

/-- Universal homeomorphisms contain the identities and are stable under composition. -/
instance isUniversalHomeomorphism_isMultiplicative :
    MorphismProperty.IsMultiplicative @IsUniversalHomeomorphism.{u} where
  id_mem _ := inferInstance

/-- Being a universal homeomorphism is local on the target. -/
instance isUniversalHomeomorphism_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget @IsUniversalHomeomorphism.{u} := by
  rw [isUniversalHomeomorphism_eq]
  apply universally_isZariskiLocalAtTarget
  intro X Y f ι U hU H
  simp_rw [topologically, morphismRestrict_base] at H
  exact (hU.isHomeomorph_iff_restrictPreimage f.continuous).mpr H

/-- The restriction of a universal homeomorphism over an open subscheme of the target is a
universal homeomorphism. -/
instance IsUniversalHomeomorphism.morphismRestrict (f : X ⟶ Y) (V : Y.Opens)
    [IsUniversalHomeomorphism f] : IsUniversalHomeomorphism (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsUniversalHomeomorphism f]

/-- The homeomorphism of underlying spaces induced by a universal homeomorphism. -/
noncomputable def homeomorphOfIsUniversalHomeomorphism : X ≃ₜ Y :=
  (IsUniversalHomeomorphism.isHomeomorph f).homeomorph

/-- The homeomorphism induced by a universal homeomorphism `f` is the underlying map of `f`. -/
@[simp]
theorem coe_homeomorphOfIsUniversalHomeomorphism :
    ⇑(f.homeomorphOfIsUniversalHomeomorphism) = f :=
  (rfl)

/-- The inverse homeomorphism sends `f x` back to `x`. -/
@[simp]
theorem homeomorphOfIsUniversalHomeomorphism_symm_apply_apply (x : X) :
    (f.homeomorphOfIsUniversalHomeomorphism).symm (f x) = x :=
  (f.homeomorphOfIsUniversalHomeomorphism).symm_apply_apply x

/-- `f` sends the image of `y` under the inverse homeomorphism back to `y`. -/
@[simp]
theorem apply_homeomorphOfIsUniversalHomeomorphism_symm_apply (y : Y) :
    f ((f.homeomorphOfIsUniversalHomeomorphism).symm y) = y :=
  (f.homeomorphOfIsUniversalHomeomorphism).apply_symm_apply y

end AlgebraicGeometry.Scheme.Hom
