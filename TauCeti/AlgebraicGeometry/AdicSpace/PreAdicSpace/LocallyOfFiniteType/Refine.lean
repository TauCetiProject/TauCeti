/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyOfFiniteType.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.FiniteType
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp

/-!
# Refining finite-type charts by opens of the source

A morphism `f : X ⟶ Y` of pre-adic spaces is locally of finite type
(`TauCeti.PreAdicSpace.LocallyOfFiniteType`, Wedhorn, Definition 8.48) when it is, near every
point of `X`, the morphism of adic spectra induced by a morphism of Huber pairs topologically of
finite type. This file shows that such a chart may be shrunk on the source side: the restriction of
a chart morphism to any open of its source is again locally of finite type.

Let `φ : (A, A⁺) → (B, B⁺)` be topologically of finite type, with `A` a Tate ring and
`Spa(B, B⁺)` sheafy. For a rational subset `R(T/s)` of `Spa(B, B⁺)`, Wedhorn's Remark 8.8
(`TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComap_toCompletionLoc`) identifies the
inclusion of `R(T/s)` with the morphism `Spa(B⟨T/s⟩, B_V⁺) ⟶ Spa(B, B⁺)` induced by the
structure map `ψ : (B, B⁺) → (B⟨T/s⟩, B_V⁺)` of the rational localisation. So the restriction of
`Spa(φ)` to `R(T/s)` is, up to isomorphism, the morphism induced by `ψ ∘ φ`. Rational localisation
is topologically of finite type
(`TauCeti.Huber.PairOfDefinition.isTopologicallyFiniteType_toCompletionLocHom`), and over a Tate
base so is the composite (`TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType.comp`, Wedhorn,
Proposition 8.46). Rational subsets form a basis of `Spa(B, B⁺)`, and being locally of finite type
on an open can be checked on smaller opens around each of its points
(`TauCeti.PreAdicSpace.LocallyOfFiniteType.ofRestrict_comp_of_forall_exists_le`), which gives the
same for every open of the source.

The Tate hypothesis enters only through the composition of morphisms topologically of finite type.
The chart rings `B⟨T/s⟩` are completions, so `B` itself need not be complete.

## Main results

* `locallyOfFiniteType_ofRestrict_comp_presentationLimitPreAdicSpaceComap`, in the namespace
  `TauCeti.ValuationSpectrum`: over a Tate ring `A`, the morphism induced by a morphism of Huber
  pairs topologically of finite type restricts to a morphism locally of finite type on every open
  of `Spa(B, B⁺)`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Example 6.38, Remark 8.8, Definitions 8.42 and
  8.48, and Proposition 8.46.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber Huber.PairOfDefinition

universe u

namespace ValuationSpectrum

open PreAdicSpace

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {U : Pair A} {U' : Pair B} (P : PairOfDefinition A) (P' : PairOfDefinition B)
  (hP : P.ringOfDefinition ≤ U.plus) (hP' : P'.ringOfDefinition ≤ U'.plus) (φ : Pair.Hom U U')
  (hφ : φ.IsTopologicallyFiniteType)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U'.plus))
    (presentationLimitPresheaf P' U'.plus))

-- The restriction of `Spa(φ)` along the open embedding `j : Spa(B⟨T/s⟩, B_V⁺) → Spa(B, B⁺)` is
-- locally of finite type once the morphism induced by `χ = ψ ∘ φ` is, where
-- `ψ : B → B⟨T/s⟩` is the structure map. The pair `V` and the morphism `χ` are left variable,
-- constrained only by their plus ring and underlying ring homomorphism, because the rational
-- localisation pair and the composite of morphisms of pairs are available only through their
-- unfolding lemmas `rationalLocalizationPair_plus` and `Pair.Hom.toRingHom_comp`.
private theorem locallyOfFiniteType_ofRestrict_comp_of_toRingHom_eq {T : Finset B} {s : B}
    (hT : IsOpen (Ideal.span (T : Set B) : Set B)) (L : Type u) [CommRing L] [Algebra B L]
    [IsLocalization.Away s L] (hden : P'.HasDenominatorPower T s L) :
    letI := P'.locUniformSpace T s L hden
    letI := P'.isUniformAddGroup_locUniformSpace T s L hden
    letI := P'.isTopologicalRing_locUniformSpace T s L hden
    letI := P'.isHuberRing_completion_locTopology T s L hden
    ∀ (V : Pair (UniformSpace.Completion L))
      (_ : V.plus = P'.completedPlusSubring U'.plus T s L hden) (χ : Pair.Hom U V)
      (_ : χ.toRingHom = (P'.toCompletionLoc T s L hden).comp φ.toRingHom) (hopen)
      (hPV : (P'.completionLocalization T s L hden).ringOfDefinition ≤ V.plus) (hsheafV),
      LocallyOfFiniteType (presentationLimitPreAdicSpaceComap χ.toRingHom χ.continuous_toRingHom
        hopen χ.map_mem_plus U.isRingOfIntegralElements.isPowerBounded_of_mem
        V.isRingOfIntegralElements.isPowerBounded_of_mem hP hPV hsheafV) →
      LocallyOfFiniteType
        ((presentationLimitPreAdicSpace P' U'.plus U'.isRingOfIntegralElements.isPowerBounded_of_mem
            hP').ofRestrict (isOpenEmbedding_spaComapLocHom P' U'.plus hP' T s L hden) ≫
          presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
            (fun _ hJ ↦ hφ.isTopologicallyFiniteType_toRingHom.isOpen_map hJ) φ.map_mem_plus
            U.isRingOfIntegralElements.isPowerBounded_of_mem
            U'.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf) := by
  let _ := P'.locUniformSpace T s L hden
  have _ := P'.isUniformAddGroup_locUniformSpace T s L hden
  have _ := P'.isTopologicalRing_locUniformSpace T s L hden
  rintro ⟨_, _⟩ rfl ⟨_, _, _⟩ rfl _ _ _ key
  have hU' := U'.isRingOfIntegralElements.isPowerBounded_of_mem
  have hsheafL := isSheaf_presentationLimitPresheaf_completionLocalization P' U'.plus hU' hP' T s
    L hden hT hsheaf
  -- `Spa(ψ ∘ φ)` is `Spa(ψ) ≫ Spa(φ)`, and `Spa(ψ)` is the inclusion along `j` up to the
  -- isomorphism `e` of Wedhorn's Remark 8.8. The source of `j` is `Spa(B⟨T/s⟩, B_V⁺)` only up to
  -- unfolding, so the equalities are composed as terms rather than rewritten in the goal.
  have heq := (presentationLimitPreAdicSpaceComap_comp φ.toRingHom φ.continuous_toRingHom
      (fun _ hJ ↦ hφ.isTopologicallyFiniteType_toRingHom.isOpen_map hJ) φ.map_mem_plus
      (P'.toCompletionLoc T s L hden) (P'.continuous_toCompletionLoc T s L hden)
      (fun _ hJ ↦ P'.isOpen_map_toCompletionLoc T s L hden hJ)
      (fun _ ha ↦ P'.toCompletionLoc_mem_completedPlusSubring U'.plus T s L hden ha)
      U.isRingOfIntegralElements.isPowerBounded_of_mem hU'
      (P'.isPowerBounded_of_mem_completedPlusSubring U'.plus hU' T s L hden) hP hP'
      (P'.completionLocalization_ringOfDefinition_le_completedPlusSubring U'.plus hP' T s L hden)
      hsheaf hsheafL).trans ((congrArg (· ≫ _)
        (presentationLimitPreAdicSpaceComap_toCompletionLoc P' U'.plus T s L hden hU' hP' hT
          hsheafL)).trans (Category.assoc _ _ _))
  exact (MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType.{u} _ _).mp
    (cast (congrArg LocallyOfFiniteType heq) key)

/-- **A finite-type morphism over a Tate ring restricts to every open of its source**: let
`φ : (A, A⁺) → (B, B⁺)` be topologically of finite type, with `A` a Tate ring and `Spa(B, B⁺)`
sheafy. For every open `W` of `Spa(B, B⁺)`, the restriction `W → Spa(A, A⁺)` of
`Spa(φ) : Spa(B, B⁺) ⟶ Spa(A, A⁺)` is locally of finite type. -/
theorem locallyOfFiniteType_ofRestrict_comp_presentationLimitPreAdicSpaceComap
    (W : Opens (presentationLimitPreAdicSpace P' U'.plus
      U'.isRingOfIntegralElements.isPowerBounded_of_mem hP')) :
    LocallyOfFiniteType
      ((presentationLimitPreAdicSpace P' U'.plus U'.isRingOfIntegralElements.isPowerBounded_of_mem
          hP').ofRestrict W.isOpenEmbedding ≫
        presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
          (fun _ hJ ↦ hφ.isTopologicallyFiniteType_toRingHom.isOpen_map hJ) φ.map_mem_plus
          U.isRingOfIntegralElements.isPowerBounded_of_mem
          U'.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf) := by
  have hU' := U'.isRingOfIntegralElements.isPowerBounded_of_mem
  -- every point of `W` lies in a rational subset `R(T/s)` contained in `W`
  refine LocallyOfFiniteType.ofRestrict_comp_of_forall_exists_le W fun y ↦ ?_
  obtain ⟨R, hR, hyR, hRW⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens U'.plus) y.2
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hR
  refine ⟨spaBasicOpen U'.plus T s, hyR, hRW, ?_⟩
  have hden := P'.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
  let _ := P'.locUniformSpace T s _ hden
  have _ := P'.isUniformAddGroup_locUniformSpace T s _ hden
  have _ := P'.isTopologicalRing_locUniformSpace T s _ hden
  have _ := P'.isHuberRing_completion_locTopology T s _ hden
  -- `R(T/s)` is the range of `j : Spa(B⟨T/s⟩, B_V⁺) → Spa(B, B⁺)`
  have hrange : Set.range (Opens.inclusion' (spaBasicOpen U'.plus T s)) =
      Set.range (spaComapLocHom P' U'.plus T s _ hden) := by
    rw [Opens.set_range_inclusion', coe_spaComapLocHom, range_spaComapLoc P' U'.plus hP' T s _ hden]
  refine LocallyOfFiniteType.ofRestrict_comp_of_range_eq _
    (isOpenEmbedding_spaComapLocHom P' U'.plus hP' T s _ hden) hrange ?_
  -- the rational localisation `ψ : (B, B⁺) → (B⟨T/s⟩, B_V⁺)` is topologically of finite type,
  -- hence so is `ψ ∘ φ` over the Tate ring `A`, and `Spa(B⟨T/s⟩, B_V⁺)` is sheafy
  have hψ := P'.isTopologicallyFiniteType_toCompletionLocHom U' hP' T s _ hden
    (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert s _)) hT)
  have hPV : (P'.completionLocalization T s _ hden).ringOfDefinition ≤
      (P'.rationalLocalizationPair U' hP' T s _ hden).plus := by
    rw [rationalLocalizationPair_plus]
    exact P'.completionLocalization_ringOfDefinition_le_completedPlusSubring U'.plus hP' T s _ hden
  have hsheafV : Presheaf.IsSheaf
      (Opens.grothendieckTopology ↥(spa (P'.rationalLocalizationPair U' hP' T s _ hden).plus))
      (presentationLimitPresheaf (P'.completionLocalization T s _ hden)
        (P'.rationalLocalizationPair U' hP' T s _ hden).plus) := by
    rw [rationalLocalizationPair_plus]
    exact isSheaf_presentationLimitPresheaf_completionLocalization P' U'.plus hU' hP' T s _ hden hT
      hsheaf
  exact locallyOfFiniteType_ofRestrict_comp_of_toRingHom_eq P P' hP hP' φ hφ hsheaf hT _ hden _
    (rationalLocalizationPair_plus ..) _
    (by rw [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom]) _ hPV hsheafV
    (locallyOfFiniteType_presentationLimitPreAdicSpaceComap P _ hP hPV hsheafV _ (hψ.comp hφ))

end ValuationSpectrum

end TauCeti
