/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.RingTheory.Huber.LocalizationTopology.BaseChange

/-!
# Restricting induced morphisms over rational subsets

Let `φ : (A, A⁺) → (B, B⁺)` be a morphism of Huber pairs carrying open ideals to ideals generating
open ideals, with `Spa(B, B⁺)` sheafy, so that it induces a morphism of pre-adic spaces
`Spa(φ) : Spa(B, B⁺) ⟶ Spa(A, A⁺)`. For a rational subset `R(T/s)` of `Spa(A, A⁺)`, its preimage
under `Spa(φ)` is `R(φ(T)/φ(s))` (Wedhorn, Lemma 7.46(3)). By Wedhorn's Remark 8.8 the two
rational subsets are the adic spectra of `(A⟨T/s⟩, A_U⁺)` and `(B⟨φ(T)/φ(s)⟩, B_V⁺)`, and under
these identifications the restriction of `Spa(φ)` over `R(T/s)` is the morphism induced by the
base change `(A⟨T/s⟩, A_U⁺) → (B⟨φ(T)/φ(s)⟩, B_V⁺)` of `φ`
(`TauCeti.Huber.PairOfDefinition.completionLocPairMap`).

The precise statement is that the square of pre-adic spaces

```text
Spa(B⟨φ(T)/φ(s)⟩) ⟶ Spa(A⟨T/s⟩)
        ↓                  ↓
   Spa(B, B⁺)     ⟶   Spa(A, A⁺)
```

induced by the square of Huber pairs commutes, and its vertical sides are open immersions onto
`R(φ(T)/φ(s))` and `R(T/s)`. Every isomorphism-invariant property of morphisms therefore holds for
the restriction `Spa(φ)⁻¹(R(T/s)) → R(T/s)` exactly when it holds for the morphism induced by the
base change. This is how a property of morphisms stated through affinoid charts, such as being
locally of finite type, is carried to smaller charts of the target.

The vertical side over `A` is the morphism induced by `A → A⟨T/s⟩`, which needs the structure
presheaf of `Spa(A⟨T/s⟩, A_U⁺)` to be a sheaf; that is the one sheaf condition on the target side.

## Main results

* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComap_completionLocPairMap_comp`: the
  square above commutes.
* `TauCeti.ValuationSpectrum.prop_restrictPreimage_presentationLimitPreAdicSpaceComap_iff`: an
  isomorphism-invariant property holds for the restriction of `Spa(φ)` over `R(T/s)` exactly when
  it holds for the morphism induced by the base change of `φ`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition and Definition 5.51, Lemma 7.46,
  Remark 8.8 and §8.1.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti.ValuationSpectrum

open Huber Huber.PairOfDefinition PreAdicSpace

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {U : Pair A} {U' : Pair B} (P : PairOfDefinition A) (P' : PairOfDefinition B)
  (hP : P.ringOfDefinition ≤ U.plus) (hP' : P'.ringOfDefinition ≤ U'.plus) (φ : Pair.Hom U U')
  (hopen : ∀ ⦃J : Ideal A⦄, IsOpen (J : Set A) → IsOpen (J.map φ.toRingHom : Set B))
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U'.plus))
    (presentationLimitPresheaf P' U'.plus))
  (T : Finset A) (s : A) (L : Type u) [CommRing L] [Algebra A L] [IsLocalization.Away s L]
  (hden : P.HasDenominatorPower T s L)
  (L' : Type u) [CommRing L'] [Algebra B L'] [IsLocalization.Away (φ.toRingHom s) L']

open scoped Classical in
/-- **The square induced by a base change of rational localisations commutes**: the morphism
`Spa(B⟨φ(T)/φ(s)⟩, B_V⁺) ⟶ Spa(A⟨T/s⟩, A_U⁺)` induced by the base change of `φ`, followed by the
morphism induced by `A → A⟨T/s⟩`, is the morphism induced by `B → B⟨φ(T)/φ(s)⟩` followed by
`Spa(φ)`. -/
theorem presentationLimitPreAdicSpaceComap_completionLocPairMap_comp
    (hden' : P'.HasDenominatorPower (T.image φ.toRingHom) (φ.toRingHom s) L')
    (hsheafU : letI := P.locUniformSpace T s L hden
      letI := P.isUniformAddGroup_locUniformSpace T s L hden
      letI := P.isTopologicalRing_locUniformSpace T s L hden
      letI := P.isHuberRing_completion_locTopology T s L hden
      Presheaf.IsSheaf
        (Opens.grothendieckTopology ↥(spa (P.rationalLocalizationPair U hP T s L hden).plus))
        (presentationLimitPresheaf (P.completionLocalization T s L hden)
          (P.rationalLocalizationPair U hP T s L hden).plus))
    (hsheafU' : letI := P'.locUniformSpace (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
      letI := P'.isUniformAddGroup_locUniformSpace (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
      letI := P'.isTopologicalRing_locUniformSpace (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
      letI := P'.isHuberRing_completion_locTopology (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
      Presheaf.IsSheaf (Opens.grothendieckTopology
          ↥(spa (P'.rationalLocalizationPair U' hP' (T.image φ.toRingHom) (φ.toRingHom s) L'
            hden').plus))
        (presentationLimitPresheaf
          (P'.completionLocalization (T.image φ.toRingHom) (φ.toRingHom s) L' hden')
          (P'.rationalLocalizationPair U' hP' (T.image φ.toRingHom) (φ.toRingHom s) L'
            hden').plus)) :
    letI := P.locUniformSpace T s L hden
    letI := P.isUniformAddGroup_locUniformSpace T s L hden
    letI := P.isTopologicalRing_locUniformSpace T s L hden
    letI := P.isHuberRing_completion_locTopology T s L hden
    letI := P'.locUniformSpace (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
    letI := P'.isUniformAddGroup_locUniformSpace (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
    letI := P'.isTopologicalRing_locUniformSpace (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
    letI := P'.isHuberRing_completion_locTopology (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
    presentationLimitPreAdicSpaceComap
        (P := P.completionLocalization T s L hden)
        (P' := P'.completionLocalization (T.image φ.toRingHom) (φ.toRingHom s) L' hden')
        (P.completionLocPairMap U hP T s L hden P' U' hP' φ (T.image φ.toRingHom) (φ.toRingHom s)
          L' hden' rfl fun _ ht ↦ Finset.mem_image_of_mem _ ht).toRingHom
        (P.completionLocPairMap U hP T s L hden P' U' hP' φ (T.image φ.toRingHom) (φ.toRingHom s)
          L' hden' rfl fun _ ht ↦ Finset.mem_image_of_mem _ ht).continuous_toRingHom
        (fun _ hJ ↦ by
          rw [toRingHom_completionLocPairMap]
          exact P.isOpen_map_completionLocMap T s L hden P' φ.toRingHom
            φ.continuous_toRingHom.continuousAt _ _ L' hden' rfl _ hopen hJ)
        (P.completionLocPairMap U hP T s L hden P' U' hP' φ (T.image φ.toRingHom) (φ.toRingHom s)
          L' hden' rfl fun _ ht ↦ Finset.mem_image_of_mem _ ht).map_mem_plus
        (P.rationalLocalizationPair U hP T s L hden).isRingOfIntegralElements.isPowerBounded_of_mem
        (P'.rationalLocalizationPair U' hP' (T.image φ.toRingHom) (φ.toRingHom s) L'
          hden').isRingOfIntegralElements.isPowerBounded_of_mem
        (by rw [rationalLocalizationPair_plus]
            exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring U.plus hP T s
              L hden)
        (by rw [rationalLocalizationPair_plus]
            exact P'.completionLocalization_ringOfDefinition_le_completedPlusSubring U'.plus hP' _
              _ L' hden')
        hsheafU' ≫
      presentationLimitPreAdicSpaceComap (P' := P.completionLocalization T s L hden)
        (P.toCompletionLocHom U hP T s L hden).toRingHom
        (P.toCompletionLocHom U hP T s L hden).continuous_toRingHom
        (fun _ hJ ↦ by
          rw [toRingHom_toCompletionLocHom]
          exact P.isOpen_map_toCompletionLoc T s L hden hJ)
        (P.toCompletionLocHom U hP T s L hden).map_mem_plus
        U.isRingOfIntegralElements.isPowerBounded_of_mem
        (P.rationalLocalizationPair U hP T s L hden).isRingOfIntegralElements.isPowerBounded_of_mem
        hP
        (by rw [rationalLocalizationPair_plus]
            exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring U.plus hP T s
              L hden)
        hsheafU =
    presentationLimitPreAdicSpaceComap
        (P' := P'.completionLocalization (T.image φ.toRingHom) (φ.toRingHom s) L' hden')
        (P'.toCompletionLocHom U' hP' (T.image φ.toRingHom) (φ.toRingHom s) L' hden').toRingHom
        (P'.toCompletionLocHom U' hP' (T.image φ.toRingHom) (φ.toRingHom s) L'
          hden').continuous_toRingHom
        (fun _ hJ ↦ by
          rw [toRingHom_toCompletionLocHom]
          exact P'.isOpen_map_toCompletionLoc _ _ L' hden' hJ)
        (P'.toCompletionLocHom U' hP' (T.image φ.toRingHom) (φ.toRingHom s) L' hden').map_mem_plus
        U'.isRingOfIntegralElements.isPowerBounded_of_mem
        (P'.rationalLocalizationPair U' hP' (T.image φ.toRingHom) (φ.toRingHom s) L'
          hden').isRingOfIntegralElements.isPowerBounded_of_mem
        hP'
        (by rw [rationalLocalizationPair_plus]
            exact P'.completionLocalization_ringOfDefinition_le_completedPlusSubring U'.plus hP' _
              _ L' hden')
        hsheafU' ≫
      presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom hopen φ.map_mem_plus
        U.isRingOfIntegralElements.isPowerBounded_of_mem
        U'.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf := by
  let _ := P.locUniformSpace T s L hden
  have _ := P.isUniformAddGroup_locUniformSpace T s L hden
  have _ := P.isTopologicalRing_locUniformSpace T s L hden
  have _ := P.isHuberRing_completion_locTopology T s L hden
  let _ := P'.locUniformSpace (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
  have _ := P'.isUniformAddGroup_locUniformSpace (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
  have _ := P'.isTopologicalRing_locUniformSpace (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
  have _ := P'.isHuberRing_completion_locTopology (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
  rw [← presentationLimitPreAdicSpaceComap_comp, ← presentationLimitPreAdicSpaceComap_comp]
  congr 1
  rw [← Pair.Hom.toRingHom_comp, ← Pair.Hom.toRingHom_comp,
    completionLocPairMap_comp_toCompletionLocHom]

open scoped Classical in
/-- **Restricting an induced morphism over a rational subset is inducing the base change.** Let
`φ : (A, A⁺) → (B, B⁺)` induce `Spa(φ) : Spa(B, B⁺) ⟶ Spa(A, A⁺)`, let `T` span an open ideal of
`A`, and let the structure presheaf of `Spa(A⟨T/s⟩, A_U⁺)` be a sheaf. Then an
isomorphism-invariant property of morphisms of pre-adic spaces holds for the restriction
`Spa(φ)⁻¹(R(T/s)) → R(T/s)` exactly when it holds for the morphism
`Spa(B⟨φ(T)/φ(s)⟩, B_V⁺) ⟶ Spa(A⟨T/s⟩, A_U⁺)` induced by the base change of `φ`.

The structure presheaf of `Spa(B⟨φ(T)/φ(s)⟩, B_V⁺)` is a sheaf because that of `Spa(B, B⁺)` is
(`isSheaf_presentationLimitPresheaf_completionLocalization`). -/
theorem prop_restrictPreimage_presentationLimitPreAdicSpaceComap_iff
    (MP : MorphismProperty PreAdicSpace.{u}) [MP.RespectsIso]
    (hden' : P'.HasDenominatorPower (T.image φ.toRingHom) (φ.toRingHom s) L')
    (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (hsheafU : letI := P.locUniformSpace T s L hden
      letI := P.isUniformAddGroup_locUniformSpace T s L hden
      letI := P.isTopologicalRing_locUniformSpace T s L hden
      letI := P.isHuberRing_completion_locTopology T s L hden
      Presheaf.IsSheaf
        (Opens.grothendieckTopology ↥(spa (P.rationalLocalizationPair U hP T s L hden).plus))
        (presentationLimitPresheaf (P.completionLocalization T s L hden)
          (P.rationalLocalizationPair U hP T s L hden).plus)) :
    letI := P.locUniformSpace T s L hden
    letI := P.isUniformAddGroup_locUniformSpace T s L hden
    letI := P.isTopologicalRing_locUniformSpace T s L hden
    letI := P.isHuberRing_completion_locTopology T s L hden
    letI := P'.locUniformSpace (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
    letI := P'.isUniformAddGroup_locUniformSpace (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
    letI := P'.isTopologicalRing_locUniformSpace (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
    letI := P'.isHuberRing_completion_locTopology (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
    MP ((presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom hopen
        φ.map_mem_plus U.isRingOfIntegralElements.isPowerBounded_of_mem
        U'.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf).restrictPreimage
          (spaBasicOpen U.plus T s)) ↔
      MP (presentationLimitPreAdicSpaceComap
        (P := P.completionLocalization T s L hden)
        (P' := P'.completionLocalization (T.image φ.toRingHom) (φ.toRingHom s) L' hden')
        (P.completionLocPairMap U hP T s L hden P' U' hP' φ (T.image φ.toRingHom) (φ.toRingHom s)
          L' hden' rfl fun _ ht ↦ Finset.mem_image_of_mem _ ht).toRingHom
        (P.completionLocPairMap U hP T s L hden P' U' hP' φ (T.image φ.toRingHom) (φ.toRingHom s)
          L' hden' rfl fun _ ht ↦ Finset.mem_image_of_mem _ ht).continuous_toRingHom
        (fun _ hJ ↦ by
          rw [toRingHom_completionLocPairMap]
          exact P.isOpen_map_completionLocMap T s L hden P' φ.toRingHom
            φ.continuous_toRingHom.continuousAt _ _ L' hden' rfl _ hopen hJ)
        (P.completionLocPairMap U hP T s L hden P' U' hP' φ (T.image φ.toRingHom) (φ.toRingHom s)
          L' hden' rfl fun _ ht ↦ Finset.mem_image_of_mem _ ht).map_mem_plus
        (P.rationalLocalizationPair U hP T s L hden).isRingOfIntegralElements.isPowerBounded_of_mem
        (P'.rationalLocalizationPair U' hP' (T.image φ.toRingHom) (φ.toRingHom s) L'
          hden').isRingOfIntegralElements.isPowerBounded_of_mem
        (by rw [rationalLocalizationPair_plus]
            exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring U.plus hP T s
              L hden)
        (by rw [rationalLocalizationPair_plus]
            exact P'.completionLocalization_ringOfDefinition_le_completedPlusSubring U'.plus hP' _
              _ L' hden')
        (by rw [rationalLocalizationPair_plus]
            exact isSheaf_presentationLimitPresheaf_completionLocalization P' U'.plus
              U'.isRingOfIntegralElements.isPowerBounded_of_mem hP' _ _ L' hden'
              (by rw [Finset.coe_image, ← Ideal.map_span]; exact hopen hT) hsheaf)) := by
  let _ := P.locUniformSpace T s L hden
  have _ := P.isUniformAddGroup_locUniformSpace T s L hden
  have _ := P.isTopologicalRing_locUniformSpace T s L hden
  have _ := P.isHuberRing_completion_locTopology T s L hden
  let _ := P'.locUniformSpace (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
  have _ := P'.isUniformAddGroup_locUniformSpace (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
  have _ := P'.isTopologicalRing_locUniformSpace (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
  have _ := P'.isHuberRing_completion_locTopology (T.image φ.toRingHom) (φ.toRingHom s) L' hden'
  have hT' : IsOpen (Ideal.span ((T.image φ.toRingHom : Finset B) : Set B) : Set B) := by
    rw [Finset.coe_image, ← Ideal.map_span]
    exact hopen hT
  have hsheafU' : Presheaf.IsSheaf (Opens.grothendieckTopology
      ↥(spa (P'.rationalLocalizationPair U' hP' (T.image φ.toRingHom) (φ.toRingHom s) L'
        hden').plus))
      (presentationLimitPresheaf
        (P'.completionLocalization (T.image φ.toRingHom) (φ.toRingHom s) L' hden')
        (P'.rationalLocalizationPair U' hP' (T.image φ.toRingHom) (φ.toRingHom s) L'
          hden').plus) := by
    rw [rationalLocalizationPair_plus]
    exact isSheaf_presentationLimitPresheaf_completionLocalization P' U'.plus
      U'.isRingOfIntegralElements.isPowerBounded_of_mem hP' _ _ L' hden' hT' hsheaf
  -- the vertical sides of the square are open immersions onto `R(T/s)` and `R(φ(T)/φ(s))`
  have := isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom P hP T s L hden hT
    hsheafU
  have := isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom P' hP'
    (T.image φ.toRingHom) (φ.toRingHom s) L' hden' hT' hsheafU'
  refine (Hom.prop_restrictPreimage_iff_of_isOpenImmersion _ _ MP _ _ _
    (range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base P hP T s L hden hsheafU) ?_
    (presentationLimitPreAdicSpaceComap_completionLocPairMap_comp P P' hP hP' φ hopen hsheaf T s L
      hden L' hden' hsheafU hsheafU'))
  -- the preimage of `R(T/s)` under `Spa(φ)` is `R(φ(T)/φ(s))`
  rw [range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base P' hP'
    (T.image φ.toRingHom) (φ.toRingHom s) L' hden' hsheafU',
    presentationLimitPreAdicSpaceComap_toHom, presentationLimitPresheafedSpaceComap_base]
  exact congrArg SetLike.coe (map_spaComapTopHom_obj_spaBasicOpen φ.toRingHom
    φ.continuous_toRingHom φ.map_mem_plus T s).symm

end TauCeti.ValuationSpectrum
