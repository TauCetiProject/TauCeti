/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.UniversalProperty.Pair

/-!
# Geometric base change of rational-localisation Huber pairs

This file provides geometric base change between rational-localisation Huber pairs: a morphism
`f : (A, A⁺) → (B, B⁺)` whose induced map on `Spa` carries `U = R(T'/s') ⊆ Spa(B, B⁺)` into
`W = R(T/s) ⊆ Spa(A, A⁺)` induces a unique compatible morphism of rational-localisation Huber pairs
`(A⟨T/s⟩, A_W⁺) → (B⟨T'/s'⟩, B_U⁺)`, which is adic whenever `f` is adic.

See `TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.UniversalProperty.Pair` for the
underlying bundled universal property into any complete separated target Huber pair.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.pairHomOfSpaComapImageSubset`: unique compatible morphism of
  rational-localisation Huber pairs `(A⟨T/s⟩, A_W⁺) → (B⟨T'/s'⟩, B_U⁺)` when `Spa(f)(U) ⊆ W`.

## Main results

* `TauCeti.Huber.PairOfDefinition.pairHomOfSpaComapImageSubset_comp_toCompletionLocHom`,
  `TauCeti.Huber.PairOfDefinition.toRingHom_pairHomOfSpaComapImageSubset_comp_toCompletionLoc`:
  compatibility with the structure morphisms.
* `TauCeti.Huber.PairOfDefinition.eq_pairHomOfSpaComapImageSubset`: uniqueness of the localised
  Huber-pair morphism.
* `TauCeti.Huber.PairOfDefinition.isAdicHom_pairHomOfSpaComapImageSubset`: adicness is preserved
  under passage to rational localisations.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  §1, Lemma 1.5.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1, Lemma 8.1 and
  Proposition 8.2.
-/

public section

open UniformSpace

namespace TauCeti.Huber.PairOfDefinition

open ValuationSpectrum

local macro "withLocHuber " P:term:max T:term:max s:term:max S:term:max hden:term:max
    " in " t:term : term =>
  `(letI := locUniformSpace $P $T $s $S $hden
    letI := isUniformAddGroup_locUniformSpace $P $T $s $S $hden
    letI := isTopologicalRing_locUniformSpace $P $T $s $S $hden
    letI := isHuberRing_completion_locTopology $P $T $s $S $hden
    $t)

section LocalizedPairMap

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
  (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower PA T s S)
  (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
  (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
  (hden' : HasDenominatorPower PB T' s' S')
  (f : Pair.Hom UA UB)
  (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus T' s') ⊆
    Subtype.val ⁻¹' rationalSubset UA.plus T s)

include f hf in
/-- **Geometric base change between rational-localisation Huber pairs.** Given
`f : (A, A⁺) → (B, B⁺)` such that `Spa(f)` carries `U = R(T'/s') ⊆ Spa(B, B⁺)` into
`W = R(T/s) ⊆ Spa(A, A⁺)`, the unique compatible morphism of rational-localisation Huber pairs
`(A⟨T/s⟩, A_W⁺) → (B⟨T'/s'⟩, B_U⁺)`. -/
noncomputable def pairHomOfSpaComapImageSubset :
    withLocHuber PA T s S hden in withLocHuber PB T' s' S' hden' in
    Pair.Hom (rationalLocalizationPair PA UA hPA T s S hden)
      (rationalLocalizationPair PB UB hPB T' s' S' hden') :=
  withLocHuber PA T s S hden in withLocHuber PB T' s' S' hden' in by
    refine pairHomOfForallSpaComapMemRationalSubset PA UA hPA T s S hden
      ((toCompletionLocHom PB UB hPB T' s' S' hden').comp f) fun w ↦ ?_
    rw [Pair.Hom.spaComap_comp, Function.comp_apply]
    apply hf
    refine ⟨(toCompletionLocHom PB UB hPB T' s' S' hden').spaComap w, ?_, rfl⟩
    have hw : w.val ∈ spa (completedPlusSubring PB UB.plus T' s' S' hden') := by
      simpa only [rationalLocalizationPair_plus] using w.property
    simpa only [Set.mem_preimage, Pair.Hom.spaComap_val, toRingHom_toCompletionLocHom,
      ← spaComapLoc_val PB UB.plus T' s' S' hden' ⟨w.val, hw⟩] using
      spaComapLoc_mem_rationalSubset PB UB.plus T' s' S' hden' ⟨w.val, hw⟩

/-- `pairHomOfSpaComapImageSubset` commutes with the structure morphisms from `(A, A⁺)` and
`(B, B⁺)`. -/
@[simp] theorem pairHomOfSpaComapImageSubset_comp_toCompletionLocHom :
    withLocHuber PA T s S hden in withLocHuber PB T' s' S' hden' in
    (pairHomOfSpaComapImageSubset PA UA hPA T s S hden PB UB hPB T' s' S' hden' f hf).comp
        (toCompletionLocHom PA UA hPA T s S hden) =
      (toCompletionLocHom PB UB hPB T' s' S' hden').comp f :=
  withLocHuber PA T s S hden in withLocHuber PB T' s' S' hden' in
    pairHomOfForallSpaComapMemRationalSubset_comp_toCompletionLocHom PA UA hPA T s S hden _ _

/-- Ring-homomorphism compatibility of `pairHomOfSpaComapImageSubset` with `toCompletionLoc`. -/
@[simp] theorem toRingHom_pairHomOfSpaComapImageSubset_comp_toCompletionLoc :
    withLocHuber PA T s S hden in withLocHuber PB T' s' S' hden' in
    (pairHomOfSpaComapImageSubset PA UA hPA T s S hden PB UB hPB T' s' S' hden' f hf).toRingHom.comp
        (toCompletionLoc PA T s S hden) =
      (toCompletionLoc PB T' s' S' hden').comp f.toRingHom :=
  withLocHuber PA T s S hden in withLocHuber PB T' s' S' hden' in by
    simpa only [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom] using
      congrArg Pair.Hom.toRingHom
        (pairHomOfSpaComapImageSubset_comp_toCompletionLocHom PA UA hPA T s S hden PB UB hPB
          T' s' S' hden' f hf)

/-- Uniqueness of `pairHomOfSpaComapImageSubset`: any morphism of Huber pairs out of
`rationalLocalizationPair PA UA hPA T s S hden` commuting with `toCompletionLocHom` equals
`pairHomOfSpaComapImageSubset`. -/
theorem eq_pairHomOfSpaComapImageSubset :
    withLocHuber PA T s S hden in withLocHuber PB T' s' S' hden' in
    ∀ k : Pair.Hom (rationalLocalizationPair PA UA hPA T s S hden)
        (rationalLocalizationPair PB UB hPB T' s' S' hden'),
      k.comp (toCompletionLocHom PA UA hPA T s S hden) =
        (toCompletionLocHom PB UB hPB T' s' S' hden').comp f →
      k = pairHomOfSpaComapImageSubset PA UA hPA T s S hden PB UB hPB T' s' S' hden' f hf :=
  withLocHuber PA T s S hden in withLocHuber PB T' s' S' hden' in by
    intro k hk
    refine Pair.Hom.ext (completion_locTopology_ringHom_ext_of_continuous PA T s S hden _ _
      k.continuous_toRingHom (pairHomOfSpaComapImageSubset PA UA hPA T s S hden PB UB hPB T' s' S'
        hden' f hf).continuous_toRingHom ?_)
    have hk' : k.toRingHom.comp (toCompletionLoc PA T s S hden) =
        (toCompletionLoc PB T' s' S' hden').comp f.toRingHom := by
      simpa only [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom] using
        congrArg Pair.Hom.toRingHom hk
    exact hk'.trans
      (toRingHom_pairHomOfSpaComapImageSubset_comp_toCompletionLoc PA UA hPA T s S hden PB UB hPB
        T' s' S' hden' f hf).symm

/-- When `f` is adic, the localised Huber-pair morphism `pairHomOfSpaComapImageSubset` is adic. -/
theorem isAdicHom_pairHomOfSpaComapImageSubset [IsAdicHom f.toRingHom] :
    withLocHuber PA T s S hden in withLocHuber PB T' s' S' hden' in
    IsAdicHom
      (pairHomOfSpaComapImageSubset PA UA hPA T s S hden PB UB hPB T' s' S' hden'
        f hf).toRingHom :=
  withLocHuber PA T s S hden in withLocHuber PB T' s' S' hden' in by
    have _ : IsAdicHom ((toCompletionLocHom PB UB hPB T' s' S' hden').comp f).toRingHom := by
      rw [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom]
      exact IsAdicHom.comp (isAdicHom_toCompletionLoc PB T' s' S' hden')
        (inferInstanceAs (IsAdicHom f.toRingHom))
    exact isAdicHom_pairHomOfForallSpaComapMemRationalSubset PA UA hPA T s S hden _ _

end LocalizedPairMap

end TauCeti.Huber.PairOfDefinition
