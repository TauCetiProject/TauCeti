/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PlusComparison
public import TauCeti.RingTheory.Huber.AdicHom.Localization
public import TauCeti.RingTheory.Huber.LocalizationTopology.Pair

/-!
# Geometric base change of rational-localisation Huber pairs

This file provides Wedhorn's geometric universal property for morphisms of rational-localisation
Huber pairs: a morphism `f : (A, A⁺) → (B, B⁺)` whose induced map on `Spa` carries
`U = R(T'/s') ⊆ Spa(B, B⁺)` into `W = R(T/s) ⊆ Spa(A, A⁺)` induces a unique compatible morphism
of rational-localisation Huber pairs `(A⟨T/s⟩, A_W⁺) → (B⟨T'/s'⟩, B_U⁺)`, which is adic whenever
`f` is adic.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.pairHomOfForallSpaComapMemRationalSubset`: unique extension of
  `f : (A, A⁺) → (B, B⁺)` across `toCompletionLocHom` when `B` is complete and separated and
  `Spa(f)` lands in `R(T/s)`.
* `TauCeti.Huber.PairOfDefinition.pairHomOfSpaComapImageSubset`: unique compatible morphism of
  rational-localisation Huber pairs `(A⟨T/s⟩, A_W⁺) → (B⟨T'/s'⟩, B_U⁺)` when `Spa(f)(U) ⊆ W`.

## Main results

* `TauCeti.Huber.PairOfDefinition.existsUnique_pairHom_of_forall_spaComap_mem_rationalSubset`,
  `TauCeti.Huber.PairOfDefinition.eq_pairHomOfSpaComapImageSubset`: existence and uniqueness of
  localised Huber-pair morphisms.
* `TauCeti.Huber.PairOfDefinition.isAdicHom_pairHomOfForallSpaComapMemRationalSubset`,
  `TauCeti.Huber.PairOfDefinition.isAdicHom_pairHomOfSpaComapImageSubset`: adicness is preserved
  under passage to rational localisations.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  §1, Lemma 1.5.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1, Lemma 8.1 and
  Proposition 8.2.
-/

public section

open UniformSpace

open TauCeti.Huber.PairOfDefinition in
local macro "withLocHuber " P:term:max T:term:max s:term:max S:term:max hden:term:max
    " in " t:term : term =>
  `(letI := locUniformSpace $P $T $s $S $hden
    letI := isUniformAddGroup_locUniformSpace $P $T $s $S $hden
    letI := isTopologicalRing_locUniformSpace $P $T $s $S $hden
    letI := isHuberRing_completion_locTopology $P $T $s $S $hden
    $t)

namespace TauCeti.Huber.PairOfDefinition

open ValuationSpectrum

section GeometricUniversalProperty

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [IsHuberRing B] [CompleteSpace B] [T0Space B]
  (P : PairOfDefinition A) (UA : Pair A) (hP : P.ringOfDefinition ≤ UA.plus)
  (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S) {UB : Pair B} (f : Pair.Hom UA UB)
  (hf : ∀ w : spa UB.plus, f.spaComap w ∈ Subtype.val ⁻¹' rationalSubset UA.plus T s)

include hf in
/-- **Wedhorn's Lemma 8.1 for morphisms of Huber pairs.** A morphism `f : (A, A⁺) → (B, B⁺)` into a
complete separated Huber pair whose induced map on `Spa` lands in `R(T/s)` extends uniquely across
the structure morphism `toCompletionLocHom : (A, A⁺) → (A⟨T/s⟩, A_U⁺)`. -/
theorem existsUnique_pairHom_of_forall_spaComap_mem_rationalSubset :
    withLocHuber P T s S hden in
    ∃! g : Pair.Hom (rationalLocalizationPair P UA hP T s S hden) UB,
      g.comp (toCompletionLocHom P UA hP T s S hden) = f :=
  withLocHuber P T s S hden in by
    have hfac : ∀ w ∈ spa UB.plus, ValuationSpectrum.comap f.toRingHom w ∈
        rationalSubset UA.plus T s := fun w hw ↦ by
      simpa only [Set.mem_preimage, Pair.Hom.spaComap_val] using hf ⟨w, hw⟩
    obtain ⟨g₀, ⟨hg₀c, hg₀⟩, hg₀_uniq⟩ :=
      existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset P UA.plus T s S hden
        UB.plus UB.isRingOfIntegralElements f.continuous_toRingHom.continuousAt hfac
    have hg₀_plus : ∀ x ∈ (rationalLocalizationPair P UA hP T s S hden).plus, g₀ x ∈ UB.plus := by
      rw [rationalLocalizationPair_plus]
      intro x hx
      refine UB.isRingOfIntegralElements.mem_of_forall_vle_one fun w hw ↦ ?_
      have hmem := comap_mem_spa_completedPlusSubring P UA.plus T s S hden g₀ hg₀c
        ((mem_spa_iff _ _).mp hw).1 (hg₀.symm ▸ hfac w hw)
      simpa only [comap_vle, map_one] using ((mem_spa_iff _ _).mp hmem).2 x hx
    refine ⟨⟨g₀, hg₀c, hg₀_plus⟩, Pair.Hom.ext ?_, fun k hk ↦ Pair.Hom.ext ?_⟩
    · simpa only [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom] using hg₀
    · refine hg₀_uniq k.toRingHom ⟨k.continuous_toRingHom, ?_⟩
      simpa only [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom] using
        congrArg Pair.Hom.toRingHom hk

include f hf in
/-- **The Huber-pair morphism induced by a factorisation on `Spa`** (Wedhorn, Lemma 8.1): given
`f : (A, A⁺) → (B, B⁺)` into a complete separated Huber pair with `Spa(f)(Spa(B, B⁺)) ⊆ R(T/s)`,
the unique extension `(A⟨T/s⟩, A_U⁺) → (B, B⁺)`. -/
noncomputable def pairHomOfForallSpaComapMemRationalSubset :
    withLocHuber P T s S hden in
    Pair.Hom (rationalLocalizationPair P UA hP T s S hden) UB :=
  (existsUnique_pairHom_of_forall_spaComap_mem_rationalSubset P UA hP T s S hden f hf).choose

/-- `pairHomOfForallSpaComapMemRationalSubset` extends `f` across `toCompletionLocHom`. -/
@[simp] theorem pairHomOfForallSpaComapMemRationalSubset_comp_toCompletionLocHom :
    withLocHuber P T s S hden in
    (pairHomOfForallSpaComapMemRationalSubset P UA hP T s S hden f hf).comp
        (toCompletionLocHom P UA hP T s S hden) = f :=
  (existsUnique_pairHom_of_forall_spaComap_mem_rationalSubset P UA hP T s S hden
    f hf).choose_spec.1

/-- Ring-homomorphism compatibility of `pairHomOfForallSpaComapMemRationalSubset` with
`toCompletionLoc`. -/
@[simp] theorem toRingHom_pairHomOfForallSpaComapMemRationalSubset_comp_toCompletionLoc :
    withLocHuber P T s S hden in
    (pairHomOfForallSpaComapMemRationalSubset P UA hP T s S hden f hf).toRingHom.comp
        (toCompletionLoc P T s S hden) = f.toRingHom :=
  withLocHuber P T s S hden in by
    simpa only [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom] using
      congrArg Pair.Hom.toRingHom
        (pairHomOfForallSpaComapMemRationalSubset_comp_toCompletionLocHom P UA hP T s S hden f hf)

/-- If `f` is adic, its extension `pairHomOfForallSpaComapMemRationalSubset` is also adic. -/
theorem isAdicHom_pairHomOfForallSpaComapMemRationalSubset [IsAdicHom f.toRingHom] :
    withLocHuber P T s S hden in
    IsAdicHom (pairHomOfForallSpaComapMemRationalSubset P UA hP T s S hden f hf).toRingHom :=
  withLocHuber P T s S hden in
    isAdicHom_of_comp_toCompletionLoc P T s S hden
      (pairHomOfForallSpaComapMemRationalSubset P UA hP T s S hden f hf).continuous_toRingHom
      ((toRingHom_pairHomOfForallSpaComapMemRationalSubset_comp_toCompletionLoc P UA hP T s S hden
        f hf).symm ▸ inferInstanceAs (IsAdicHom f.toRingHom))

end GeometricUniversalProperty

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
    have hw : w.1 ∈ spa (completedPlusSubring PB UB.plus T' s' S' hden') := by
      simpa only [rationalLocalizationPair_plus] using w.2
    simpa only [Set.mem_preimage, Pair.Hom.spaComap_val, toRingHom_toCompletionLocHom,
      ← spaComapLoc_val PB UB.plus T' s' S' hden' ⟨w.1, hw⟩] using
      spaComapLoc_mem_rationalSubset PB UB.plus T' s' S' hden' ⟨w.1, hw⟩

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
