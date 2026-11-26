/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.UniversalProperty.Basic
public import TauCeti.RingTheory.Huber.AdicHom.Localization
public import TauCeti.RingTheory.Huber.LocalizationTopology.Pair
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Integral

/-!
# The geometric universal property for morphisms of Huber pairs

This file provides Wedhorn's geometric universal property for morphisms of Huber pairs into any
complete separated target Huber pair `(B, B⁺)`: a morphism `f : (A, A⁺) → (B, B⁺)` whose induced
map on `Spa` lands in `R(T/s) ⊆ Spa(A, A⁺)` extends uniquely across the structure morphism
`toCompletionLocHom : (A, A⁺) → (A⟨T/s⟩, A_U⁺)`, and the extension is adic whenever `f` is adic.

See `TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.UniversalProperty.Basic` for the
ring-level geometric universal property, and
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.BaseChange` for the induced map between two
rational localisations.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.pairHomOfForallSpaComapMemRationalSubset`: unique extension of
  `f : (A, A⁺) → (B, B⁺)` across `toCompletionLocHom` when `B` is complete and separated and
  `Spa(f)` lands in `R(T/s)`.

## Main results

* `TauCeti.Huber.PairOfDefinition.existsUnique_pairHom_of_forall_spaComap_mem_rationalSubset`:
  existence and uniqueness of the extended Huber-pair morphism.
* `TauCeti.Huber.PairOfDefinition.pairHomOfForallSpaComapMemRationalSubset_comp_toCompletionLocHom`,
  `toRingHom_pairHomOfForallSpaComapMemRationalSubset_comp_toCompletionLoc`:
  compatibility with the structure morphism.
* `TauCeti.Huber.PairOfDefinition.isAdicHom_pairHomOfForallSpaComapMemRationalSubset`: adicness is
  preserved under extension.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  §1, Lemma 1.5.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1, Lemma 8.1.
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

end TauCeti.Huber.PairOfDefinition
