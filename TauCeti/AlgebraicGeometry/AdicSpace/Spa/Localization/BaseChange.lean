/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedRationalSubset
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.PlusComparison
public import TauCeti.RingTheory.Huber.AdicHom.Localization
public import TauCeti.RingTheory.Huber.LocalizationTopology.Pair

/-!
# Geometric base change of rational-localisation Huber pairs

This file provides three Huber-pair and adic-spectrum comparisons used when pulling back and
gluing completed rational localisations:

1. **Homeomorphism of adic spectra along a topological ring equivalence**
   (`spaHomeomorphOfRingEquiv` and `bijOn_preimage_spaHomeomorphOfRingEquiv_spaRationalFamily`): a
   topological ring isomorphism `e : A ≃+* B` carrying `A⁺` onto `B⁺` induces a homeomorphism
   `Spa(A, A⁺) ≃ₜ Spa(B, B⁺)` pulling valuations back along `e.symm`, whose preimage map bijects
   `spaRationalFamily B⁺` onto `spaRationalFamily A⁺`.
2. **Presentation independence of `completedPlusSubring`**
   (`map_completedPlusSubring_presentationRingEquivOfEq`): for two presentations of the same
   rational subset of `Spa(A, A⁺)`, `presentationRingEquivOfEq` maps the completed plus subring of
   the first onto that of the second.
3. **Wedhorn's geometric universal property for morphisms of Huber pairs**
   (`existsUnique_pairHom_of_forall_spaComap_mem_rationalSubset`,
   `pairHomOfForallSpaComapMemRationalSubset`, and `pairHomOfSpaComapImageSubset`): a morphism
   `f : (A, A⁺) → (B, B⁺)` whose induced map on `Spa` carries `U = R(T'/s') ⊆ Spa(B, B⁺)` into
   `W = R(T/s) ⊆ Spa(A, A⁺)` induces a unique compatible morphism of rational-localisation Huber
   pairs `(A⟨T/s⟩, A_W⁺) → (B⟨T'/s'⟩, B_U⁺)`, which is adic whenever `f` is adic.

## Main definitions

* `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv`: homeomorphism `Spa(A, A⁺) ≃ₜ Spa(B, B⁺)`
  induced by a topological ring equivalence `e : A ≃+* B` with `A⁺.map e = B⁺`.
* `TauCeti.Huber.PairOfDefinition.pairHomOfForallSpaComapMemRationalSubset`: unique extension of
  `f : (A, A⁺) → (B, B⁺)` across `toCompletionLocHom` when `B` is complete and separated and
  `Spa(f)` lands in `R(T/s)`.
* `TauCeti.Huber.PairOfDefinition.pairHomOfSpaComapImageSubset`: unique compatible morphism of
  rational-localisation Huber pairs `(A⟨T/s⟩, A_W⁺) → (B⟨T'/s'⟩, B_U⁺)` when `Spa(f)(U) ⊆ W`.

## Main results

* `TauCeti.ValuationSpectrum.bijOn_preimage_spaHomeomorphOfRingEquiv_spaRationalFamily`: preimage
  along `spaHomeomorphOfRingEquiv` bijects `spaRationalFamily B⁺` onto `spaRationalFamily A⁺`.
* `TauCeti.ValuationSpectrum.map_completedPlusSubring_presentationRingEquivOfEq`:
  `presentationRingEquivOfEq` preserves `completedPlusSubring`.
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

namespace TauCeti.ValuationSpectrum

section RingEquiv

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
  {Aplus : Subring A} {Bplus : Subring B}

/-- **Homeomorphism of adic spectra induced by a topological ring equivalence.** Given a ring
isomorphism `e : A ≃+* B` continuous in both directions with `A⁺.map e = B⁺`, pulling valuations
back along `e.symm` identifies `Spa(A, A⁺)` homeomorphically with `Spa(B, B⁺)`. -/
noncomputable def spaHomeomorphOfRingEquiv (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (hplus : Aplus.map (e : A →+* B) = Bplus) :
    spa Aplus ≃ₜ spa Bplus where
  toFun := spaComap (e.symm : B →+* A) he' Bplus Aplus fun b hb ↦ by
    obtain ⟨a, ha, rfl⟩ := hplus ▸ hb
    simpa using ha
  invFun := spaComap (e : A →+* B) he Aplus Bplus fun a ha ↦ hplus ▸ ⟨a, ha, rfl⟩
  left_inv := spaComap_spaComap (e : A →+* B) he (fun a ha ↦ hplus ▸ ⟨a, ha, rfl⟩)
    (e.symm : B →+* A) he' e.symm_apply_apply fun b hb ↦ by
      obtain ⟨a, ha, rfl⟩ := hplus ▸ hb
      simpa using ha
  right_inv := spaComap_spaComap (e.symm : B →+* A) he'
    (fun b hb ↦ by obtain ⟨a, ha, rfl⟩ := hplus ▸ hb; simpa using ha)
    (e : A →+* B) he e.apply_symm_apply fun a ha ↦ hplus ▸ ⟨a, ha, rfl⟩
  continuous_toFun := continuous_spaComap _ he' _ _ _
  continuous_invFun := continuous_spaComap _ he _ _ _

/-- `spaHomeomorphOfRingEquiv` pulls valuations back along `e.symm`. -/
@[simp]
theorem spaHomeomorphOfRingEquiv_val (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (hplus : Aplus.map (e : A →+* B) = Bplus) (v : spa Aplus) :
    (spaHomeomorphOfRingEquiv e he he' hplus v : Spv B) = comap (e.symm : B →+* A) v.1 :=
  spaComap_val (e.symm : B →+* A) he' Bplus Aplus _ v

/-- The inverse of `spaHomeomorphOfRingEquiv` pulls valuations back along `e`. -/
@[simp]
theorem spaHomeomorphOfRingEquiv_symm_val (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (hplus : Aplus.map (e : A →+* B) = Bplus) (w : spa Bplus) :
    ((spaHomeomorphOfRingEquiv e he he' hplus).symm w : Spv A) = comap (e : A →+* B) w.1 :=
  spaComap_val (e : A →+* B) he Aplus Bplus _ w

/-- Preimage under `spaHomeomorphOfRingEquiv` bijects `spaRationalFamily B⁺` onto
`spaRationalFamily A⁺`. -/
theorem bijOn_preimage_spaHomeomorphOfRingEquiv_spaRationalFamily (e : A ≃+* B)
    (he : Continuous e) (he' : Continuous e.symm) (hplus : Aplus.map (e : A →+* B) = Bplus) :
    Set.BijOn (fun V : Set (spa Bplus) ↦ spaHomeomorphOfRingEquiv e he he' hplus ⁻¹' V)
      (spaRationalFamily Bplus) (spaRationalFamily Aplus) := by
  have hopen_symm : ∀ J : Ideal B, IsOpen (J : Set B) →
      IsOpen (Ideal.map (e.symm : B →+* A) J : Set A) := fun J hJ ↦ by
    rw [Ideal.map_eq_image_of_surjective (e.symm : B →+* A) e.symm.surjective]
    exact (IsOpenMap.of_inverse he e.symm_apply_apply e.apply_symm_apply) J hJ
  have hopen : ∀ J : Ideal A, IsOpen (J : Set A) →
      IsOpen (Ideal.map (e : A →+* B) J : Set B) := fun J hJ ↦ by
    rw [Ideal.map_eq_image_of_surjective (e : A →+* B) e.surjective]
    exact (IsOpenMap.of_inverse he' e.apply_symm_apply e.symm_apply_apply) J hJ
  refine ⟨fun V hV ↦ spaComap_preimage_mem_spaRationalFamily (e.symm : B →+* A) he' Bplus Aplus _
      hopen_symm hV,
    (spaHomeomorphOfRingEquiv e he he' hplus).surjective.preimage_injective.injOn,
    fun U hU ↦ ⟨(spaHomeomorphOfRingEquiv e he he' hplus).symm ⁻¹' U,
      spaComap_preimage_mem_spaRationalFamily (e : A →+* B) he Aplus Bplus _ hopen hU, ?_⟩⟩
  ext x
  simp

/-- Two rational subsets are equal in `Spv A` as soon as their traces on `spa A⁺` agree. -/
theorem rationalSubset_eq_of_val_preimage_eq {T₁ T₂ : Finset A} {s₁ s₂ : A}
    (h : (Subtype.val ⁻¹' rationalSubset Aplus T₁ s₁ : Set (spa Aplus)) =
      Subtype.val ⁻¹' rationalSubset Aplus T₂ s₂) :
    rationalSubset Aplus T₁ s₁ = rationalSubset Aplus T₂ s₂ := by
  ext v
  refine ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩
  · have hx : (⟨v, rationalSubset_subset_spa Aplus T₁ s₁ hv⟩ : spa Aplus) ∈
        Subtype.val ⁻¹' rationalSubset Aplus T₁ s₁ := hv
    rwa [h] at hx
  · have hx : (⟨v, rationalSubset_subset_spa Aplus T₂ s₂ hv⟩ : spa Aplus) ∈
        Subtype.val ⁻¹' rationalSubset Aplus T₂ s₂ := hv
    rwa [← h] at hx

end RingEquiv

section PresentationPlus

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Presentation independence preserves `completedPlusSubring`.** For two presentations of the
same rational subset of `Spa(A, A⁺)`, `presentationRingEquivOfEq` maps the completed plus subring
of the first onto that of the second. -/
theorem map_completedPlusSubring_presentationRingEquivOfEq (P : PairOfDefinition A)
    (Aplus : Subring A)
    (hIplus : ∀ j : P.ringOfDefinition, j ∈ P.idealOfDefinition → (j : A) ∈ Aplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) (T' : Finset A)
    (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (heq : rationalSubset Aplus T s = rationalSubset Aplus T' s') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    (completedPlusSubring P Aplus T s S hden).map
        (presentationRingEquivOfEq P Aplus hAplus T s S hden T' s' S' hden' heq).toRingHom =
      completedPlusSubring P Aplus T' s' S' hden' := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  let e := presentationRingEquivOfEq P Aplus hAplus T s S hden T' s' S' hden' heq
  have he_fwd : (e : Completion S →+* Completion S') =
      ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' heq.ge :=
    eq_ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' heq.ge _
      (continuous_presentationRingEquivOfEq P Aplus hAplus T s S hden T' s' S' hden' heq)
      (presentationRingEquivOfEq_coe_comp_toCompletionLoc P Aplus hAplus T s S hden T' s' S' hden'
        heq)
  have he_inv : (e.symm : Completion S' →+* Completion S) =
      ringHomOfRationalSubsetSubset P Aplus hAplus T' s' S' hden' T s S hden heq.le :=
    eq_ringHomOfRationalSubsetSubset P Aplus hAplus T' s' S' hden' T s S hden heq.le _
      (continuous_presentationRingEquivOfEq_symm P Aplus hAplus T s S hden T' s' S' hden' heq)
      (presentationRingEquivOfEq_symm_coe_comp_toCompletionLoc P Aplus hAplus T s S hden T' s' S'
        hden' heq)
  refine le_antisymm (Subring.map_le_iff_le_comap.mpr fun x hx ↦ ?_) fun y hy ↦
    Subring.mem_map.mpr ⟨e.symm y, ?_,
      by simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using
        e.apply_symm_apply y⟩
  · rw [Subring.mem_comap, RingEquiv.toRingHom_eq_coe, he_fwd]
    exact ringHomOfRationalSubsetSubset_mem_completedPlusSubring P Aplus hIplus hAplus
      T s S hden T' s' S' hden' heq.ge x hx
  · simpa only [← DFunLike.congr_fun he_inv y, RingEquiv.coe_toRingHom] using
      ringHomOfRationalSubsetSubset_mem_completedPlusSubring P Aplus hIplus hAplus
        T' s' S' hden' T s S hden heq.le y hy

end PresentationPlus

end TauCeti.ValuationSpectrum

namespace TauCeti.Huber.PairOfDefinition

open ValuationSpectrum

section GeometricUniversalProperty

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [IsHuberRing B] [CompleteSpace B] [T0Space B]

/-- **Wedhorn's Lemma 8.1 for morphisms of Huber pairs.** A morphism `f : (A, A⁺) → (B, B⁺)` into a
complete separated Huber pair whose induced map on `Spa` lands in `R(T/s)` extends uniquely across
the structure morphism `toCompletionLocHom : (A, A⁺) → (A⟨T/s⟩, A_U⁺)`. -/
theorem existsUnique_pairHom_of_forall_spaComap_mem_rationalSubset
    (P : PairOfDefinition A) (UA : Pair A) (hP : P.ringOfDefinition ≤ UA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) {UB : Pair B} (f : Pair.Hom UA UB)
    (hf : ∀ w : spa UB.plus, f.spaComap w ∈ Subtype.val ⁻¹' rationalSubset UA.plus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    ∃! g : Pair.Hom (rationalLocalizationPair P UA hP T s S hden) UB,
      g.comp (toCompletionLocHom P UA hP T s S hden) = f := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
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

/-- **The Huber-pair morphism induced by a factorisation on `Spa`** (Wedhorn, Lemma 8.1): given
`f : (A, A⁺) → (B, B⁺)` into a complete separated Huber pair with `Spa(f)(Spa(B, B⁺)) ⊆ R(T/s)`,
the unique extension `(A⟨T/s⟩, A_U⁺) → (B, B⁺)`. -/
noncomputable def pairHomOfForallSpaComapMemRationalSubset
    (P : PairOfDefinition A) (UA : Pair A) (hP : P.ringOfDefinition ≤ UA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) {UB : Pair B} (f : Pair.Hom UA UB)
    (hf : ∀ w : spa UB.plus, f.spaComap w ∈ Subtype.val ⁻¹' rationalSubset UA.plus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    Pair.Hom (rationalLocalizationPair P UA hP T s S hden) UB :=
  (existsUnique_pairHom_of_forall_spaComap_mem_rationalSubset P UA hP T s S hden f hf).choose

/-- `pairHomOfForallSpaComapMemRationalSubset` extends `f` across `toCompletionLocHom`. -/
@[simp]
theorem pairHomOfForallSpaComapMemRationalSubset_comp_toCompletionLocHom
    (P : PairOfDefinition A) (UA : Pair A) (hP : P.ringOfDefinition ≤ UA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) {UB : Pair B} (f : Pair.Hom UA UB)
    (hf : ∀ w : spa UB.plus, f.spaComap w ∈ Subtype.val ⁻¹' rationalSubset UA.plus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (pairHomOfForallSpaComapMemRationalSubset P UA hP T s S hden f hf).comp
        (toCompletionLocHom P UA hP T s S hden) = f :=
  (existsUnique_pairHom_of_forall_spaComap_mem_rationalSubset P UA hP T s S hden
    f hf).choose_spec.1

/-- Ring-homomorphism compatibility of `pairHomOfForallSpaComapMemRationalSubset` with
`toCompletionLoc`. -/
@[simp]
theorem toRingHom_pairHomOfForallSpaComapMemRationalSubset_comp_toCompletionLoc
    (P : PairOfDefinition A) (UA : Pair A) (hP : P.ringOfDefinition ≤ UA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) {UB : Pair B} (f : Pair.Hom UA UB)
    (hf : ∀ w : spa UB.plus, f.spaComap w ∈ Subtype.val ⁻¹' rationalSubset UA.plus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    (pairHomOfForallSpaComapMemRationalSubset P UA hP T s S hden f hf).toRingHom.comp
        (toCompletionLoc P T s S hden) = f.toRingHom := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  simpa only [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom] using
    congrArg Pair.Hom.toRingHom
      (pairHomOfForallSpaComapMemRationalSubset_comp_toCompletionLocHom P UA hP T s S hden f hf)

/-- If `f` is adic, its extension `pairHomOfForallSpaComapMemRationalSubset` is also adic. -/
theorem isAdicHom_pairHomOfForallSpaComapMemRationalSubset
    (P : PairOfDefinition A) (UA : Pair A) (hP : P.ringOfDefinition ≤ UA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) {UB : Pair B} (f : Pair.Hom UA UB)
    [IsAdicHom f.toRingHom]
    (hf : ∀ w : spa UB.plus, f.spaComap w ∈ Subtype.val ⁻¹' rationalSubset UA.plus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    IsAdicHom (pairHomOfForallSpaComapMemRationalSubset P UA hP T s S hden f hf).toRingHom := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  exact IsAdicHom.of_comp
    ((toRingHom_pairHomOfForallSpaComapMemRationalSubset_comp_toCompletionLoc P UA hP T s S hden
      f hf).symm ▸ inferInstanceAs (IsAdicHom f.toRingHom))
    (continuous_toCompletionLoc P T s S hden)
    (pairHomOfForallSpaComapMemRationalSubset P UA hP T s S hden f hf).continuous_toRingHom

end GeometricUniversalProperty

section LocalizedPairMap

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]

/-- **Geometric base change between rational-localisation Huber pairs.** Given
`f : (A, A⁺) → (B, B⁺)` such that `Spa(f)` carries `U = R(T'/s') ⊆ Spa(B, B⁺)` into
`W = R(T/s) ⊆ Spa(A, A⁺)`, the unique compatible morphism of rational-localisation Huber pairs
`(A⟨T/s⟩, A_W⁺) → (B⟨T'/s'⟩, B_U⁺)`. -/
noncomputable def pairHomOfSpaComapImageSubset
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower PB T' s' S')
    (f : Pair.Hom UA UB)
    (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus T' s') ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus T s) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := isHuberRing_completion_locTopology PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    letI := isHuberRing_completion_locTopology PB T' s' S' hden'
    Pair.Hom (rationalLocalizationPair PA UA hPA T s S hden)
      (rationalLocalizationPair PB UB hPB T' s' S' hden') := by
  let _ := locUniformSpace PA T s S hden
  have _ := isUniformAddGroup_locUniformSpace PA T s S hden
  have _ := isTopologicalRing_locUniformSpace PA T s S hden
  have _ := isHuberRing_completion_locTopology PA T s S hden
  let _ := locUniformSpace PB T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace PB T' s' S' hden'
  have _ := isHuberRing_completion_locTopology PB T' s' S' hden'
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
@[simp]
theorem pairHomOfSpaComapImageSubset_comp_toCompletionLocHom
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower PB T' s' S')
    (f : Pair.Hom UA UB)
    (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus T' s') ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus T s) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := isHuberRing_completion_locTopology PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    letI := isHuberRing_completion_locTopology PB T' s' S' hden'
    (pairHomOfSpaComapImageSubset PA UA hPA T s S hden PB UB hPB T' s' S' hden' f hf).comp
        (toCompletionLocHom PA UA hPA T s S hden) =
      (toCompletionLocHom PB UB hPB T' s' S' hden').comp f := by
  let _ := locUniformSpace PA T s S hden
  have _ := isUniformAddGroup_locUniformSpace PA T s S hden
  have _ := isTopologicalRing_locUniformSpace PA T s S hden
  have _ := isHuberRing_completion_locTopology PA T s S hden
  let _ := locUniformSpace PB T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace PB T' s' S' hden'
  have _ := isHuberRing_completion_locTopology PB T' s' S' hden'
  dsimp only [pairHomOfSpaComapImageSubset]
  exact pairHomOfForallSpaComapMemRationalSubset_comp_toCompletionLocHom PA UA hPA T s S hden _ _

/-- Ring-homomorphism compatibility of `pairHomOfSpaComapImageSubset` with `toCompletionLoc`. -/
@[simp]
theorem toRingHom_pairHomOfSpaComapImageSubset_comp_toCompletionLoc
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower PB T' s' S')
    (f : Pair.Hom UA UB)
    (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus T' s') ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus T s) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := isHuberRing_completion_locTopology PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    letI := isHuberRing_completion_locTopology PB T' s' S' hden'
    (pairHomOfSpaComapImageSubset PA UA hPA T s S hden PB UB hPB T' s' S' hden' f hf).toRingHom.comp
        (toCompletionLoc PA T s S hden) =
      (toCompletionLoc PB T' s' S' hden').comp f.toRingHom := by
  let _ := locUniformSpace PA T s S hden
  have _ := isUniformAddGroup_locUniformSpace PA T s S hden
  have _ := isTopologicalRing_locUniformSpace PA T s S hden
  have _ := isHuberRing_completion_locTopology PA T s S hden
  let _ := locUniformSpace PB T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace PB T' s' S' hden'
  have _ := isHuberRing_completion_locTopology PB T' s' S' hden'
  simpa only [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom] using
    congrArg Pair.Hom.toRingHom
      (pairHomOfSpaComapImageSubset_comp_toCompletionLocHom PA UA hPA T s S hden PB UB hPB T' s' S'
        hden' f hf)

/-- Uniqueness of `pairHomOfSpaComapImageSubset`: any morphism of Huber pairs out of
`rationalLocalizationPair PA UA hPA T s S hden` commuting with `toCompletionLocHom` equals
`pairHomOfSpaComapImageSubset`. -/
theorem eq_pairHomOfSpaComapImageSubset
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower PB T' s' S')
    (f : Pair.Hom UA UB)
    (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus T' s') ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus T s) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := isHuberRing_completion_locTopology PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    letI := isHuberRing_completion_locTopology PB T' s' S' hden'
    ∀ k : Pair.Hom (rationalLocalizationPair PA UA hPA T s S hden)
        (rationalLocalizationPair PB UB hPB T' s' S' hden'),
      k.comp (toCompletionLocHom PA UA hPA T s S hden) =
        (toCompletionLocHom PB UB hPB T' s' S' hden').comp f →
      k = pairHomOfSpaComapImageSubset PA UA hPA T s S hden PB UB hPB T' s' S' hden' f hf := by
  let _ := locUniformSpace PA T s S hden
  have _ := isUniformAddGroup_locUniformSpace PA T s S hden
  have _ := isTopologicalRing_locUniformSpace PA T s S hden
  have _ := isHuberRing_completion_locTopology PA T s S hden
  let _ := locUniformSpace PB T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace PB T' s' S' hden'
  have _ := isHuberRing_completion_locTopology PB T' s' S' hden'
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
theorem isAdicHom_pairHomOfSpaComapImageSubset
    (PA : PairOfDefinition A) (UA : Pair A) (hPA : PA.ringOfDefinition ≤ UA.plus)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower PA T s S)
    (PB : PairOfDefinition B) (UB : Pair B) (hPB : PB.ringOfDefinition ≤ UB.plus)
    (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower PB T' s' S')
    (f : Pair.Hom UA UB) [IsAdicHom f.toRingHom]
    (hf : f.spaComap '' (Subtype.val ⁻¹' rationalSubset UB.plus T' s') ⊆
      Subtype.val ⁻¹' rationalSubset UA.plus T s) :
    letI := locUniformSpace PA T s S hden
    letI := isUniformAddGroup_locUniformSpace PA T s S hden
    letI := isTopologicalRing_locUniformSpace PA T s S hden
    letI := isHuberRing_completion_locTopology PA T s S hden
    letI := locUniformSpace PB T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace PB T' s' S' hden'
    letI := isHuberRing_completion_locTopology PB T' s' S' hden'
    IsAdicHom
        (pairHomOfSpaComapImageSubset PA UA hPA T s S hden PB UB hPB T' s' S' hden'
          f hf).toRingHom := by
  let _ := locUniformSpace PA T s S hden
  have _ := isUniformAddGroup_locUniformSpace PA T s S hden
  have _ := isTopologicalRing_locUniformSpace PA T s S hden
  have _ := isHuberRing_completion_locTopology PA T s S hden
  let _ := locUniformSpace PB T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace PB T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace PB T' s' S' hden'
  have _ := isHuberRing_completion_locTopology PB T' s' S' hden'
  have _ : IsAdicHom ((toCompletionLocHom PB UB hPB T' s' S' hden').comp f).toRingHom := by
    rw [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom]
    exact IsAdicHom.comp (isAdicHom_toCompletionLoc PB T' s' S' hden')
      (inferInstanceAs (IsAdicHom f.toRingHom))
  dsimp only [pairHomOfSpaComapImageSubset]
  exact isAdicHom_pairHomOfForallSpaComapMemRationalSubset PA UA hPA T s S hden _ _

end LocalizedPairMap

end TauCeti.Huber.PairOfDefinition
