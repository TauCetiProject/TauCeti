/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Rational.Equiv
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Homeomorph
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Adic spectrum homeomorphism and rational-subset correspondence for localized completed tensors

Continuing in the setup of `TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Rational.Equiv`,
let `(D, D⁺) = (B, B⁺) ⊗̂_A (C, C⁺)` with projections `p_B : Spa(D, D⁺) → Spa(B, B⁺)` and
`p_C : Spa(D, D⁺) → Spa(C, C⁺)`, and let `O(W)`, `O(U)`, and `O(V)` be the completed rational
localisation Huber pairs over `W = R(T_A / s_A)`, `U = R(T_B / s_B)`, and `V = R(T_C / s_C)` with
`f.spaComap(U) ⊆ W` and `g.spaComap(V) ⊆ W`.

Combining `completedTensorRationalEquiv` with `spaHomeomorphOfRingEquiv` and
`spaRationalLocalizationPairHomeomorph`, we construct for any presentation `(T_D, s_D)` on `D`
presenting `p_B ⁻¹' U ∩ p_C ⁻¹' V` a canonical homeomorphism
```text
completedTensorRationalSpaHomeomorph :
  Spa(O(U) ⊗̂_{O(W)} O(V)) ≃ₜ ↥(p_B ⁻¹' U ∩ p_C ⁻¹' V)
```
and establish:

* `completedTensorRationalSpaHomeomorph_val_val`: it pulls valuations back along `e.symm ∘ ρ_D`;
* `inl_spaComap_completedTensorRationalSpaHomeomorph` and
  `inr_spaComap_completedTensorRationalSpaHomeomorph`: compatibility with the left and right
  projections to `Spa(B, B⁺)` and `Spa(C, C⁺)`;
* `bijOn_preimage_completedTensorRationalSpaHomeomorph_spaRationalFamily`: when `T_D · D` is open,
  inverse image under the homeomorphism bijects rational subsets of `Spa(D, D⁺)` contained in
  `p_B ⁻¹' U ∩ p_C ⁻¹' V` onto `spaRationalFamily` of `O(U) ⊗̂_{O(W)} O(V)`.

## Main definitions

* `TauCeti.Huber.Pair.completedTensorRationalSpaHomeomorph`: the canonical homeomorphism
  `Spa(O(U) ⊗̂_{O(W)} O(V)) ≃ₜ ↥(p_B ⁻¹' U ∩ p_C ⁻¹' V)`.

## Main results

* `TauCeti.Huber.Pair.completedTensorRationalSpaHomeomorph_val_val`: explicit valuation action.
* `TauCeti.Huber.Pair.inl_spaComap_completedTensorRationalSpaHomeomorph`,
  `TauCeti.Huber.Pair.inr_spaComap_completedTensorRationalSpaHomeomorph`: compatibility with the
  coprojection maps on `Spa`.
* `TauCeti.Huber.Pair.bijOn_preimage_completedTensorRationalSpaHomeomorph_spaRationalFamily`:
  bijection on rational subsets.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §1, Lemma 1.5(ii), and §3, Proposition 3.7.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, after Definition 2.4.12.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.2(2).
-/

public section

open UniformSpace

namespace TauCeti.Huber.Pair

open TauCeti.Huber.PairOfDefinition TauCeti.ValuationSpectrum

variable {A B C : Type*}
  [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing A] [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  (QA : PairOfDefinition A) (PA : Pair A) (hQA : QA.ringOfDefinition ≤ PA.plus)
  (TA : Finset A) (sA : A) (SA : Type*) [CommRing SA] [Algebra A SA] [IsLocalization.Away sA SA]
  (hdenA : HasDenominatorPower QA TA sA SA)
  (QB : PairOfDefinition B) (PB : Pair B) (hQB : QB.ringOfDefinition ≤ PB.plus)
  (TB : Finset B) (sB : B) (SB : Type*) [CommRing SB] [Algebra B SB] [IsLocalization.Away sB SB]
  (hdenB : HasDenominatorPower QB TB sB SB)
  (QC : PairOfDefinition C) (PC : Pair C) (hQC : QC.ringOfDefinition ≤ PC.plus)
  (TC : Finset C) (sC : C) (SC : Type*) [CommRing SC] [Algebra C SC] [IsLocalization.Away sC SC]
  (hdenC : HasDenominatorPower QC TC sC SC)
  (f : Hom PA PB) (g : Hom PA PC)
  (hf_alg : f.toRingHom = algebraMap A B) (hg_alg : g.toRingHom = algebraMap A C)
  (hf_sub : Set.MapsTo f.spaComap (Subtype.val ⁻¹' rationalSubset PB.plus TB sB)
    (Subtype.val ⁻¹' rationalSubset PA.plus TA sA))
  (hg_sub : Set.MapsTo g.spaComap (Subtype.val ⁻¹' rationalSubset PC.plus TC sC)
    (Subtype.val ⁻¹' rationalSubset PA.plus TA sA))
  (QD : PairOfDefinition (CompletedTensor A B C))
  (hQD : QD.ringOfDefinition ≤ (PB.completedTensor A PC).plus)
  (TD : Finset (CompletedTensor A B C)) (sD : CompletedTensor A B C)
  (SD : Type*) [CommRing SD] [Algebra (CompletedTensor A B C) SD] [IsLocalization.Away sD SD]
  (hdenD : HasDenominatorPower QD TD sD SD)
  (hD_eq : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus TD sD :
      Set (spa (PB.completedTensor A PC).plus)) =
    ((completedTensor.inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus TB sB)) ∩
      ((completedTensor.inr A PB PC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset PC.plus TC sC)))

include hQA hdenA hQB hdenB hQC hdenC hf_alg hg_alg hf_sub hg_sub hQD hdenD hD_eq

/-- **Homeomorphism of adic spectra** (Huber 1994, Lemma 1.5(ii); Wedhorn Proposition 8.2(2)):
`Spa(O(U) ⊗̂_{O(W)} O(V)) ≃ₜ ↥(p_B ⁻¹' U ∩ p_C ⁻¹' V)`. It pulls valuations back along
`e.symm ∘ ρ_D` (`completedTensorRationalSpaHomeomorph_val_val`). -/
noncomputable def completedTensorRationalSpaHomeomorph :
    letI := locUniformSpace QA TA sA SA hdenA
    letI := isUniformAddGroup_locUniformSpace QA TA sA SA hdenA
    letI := isTopologicalRing_locUniformSpace QA TA sA SA hdenA
    letI := isHuberRing_completion_locTopology QA TA sA SA hdenA
    letI := locUniformSpace QB TB sB SB hdenB
    letI := isUniformAddGroup_locUniformSpace QB TB sB SB hdenB
    letI := isTopologicalRing_locUniformSpace QB TB sB SB hdenB
    letI := isHuberRing_completion_locTopology QB TB sB SB hdenB
    letI := locUniformSpace QC TC sC SC hdenC
    letI := isUniformAddGroup_locUniformSpace QC TC sC SC hdenC
    letI := isTopologicalRing_locUniformSpace QC TC sC SC hdenC
    letI := isHuberRing_completion_locTopology QC TC sC SC hdenC
    haveI : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
    haveI : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
    letI : Algebra (Completion SA) (Completion SB) :=
      (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
        hf_sub).toRingHom.toAlgebra
    letI : Algebra (Completion SA) (Completion SC) :=
      (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
        hg_sub).toRingHom.toAlgebra
    haveI : IsAdicHom (algebraMap (Completion SA) (Completion SB)) :=
      isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
        hf_sub
    haveI : IsAdicHom (algebraMap (Completion SA) (Completion SC)) :=
      isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
        hg_sub
    spa ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor (Completion SA)
        (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).plus ≃ₜ
      ↥(((completedTensor.inl A PB PC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset PB.plus TB sB)) ∩
        ((completedTensor.inr A PB PC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset PC.plus TC sC))) :=
  let _ := locUniformSpace QA TA sA SA hdenA
  have _ := isUniformAddGroup_locUniformSpace QA TA sA SA hdenA
  have _ := isTopologicalRing_locUniformSpace QA TA sA SA hdenA
  have _ := isHuberRing_completion_locTopology QA TA sA SA hdenA
  let _ := locUniformSpace QB TB sB SB hdenB
  have _ := isUniformAddGroup_locUniformSpace QB TB sB SB hdenB
  have _ := isTopologicalRing_locUniformSpace QB TB sB SB hdenB
  have _ := isHuberRing_completion_locTopology QB TB sB SB hdenB
  let _ := locUniformSpace QC TC sC SC hdenC
  have _ := isUniformAddGroup_locUniformSpace QC TC sC SC hdenC
  have _ := isTopologicalRing_locUniformSpace QC TC sC SC hdenC
  have _ := isHuberRing_completion_locTopology QC TC sC SC hdenC
  have _ : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
  have _ : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
  let _ : Algebra (Completion SA) (Completion SB) :=
    (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
      hf_sub).toRingHom.toAlgebra
  let _ : Algebra (Completion SA) (Completion SC) :=
    (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
      hg_sub).toRingHom.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion SA) (Completion SB)) :=
    isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
      hf_sub
  have _ : IsAdicHom (algebraMap (Completion SA) (Completion SC)) :=
    isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
      hg_sub
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  ((spaHomeomorphOfRingEquiv
      (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).symm
      (continuous_completedTensorRationalEquiv_symm QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB
        hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
        hD_eq)
      (by
        simpa only [RingEquiv.symm_symm] using
          continuous_completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB
            hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
            hD_eq)
      (rationalLocalizationPair QD (PB.completedTensor A PC) hQD TD sD SD hdenD).plus
      ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor (Completion SA)
        (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).plus
      (completedTensorRationalEquiv_symm_mem_plus QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB
        hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
        hD_eq)
      (fun x hx ↦ by
        rw [RingEquiv.symm_symm]
        exact completedTensorRationalEquiv_mem_plus QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB
          hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
          hD_eq x hx)).trans
    (spaRationalLocalizationPairHomeomorph QD (PB.completedTensor A PC) hQD TD sD SD
      hdenD)).trans
    (Homeomorph.setCongr hD_eq)

/-- The underlying valuation in `Spv D` of `completedTensorRationalSpaHomeomorph … z` is pulled
back along `e.symm` and then `ρ_D`. -/
@[simp]
theorem completedTensorRationalSpaHomeomorph_val_val :
    letI := locUniformSpace QA TA sA SA hdenA
    letI := isUniformAddGroup_locUniformSpace QA TA sA SA hdenA
    letI := isTopologicalRing_locUniformSpace QA TA sA SA hdenA
    letI := isHuberRing_completion_locTopology QA TA sA SA hdenA
    letI := locUniformSpace QB TB sB SB hdenB
    letI := isUniformAddGroup_locUniformSpace QB TB sB SB hdenB
    letI := isTopologicalRing_locUniformSpace QB TB sB SB hdenB
    letI := isHuberRing_completion_locTopology QB TB sB SB hdenB
    letI := locUniformSpace QC TC sC SC hdenC
    letI := isUniformAddGroup_locUniformSpace QC TC sC SC hdenC
    letI := isTopologicalRing_locUniformSpace QC TC sC SC hdenC
    letI := isHuberRing_completion_locTopology QC TC sC SC hdenC
    haveI : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
    haveI : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
    letI : Algebra (Completion SA) (Completion SB) :=
      (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
        hf_sub).toRingHom.toAlgebra
    letI : Algebra (Completion SA) (Completion SC) :=
      (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
        hg_sub).toRingHom.toAlgebra
    haveI : IsAdicHom (algebraMap (Completion SA) (Completion SB)) :=
      isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
        hf_sub
    haveI : IsAdicHom (algebraMap (Completion SA) (Completion SC)) :=
      isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
        hg_sub
    letI := locUniformSpace QD TD sD SD hdenD
    letI := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
    letI := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
    ∀ z : spa ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor (Completion SA)
        (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).plus,
      ((completedTensorRationalSpaHomeomorph QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
          QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq
          z : spa (PB.completedTensor A PC).plus) : Spv (CompletedTensor A B C)) =
        ValuationSpectrum.comap (toCompletionLoc QD TD sD SD hdenD)
          (ValuationSpectrum.comap
            (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC
              hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
              hD_eq).symm.toRingHom
            z.1) := by
  let _ := locUniformSpace QA TA sA SA hdenA
  have _ := isUniformAddGroup_locUniformSpace QA TA sA SA hdenA
  have _ := isTopologicalRing_locUniformSpace QA TA sA SA hdenA
  have _ := isHuberRing_completion_locTopology QA TA sA SA hdenA
  let _ := locUniformSpace QB TB sB SB hdenB
  have _ := isUniformAddGroup_locUniformSpace QB TB sB SB hdenB
  have _ := isTopologicalRing_locUniformSpace QB TB sB SB hdenB
  have _ := isHuberRing_completion_locTopology QB TB sB SB hdenB
  let _ := locUniformSpace QC TC sC SC hdenC
  have _ := isUniformAddGroup_locUniformSpace QC TC sC SC hdenC
  have _ := isTopologicalRing_locUniformSpace QC TC sC SC hdenC
  have _ := isHuberRing_completion_locTopology QC TC sC SC hdenC
  have _ : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
  have _ : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
  let _ : Algebra (Completion SA) (Completion SB) :=
    (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
      hf_sub).toRingHom.toAlgebra
  let _ : Algebra (Completion SA) (Completion SC) :=
    (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
      hg_sub).toRingHom.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion SA) (Completion SB)) :=
    isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
      hf_sub
  have _ : IsAdicHom (algebraMap (Completion SA) (Completion SC)) :=
    isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
      hg_sub
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  intro z
  rw [completedTensorRationalSpaHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply,
    Homeomorph.setCongr_apply]
  dsimp only
  rw [spaRationalLocalizationPairHomeomorph_val_val]
  exact congrArg (ValuationSpectrum.comap (toCompletionLoc QD TD sD SD hdenD))
    (spaHomeomorphOfRingEquiv_val _ _ _ _ _ _ _ z)

/-- Compatibility of `completedTensorRationalSpaHomeomorph` with the left projection `p_B`. -/
theorem inl_spaComap_completedTensorRationalSpaHomeomorph :
    letI := locUniformSpace QA TA sA SA hdenA
    letI := isUniformAddGroup_locUniformSpace QA TA sA SA hdenA
    letI := isTopologicalRing_locUniformSpace QA TA sA SA hdenA
    letI := isHuberRing_completion_locTopology QA TA sA SA hdenA
    letI := locUniformSpace QB TB sB SB hdenB
    letI := isUniformAddGroup_locUniformSpace QB TB sB SB hdenB
    letI := isTopologicalRing_locUniformSpace QB TB sB SB hdenB
    letI := isHuberRing_completion_locTopology QB TB sB SB hdenB
    letI := locUniformSpace QC TC sC SC hdenC
    letI := isUniformAddGroup_locUniformSpace QC TC sC SC hdenC
    letI := isTopologicalRing_locUniformSpace QC TC sC SC hdenC
    letI := isHuberRing_completion_locTopology QC TC sC SC hdenC
    haveI : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
    haveI : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
    letI : Algebra (Completion SA) (Completion SB) :=
      (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
        hf_sub).toRingHom.toAlgebra
    letI : Algebra (Completion SA) (Completion SC) :=
      (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
        hg_sub).toRingHom.toAlgebra
    haveI : IsAdicHom (algebraMap (Completion SA) (Completion SB)) :=
      isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
        hf_sub
    haveI : IsAdicHom (algebraMap (Completion SA) (Completion SC)) :=
      isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
        hg_sub
    ∀ z : spa ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor (Completion SA)
        (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).plus,
      (completedTensor.inl A PB PC).spaComap
          (completedTensorRationalSpaHomeomorph QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
            QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq
            z).1 =
        (toCompletionLocHom QB PB hQB TB sB SB hdenB).spaComap
          ((completedTensor.inl (Completion SA)
            (rationalLocalizationPair QB PB hQB TB sB SB hdenB)
            (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).spaComap z) := by
  let _ := locUniformSpace QA TA sA SA hdenA
  have _ := isUniformAddGroup_locUniformSpace QA TA sA SA hdenA
  have _ := isTopologicalRing_locUniformSpace QA TA sA SA hdenA
  have _ := isHuberRing_completion_locTopology QA TA sA SA hdenA
  let _ := locUniformSpace QB TB sB SB hdenB
  have _ := isUniformAddGroup_locUniformSpace QB TB sB SB hdenB
  have _ := isTopologicalRing_locUniformSpace QB TB sB SB hdenB
  have _ := isHuberRing_completion_locTopology QB TB sB SB hdenB
  let _ := locUniformSpace QC TC sC SC hdenC
  have _ := isUniformAddGroup_locUniformSpace QC TC sC SC hdenC
  have _ := isTopologicalRing_locUniformSpace QC TC sC SC hdenC
  have _ := isHuberRing_completion_locTopology QC TC sC SC hdenC
  have _ : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
  have _ : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
  let _ : Algebra (Completion SA) (Completion SB) :=
    (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
      hf_sub).toRingHom.toAlgebra
  let _ : Algebra (Completion SA) (Completion SC) :=
    (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
      hg_sub).toRingHom.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion SA) (Completion SB)) :=
    isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
      hf_sub
  have _ : IsAdicHom (algebraMap (Completion SA) (Completion SC)) :=
    isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
      hg_sub
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  intro z
  apply Subtype.ext
  rw [Hom.spaComap_val, completedTensorRationalSpaHomeomorph_val_val,
    toRingHom_completedTensorRationalEquiv_symm, Hom.spaComap_val, Hom.spaComap_val,
    ValuationSpectrum.comap_comap, ValuationSpectrum.comap_comap, ValuationSpectrum.comap_comap]
  congr 1
  rw [← toRingHom_toCompletionLocHom QD (PB.completedTensor A PC) hQD TD sD SD hdenD]
  simpa only [Hom.toRingHom_comp, RingHom.comp_assoc] using congrArg Hom.toRingHom
    (completedTensorRationalOfLocHom_comp_toCompletionLocHom_comp_inl QA PA hQA TA sA SA hdenA QB
      PB hQB TB sB SB hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD
      SD hdenD hD_eq)

/-- Compatibility of `completedTensorRationalSpaHomeomorph` with the right projection `p_C`. -/
theorem inr_spaComap_completedTensorRationalSpaHomeomorph :
    letI := locUniformSpace QA TA sA SA hdenA
    letI := isUniformAddGroup_locUniformSpace QA TA sA SA hdenA
    letI := isTopologicalRing_locUniformSpace QA TA sA SA hdenA
    letI := isHuberRing_completion_locTopology QA TA sA SA hdenA
    letI := locUniformSpace QB TB sB SB hdenB
    letI := isUniformAddGroup_locUniformSpace QB TB sB SB hdenB
    letI := isTopologicalRing_locUniformSpace QB TB sB SB hdenB
    letI := isHuberRing_completion_locTopology QB TB sB SB hdenB
    letI := locUniformSpace QC TC sC SC hdenC
    letI := isUniformAddGroup_locUniformSpace QC TC sC SC hdenC
    letI := isTopologicalRing_locUniformSpace QC TC sC SC hdenC
    letI := isHuberRing_completion_locTopology QC TC sC SC hdenC
    haveI : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
    haveI : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
    letI : Algebra (Completion SA) (Completion SB) :=
      (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
        hf_sub).toRingHom.toAlgebra
    letI : Algebra (Completion SA) (Completion SC) :=
      (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
        hg_sub).toRingHom.toAlgebra
    haveI : IsAdicHom (algebraMap (Completion SA) (Completion SB)) :=
      isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
        hf_sub
    haveI : IsAdicHom (algebraMap (Completion SA) (Completion SC)) :=
      isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
        hg_sub
    ∀ z : spa ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor (Completion SA)
        (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).plus,
      (completedTensor.inr A PB PC).spaComap
          (completedTensorRationalSpaHomeomorph QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
            QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq
            z).1 =
        (toCompletionLocHom QC PC hQC TC sC SC hdenC).spaComap
          ((completedTensor.inr (Completion SA)
            (rationalLocalizationPair QB PB hQB TB sB SB hdenB)
            (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).spaComap z) := by
  let _ := locUniformSpace QA TA sA SA hdenA
  have _ := isUniformAddGroup_locUniformSpace QA TA sA SA hdenA
  have _ := isTopologicalRing_locUniformSpace QA TA sA SA hdenA
  have _ := isHuberRing_completion_locTopology QA TA sA SA hdenA
  let _ := locUniformSpace QB TB sB SB hdenB
  have _ := isUniformAddGroup_locUniformSpace QB TB sB SB hdenB
  have _ := isTopologicalRing_locUniformSpace QB TB sB SB hdenB
  have _ := isHuberRing_completion_locTopology QB TB sB SB hdenB
  let _ := locUniformSpace QC TC sC SC hdenC
  have _ := isUniformAddGroup_locUniformSpace QC TC sC SC hdenC
  have _ := isTopologicalRing_locUniformSpace QC TC sC SC hdenC
  have _ := isHuberRing_completion_locTopology QC TC sC SC hdenC
  have _ : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
  have _ : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
  let _ : Algebra (Completion SA) (Completion SB) :=
    (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
      hf_sub).toRingHom.toAlgebra
  let _ : Algebra (Completion SA) (Completion SC) :=
    (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
      hg_sub).toRingHom.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion SA) (Completion SB)) :=
    isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
      hf_sub
  have _ : IsAdicHom (algebraMap (Completion SA) (Completion SC)) :=
    isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
      hg_sub
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  intro z
  apply Subtype.ext
  rw [Hom.spaComap_val, completedTensorRationalSpaHomeomorph_val_val,
    toRingHom_completedTensorRationalEquiv_symm, Hom.spaComap_val, Hom.spaComap_val,
    ValuationSpectrum.comap_comap, ValuationSpectrum.comap_comap, ValuationSpectrum.comap_comap]
  congr 1
  rw [← toRingHom_toCompletionLocHom QD (PB.completedTensor A PC) hQD TD sD SD hdenD]
  simpa only [Hom.toRingHom_comp, RingHom.comp_assoc] using congrArg Hom.toRingHom
    (completedTensorRationalOfLocHom_comp_toCompletionLocHom_comp_inr QA PA hQA TA sA SA hdenA QB
      PB hQB TB sB SB hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD
      SD hdenD hD_eq)

/-- **Matching of rational subsets** (Wedhorn Proposition 8.2(2)): when `T_D · D` is open, preimage
under `completedTensorRationalSpaHomeomorph` bijects rational subsets of `Spa(D, D⁺)` contained in
`p_B ⁻¹' U ∩ p_C ⁻¹' V` onto `spaRationalFamily` of `O(U) ⊗̂_{O(W)} O(V)`. -/
theorem bijOn_preimage_completedTensorRationalSpaHomeomorph_spaRationalFamily
    (hTD : IsOpen (Ideal.span (TD : Set (CompletedTensor A B C)) : Set (CompletedTensor A B C))) :
    letI := locUniformSpace QA TA sA SA hdenA
    letI := isUniformAddGroup_locUniformSpace QA TA sA SA hdenA
    letI := isTopologicalRing_locUniformSpace QA TA sA SA hdenA
    letI := isHuberRing_completion_locTopology QA TA sA SA hdenA
    letI := locUniformSpace QB TB sB SB hdenB
    letI := isUniformAddGroup_locUniformSpace QB TB sB SB hdenB
    letI := isTopologicalRing_locUniformSpace QB TB sB SB hdenB
    letI := isHuberRing_completion_locTopology QB TB sB SB hdenB
    letI := locUniformSpace QC TC sC SC hdenC
    letI := isUniformAddGroup_locUniformSpace QC TC sC SC hdenC
    letI := isTopologicalRing_locUniformSpace QC TC sC SC hdenC
    letI := isHuberRing_completion_locTopology QC TC sC SC hdenC
    haveI : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
    haveI : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
    letI : Algebra (Completion SA) (Completion SB) :=
      (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
        hf_sub).toRingHom.toAlgebra
    letI : Algebra (Completion SA) (Completion SC) :=
      (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
        hg_sub).toRingHom.toAlgebra
    haveI : IsAdicHom (algebraMap (Completion SA) (Completion SB)) :=
      isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
        hf_sub
    haveI : IsAdicHom (algebraMap (Completion SA) (Completion SC)) :=
      isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
        hg_sub
    Set.BijOn
      (fun Z : Set (spa (PB.completedTensor A PC).plus) ↦
        completedTensorRationalSpaHomeomorph QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
          QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq ⁻¹'
          (Subtype.val ⁻¹' Z))
      {Z ∈ spaRationalFamily (PB.completedTensor A PC).plus |
        Z ⊆ ((completedTensor.inl A PB PC).spaComap ⁻¹'
            (Subtype.val ⁻¹' rationalSubset PB.plus TB sB)) ∩
          ((completedTensor.inr A PB PC).spaComap ⁻¹'
            (Subtype.val ⁻¹' rationalSubset PC.plus TC sC))}
      (spaRationalFamily
        ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor (Completion SA)
          (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).plus) := by
  let _ := locUniformSpace QA TA sA SA hdenA
  have _ := isUniformAddGroup_locUniformSpace QA TA sA SA hdenA
  have _ := isTopologicalRing_locUniformSpace QA TA sA SA hdenA
  have _ := isHuberRing_completion_locTopology QA TA sA SA hdenA
  let _ := locUniformSpace QB TB sB SB hdenB
  have _ := isUniformAddGroup_locUniformSpace QB TB sB SB hdenB
  have _ := isTopologicalRing_locUniformSpace QB TB sB SB hdenB
  have _ := isHuberRing_completion_locTopology QB TB sB SB hdenB
  let _ := locUniformSpace QC TC sC SC hdenC
  have _ := isUniformAddGroup_locUniformSpace QC TC sC SC hdenC
  have _ := isTopologicalRing_locUniformSpace QC TC sC SC hdenC
  have _ := isHuberRing_completion_locTopology QC TC sC SC hdenC
  have _ : IsAdicHom f.toRingHom := hf_alg ▸ inferInstance
  have _ : IsAdicHom g.toRingHom := hg_alg ▸ inferInstance
  let _ : Algebra (Completion SA) (Completion SB) :=
    (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
      hf_sub).toRingHom.toAlgebra
  let _ : Algebra (Completion SA) (Completion SC) :=
    (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
      hg_sub).toRingHom.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion SA) (Completion SB)) :=
    isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
      hf_sub
  have _ : IsAdicHom (algebraMap (Completion SA) (Completion SC)) :=
    isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
      hg_sub
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  have hcont_inv : Continuous
      ⇑(completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).symm.symm := by
    simpa only [RingEquiv.symm_symm] using
      continuous_completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC
        PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq
  have hmem_inv : ∀ x ∈ ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor
        (Completion SA) (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).plus,
      (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
        hD_eq).symm.symm x ∈
        (rationalLocalizationPair QD (PB.completedTensor A PC) hQD TD sD SD hdenD).plus :=
    fun x hx ↦ by
      rw [RingEquiv.symm_symm]
      exact completedTensorRationalEquiv_mem_plus QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB
        hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
        hD_eq x hx
  set H₁ := spaHomeomorphOfRingEquiv
    (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
      TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).symm
    (continuous_completedTensorRationalEquiv_symm QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
      QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq)
    hcont_inv
    (rationalLocalizationPair QD (PB.completedTensor A PC) hQD TD sD SD hdenD).plus
    ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor (Completion SA)
      (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).plus
    (completedTensorRationalEquiv_symm_mem_plus QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
      QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq)
    hmem_inv
  set H₂ := spaRationalLocalizationPairHomeomorph QD (PB.completedTensor A PC) hQD TD sD SD hdenD
  have hbij₁ := bijOn_preimage_spaHomeomorphOfRingEquiv_spaRationalFamily
    (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
      TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).symm
    (continuous_completedTensorRationalEquiv_symm QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
      QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq)
    hcont_inv
    (rationalLocalizationPair QD (PB.completedTensor A PC) hQD TD sD SD hdenD).plus
    ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor (Completion SA)
      (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).plus
    (completedTensorRationalEquiv_symm_mem_plus QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
      QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq)
    hmem_inv
  have hbij₂ := bijOn_preimage_spaRationalLocalizationPairHomeomorph_spaRationalFamily QD
    (PB.completedTensor A PC) hQD TD sD SD hdenD hTD
  have hfun : (fun Z : Set (spa (PB.completedTensor A PC).plus) ↦
      completedTensorRationalSpaHomeomorph QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
        QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq ⁻¹'
        (Subtype.val ⁻¹' Z)) =
      (fun U ↦ H₁ ⁻¹' U) ∘ (fun W ↦ H₂ ⁻¹' (Subtype.val ⁻¹' W)) := by
    ext Z z
    simp only [completedTensorRationalSpaHomeomorph, Function.comp_apply, Set.mem_preimage,
      Homeomorph.trans_apply, Homeomorph.setCongr_apply, H₁, H₂]
  have hs : {Z ∈ spaRationalFamily (PB.completedTensor A PC).plus |
      Z ⊆ Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus TD sD} =
      {Z ∈ spaRationalFamily (PB.completedTensor A PC).plus |
        Z ⊆ ((completedTensor.inl A PB PC).spaComap ⁻¹'
            (Subtype.val ⁻¹' rationalSubset PB.plus TB sB)) ∩
          ((completedTensor.inr A PB PC).spaComap ⁻¹'
            (Subtype.val ⁻¹' rationalSubset PC.plus TC sC))} := by
    rw [hD_eq]
  rw [hfun, ← hs]
  exact hbij₁.comp hbij₂

end TauCeti.Huber.Pair

end
