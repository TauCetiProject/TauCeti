/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedRationalSubset
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RingEquiv
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Rational.Pair

import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Adic spectrum of a completed tensor product of rational localisations

Composing the homeomorphism of adic spectra induced by `Pair.completedTensorRationalEquiv`
(`TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv`) with
`TauCeti.ValuationSpectrum.spaCompletedLocalizationHomeomorph` identifies the adic spectrum of the
completed tensor product `(O_B(U), O_B(U)⁺) ⊗̂_{O_A(W)} (O_C(V), O_C(V)⁺)` homeomorphically with the
intersection `p_B⁻¹(U) ∩ p_C⁻¹(V)` inside `Spa ((B, B⁺) ⊗̂_A (C, C⁺))`, and matches rational subsets
on both sides.

No completeness, Hausdorffness, or sheafiness assumption is imposed on `(A, A⁺)`, `(B, B⁺)` or
`(C, C⁺)`.

## Main definitions

* `TauCeti.Huber.Pair.completedTensorRationalSpaHomeomorph`: the homeomorphism
  `Spa ((O_B(U), O_B(U)⁺) ⊗̂_{O_A(W)} (O_C(V), O_C(V)⁺)) ≃ₜ ↥(p_B⁻¹(U) ∩ p_C⁻¹(V))`.

## Main results

* `TauCeti.Huber.Pair.completedTensorRationalSpaHomeomorph_val_val`: explicit valuation pullback
  formula along `e⁻¹ ∘ ρ_D`.
* `TauCeti.Huber.Pair.inl_spaComap_completedTensorRationalSpaHomeomorph`,
  `TauCeti.Huber.Pair.inr_spaComap_completedTensorRationalSpaHomeomorph`: compatibility of
  `completedTensorRationalSpaHomeomorph` with the left and right tensor projections.
* `TauCeti.Huber.Pair.completedTensorRationalSpaHomeomorph_preimage_mem_spaRationalFamily`,
  `TauCeti.Huber.Pair.completedTensorRationalSpaHomeomorph_image_mem_spaRationalFamily`,
  `TauCeti.Huber.Pair.bijOn_preimage_completedTensorRationalSpaHomeomorph_spaRationalFamily`:
  preimage under `completedTensorRationalSpaHomeomorph` bijects rational subsets of
  `Spa ((B, B⁺) ⊗̂_A (C, C⁺))` contained in `p_B⁻¹(U) ∩ p_C⁻¹(V)` onto rational subsets of the
  completed tensor spectrum.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  Lemma 1.5(ii) and Proposition 3.7.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.2(2).
-/

public section

open UniformSpace (Completion)

namespace TauCeti.Huber

open PairOfDefinition TauCeti.ValuationSpectrum

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing A] [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  (PA : PairOfDefinition A) (SA : Pair A)
  (TA : Finset A) (sA : A) (LA : Type*) [CommRing LA] [Algebra A LA]
  [IsLocalization.Away sA LA] (hdenA : HasDenominatorPower PA TA sA LA)
  (PB : PairOfDefinition B) (SB : Pair B)
  (TB : Finset B) (sB : B) (LB : Type*) [CommRing LB] [Algebra B LB]
  [IsLocalization.Away sB LB] (hdenB : HasDenominatorPower PB TB sB LB)
  (PC : PairOfDefinition C) (SC : Pair C)
  (TC : Finset C) (sC : C) (LC : Type*) [CommRing LC] [Algebra C LC]
  [IsLocalization.Away sC LC] (hdenC : HasDenominatorPower PC TC sC LC)
  (PD : PairOfDefinition (CompletedTensor A B C))
  (TD : Finset (CompletedTensor A B C)) (sD : CompletedTensor A B C)
  (LD : Type*) [CommRing LD] [Algebra (CompletedTensor A B C) LD]
  [IsLocalization.Away sD LD] (hdenD : HasDenominatorPower PD TD sD LD)

/-- **Homeomorphism of the adic spectrum of a completed tensor product of rational localisations
onto the intersection `p_B⁻¹(U) ∩ p_C⁻¹(V)`** in `Spa ((B, B⁺) ⊗̂_A (C, C⁺))`. -/
noncomputable def Pair.completedTensorRationalSpaHomeomorph
    (hPB : PB.ringOfDefinition ≤ SB.plus)
    (hPC : PC.ringOfDefinition ≤ SC.plus)
    (hPD : PD.ringOfDefinition ≤ (SB.completedTensor A SC).plus)
    (hf : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset SB.plus TB sB) (rationalSubset SA.plus TA sA))
    (hg : Set.MapsTo (comap (algebraMap A C))
      (rationalSubset SC.plus TC sC) (rationalSubset SA.plus TA sA))
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC))) :
    letI := locUniformSpace PA TA sA LA hdenA
    letI := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
    letI := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
    letI := locUniformSpace PB TB sB LB hdenB
    letI := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
    letI := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
    letI := isHuberRing_completion_locTopology PB TB sB LB hdenB
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
    letI := isHuberRing_completion_locTopology PC TC sC LC hdenC
    letI : Algebra (Completion LA) (Completion LB) :=
      (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
        SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
        (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).toAlgebra
    letI : Algebra (Completion LA) (Completion LC) :=
      (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
        SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
        (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).toAlgebra
    haveI : IsAdicHom (algebraMap (Completion LA) (Completion LB)) :=
      isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
        SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
        (inferInstance : IsAdicHom (algebraMap A B)) hf
    haveI : IsAdicHom (algebraMap (Completion LA) (Completion LC)) :=
      isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
        SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
        (inferInstance : IsAdicHom (algebraMap A C)) hg
    spa ((PB.rationalLocalizationPair SB hPB TB sB LB hdenB).completedTensor (Completion LA)
        (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).plus ≃ₜ
      ↥(((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
        ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
          (Subtype.val ⁻¹' rationalSubset SC.plus TC sC))) :=
  letI := locUniformSpace PA TA sA LA hdenA
  letI := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
  letI := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
  letI := locUniformSpace PB TB sB LB hdenB
  letI := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
  letI := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
  letI := isHuberRing_completion_locTopology PB TB sB LB hdenB
  letI := locUniformSpace PC TC sC LC hdenC
  letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
  letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
  letI := isHuberRing_completion_locTopology PC TC sC LC hdenC
  letI : Algebra (Completion LA) (Completion LB) :=
    (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
      SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
      (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).toAlgebra
  letI : Algebra (Completion LA) (Completion LC) :=
    (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
      SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
      (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).toAlgebra
  haveI : IsAdicHom (algebraMap (Completion LA) (Completion LB)) :=
    isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
      SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
      (inferInstance : IsAdicHom (algebraMap A B)) hf
  haveI : IsAdicHom (algebraMap (Completion LA) (Completion LC)) :=
    isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
      SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
      (inferInstance : IsAdicHom (algebraMap A C)) hg
  letI := locUniformSpace PD TD sD LD hdenD
  letI := isUniformAddGroup_locUniformSpace PD TD sD LD hdenD
  letI := isTopologicalRing_locUniformSpace PD TD sD LD hdenD
  let e := Pair.completedTensorRationalEquiv PA SA TA sA LA hdenA PB SB TB sB LB hdenB
    PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd
  (spaHomeomorphOfRingEquiv e
    (Pair.continuous_completedTensorRationalEquiv PA SA TA sA LA hdenA PB SB TB sB LB hdenB
      PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd)
    (Pair.continuous_completedTensorRationalEquiv_symm PA SA TA sA LA hdenA PB SB TB sB LB hdenB
      PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd)
    (fun x hx ↦ (Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
      PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
      PD TD sD LD hdenD hPB hPC hf hg hd x).mpr hx)
    (fun y hy ↦ (Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
      PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
      PD TD sD LD hdenD hPB hPC hf hg hd (e.symm y)).mp (by simpa [e] using hy))).symm.trans
    ((spaCompletedLocalizationHomeomorph PD (SB.completedTensor A SC).plus hPD TD sD LD hdenD).trans
      (Homeomorph.setCongr hd))

/-- `Pair.completedTensorRationalSpaHomeomorph` acts on points by pulling valuations back along
`e⁻¹ ∘ ρ_D`. -/
@[simp]
theorem Pair.completedTensorRationalSpaHomeomorph_val_val
    (hPB : PB.ringOfDefinition ≤ SB.plus)
    (hPC : PC.ringOfDefinition ≤ SC.plus)
    (hPD : PD.ringOfDefinition ≤ (SB.completedTensor A SC).plus)
    (hf : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset SB.plus TB sB) (rationalSubset SA.plus TA sA))
    (hg : Set.MapsTo (comap (algebraMap A C))
      (rationalSubset SC.plus TC sC) (rationalSubset SA.plus TA sA))
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC))) :
    letI := locUniformSpace PA TA sA LA hdenA
    letI := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
    letI := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
    letI := locUniformSpace PB TB sB LB hdenB
    letI := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
    letI := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
    letI := isHuberRing_completion_locTopology PB TB sB LB hdenB
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
    letI := isHuberRing_completion_locTopology PC TC sC LC hdenC
    letI : Algebra (Completion LA) (Completion LB) :=
      (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
        SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
        (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).toAlgebra
    letI : Algebra (Completion LA) (Completion LC) :=
      (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
        SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
        (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).toAlgebra
    haveI : IsAdicHom (algebraMap (Completion LA) (Completion LB)) :=
      isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
        SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
        (inferInstance : IsAdicHom (algebraMap A B)) hf
    haveI : IsAdicHom (algebraMap (Completion LA) (Completion LC)) :=
      isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
        SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
        (inferInstance : IsAdicHom (algebraMap A C)) hg
    letI := locUniformSpace PD TD sD LD hdenD
    letI := isUniformAddGroup_locUniformSpace PD TD sD LD hdenD
    letI := isTopologicalRing_locUniformSpace PD TD sD LD hdenD
    ∀ z : spa ((PB.rationalLocalizationPair SB hPB TB sB LB hdenB).completedTensor (Completion LA)
        (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).plus,
      (((Pair.completedTensorRationalSpaHomeomorph PA SA TA sA LA hdenA PB SB TB sB LB hdenB
          PC SC TC sC LC hdenC PD TD sD LD hdenD hPB hPC hPD hf hg hd z).1 :
          spa (SB.completedTensor A SC).plus) : Spv (CompletedTensor A B C)) =
        comap (((Pair.completedTensorRationalEquiv PA SA TA sA LA hdenA PB SB TB sB LB hdenB
            PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd).symm :
            Completion LD →+*
              CompletedTensor (Completion LA) (Completion LB) (Completion LC)).comp
          (toCompletionLoc PD TD sD LD hdenD)) z.1 := by
  let _ := locUniformSpace PA TA sA LA hdenA
  have _ := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
  have _ := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
  let _ := locUniformSpace PB TB sB LB hdenB
  have _ := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
  have _ := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
  have _ := isHuberRing_completion_locTopology PB TB sB LB hdenB
  let _ := locUniformSpace PC TC sC LC hdenC
  have _ := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
  have _ := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
  have _ := isHuberRing_completion_locTopology PC TC sC LC hdenC
  let _ : Algebra (Completion LA) (Completion LB) :=
    (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
      SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
      (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).toAlgebra
  let _ : Algebra (Completion LA) (Completion LC) :=
    (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
      SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
      (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).toAlgebra
  have _ : IsAdicHom (algebraMap (Completion LA) (Completion LB)) :=
    isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
      SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
      (inferInstance : IsAdicHom (algebraMap A B)) hf
  have _ : IsAdicHom (algebraMap (Completion LA) (Completion LC)) :=
    isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
      SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
      (inferInstance : IsAdicHom (algebraMap A C)) hg
  let _ := locUniformSpace PD TD sD LD hdenD
  have _ := isUniformAddGroup_locUniformSpace PD TD sD LD hdenD
  have _ := isTopologicalRing_locUniformSpace PD TD sD LD hdenD
  intro z
  dsimp only [Pair.completedTensorRationalSpaHomeomorph]
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.setCongr_apply]
  dsimp only
  rw [spaCompletedLocalizationHomeomorph_apply, spaLocToRationalSubset_val, spaComapLoc_val,
    spaHomeomorphOfRingEquiv_symm_val,
    ← Function.comp_apply (f := comap (toCompletionLoc PD TD sD LD hdenD)), ← comap_comp]

/-- Compatibility of `Pair.completedTensorRationalSpaHomeomorph` with the left completed tensor
projection onto `Spa (B, B⁺)`. -/
theorem Pair.inl_spaComap_completedTensorRationalSpaHomeomorph
    (hPB : PB.ringOfDefinition ≤ SB.plus)
    (hPC : PC.ringOfDefinition ≤ SC.plus)
    (hPD : PD.ringOfDefinition ≤ (SB.completedTensor A SC).plus)
    (hf : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset SB.plus TB sB) (rationalSubset SA.plus TA sA))
    (hg : Set.MapsTo (comap (algebraMap A C))
      (rationalSubset SC.plus TC sC) (rationalSubset SA.plus TA sA))
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC))) :
    letI := locUniformSpace PA TA sA LA hdenA
    letI := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
    letI := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
    letI := locUniformSpace PB TB sB LB hdenB
    letI := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
    letI := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
    letI := isHuberRing_completion_locTopology PB TB sB LB hdenB
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
    letI := isHuberRing_completion_locTopology PC TC sC LC hdenC
    letI : Algebra (Completion LA) (Completion LB) :=
      (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
        SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
        (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).toAlgebra
    letI : Algebra (Completion LA) (Completion LC) :=
      (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
        SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
        (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).toAlgebra
    haveI : IsAdicHom (algebraMap (Completion LA) (Completion LB)) :=
      isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
        SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
        (inferInstance : IsAdicHom (algebraMap A B)) hf
    haveI : IsAdicHom (algebraMap (Completion LA) (Completion LC)) :=
      isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
        SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
        (inferInstance : IsAdicHom (algebraMap A C)) hg
    ∀ z : spa ((PB.rationalLocalizationPair SB hPB TB sB LB hdenB).completedTensor (Completion LA)
        (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).plus,
      (Pair.completedTensor.inl A SB SC).spaComap
          (Pair.completedTensorRationalSpaHomeomorph PA SA TA sA LA hdenA PB SB TB sB LB hdenB
            PC SC TC sC LC hdenC PD TD sD LD hdenD hPB hPC hPD hf hg hd z).1 =
        spaComapLoc PB SB.plus TB sB LB hdenB
          ⟨((Pair.completedTensor.inl (Completion LA)
              (PB.rationalLocalizationPair SB hPB TB sB LB hdenB)
              (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).spaComap z).1,
            by
              rw [← rationalLocalizationPair_plus PB SB hPB TB sB LB hdenB]
              exact ((Pair.completedTensor.inl (Completion LA)
                (PB.rationalLocalizationPair SB hPB TB sB LB hdenB)
                (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).spaComap z).2⟩ := by
  let _ := locUniformSpace PA TA sA LA hdenA
  have _ := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
  have _ := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
  let _ := locUniformSpace PB TB sB LB hdenB
  have _ := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
  have _ := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
  have _ := isHuberRing_completion_locTopology PB TB sB LB hdenB
  let _ := locUniformSpace PC TC sC LC hdenC
  have _ := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
  have _ := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
  have _ := isHuberRing_completion_locTopology PC TC sC LC hdenC
  let _ : Algebra (Completion LA) (Completion LB) :=
    (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
      SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
      (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).toAlgebra
  let _ : Algebra (Completion LA) (Completion LC) :=
    (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
      SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
      (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).toAlgebra
  have _ : IsAdicHom (algebraMap (Completion LA) (Completion LB)) :=
    isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
      SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
      (inferInstance : IsAdicHom (algebraMap A B)) hf
  have _ : IsAdicHom (algebraMap (Completion LA) (Completion LC)) :=
    isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
      SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
      (inferInstance : IsAdicHom (algebraMap A C)) hg
  let _ := locUniformSpace PD TD sD LD hdenD
  have _ := isUniformAddGroup_locUniformSpace PD TD sD LD hdenD
  have _ := isTopologicalRing_locUniformSpace PD TD sD LD hdenD
  intro z
  apply Subtype.ext
  simp only [Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inl,
    Pair.completedTensorRationalSpaHomeomorph_val_val, spaComapLoc_val]
  rw [← Function.comp_apply (f := comap (CompletedTensor.inl A B C)), ← comap_comp,
    ← Function.comp_apply (f := comap (toCompletionLoc PB TB sB LB hdenB)), ← comap_comp]
  refine congrFun (congrArg comap ?_) z.1
  ext b
  simp [toCompletionLoc_apply]

/-- Compatibility of `Pair.completedTensorRationalSpaHomeomorph` with the right completed tensor
projection onto `Spa (C, C⁺)`. -/
theorem Pair.inr_spaComap_completedTensorRationalSpaHomeomorph
    (hPB : PB.ringOfDefinition ≤ SB.plus)
    (hPC : PC.ringOfDefinition ≤ SC.plus)
    (hPD : PD.ringOfDefinition ≤ (SB.completedTensor A SC).plus)
    (hf : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset SB.plus TB sB) (rationalSubset SA.plus TA sA))
    (hg : Set.MapsTo (comap (algebraMap A C))
      (rationalSubset SC.plus TC sC) (rationalSubset SA.plus TA sA))
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC))) :
    letI := locUniformSpace PA TA sA LA hdenA
    letI := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
    letI := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
    letI := locUniformSpace PB TB sB LB hdenB
    letI := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
    letI := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
    letI := isHuberRing_completion_locTopology PB TB sB LB hdenB
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
    letI := isHuberRing_completion_locTopology PC TC sC LC hdenC
    letI : Algebra (Completion LA) (Completion LB) :=
      (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
        SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
        (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).toAlgebra
    letI : Algebra (Completion LA) (Completion LC) :=
      (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
        SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
        (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).toAlgebra
    haveI : IsAdicHom (algebraMap (Completion LA) (Completion LB)) :=
      isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
        SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
        (inferInstance : IsAdicHom (algebraMap A B)) hf
    haveI : IsAdicHom (algebraMap (Completion LA) (Completion LC)) :=
      isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
        SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
        (inferInstance : IsAdicHom (algebraMap A C)) hg
    ∀ z : spa ((PB.rationalLocalizationPair SB hPB TB sB LB hdenB).completedTensor (Completion LA)
        (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).plus,
      (Pair.completedTensor.inr A SB SC).spaComap
          (Pair.completedTensorRationalSpaHomeomorph PA SA TA sA LA hdenA PB SB TB sB LB hdenB
            PC SC TC sC LC hdenC PD TD sD LD hdenD hPB hPC hPD hf hg hd z).1 =
        spaComapLoc PC SC.plus TC sC LC hdenC
          ⟨((Pair.completedTensor.inr (Completion LA)
              (PB.rationalLocalizationPair SB hPB TB sB LB hdenB)
              (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).spaComap z).1,
            by
              rw [← rationalLocalizationPair_plus PC SC hPC TC sC LC hdenC]
              exact ((Pair.completedTensor.inr (Completion LA)
                (PB.rationalLocalizationPair SB hPB TB sB LB hdenB)
                (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).spaComap z).2⟩ := by
  let _ := locUniformSpace PA TA sA LA hdenA
  have _ := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
  have _ := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
  let _ := locUniformSpace PB TB sB LB hdenB
  have _ := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
  have _ := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
  have _ := isHuberRing_completion_locTopology PB TB sB LB hdenB
  let _ := locUniformSpace PC TC sC LC hdenC
  have _ := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
  have _ := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
  have _ := isHuberRing_completion_locTopology PC TC sC LC hdenC
  let _ : Algebra (Completion LA) (Completion LB) :=
    (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
      SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
      (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).toAlgebra
  let _ : Algebra (Completion LA) (Completion LC) :=
    (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
      SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
      (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).toAlgebra
  have _ : IsAdicHom (algebraMap (Completion LA) (Completion LB)) :=
    isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
      SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
      (inferInstance : IsAdicHom (algebraMap A B)) hf
  have _ : IsAdicHom (algebraMap (Completion LA) (Completion LC)) :=
    isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
      SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
      (inferInstance : IsAdicHom (algebraMap A C)) hg
  let _ := locUniformSpace PD TD sD LD hdenD
  have _ := isUniformAddGroup_locUniformSpace PD TD sD LD hdenD
  have _ := isTopologicalRing_locUniformSpace PD TD sD LD hdenD
  intro z
  apply Subtype.ext
  simp only [Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inr,
    Pair.completedTensorRationalSpaHomeomorph_val_val, spaComapLoc_val]
  rw [← Function.comp_apply (f := comap (CompletedTensor.inr A B C)), ← comap_comp,
    ← Function.comp_apply (f := comap (toCompletionLoc PC TC sC LC hdenC)), ← comap_comp]
  refine congrFun (congrArg comap ?_) z.1
  ext c
  simp [toCompletionLoc_apply]

/-- Preimage under `Pair.completedTensorRationalSpaHomeomorph` carries rational subsets of
`Spa ((B, B⁺) ⊗̂_A (C, C⁺))` to rational subsets of the completed tensor spectrum. -/
theorem Pair.completedTensorRationalSpaHomeomorph_preimage_mem_spaRationalFamily
    (hPB : PB.ringOfDefinition ≤ SB.plus)
    (hPC : PC.ringOfDefinition ≤ SC.plus)
    (hPD : PD.ringOfDefinition ≤ (SB.completedTensor A SC).plus)
    (hf : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset SB.plus TB sB) (rationalSubset SA.plus TA sA))
    (hg : Set.MapsTo (comap (algebraMap A C))
      (rationalSubset SC.plus TC sC) (rationalSubset SA.plus TA sA))
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC)))
    {Z : Set (spa (SB.completedTensor A SC).plus)}
    (hZ : Z ∈ spaRationalFamily (SB.completedTensor A SC).plus) :
    letI := locUniformSpace PA TA sA LA hdenA
    letI := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
    letI := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
    letI := locUniformSpace PB TB sB LB hdenB
    letI := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
    letI := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
    letI := isHuberRing_completion_locTopology PB TB sB LB hdenB
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
    letI := isHuberRing_completion_locTopology PC TC sC LC hdenC
    letI : Algebra (Completion LA) (Completion LB) :=
      (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
        SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
        (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).toAlgebra
    letI : Algebra (Completion LA) (Completion LC) :=
      (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
        SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
        (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).toAlgebra
    haveI : IsAdicHom (algebraMap (Completion LA) (Completion LB)) :=
      isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
        SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
        (inferInstance : IsAdicHom (algebraMap A B)) hf
    haveI : IsAdicHom (algebraMap (Completion LA) (Completion LC)) :=
      isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
        SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
        (inferInstance : IsAdicHom (algebraMap A C)) hg
    Pair.completedTensorRationalSpaHomeomorph PA SA TA sA LA hdenA PB SB TB sB LB hdenB
        PC SC TC sC LC hdenC PD TD sD LD hdenD hPB hPC hPD hf hg hd ⁻¹' (Subtype.val ⁻¹' Z) ∈
      spaRationalFamily
        ((PB.rationalLocalizationPair SB hPB TB sB LB hdenB).completedTensor (Completion LA)
          (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).plus := by
  let _ := locUniformSpace PA TA sA LA hdenA
  have _ := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
  have _ := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
  let _ := locUniformSpace PB TB sB LB hdenB
  have _ := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
  have _ := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
  have _ := isHuberRing_completion_locTopology PB TB sB LB hdenB
  let _ := locUniformSpace PC TC sC LC hdenC
  have _ := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
  have _ := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
  have _ := isHuberRing_completion_locTopology PC TC sC LC hdenC
  let _ : Algebra (Completion LA) (Completion LB) :=
    (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
      SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
      (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).toAlgebra
  let _ : Algebra (Completion LA) (Completion LC) :=
    (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
      SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
      (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).toAlgebra
  have _ : IsAdicHom (algebraMap (Completion LA) (Completion LB)) :=
    isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
      SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
      (inferInstance : IsAdicHom (algebraMap A B)) hf
  have _ : IsAdicHom (algebraMap (Completion LA) (Completion LC)) :=
    isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
      SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
      (inferInstance : IsAdicHom (algebraMap A C)) hg
  let _ := locUniformSpace PD TD sD LD hdenD
  have _ := isUniformAddGroup_locUniformSpace PD TD sD LD hdenD
  have _ := isTopologicalRing_locUniformSpace PD TD sD LD hdenD
  convert spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily
      (Pair.completedTensorRationalEquiv PA SA TA sA LA hdenA PB SB TB sB LB hdenB
        PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd).symm
      (Pair.continuous_completedTensorRationalEquiv_symm PA SA TA sA LA hdenA PB SB TB sB LB hdenB
        PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd)
      (Pair.continuous_completedTensorRationalEquiv PA SA TA sA LA hdenA PB SB TB sB LB hdenB
        PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd)
      (fun y hy ↦ (Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
        PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
        PD TD sD LD hdenD hPB hPC hf hg hd _).mp (by simpa using hy))
      (fun x hx ↦ (Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
        PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
        PD TD sD LD hdenD hPB hPC hf hg hd x).mpr hx)
      (spaCompletedLocalizationHomeomorph_preimage_mem_spaRationalFamily
        PD (SB.completedTensor A SC).plus hPD TD sD LD hdenD hZ) using 1
  ext x
  simp only [Pair.completedTensorRationalSpaHomeomorph, Set.mem_preimage, Homeomorph.trans_apply,
    Homeomorph.setCongr_apply, spaHomeomorphOfRingEquiv_symm]

/-- **Rational subsets match across `Pair.completedTensorRationalSpaHomeomorph`**
(Huber Lemma 1.5(ii); Wedhorn Proposition 8.2(2)): when `T_D` generates an open ideal in
`B ⊗̂_A C`, preimage under `completedTensorRationalSpaHomeomorph` bijects the rational subsets of
`Spa ((B, B⁺) ⊗̂_A (C, C⁺))` contained in `p_B⁻¹(U) ∩ p_C⁻¹(V)` onto the rational subsets of
`Spa ((O_B(U), O_B(U)⁺) ⊗̂_{O_A(W)} (O_C(V), O_C(V)⁺))`. -/
theorem Pair.bijOn_preimage_completedTensorRationalSpaHomeomorph_spaRationalFamily
    (hPB : PB.ringOfDefinition ≤ SB.plus)
    (hPC : PC.ringOfDefinition ≤ SC.plus)
    (hPD : PD.ringOfDefinition ≤ (SB.completedTensor A SC).plus)
    (hTD : IsOpen (Ideal.span (TD : Set (CompletedTensor A B C)) : Set (CompletedTensor A B C)))
    (hf : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset SB.plus TB sB) (rationalSubset SA.plus TA sA))
    (hg : Set.MapsTo (comap (algebraMap A C))
      (rationalSubset SC.plus TC sC) (rationalSubset SA.plus TA sA))
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC))) :
    letI := locUniformSpace PA TA sA LA hdenA
    letI := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
    letI := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
    letI := locUniformSpace PB TB sB LB hdenB
    letI := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
    letI := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
    letI := isHuberRing_completion_locTopology PB TB sB LB hdenB
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
    letI := isHuberRing_completion_locTopology PC TC sC LC hdenC
    letI : Algebra (Completion LA) (Completion LB) :=
      (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
        SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
        (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).toAlgebra
    letI : Algebra (Completion LA) (Completion LC) :=
      (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
        SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
        (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).toAlgebra
    haveI : IsAdicHom (algebraMap (Completion LA) (Completion LB)) :=
      isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
        SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
        (inferInstance : IsAdicHom (algebraMap A B)) hf
    haveI : IsAdicHom (algebraMap (Completion LA) (Completion LC)) :=
      isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
        SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
        (inferInstance : IsAdicHom (algebraMap A C)) hg
    Set.BijOn
      (fun Z : Set (spa (SB.completedTensor A SC).plus) ↦
        Pair.completedTensorRationalSpaHomeomorph PA SA TA sA LA hdenA PB SB TB sB LB hdenB
          PC SC TC sC LC hdenC PD TD sD LD hdenD hPB hPC hPD hf hg hd ⁻¹' (Subtype.val ⁻¹' Z))
      {Z ∈ spaRationalFamily (SB.completedTensor A SC).plus |
        Z ⊆ ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
            (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
          ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
            (Subtype.val ⁻¹' rationalSubset SC.plus TC sC))}
      (spaRationalFamily
        ((PB.rationalLocalizationPair SB hPB TB sB LB hdenB).completedTensor (Completion LA)
          (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).plus) := by
  let _ := locUniformSpace PA TA sA LA hdenA
  have _ := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
  have _ := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
  let _ := locUniformSpace PB TB sB LB hdenB
  have _ := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
  have _ := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
  have _ := isHuberRing_completion_locTopology PB TB sB LB hdenB
  let _ := locUniformSpace PC TC sC LC hdenC
  have _ := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
  have _ := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
  have _ := isHuberRing_completion_locTopology PC TC sC LC hdenC
  let _ : Algebra (Completion LA) (Completion LB) :=
    (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
      SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
      (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).toAlgebra
  let _ : Algebra (Completion LA) (Completion LC) :=
    (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
      SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
      (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).toAlgebra
  have _ : IsAdicHom (algebraMap (Completion LA) (Completion LB)) :=
    isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
      SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
      (inferInstance : IsAdicHom (algebraMap A B)) hf
  have _ : IsAdicHom (algebraMap (Completion LA) (Completion LC)) :=
    isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
      SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
      (inferInstance : IsAdicHom (algebraMap A C)) hg
  let _ := locUniformSpace PD TD sD LD hdenD
  have _ := isUniformAddGroup_locUniformSpace PD TD sD LD hdenD
  have _ := isTopologicalRing_locUniformSpace PD TD sD LD hdenD
  let e := Pair.completedTensorRationalEquiv PA SA TA sA LA hdenA PB SB TB sB LB hdenB
    PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd
  have hdom :
      {Z ∈ spaRationalFamily (SB.completedTensor A SC).plus |
        Z ⊆ ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
            (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
          ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
            (Subtype.val ⁻¹' rationalSubset SC.plus TC sC))} =
      {Z ∈ spaRationalFamily (SB.completedTensor A SC).plus |
        Z ⊆ Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD} := by
    rw [hd]
  rw [hdom]
  have hb₁ := bijOn_preimage_spaHomeomorphOfRingEquiv_spaRationalFamily e.symm
    (Pair.continuous_completedTensorRationalEquiv_symm PA SA TA sA LA hdenA PB SB TB sB LB hdenB
      PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd)
    (Pair.continuous_completedTensorRationalEquiv PA SA TA sA LA hdenA PB SB TB sB LB hdenB
      PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd)
    (fun y hy ↦ (Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
      PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
      PD TD sD LD hdenD hPB hPC hf hg hd (e.symm y)).mp (by simpa [e] using hy))
    (fun x hx ↦ (Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
      PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
      PD TD sD LD hdenD hPB hPC hf hg hd x).mpr hx)
  have hb₂ := bijOn_preimage_spaCompletedLocalizationHomeomorph_spaRationalFamily
    PD (SB.completedTensor A SC).plus hPD TD sD hTD LD hdenD
  refine (hb₁.comp hb₂).congr fun Z _ ↦ ?_
  ext x
  simp only [Function.comp_apply, Pair.completedTensorRationalSpaHomeomorph, Set.mem_preimage,
    Homeomorph.trans_apply, Homeomorph.setCongr_apply, spaHomeomorphOfRingEquiv_symm]
  exact Iff.rfl

/-- Image under `Pair.completedTensorRationalSpaHomeomorph` in `Spa ((B, B⁺) ⊗̂_A (C, C⁺))` of a
rational subset of the completed tensor spectrum is again a rational subset when `T_D` generates an
open ideal. -/
theorem Pair.completedTensorRationalSpaHomeomorph_image_mem_spaRationalFamily
    (hPB : PB.ringOfDefinition ≤ SB.plus)
    (hPC : PC.ringOfDefinition ≤ SC.plus)
    (hPD : PD.ringOfDefinition ≤ (SB.completedTensor A SC).plus)
    (hTD : IsOpen (Ideal.span (TD : Set (CompletedTensor A B C)) : Set (CompletedTensor A B C)))
    (hf : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset SB.plus TB sB) (rationalSubset SA.plus TA sA))
    (hg : Set.MapsTo (comap (algebraMap A C))
      (rationalSubset SC.plus TC sC) (rationalSubset SA.plus TA sA))
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC))) :
    letI := locUniformSpace PA TA sA LA hdenA
    letI := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
    letI := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
    letI := locUniformSpace PB TB sB LB hdenB
    letI := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
    letI := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
    letI := isHuberRing_completion_locTopology PB TB sB LB hdenB
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
    letI := isHuberRing_completion_locTopology PC TC sC LC hdenC
    letI : Algebra (Completion LA) (Completion LB) :=
      (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
        SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
        (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).toAlgebra
    letI : Algebra (Completion LA) (Completion LC) :=
      (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
        SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
        (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).toAlgebra
    haveI : IsAdicHom (algebraMap (Completion LA) (Completion LB)) :=
      isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
        SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
        (inferInstance : IsAdicHom (algebraMap A B)) hf
    haveI : IsAdicHom (algebraMap (Completion LA) (Completion LC)) :=
      isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
        SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
        (inferInstance : IsAdicHom (algebraMap A C)) hg
    ∀ {Y : Set (spa
        ((PB.rationalLocalizationPair SB hPB TB sB LB hdenB).completedTensor (Completion LA)
          (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).plus)},
      Y ∈ spaRationalFamily
        ((PB.rationalLocalizationPair SB hPB TB sB LB hdenB).completedTensor (Completion LA)
          (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).plus →
      Subtype.val ''
          (Pair.completedTensorRationalSpaHomeomorph PA SA TA sA LA hdenA PB SB TB sB LB hdenB
            PC SC TC sC LC hdenC PD TD sD LD hdenD hPB hPC hPD hf hg hd '' Y) ∈
        spaRationalFamily (SB.completedTensor A SC).plus := by
  let _ := locUniformSpace PA TA sA LA hdenA
  have _ := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
  have _ := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
  let _ := locUniformSpace PB TB sB LB hdenB
  have _ := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
  have _ := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
  have _ := isHuberRing_completion_locTopology PB TB sB LB hdenB
  let _ := locUniformSpace PC TC sC LC hdenC
  have _ := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
  have _ := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
  have _ := isHuberRing_completion_locTopology PC TC sC LC hdenC
  let _ : Algebra (Completion LA) (Completion LB) :=
    (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
      SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
      (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).toAlgebra
  let _ : Algebra (Completion LA) (Completion LC) :=
    (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
      SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
      (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).toAlgebra
  have _ : IsAdicHom (algebraMap (Completion LA) (Completion LB)) :=
    isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
      SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
      (inferInstance : IsAdicHom (algebraMap A B)) hf
  have _ : IsAdicHom (algebraMap (Completion LA) (Completion LC)) :=
    isAdicHom_ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
      SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
      (inferInstance : IsAdicHom (algebraMap A C)) hg
  intro Y hY
  obtain ⟨Z, ⟨hZ, hZsub⟩, rfl⟩ :=
    (Pair.bijOn_preimage_completedTensorRationalSpaHomeomorph_spaRationalFamily
      PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
      PD TD sD LD hdenD hPB hPC hPD hTD hf hg hd).surjOn hY
  rw [Set.image_preimage_eq _
      (Pair.completedTensorRationalSpaHomeomorph PA SA TA sA LA hdenA PB SB TB sB LB hdenB
        PC SC TC sC LC hdenC PD TD sD LD hdenD hPB hPC hPD hf hg hd).surjective,
    Subtype.image_preimage_coe, Set.inter_eq_self_of_subset_right hZsub]
  exact hZ

end TauCeti.Huber

end
