/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.BaseChange
public import TauCeti.RingTheory.Huber.TensorProduct.Pushout

/-!
# Completed pushout of rational localisation Huber pairs

Let `f : (A, A⁺) → (B, B⁺)` and `g : (A, A⁺) → (C, C⁺)` be morphisms of Huber pairs whose
underlying ring homomorphisms `A → B` and `A → C` are adic, and let
`(D, D⁺) = (B, B⁺) ⊗̂_A (C, C⁺)` be Huber's completed tensor product.

Given rational subsets `U = R(T_B / s_B) ⊆ Spa(B, B⁺)`, `V = R(T_C / s_C) ⊆ Spa(C, C⁺)`, and
`W = R(T_A / s_A) ⊆ Spa(A, A⁺)` with `f.spaComap(U) ⊆ W` and `g.spaComap(V) ⊆ W`, let `O(W)`,
`O(U)`, and `O(V)` be the corresponding completed rational localisation Huber pairs
(`rationalLocalizationPair`). For *any* presentation `(T_D, s_D)` on `D` whose rational subset
equals `p_B ⁻¹' U ∩ p_C ⁻¹' V`, we construct:

* the canonical localized leg morphisms `completedTensorRationalLeftHom : O(U) → O_D(T_D / s_D)`
  and `completedTensorRationalRightHom : O(V) → O_D(T_D / s_D)` extending `ρ_D ∘ inl` and
  `ρ_D ∘ inr`, and prove they commute with the adic base-change maps `O(W) → O(U)` and
  `O(W) → O(V)` (`completedTensorRationalLeftHom_comp_eq_rightHom_comp`);
* the mutually inverse morphisms of Huber pairs
  `completedTensorRationalToLocHom : O(U) ⊗̂_{O(W)} O(V) → O_D(T_D / s_D)` and
  `completedTensorRationalOfLocHom : O_D(T_D / s_D) → O(U) ⊗̂_{O(W)} O(V)` purely from the
  universal properties `rationalLocalizationLift` and `Pair.completedTensor.lift`, without
  assuming completeness or sheafiness of `A`, `B`, or `C`;
* the completed pushout property `isCompletedPushout_rationalLocalizationPair` for the localized
  square `O(W) → O(U), O(V) → O_D(T_D / s_D)`.

## Main definitions

* `TauCeti.Huber.Pair.completedTensorRationalLeftHom`,
  `TauCeti.Huber.Pair.completedTensorRationalRightHom`: the canonical Huber-pair morphisms
  `O(U) → O_D(T_D / s_D)` and `O(V) → O_D(T_D / s_D)`.
* `TauCeti.Huber.Pair.completedTensorRationalToLocHom`,
  `TauCeti.Huber.Pair.completedTensorRationalOfLocHom`: the mutually inverse morphisms of Huber
  pairs between `O(U) ⊗̂_{O(W)} O(V)` and `O_D(T_D / s_D)`.

## Main results

* `TauCeti.Huber.Pair.completedTensorRationalToLocHom_comp_ofLocHom`,
  `TauCeti.Huber.Pair.completedTensorRationalOfLocHom_comp_toLocHom`: the two composites are
  `Hom.id`.
* `TauCeti.Huber.Pair.isCompletedPushout_rationalLocalizationPair`: the localized square of Huber
  pairs is a completed pushout.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, after Definition 2.4.12.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.1 and Proposition 8.2(2).
-/

public section

open UniformSpace

namespace TauCeti.Huber.Pair

open TauCeti.Huber.PairOfDefinition TauCeti.ValuationSpectrum

section Legs

variable {A B C : Type*}
  [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

section Left

variable (QB : PairOfDefinition B) (PB : Pair B) (hQB : QB.ringOfDefinition ≤ PB.plus)
  (TB : Finset B) (sB : B) (SB : Type*) [CommRing SB] [Algebra B SB] [IsLocalization.Away sB SB]
  (hdenB : HasDenominatorPower QB TB sB SB)
  (PC : Pair C) (TC : Finset C) (sC : C)
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

include hD_eq

/-- The canonical left localized morphism `O(U) → O_D(T_D / s_D)` extending `ρ_D ∘ inl`. -/
noncomputable def completedTensorRationalLeftHom :
    letI := locUniformSpace QB TB sB SB hdenB
    letI := isUniformAddGroup_locUniformSpace QB TB sB SB hdenB
    letI := isTopologicalRing_locUniformSpace QB TB sB SB hdenB
    letI := isHuberRing_completion_locTopology QB TB sB SB hdenB
    letI := locUniformSpace QD TD sD SD hdenD
    letI := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
    letI := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    Hom (rationalLocalizationPair QB PB hQB TB sB SB hdenB)
      (rationalLocalizationPair QD (PB.completedTensor A PC) hQD TD sD SD hdenD) :=
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  rationalLocalizationLift QB PB hQB TB sB SB hdenB
    ((toCompletionLocHom QD (PB.completedTensor A PC) hQD TD sD SD hdenD).comp
      (completedTensor.inl A PB PC))
    (fun z ↦ by
      have hz := toCompletionLocHom_spaComap_mem_rationalSubset QD (PB.completedTensor A PC) hQD
        TD sD SD hdenD z
      rw [hD_eq] at hz
      rw [Hom.spaComap_comp, Function.comp_apply]
      exact hz.1)

/-- `completedTensorRationalLeftHom` restricts along `toCompletionLocHom` to `ρ_D ∘ inl`. -/
@[simp]
theorem completedTensorRationalLeftHom_comp_toCompletionLocHom :
    letI := locUniformSpace QB TB sB SB hdenB
    letI := isUniformAddGroup_locUniformSpace QB TB sB SB hdenB
    letI := isTopologicalRing_locUniformSpace QB TB sB SB hdenB
    letI := isHuberRing_completion_locTopology QB TB sB SB hdenB
    letI := locUniformSpace QD TD sD SD hdenD
    letI := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
    letI := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    (completedTensorRationalLeftHom QB PB hQB TB sB SB hdenB PC TC sC QD hQD TD sD SD hdenD
        hD_eq).comp (toCompletionLocHom QB PB hQB TB sB SB hdenB) =
      (toCompletionLocHom QD (PB.completedTensor A PC) hQD TD sD SD hdenD).comp
        (completedTensor.inl A PB PC) := by
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  exact rationalLocalizationLift_comp_toCompletionLocHom QB PB hQB TB sB SB hdenB _ _

/-- Ring-homomorphism form of `completedTensorRationalLeftHom_comp_toCompletionLocHom`. -/
@[simp]
theorem toRingHom_completedTensorRationalLeftHom_comp_toCompletionLoc :
    letI := locUniformSpace QB TB sB SB hdenB
    letI := isUniformAddGroup_locUniformSpace QB TB sB SB hdenB
    letI := isTopologicalRing_locUniformSpace QB TB sB SB hdenB
    letI := isHuberRing_completion_locTopology QB TB sB SB hdenB
    letI := locUniformSpace QD TD sD SD hdenD
    letI := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
    letI := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    (completedTensorRationalLeftHom QB PB hQB TB sB SB hdenB PC TC sC QD hQD TD sD SD hdenD
        hD_eq).toRingHom.comp (toCompletionLoc QB TB sB SB hdenB) =
      (toCompletionLoc QD TD sD SD hdenD).comp (CompletedTensor.inl A B C) := by
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  simpa only [Hom.toRingHom_comp, toRingHom_toCompletionLocHom, completedTensor.toRingHom_inl]
    using congrArg Hom.toRingHom
      (completedTensorRationalLeftHom_comp_toCompletionLocHom QB PB hQB TB sB SB hdenB PC TC sC
        QD hQD TD sD SD hdenD hD_eq)

end Left

section Right

variable (PB : Pair B) (TB : Finset B) (sB : B)
  (QC : PairOfDefinition C) (PC : Pair C) (hQC : QC.ringOfDefinition ≤ PC.plus)
  (TC : Finset C) (sC : C) (SC : Type*) [CommRing SC] [Algebra C SC] [IsLocalization.Away sC SC]
  (hdenC : HasDenominatorPower QC TC sC SC)
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

include hD_eq

/-- The canonical right localized morphism `O(V) → O_D(T_D / s_D)` extending `ρ_D ∘ inr`. -/
noncomputable def completedTensorRationalRightHom :
    letI := locUniformSpace QC TC sC SC hdenC
    letI := isUniformAddGroup_locUniformSpace QC TC sC SC hdenC
    letI := isTopologicalRing_locUniformSpace QC TC sC SC hdenC
    letI := isHuberRing_completion_locTopology QC TC sC SC hdenC
    letI := locUniformSpace QD TD sD SD hdenD
    letI := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
    letI := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    Hom (rationalLocalizationPair QC PC hQC TC sC SC hdenC)
      (rationalLocalizationPair QD (PB.completedTensor A PC) hQD TD sD SD hdenD) :=
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  rationalLocalizationLift QC PC hQC TC sC SC hdenC
    ((toCompletionLocHom QD (PB.completedTensor A PC) hQD TD sD SD hdenD).comp
      (completedTensor.inr A PB PC))
    (fun z ↦ by
      have hz := toCompletionLocHom_spaComap_mem_rationalSubset QD (PB.completedTensor A PC) hQD
        TD sD SD hdenD z
      rw [hD_eq] at hz
      rw [Hom.spaComap_comp, Function.comp_apply]
      exact hz.2)

/-- `completedTensorRationalRightHom` restricts along `toCompletionLocHom` to `ρ_D ∘ inr`. -/
@[simp]
theorem completedTensorRationalRightHom_comp_toCompletionLocHom :
    letI := locUniformSpace QC TC sC SC hdenC
    letI := isUniformAddGroup_locUniformSpace QC TC sC SC hdenC
    letI := isTopologicalRing_locUniformSpace QC TC sC SC hdenC
    letI := isHuberRing_completion_locTopology QC TC sC SC hdenC
    letI := locUniformSpace QD TD sD SD hdenD
    letI := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
    letI := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    (completedTensorRationalRightHom PB TB sB QC PC hQC TC sC SC hdenC QD hQD TD sD SD hdenD
        hD_eq).comp (toCompletionLocHom QC PC hQC TC sC SC hdenC) =
      (toCompletionLocHom QD (PB.completedTensor A PC) hQD TD sD SD hdenD).comp
        (completedTensor.inr A PB PC) := by
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  exact rationalLocalizationLift_comp_toCompletionLocHom QC PC hQC TC sC SC hdenC _ _

/-- Ring-homomorphism form of `completedTensorRationalRightHom_comp_toCompletionLocHom`. -/
@[simp]
theorem toRingHom_completedTensorRationalRightHom_comp_toCompletionLoc :
    letI := locUniformSpace QC TC sC SC hdenC
    letI := isUniformAddGroup_locUniformSpace QC TC sC SC hdenC
    letI := isTopologicalRing_locUniformSpace QC TC sC SC hdenC
    letI := isHuberRing_completion_locTopology QC TC sC SC hdenC
    letI := locUniformSpace QD TD sD SD hdenD
    letI := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
    letI := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    (completedTensorRationalRightHom PB TB sB QC PC hQC TC sC SC hdenC QD hQD TD sD SD hdenD
        hD_eq).toRingHom.comp (toCompletionLoc QC TC sC SC hdenC) =
      (toCompletionLoc QD TD sD SD hdenD).comp (CompletedTensor.inr A B C) := by
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  simpa only [Hom.toRingHom_comp, toRingHom_toCompletionLocHom, completedTensor.toRingHom_inr]
    using congrArg Hom.toRingHom
      (completedTensorRationalRightHom_comp_toCompletionLocHom PB TB sB QC PC hQC TC sC SC hdenC
        QD hQD TD sD SD hdenD hD_eq)

end Right

end Legs

section Iso

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

include hQA hdenA hQB hdenB hQC hdenC hf_alg hg_alg hf_sub hg_sub

/-- Unlocalized tensor morphism `(B, B⁺) ⊗̂_A (C, C⁺) → O(U) ⊗̂_{O(W)} O(V)`. -/
private noncomputable def completedTensorToLocalizedTensorHom :
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
    Hom (PB.completedTensor A PC)
      ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor (Completion SA)
        (rationalLocalizationPair QC PC hQC TC sC SC hdenC)) :=
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
  let fLoc := rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB hf_sub
  let gLoc := rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC hg_sub
  let _ : Algebra (Completion SA) (Completion SB) := fLoc.toRingHom.toAlgebra
  let _ : Algebra (Completion SA) (Completion SC) := gLoc.toRingHom.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion SA) (Completion SB)) :=
    isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
      hf_sub
  have _ : IsAdicHom (algebraMap (Completion SA) (Completion SC)) :=
    isAdicHom_rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
      hg_sub
  let OB := rationalLocalizationPair QB PB hQB TB sB SB hdenB
  let OC := rationalLocalizationPair QC PC hQC TC sC SC hdenC
  completedTensor.lift
    ((completedTensor.inl (Completion SA) OB OC).comp
      (toCompletionLocHom QB PB hQB TB sB SB hdenB))
    ((completedTensor.inr (Completion SA) OB OC).comp
      (toCompletionLocHom QC PC hQC TC sC SC hdenC))
    (by
      have hcomm :
          ((completedTensor.inl (Completion SA) OB OC).comp
              (toCompletionLocHom QB PB hQB TB sB SB hdenB)).comp f =
            ((completedTensor.inr (Completion SA) OB OC).comp
              (toCompletionLocHom QC PC hQC TC sC SC hdenC)).comp g := by
        calc
          ((completedTensor.inl (Completion SA) OB OC).comp
              (toCompletionLocHom QB PB hQB TB sB SB hdenB)).comp f
            = ((completedTensor.inl (Completion SA) OB OC).comp fLoc).comp
                (toCompletionLocHom QA PA hQA TA sA SA hdenA) := by
              rw [Hom.comp_assoc, ← rationalLocalizationPairMap_comp_toCompletionLocHom QA PA hQA
                TA sA SA hdenA QB PB hQB f TB sB SB hdenB hf_sub, ← Hom.comp_assoc]
          _ = ((completedTensor.inr (Completion SA) OB OC).comp gLoc).comp
                (toCompletionLocHom QA PA hQA TA sA SA hdenA) := by
              rw [completedTensor.inl_comp (f := fLoc) (g := gLoc) rfl rfl]
          _ = ((completedTensor.inr (Completion SA) OB OC).comp
              (toCompletionLocHom QC PC hQC TC sC SC hdenC)).comp g := by
              rw [Hom.comp_assoc, rationalLocalizationPairMap_comp_toCompletionLocHom QA PA hQA
                TA sA SA hdenA QC PC hQC g TC sC SC hdenC hg_sub, ← Hom.comp_assoc]
      simpa only [Hom.toRingHom_comp, hf_alg, hg_alg] using congrArg Hom.toRingHom hcomm)

variable (QD : PairOfDefinition (CompletedTensor A B C))
  (hQD : QD.ringOfDefinition ≤ (PB.completedTensor A PC).plus)
  (TD : Finset (CompletedTensor A B C)) (sD : CompletedTensor A B C)
  (SD : Type*) [CommRing SD] [Algebra (CompletedTensor A B C) SD] [IsLocalization.Away sD SD]
  (hdenD : HasDenominatorPower QD TD sD SD)
  (hD_eq : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus TD sD :
      Set (spa (PB.completedTensor A PC).plus)) =
    ((completedTensor.inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus TB sB)) ∩
      ((completedTensor.inr A PB PC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset PC.plus TC sC)))

include hQD hdenD hD_eq

/-- The left and right localized maps into `O_D(T_D / s_D)` commute with the base-change maps from
`O(W)`. -/
theorem completedTensorRationalLeftHom_comp_eq_rightHom_comp :
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
    letI := locUniformSpace QD TD sD SD hdenD
    letI := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
    letI := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    (completedTensorRationalLeftHom QB PB hQB TB sB SB hdenB PC TC sC QD hQD TD sD SD hdenD
        hD_eq).comp
      (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB hf_sub) =
    (completedTensorRationalRightHom PB TB sB QC PC hQC TC sC SC hdenC QD hQD TD sD SD hdenD
        hD_eq).comp
      (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC hg_sub) := by
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
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  refine pairHom_ext_of_comp_toCompletionLocHom QA PA hQA TA sA SA hdenA ?_
  calc
    ((completedTensorRationalLeftHom QB PB hQB TB sB SB hdenB PC TC sC QD hQD TD sD SD hdenD
          hD_eq).comp
        (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB
          hf_sub)).comp (toCompletionLocHom QA PA hQA TA sA SA hdenA)
      = (completedTensorRationalLeftHom QB PB hQB TB sB SB hdenB PC TC sC QD hQD TD sD SD hdenD
          hD_eq).comp ((toCompletionLocHom QB PB hQB TB sB SB hdenB).comp f) := by
          rw [Hom.comp_assoc, rationalLocalizationPairMap_comp_toCompletionLocHom]
    _ = ((toCompletionLocHom QD (PB.completedTensor A PC) hQD TD sD SD hdenD).comp
          (completedTensor.inl A PB PC)).comp f := by
          rw [← Hom.comp_assoc, completedTensorRationalLeftHom_comp_toCompletionLocHom]
    _ = ((toCompletionLocHom QD (PB.completedTensor A PC) hQD TD sD SD hdenD).comp
          (completedTensor.inr A PB PC)).comp g := by
          rw [Hom.comp_assoc, completedTensor.inl_comp hf_alg hg_alg, ← Hom.comp_assoc]
    _ = (completedTensorRationalRightHom PB TB sB QC PC hQC TC sC SC hdenC QD hQD TD sD SD hdenD
          hD_eq).comp ((toCompletionLocHom QC PC hQC TC sC SC hdenC).comp g) := by
          rw [← Hom.comp_assoc, completedTensorRationalRightHom_comp_toCompletionLocHom]
    _ = ((completedTensorRationalRightHom PB TB sB QC PC hQC TC sC SC hdenC QD hQD TD sD SD hdenD
          hD_eq).comp
        (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC
          hg_sub)).comp (toCompletionLocHom QA PA hQA TA sA SA hdenA) := by
          rw [Hom.comp_assoc, rationalLocalizationPairMap_comp_toCompletionLocHom]

/-- **The canonical forward morphism of Huber pairs**
`O(U) ⊗̂_{O(W)} O(V) → O_D(T_D / s_D)`. -/
noncomputable def completedTensorRationalToLocHom :
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
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    Hom ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor (Completion SA)
        (rationalLocalizationPair QC PC hQC TC sC SC hdenC))
      (rationalLocalizationPair QD (PB.completedTensor A PC) hQD TD sD SD hdenD) :=
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
  completedTensor.lift
    (completedTensorRationalLeftHom QB PB hQB TB sB SB hdenB PC TC sC QD hQD TD sD SD hdenD hD_eq)
    (completedTensorRationalRightHom PB TB sB QC PC hQC TC sC SC hdenC QD hQD TD sD SD hdenD hD_eq)
    (by
      simpa only [Hom.toRingHom_comp, RingHom.algebraMap_toAlgebra] using congrArg Hom.toRingHom
        (completedTensorRationalLeftHom_comp_eq_rightHom_comp QA PA hQA TA sA SA hdenA QB PB hQB
          TB sB SB hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD
          hdenD hD_eq))

/-- `completedTensorRationalToLocHom` restricts along `inl` to `completedTensorRationalLeftHom`. -/
@[simp]
theorem completedTensorRationalToLocHom_comp_inl :
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
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    (completedTensorRationalToLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).comp
      (completedTensor.inl (Completion SA) (rationalLocalizationPair QB PB hQB TB sB SB hdenB)
        (rationalLocalizationPair QC PC hQC TC sC SC hdenC)) =
      completedTensorRationalLeftHom QB PB hQB TB sB SB hdenB PC TC sC QD hQD TD sD SD hdenD
        hD_eq := by
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
  exact completedTensor.lift_comp_inl _ _ _

/-- `completedTensorRationalToLocHom` restricts along `inr` to `completedTensorRationalRightHom`. -/
@[simp]
theorem completedTensorRationalToLocHom_comp_inr :
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
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    (completedTensorRationalToLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).comp
      (completedTensor.inr (Completion SA) (rationalLocalizationPair QB PB hQB TB sB SB hdenB)
        (rationalLocalizationPair QC PC hQC TC sC SC hdenC)) =
      completedTensorRationalRightHom PB TB sB QC PC hQC TC sC SC hdenC QD hQD TD sD SD hdenD
        hD_eq := by
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
  exact completedTensor.lift_comp_inr _ _ _

/-- **The canonical inverse morphism of Huber pairs**
`O_D(T_D / s_D) → O(U) ⊗̂_{O(W)} O(V)`. -/
noncomputable def completedTensorRationalOfLocHom :
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
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    Hom (rationalLocalizationPair QD (PB.completedTensor A PC) hQD TD sD SD hdenD)
      ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor (Completion SA)
        (rationalLocalizationPair QC PC hQC TC sC SC hdenC)) :=
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
  rationalLocalizationLift QD (PB.completedTensor A PC) hQD TD sD SD hdenD
    (completedTensorToLocalizedTensorHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC
      hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub)
    (fun z ↦ by
      rw [hD_eq]
      constructor
      · rw [Set.mem_preimage, ← Function.comp_apply (f := (completedTensor.inl A PB PC).spaComap),
          ← Hom.spaComap_comp, completedTensorToLocalizedTensorHom, completedTensor.lift_comp_inl,
          Hom.spaComap_comp, Function.comp_apply]
        exact toCompletionLocHom_spaComap_mem_rationalSubset QB PB hQB TB sB SB hdenB _
      · rw [Set.mem_preimage, ← Function.comp_apply (f := (completedTensor.inr A PB PC).spaComap),
          ← Hom.spaComap_comp, completedTensorToLocalizedTensorHom, completedTensor.lift_comp_inr,
          Hom.spaComap_comp, Function.comp_apply]
        exact toCompletionLocHom_spaComap_mem_rationalSubset QC PC hQC TC sC SC hdenC _)

/-- Left universal-property equation characterizing `completedTensorRationalOfLocHom` on `B`. -/
theorem completedTensorRationalOfLocHom_comp_toCompletionLocHom_comp_inl :
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
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    ((completedTensorRationalOfLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).comp
      (toCompletionLocHom QD (PB.completedTensor A PC) hQD TD sD SD hdenD)).comp
      (completedTensor.inl A PB PC) =
      (completedTensor.inl (Completion SA) (rationalLocalizationPair QB PB hQB TB sB SB hdenB)
        (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).comp
        (toCompletionLocHom QB PB hQB TB sB SB hdenB) := by
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
  rw [completedTensorRationalOfLocHom, rationalLocalizationLift_comp_toCompletionLocHom,
    completedTensorToLocalizedTensorHom, completedTensor.lift_comp_inl]

/-- Right universal-property equation characterizing `completedTensorRationalOfLocHom` on `C`. -/
theorem completedTensorRationalOfLocHom_comp_toCompletionLocHom_comp_inr :
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
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    ((completedTensorRationalOfLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).comp
      (toCompletionLocHom QD (PB.completedTensor A PC) hQD TD sD SD hdenD)).comp
      (completedTensor.inr A PB PC) =
      (completedTensor.inr (Completion SA) (rationalLocalizationPair QB PB hQB TB sB SB hdenB)
        (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).comp
        (toCompletionLocHom QC PC hQC TC sC SC hdenC) := by
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
  rw [completedTensorRationalOfLocHom, rationalLocalizationLift_comp_toCompletionLocHom,
    completedTensorToLocalizedTensorHom, completedTensor.lift_comp_inr]

/-- `completedTensorRationalOfLocHom` is a right inverse of `completedTensorRationalToLocHom`. -/
@[simp]
theorem completedTensorRationalToLocHom_comp_ofLocHom :
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
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    (completedTensorRationalToLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).comp
      (completedTensorRationalOfLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq) =
      Hom.id _ := by
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
  refine pairHom_ext_of_comp_toCompletionLocHom QD (PB.completedTensor A PC) hQD TD sD SD hdenD ?_
  rw [Hom.id_comp, Hom.comp_assoc]
  refine completedTensor.hom_ext ?_ ?_
  · rw [Hom.comp_assoc, completedTensorRationalOfLocHom_comp_toCompletionLocHom_comp_inl,
      ← Hom.comp_assoc, completedTensorRationalToLocHom_comp_inl,
      completedTensorRationalLeftHom_comp_toCompletionLocHom]
  · rw [Hom.comp_assoc, completedTensorRationalOfLocHom_comp_toCompletionLocHom_comp_inr,
      ← Hom.comp_assoc, completedTensorRationalToLocHom_comp_inr,
      completedTensorRationalRightHom_comp_toCompletionLocHom]

/-- `completedTensorRationalOfLocHom` is a left inverse of `completedTensorRationalToLocHom`. -/
@[simp]
theorem completedTensorRationalOfLocHom_comp_toLocHom :
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
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    (completedTensorRationalOfLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).comp
      (completedTensorRationalToLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq) =
      Hom.id _ := by
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
  refine completedTensor.hom_ext ?_ ?_
  · rw [Hom.id_comp, Hom.comp_assoc, completedTensorRationalToLocHom_comp_inl]
    refine pairHom_ext_of_comp_toCompletionLocHom QB PB hQB TB sB SB hdenB ?_
    rw [Hom.comp_assoc, completedTensorRationalLeftHom_comp_toCompletionLocHom, ← Hom.comp_assoc,
      completedTensorRationalOfLocHom_comp_toCompletionLocHom_comp_inl]
  · rw [Hom.id_comp, Hom.comp_assoc, completedTensorRationalToLocHom_comp_inr]
    refine pairHom_ext_of_comp_toCompletionLocHom QC PC hQC TC sC SC hdenC ?_
    rw [Hom.comp_assoc, completedTensorRationalRightHom_comp_toCompletionLocHom, ← Hom.comp_assoc,
      completedTensorRationalOfLocHom_comp_toCompletionLocHom_comp_inr]

end Iso

section Pushout

universe u

variable {A B C : Type u}
  [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing A] [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  (QA : PairOfDefinition A) (PA : Pair A) (hQA : QA.ringOfDefinition ≤ PA.plus)
  (TA : Finset A) (sA : A) (SA : Type u) [CommRing SA] [Algebra A SA] [IsLocalization.Away sA SA]
  (hdenA : HasDenominatorPower QA TA sA SA)
  (QB : PairOfDefinition B) (PB : Pair B) (hQB : QB.ringOfDefinition ≤ PB.plus)
  (TB : Finset B) (sB : B) (SB : Type u) [CommRing SB] [Algebra B SB] [IsLocalization.Away sB SB]
  (hdenB : HasDenominatorPower QB TB sB SB)
  (QC : PairOfDefinition C) (PC : Pair C) (hQC : QC.ringOfDefinition ≤ PC.plus)
  (TC : Finset C) (sC : C) (SC : Type u) [CommRing SC] [Algebra C SC] [IsLocalization.Away sC SC]
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
  (SD : Type u) [CommRing SD] [Algebra (CompletedTensor A B C) SD] [IsLocalization.Away sD SD]
  (hdenD : HasDenominatorPower QD TD sD SD)
  (hD_eq : (Subtype.val ⁻¹' rationalSubset (PB.completedTensor A PC).plus TD sD :
      Set (spa (PB.completedTensor A PC).plus)) =
    ((completedTensor.inl A PB PC).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset PB.plus TB sB)) ∩
      ((completedTensor.inr A PB PC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset PC.plus TC sC)))

include hQA hdenA hQB hdenB hQC hdenC hf_alg hg_alg hf_sub hg_sub hQD hdenD hD_eq

/-- **The localized square of Huber pairs is a completed pushout**: `O_D(T_D / s_D)` is the
completed pushout of `O(W) → O(U)` and `O(W) → O(V)`. Together with
`TauCeti.AdicSpace.isPullback_ofPair_of_isCompletedPushout`, this turns any sheafy instance of the
square into a pullback of affinoid adic spaces. -/
theorem isCompletedPushout_rationalLocalizationPair :
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
    letI := locUniformSpace QD TD sD SD hdenD
    letI := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
    letI := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
    letI := isHuberRing_completion_locTopology QD TD sD SD hdenD
    IsCompletedPushout
      (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB hf_sub)
      (rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC hg_sub)
      (completedTensorRationalLeftHom QB PB hQB TB sB SB hdenB PC TC sC QD hQD TD sD SD hdenD hD_eq)
      (completedTensorRationalRightHom PB TB sB QC PC hQC TC sC SC hdenC QD hQD TD sD SD hdenD
        hD_eq) := by
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
  let fLoc := rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QB PB hQB f TB sB SB hdenB hf_sub
  let gLoc := rationalLocalizationPairMap QA PA hQA TA sA SA hdenA QC PC hQC g TC sC SC hdenC hg_sub
  let _ : Algebra (Completion SA) (Completion SB) := fLoc.toRingHom.toAlgebra
  let _ : Algebra (Completion SA) (Completion SC) := gLoc.toRingHom.toAlgebra
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
  have hpush := completedTensor.isCompletedPushout fLoc gLoc rfl rfl
  refine ⟨completedTensorRationalLeftHom_comp_eq_rightHom_comp QA PA hQA TA sA SA hdenA QB PB hQB
    TB sB SB hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
    hD_eq, fun R _ _ _ _ _ _ _ V a b hab ↦ ?_⟩
  obtain ⟨χ, ⟨hχB, hχC⟩, hχ_uniq⟩ := hpush.existsUnique_desc R V a b hab
  let toLoc := completedTensorRationalToLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
    QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq
  let ofLoc := completedTensorRationalOfLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
    QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq
  refine ⟨χ.comp ofLoc, ⟨?_, ?_⟩, fun ψ ⟨hψB, hψC⟩ ↦ ?_⟩
  · rw [← completedTensorRationalToLocHom_comp_inl QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB
      hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq,
      ← Hom.comp_assoc, Hom.comp_assoc χ ofLoc toLoc,
      completedTensorRationalOfLocHom_comp_toLocHom, Hom.comp_id, hχB]
  · rw [← completedTensorRationalToLocHom_comp_inr QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB
      hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq,
      ← Hom.comp_assoc, Hom.comp_assoc χ ofLoc toLoc,
      completedTensorRationalOfLocHom_comp_toLocHom, Hom.comp_id, hχC]
  · have hψ_toLoc : ψ.comp toLoc = χ := hχ_uniq (ψ.comp toLoc)
      ⟨by rw [Hom.comp_assoc, completedTensorRationalToLocHom_comp_inl, hψB],
       by rw [Hom.comp_assoc, completedTensorRationalToLocHom_comp_inr, hψC]⟩
    rw [← hψ_toLoc, Hom.comp_assoc, completedTensorRationalToLocHom_comp_ofLocHom, Hom.comp_id]

end Pushout

end TauCeti.Huber.Pair

end
