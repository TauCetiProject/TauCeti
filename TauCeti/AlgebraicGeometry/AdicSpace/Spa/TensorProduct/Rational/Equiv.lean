/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Rational.Pair
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Topological ring isomorphism for completed tensor products of rational localisations

Continuing in the setup of `TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Rational.Pair`,
let `f : (A, A⁺) → (B, B⁺)` and `g : (A, A⁺) → (C, C⁺)` be morphisms of Huber pairs with adic
underlying ring homomorphisms, let `(D, D⁺) = (B, B⁺) ⊗̂_A (C, C⁺)`, and let
`U = R(T_B / s_B) ⊆ Spa(B, B⁺)`, `V = R(T_C / s_C) ⊆ Spa(C, C⁺)`, and
`W = R(T_A / s_A) ⊆ Spa(A, A⁺)` be rational subsets with `f.spaComap(U) ⊆ W` and
`g.spaComap(V) ⊆ W`.

From the mutually inverse Huber-pair morphisms `completedTensorRationalToLocHom` and
`completedTensorRationalOfLocHom` we package the canonical ring isomorphism
```text
completedTensorRationalEquiv : O(U) ⊗̂_{O(W)} O(V) ≃+* O_D(T_D / s_D)
```
for *any* presentation `(T_D, s_D)` on `D` whose rational subset equals `p_B ⁻¹' U ∩ p_C ⁻¹' V`,
and prove:

* `isHomeomorph_completedTensorRationalEquiv`: it is a homeomorphism of topological rings;
* `completedTensorRationalEquiv_tmul`: elementary tensors satisfy `e(ρ_B(b) ⊗ ρ_C(c)) = ρ_D(b ⊗ c)`;
* `completedTensorRationalEquiv_map_plus` and
  `completedTensorRationalEquiv_mem_completedPlusSubring_iff`: it maps the plus ring of
  `O(U) ⊗̂_{O(W)} O(V)` onto `completedPlusSubring` of `O_D(T_D / s_D)`.

## Main definitions

* `TauCeti.Huber.Pair.completedTensorRationalEquiv`: the canonical ring isomorphism
  `O(U) ⊗̂_{O(W)} O(V) ≃+* O_D(T_D / s_D)`.

## Main results

* `TauCeti.Huber.Pair.continuous_completedTensorRationalEquiv`,
  `TauCeti.Huber.Pair.continuous_completedTensorRationalEquiv_symm`,
  `TauCeti.Huber.Pair.isHomeomorph_completedTensorRationalEquiv`: topological isomorphism.
* `TauCeti.Huber.Pair.completedTensorRationalEquiv_inl_algebraMap`,
  `TauCeti.Huber.Pair.completedTensorRationalEquiv_inr_algebraMap`,
  `TauCeti.Huber.Pair.completedTensorRationalEquiv_tmul`: action on localized generators and
  elementary tensors.
* `TauCeti.Huber.Pair.completedTensorRationalEquiv_map_plus`,
  `TauCeti.Huber.Pair.completedTensorRationalEquiv_mem_completedPlusSubring_iff`: transport of
  rings of integral elements.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, after Definition 2.4.12.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.1 and Proposition 8.2(2).
-/

public section

open TensorProduct UniformSpace

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

/-- **Completed tensor products of Huber pairs commute with rational localisation**: the canonical
ring isomorphism `O(U) ⊗̂_{O(W)} O(V) ≃+* O_D(T_D / s_D)`. It is a homeomorphism
(`isHomeomorph_completedTensorRationalEquiv`), carries the completed tensor plus ring onto
`completedPlusSubring` (`completedTensorRationalEquiv_map_plus`), and sends `ρ_B(b) ⊗ ρ_C(c)` to
`ρ_D(b ⊗ c)` (`completedTensorRationalEquiv_tmul`). -/
noncomputable def completedTensorRationalEquiv :
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
    CompletedTensor (Completion SA) (Completion SB) (Completion SC) ≃+* Completion SD :=
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
  RingEquiv.ofRingHom
    (completedTensorRationalToLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
      TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).toRingHom
    (completedTensorRationalOfLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
      TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).toRingHom
    (by
      simpa only [Hom.toRingHom_comp, Hom.toRingHom_id] using congrArg Hom.toRingHom
        (completedTensorRationalToLocHom_comp_ofLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB
          hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
          hD_eq))
    (by
      simpa only [Hom.toRingHom_comp, Hom.toRingHom_id] using congrArg Hom.toRingHom
        (completedTensorRationalOfLocHom_comp_toLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB
          hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
          hD_eq))

/-- The forward ring homomorphism of `completedTensorRationalEquiv` is the underlying ring
homomorphism of `completedTensorRationalToLocHom`. -/
theorem toRingHom_completedTensorRationalEquiv :
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
    (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
      TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).toRingHom =
    (completedTensorRationalToLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
      TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).toRingHom :=
  (rfl)

/-- The inverse ring homomorphism of `completedTensorRationalEquiv` is the underlying ring
homomorphism of `completedTensorRationalOfLocHom`. -/
theorem toRingHom_completedTensorRationalEquiv_symm :
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
    (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
      TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).symm.toRingHom =
    (completedTensorRationalOfLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
      TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).toRingHom :=
  (rfl)

/-- `completedTensorRationalEquiv` is continuous. -/
@[fun_prop]
theorem continuous_completedTensorRationalEquiv :
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
    Continuous (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
      QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq) :=
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  (completedTensorRationalToLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
    TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
    hD_eq).continuous_toRingHom

/-- The inverse of `completedTensorRationalEquiv` is continuous. -/
@[fun_prop]
theorem continuous_completedTensorRationalEquiv_symm :
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
    Continuous (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
      QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
      hD_eq).symm :=
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  (completedTensorRationalOfLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
    TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
    hD_eq).continuous_toRingHom

/-- `completedTensorRationalEquiv` is a homeomorphism. -/
theorem isHomeomorph_completedTensorRationalEquiv :
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
    IsHomeomorph (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
      QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq) :=
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
  (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
    TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
    hD_eq).toEquiv.isHomeomorph_iff.mpr
    ⟨continuous_completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
      QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq,
    continuous_completedTensorRationalEquiv_symm QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
      QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq⟩

/-- `completedTensorRationalEquiv` sends `inl(ρ_B(b))` to `ρ_D(inl(b))`. -/
@[simp]
theorem completedTensorRationalEquiv_inl_algebraMap (b : B) :
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
    completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq
      (CompletedTensor.inl (Completion SA) (Completion SB) (Completion SC)
        (algebraMap B SB b : Completion SB)) =
      (algebraMap (CompletedTensor A B C) SD (CompletedTensor.inl A B C b) : Completion SD) := by
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
  have hinl : (completedTensorRationalToLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
        QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
        hD_eq).toRingHom.comp
      (CompletedTensor.inl (Completion SA) (Completion SB) (Completion SC)) =
      (completedTensorRationalLeftHom QB PB hQB TB sB SB hdenB PC TC sC QD hQD TD sD SD hdenD
        hD_eq).toRingHom := by
    simpa only [Hom.toRingHom_comp, completedTensor.toRingHom_inl] using
      congrArg Hom.toRingHom (completedTensorRationalToLocHom_comp_inl QA PA hQA TA sA SA hdenA
        QB PB hQB TB sB SB hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD
        TD sD SD hdenD hD_eq)
  rw [← toCompletionLoc_apply QB TB sB SB hdenB, ← toCompletionLoc_apply QD TD sD SD hdenD]
  exact (RingHom.congr_fun hinl (toCompletionLoc QB TB sB SB hdenB b)).trans
    (RingHom.congr_fun (toRingHom_completedTensorRationalLeftHom_comp_toCompletionLoc QB PB hQB
      TB sB SB hdenB PC TC sC QD hQD TD sD SD hdenD hD_eq) b)

/-- `completedTensorRationalEquiv` sends `inr(ρ_C(c))` to `ρ_D(inr(c))`. -/
@[simp]
theorem completedTensorRationalEquiv_inr_algebraMap (c : C) :
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
    completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq
      (CompletedTensor.inr (Completion SA) (Completion SB) (Completion SC)
        (algebraMap C SC c : Completion SC)) =
      (algebraMap (CompletedTensor A B C) SD (CompletedTensor.inr A B C c) : Completion SD) := by
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
  have hinr : (completedTensorRationalToLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
        QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
        hD_eq).toRingHom.comp
      (CompletedTensor.inr (Completion SA) (Completion SB) (Completion SC)) =
      (completedTensorRationalRightHom PB TB sB QC PC hQC TC sC SC hdenC QD hQD TD sD SD hdenD
        hD_eq).toRingHom := by
    simpa only [Hom.toRingHom_comp, completedTensor.toRingHom_inr] using
      congrArg Hom.toRingHom (completedTensorRationalToLocHom_comp_inr QA PA hQA TA sA SA hdenA
        QB PB hQB TB sB SB hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD
        TD sD SD hdenD hD_eq)
  rw [← toCompletionLoc_apply QC TC sC SC hdenC, ← toCompletionLoc_apply QD TD sD SD hdenD]
  exact (RingHom.congr_fun hinr (toCompletionLoc QC TC sC SC hdenC c)).trans
    (RingHom.congr_fun (toRingHom_completedTensorRationalRightHom_comp_toCompletionLoc PB TB sB
      QC PC hQC TC sC SC hdenC QD hQD TD sD SD hdenD hD_eq) c)

/-- **Coefficient formula for `completedTensorRationalEquiv`**: elementary tensors of localized
elements satisfy `e(ρ_B(b) ⊗ ρ_C(c)) = ρ_D(b ⊗ c)`. -/
theorem completedTensorRationalEquiv_tmul (b : B) (c : C) :
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
    completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq
      (CompletedTensor.toCompletion (Completion SA) (Completion SB) (Completion SC)
        (toCompletionLoc QB TB sB SB hdenB b ⊗ₜ[Completion SA]
          toCompletionLoc QC TC sC SC hdenC c)) =
      toCompletionLoc QD TD sD SD hdenD (CompletedTensor.toCompletion A B C (b ⊗ₜ[A] c)) := by
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
  rw [CompletedTensor.toCompletion_tmul, CompletedTensor.toCompletion_tmul, map_mul, map_mul]
  simp only [toCompletionLoc_apply, completedTensorRationalEquiv_inl_algebraMap,
    completedTensorRationalEquiv_inr_algebraMap]

/-- The inverse of `completedTensorRationalEquiv` sends `ρ_D(inl(b))` to `inl(ρ_B(b))`. -/
@[simp]
theorem completedTensorRationalEquiv_symm_algebraMap_inl (b : B) :
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
    (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).symm
      (algebraMap (CompletedTensor A B C) SD (CompletedTensor.inl A B C b) : Completion SD) =
      CompletedTensor.inl (Completion SA) (Completion SB) (Completion SC)
        (algebraMap B SB b : Completion SB) := by
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
  exact (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
    TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).symm_apply_eq.mpr
    (completedTensorRationalEquiv_inl_algebraMap QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
      QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq b).symm

/-- The inverse of `completedTensorRationalEquiv` sends `ρ_D(inr(c))` to `inr(ρ_C(c))`. -/
@[simp]
theorem completedTensorRationalEquiv_symm_algebraMap_inr (c : C) :
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
    (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).symm
      (algebraMap (CompletedTensor A B C) SD (CompletedTensor.inr A B C c) : Completion SD) =
      CompletedTensor.inr (Completion SA) (Completion SB) (Completion SC)
        (algebraMap C SC c : Completion SC) := by
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
  exact (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
    TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).symm_apply_eq.mpr
    (completedTensorRationalEquiv_inr_algebraMap QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
      QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq c).symm

/-- `completedTensorRationalEquiv` maps elements of the completed tensor plus ring into the plus
ring of `O_D(T_D / s_D)`. -/
theorem completedTensorRationalEquiv_mem_plus :
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
    ∀ x ∈ ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor (Completion SA)
        (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).plus,
      completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
          TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq x ∈
        (rationalLocalizationPair QD (PB.completedTensor A PC) hQD TD sD SD hdenD).plus :=
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  (completedTensorRationalToLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
    TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).map_mem_plus

/-- The inverse of `completedTensorRationalEquiv` maps elements of the plus ring of
`O_D(T_D / s_D)` into the completed tensor plus ring. -/
theorem completedTensorRationalEquiv_symm_mem_plus :
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
    ∀ y ∈ (rationalLocalizationPair QD (PB.completedTensor A PC) hQD TD sD SD hdenD).plus,
      (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
          TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).symm y ∈
        ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor (Completion SA)
          (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).plus :=
  let _ := locUniformSpace QD TD sD SD hdenD
  have _ := isUniformAddGroup_locUniformSpace QD TD sD SD hdenD
  have _ := isTopologicalRing_locUniformSpace QD TD sD SD hdenD
  have _ := isHuberRing_completion_locTopology QD TD sD SD hdenD
  (completedTensorRationalOfLocHom QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
    TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).map_mem_plus

/-- **Plus-ring transport**: `completedTensorRationalEquiv` maps the plus ring of
`O(U) ⊗̂_{O(W)} O(V)` onto `completedPlusSubring` of `O_D(T_D / s_D)`. -/
theorem completedTensorRationalEquiv_map_plus :
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
    ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor (Completion SA)
        (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).plus.map
      (completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
        TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq).toRingHom =
      (rationalLocalizationPair QD (PB.completedTensor A PC) hQD TD sD SD hdenD).plus := by
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
  let e := completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC
    hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq
  refine le_antisymm (Subring.map_le_iff_le_comap.mpr fun x hx ↦
      completedTensorRationalEquiv_mem_plus QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB
        QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq x hx)
    fun y hy ↦ ⟨e.symm y,
      completedTensorRationalEquiv_symm_mem_plus QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB
        hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
        hD_eq y hy,
      e.apply_symm_apply y⟩

/-- Membership characterization of `completedPlusSubring` under `completedTensorRationalEquiv`. -/
theorem completedTensorRationalEquiv_mem_completedPlusSubring_iff :
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
    ∀ x : CompletedTensor (Completion SA) (Completion SB) (Completion SC),
      completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC hQC
          TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq x ∈
        completedPlusSubring QD (PB.completedTensor A PC).plus TD sD SD hdenD ↔
      x ∈ ((rationalLocalizationPair QB PB hQB TB sB SB hdenB).completedTensor (Completion SA)
        (rationalLocalizationPair QC PC hQC TC sC SC hdenC)).plus := by
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
  intro x
  rw [← rationalLocalizationPair_plus QD (PB.completedTensor A PC) hQD TD sD SD hdenD]
  let e := completedTensorRationalEquiv QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC
    hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq
  refine ⟨fun hx ↦ ?_, fun hx ↦
    completedTensorRationalEquiv_mem_plus QA PA hQA TA sA SA hdenA QB PB hQB TB sB SB hdenB QC PC
      hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD hD_eq x hx⟩
  have hmem := completedTensorRationalEquiv_symm_mem_plus QA PA hQA TA sA SA hdenA QB PB hQB TB
    sB SB hdenB QC PC hQC TC sC SC hdenC f g hf_alg hg_alg hf_sub hg_sub QD hQD TD sD SD hdenD
    hD_eq (e x) hx
  rwa [e.symm_apply_apply] at hmem

end TauCeti.Huber.Pair

end
