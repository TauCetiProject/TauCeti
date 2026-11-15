/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Rational.Equiv
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Rational.Preimage
public import TauCeti.RingTheory.Huber.TensorProduct.Rational

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Plus

/-!
# Plus-ring comparison and Huber-pair morphisms for completed tensor rational localisations

Continuing `TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Rational.Equiv`, this file shows
that `Pair.completedTensorRationalEquiv` maps the completed tensor plus ring of `O_B(U)` and
`O_C(V)` over `O_A(W)` onto `completedPlusSubring PD (B ⊗̂_A C)⁺ T_D s_D`, packages both directions
as mutually inverse morphisms of Huber pairs (`Pair.completedTensor.toRationalLoc` and
`Pair.completedTensor.ofRationalLoc`), and proves the analogous plus-ring identification for
`CompletedTensor.completionLocEquiv` over an unlocalised base `A`.

## Main definitions

* `TauCeti.Huber.Pair.completedTensor.toRationalLoc`,
  `TauCeti.Huber.Pair.completedTensor.ofRationalLoc`: mutually inverse morphisms of Huber pairs
  between `(O_B(U), O_B(U)⁺) ⊗̂_{O_A(W)} (O_C(V), O_C(V)⁺)` and `(O_D(d), O_D(d)⁺)`.

## Main results

* `TauCeti.Huber.Pair.map_plus_completedTensorRationalEquiv`,
  `TauCeti.Huber.Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv`:
  `completedTensorRationalEquiv` maps the completed tensor plus ring onto `completedPlusSubring`.
* `TauCeti.Huber.Pair.completedTensor.toRationalLoc_comp_ofRationalLoc`,
  `TauCeti.Huber.Pair.completedTensor.ofRationalLoc_comp_toRationalLoc`:
  `toRationalLoc` and `ofRationalLoc` are mutually inverse morphisms of Huber pairs.
* `TauCeti.Huber.Pair.map_plus_completionLocEquiv`,
  `TauCeti.Huber.Pair.mem_completedTensor_plus_iff_completionLocEquiv`:
  `CompletedTensor.completionLocEquiv` (over unlocalised `A`) maps the completed tensor plus ring
  onto `completedPlusSubring`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  §3, proof of Proposition 3.7.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.1 and Proposition 8.2(2).
-/

public section

open UniformSpace (Completion)
open scoped Pointwise

namespace TauCeti.Huber

open PairOfDefinition TauCeti.ValuationSpectrum

section RationalPair

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

/-- `Pair.completedTensorRationalEquiv` maps the completed tensor plus ring onto
`completedPlusSubring`. -/
theorem Pair.map_plus_completedTensorRationalEquiv
    (hPB : PB.ringOfDefinition ≤ SB.plus)
    (hPC : PC.ringOfDefinition ≤ SC.plus)
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
    ((PB.rationalLocalizationPair SB hPB TB sB LB hdenB).completedTensor (Completion LA)
      (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)).plus.map
      (Pair.completedTensorRationalEquiv PA SA TA sA LA hdenA PB SB TB sB LB hdenB
        PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd :
        CompletedTensor (Completion LA) (Completion LB) (Completion LC) →+* Completion LD) =
      completedPlusSubring PD (SB.completedTensor A SC).plus TD sD LD hdenD := by
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
  have _ := isHuberRing_completion_locTopology PD TD sD LD hdenD
  let OU := PB.rationalLocalizationPair SB hPB TB sB LB hdenB
  let OV := PC.rationalLocalizationPair SC hPC TC sC LC hdenC
  let SD := SB.completedTensor A SC
  let ODplus := completedPlusSubring PD SD.plus TD sD LD hdenD
  let e := Pair.completedTensorRationalEquiv PA SA TA sA LA hdenA PB SB TB sB LB hdenB
    PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd
  have he : Continuous e := Pair.continuous_completedTensorRationalEquiv
    PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd
  have he' : Continuous e.symm := Pair.continuous_completedTensorRationalEquiv_symm
    PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd
  have hOD_ring : IsRingOfIntegralElements ODplus :=
    isRingOfIntegralElements_completedPlusSubring PD SD.plus
      (fun _ hj ↦ SD.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
        (PD.isTopologicallyNilpotent_of_mem_idealOfDefinition hj))
      SD.isRingOfIntegralElements.isPowerBounded_of_mem TD sD LD hdenD
  have _ := hOD_ring.isIntegrallyClosedIn
  have hOD_closed : IsClosed (ODplus : Set (Completion LD)) :=
    ODplus.toAddSubgroup.isClosed_of_isOpen hOD_ring.isOpen
  have hfwd : (OU.completedTensor (Completion LA) OV).plus ≤ ODplus.comap (e : _ →+* _) := by
    refine OU.completedTensor_plus_le_comap OV hOD_closed he (fun u hu ↦ ?_) (fun v hv ↦ ?_)
    · have hL := eq_ringHomOfMapsToRationalSubset PB SB.plus TB sB LB hdenB PD SD.plus
        SD.isRingOfIntegralElements.isPowerBounded_of_mem TD sD LD hdenD
        (CompletedTensor.continuous_inl A B C).continuousAt
        (Pair.completedTensor.mapsTo_inl_of_inter_eq hd)
        ((e : _ →+* _).comp
          (CompletedTensor.inl (Completion LA) (Completion LB) (Completion LC)))
        (he.comp (CompletedTensor.continuous_inl _ _ _))
        (RingHom.ext fun b ↦ by simp [e, toCompletionLoc_apply])
      have hu' : u ∈ completedPlusSubring PB SB.plus TB sB LB hdenB := by
        simpa only [OU, rationalLocalizationPair_plus] using hu
      rw [← RingHom.comp_apply, hL]
      exact ringHomOfMapsToRationalSubset_mem_completedPlusSubring PB SB.plus TB sB LB hdenB
        PD SD.plus
        (fun _ hj ↦ SD.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
          (PD.isTopologicallyNilpotent_of_mem_idealOfDefinition hj))
        SD.isRingOfIntegralElements.isPowerBounded_of_mem TD sD LD hdenD
        (CompletedTensor.continuous_inl A B C).continuousAt
        (Pair.completedTensor.mapsTo_inl_of_inter_eq hd) u hu'
    · have hR := eq_ringHomOfMapsToRationalSubset PC SC.plus TC sC LC hdenC PD SD.plus
        SD.isRingOfIntegralElements.isPowerBounded_of_mem TD sD LD hdenD
        (CompletedTensor.continuous_inr A B C).continuousAt
        (Pair.completedTensor.mapsTo_inr_of_inter_eq hd)
        ((e : _ →+* _).comp
          (CompletedTensor.inr (Completion LA) (Completion LB) (Completion LC)))
        (he.comp (CompletedTensor.continuous_inr _ _ _))
        (RingHom.ext fun c ↦ by simp [e, toCompletionLoc_apply])
      have hv' : v ∈ completedPlusSubring PC SC.plus TC sC LC hdenC := by
        simpa only [OV, rationalLocalizationPair_plus] using hv
      rw [← RingHom.comp_apply, hR]
      exact ringHomOfMapsToRationalSubset_mem_completedPlusSubring PC SC.plus TC sC LC hdenC
        PD SD.plus
        (fun _ hj ↦ SD.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
          (PD.isTopologicallyNilpotent_of_mem_idealOfDefinition hj))
        SD.isRingOfIntegralElements.isPowerBounded_of_mem TD sD LD hdenD
        (CompletedTensor.continuous_inr A B C).continuousAt
        (Pair.completedTensor.mapsTo_inr_of_inter_eq hd) v hv'
  let g : CompletedTensor A B C →+*
      CompletedTensor (Completion LA) (Completion LB) (Completion LC) :=
    (e.symm : _ →+* _).comp (toCompletionLoc PD TD sD LD hdenD)
  have hg_cont : Continuous g := he'.comp (continuous_toCompletionLoc PD TD sD LD hdenD)
  have hgB : g.comp (CompletedTensor.inl A B C) =
      (CompletedTensor.inl (Completion LA) (Completion LB) (Completion LC)).comp
        (toCompletionLoc PB TB sB LB hdenB) :=
    RingHom.ext fun b ↦ by simp [g, e, toCompletionLoc_apply]
  have hgC : g.comp (CompletedTensor.inr A B C) =
      (CompletedTensor.inr (Completion LA) (Completion LB) (Completion LC)).comp
        (toCompletionLoc PC TC sC LC hdenC) :=
    RingHom.ext fun c ↦ by simp [g, e, toCompletionLoc_apply]
  have _ := (OU.completedTensor (Completion LA) OV).isRingOfIntegralElements.isIntegrallyClosedIn
  have hE_closed : IsClosed ((OU.completedTensor (Completion LA) OV).plus :
      Set (CompletedTensor (Completion LA) (Completion LB) (Completion LC))) :=
    (OU.completedTensor (Completion LA) OV).plus.toAddSubgroup.isClosed_of_isOpen
      (OU.completedTensor (Completion LA) OV).isRingOfIntegralElements.isOpen
  have hg_plus : SD.plus ≤ (OU.completedTensor (Completion LA) OV).plus.comap g := by
    refine SB.completedTensor_plus_le_comap SC hE_closed hg_cont
      (fun b hb ↦ ?_) (fun c hc ↦ ?_)
    · have hb' : toCompletionLoc PB TB sB LB hdenB b ∈ OU.plus := by
        rw [rationalLocalizationPair_plus]
        exact toCompletionLoc_mem_completedPlusSubring PB SB.plus TB sB LB hdenB hb
      have hinl := OU.inl_mem_completedTensor_plus (A := Completion LA) OV hb'
      rwa [← RingHom.comp_apply, ← hgB, RingHom.comp_apply] at hinl
    · have hc' : toCompletionLoc PC TC sC LC hdenC c ∈ OV.plus := by
        rw [rationalLocalizationPair_plus]
        exact toCompletionLoc_mem_completedPlusSubring PC SC.plus TC sC LC hdenC hc
      have hinr := OU.inr_mem_completedTensor_plus (A := Completion LA) OV hc'
      rwa [← RingHom.comp_apply, ← hgC, RingHom.comp_apply] at hinr
  ext z
  rw [Subring.mem_map]
  refine ⟨fun ⟨x, hx, hxz⟩ ↦ hxz ▸ hfwd hx, fun hz ↦ ⟨e.symm z, ?_, e.apply_symm_apply z⟩⟩
  refine (OU.completedTensor (Completion LA) OV).isRingOfIntegralElements
    |>.mem_of_forall_vle_one fun w hw ↦ ?_
  let gHom : Pair.Hom SD (OU.completedTensor (Completion LA) OV) :=
    ⟨g, hg_cont, fun d hd' ↦ hg_plus hd'⟩
  have hmemD : gHom.spaComap ⟨w, hw⟩ ∈ Subtype.val ⁻¹' rationalSubset SD.plus TD sD := by
    rw [hd]
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_preimage, Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inl]
      rw [← Function.comp_apply (f := comap (CompletedTensor.inl A B C)), ← comap_comp,
        hgB, comap_comp, Function.comp_apply]
      have hwB : comap (CompletedTensor.inl (Completion LA) (Completion LB) (Completion LC)) w ∈
          spa (completedPlusSubring PB SB.plus TB sB LB hdenB) := by
        rw [← rationalLocalizationPair_plus PB SB hPB TB sB LB hdenB]
        simpa only [Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inl] using
          ((Pair.completedTensor.inl (Completion LA) OU OV).spaComap ⟨w, hw⟩).2
      simpa only [spaComapLoc_val] using
        spaComapLoc_mem_rationalSubset PB SB.plus TB sB LB hdenB ⟨_, hwB⟩
    · simp only [Set.mem_preimage, Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inr]
      rw [← Function.comp_apply (f := comap (CompletedTensor.inr A B C)), ← comap_comp,
        hgC, comap_comp, Function.comp_apply]
      have hwC : comap (CompletedTensor.inr (Completion LA) (Completion LB) (Completion LC)) w ∈
          spa (completedPlusSubring PC SC.plus TC sC LC hdenC) := by
        rw [← rationalLocalizationPair_plus PC SC hPC TC sC LC hdenC]
        simpa only [Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inr] using
          ((Pair.completedTensor.inr (Completion LA) OU OV).spaComap ⟨w, hw⟩).2
      simpa only [spaComapLoc_val] using
        spaComapLoc_mem_rationalSubset PC SC.plus TC sC LC hdenC ⟨_, hwC⟩
  have hcomap := comap_mem_spa_completedPlusSubring PD SD.plus TD sD LD hdenD
    (e.symm : _ →+* _) he' ((mem_spa_iff _ _).mp hw).1
    (by simpa only [Set.mem_preimage, Pair.Hom.spaComap_val] using hmemD)
  simpa only [comap_vle, map_one, RingEquiv.coe_toRingHom] using
    ((mem_spa_iff _ _).mp hcomap).2 z hz

/-- Membership in the completed tensor plus ring is equivalent to membership of the image under
`Pair.completedTensorRationalEquiv` in `completedPlusSubring` (not `@[simp]` because
`mem_completedPlusSubring_iff` already rewrites the right-hand side). -/
theorem Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
    (hPB : PB.ringOfDefinition ≤ SB.plus)
    (hPC : PC.ringOfDefinition ≤ SC.plus)
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
    ∀ x : CompletedTensor (Completion LA) (Completion LB) (Completion LC),
      Pair.completedTensorRationalEquiv PA SA TA sA LA hdenA PB SB TB sB LB hdenB
        PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd x ∈
          completedPlusSubring PD (SB.completedTensor A SC).plus TD sD LD hdenD ↔
        x ∈ ((PB.rationalLocalizationPair SB hPB TB sB LB hdenB).completedTensor (Completion LA)
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
  intro x
  rw [← Pair.map_plus_completedTensorRationalEquiv
    PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
    PD TD sD LD hdenD hPB hPC hf hg hd]
  simp only [Subring.mem_map_equiv, RingEquiv.symm_apply_apply]

/-- The forward morphism of Huber pairs `O_B(U) ⊗̂_{O_A(W)} O_C(V) → O_D(d)` underlying
`Pair.completedTensorRationalEquiv`. -/
noncomputable def Pair.completedTensor.toRationalLoc
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
    letI := isHuberRing_completion_locTopology PD TD sD LD hdenD
    Pair.Hom
      ((PB.rationalLocalizationPair SB hPB TB sB LB hdenB).completedTensor (Completion LA)
        (PC.rationalLocalizationPair SC hPC TC sC LC hdenC))
      (PD.rationalLocalizationPair (SB.completedTensor A SC) hPD TD sD LD hdenD) :=
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
  letI := isHuberRing_completion_locTopology PD TD sD LD hdenD
  { toRingHom := (Pair.completedTensorRationalEquiv
      PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
      PD TD sD LD hdenD hf hg hd).toRingHom
    continuous_toRingHom := Pair.continuous_completedTensorRationalEquiv
      PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
      PD TD sD LD hdenD hf hg hd
    map_mem_plus := fun x hx ↦ by
      rw [rationalLocalizationPair_plus]
      exact (Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
        PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
        PD TD sD LD hdenD hPB hPC hf hg hd x).mpr hx }

/-- The inverse morphism of Huber pairs `O_D(d) → O_B(U) ⊗̂_{O_A(W)} O_C(V)` underlying
`Pair.completedTensorRationalEquiv.symm`. -/
noncomputable def Pair.completedTensor.ofRationalLoc
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
    letI := isHuberRing_completion_locTopology PD TD sD LD hdenD
    Pair.Hom
      (PD.rationalLocalizationPair (SB.completedTensor A SC) hPD TD sD LD hdenD)
      ((PB.rationalLocalizationPair SB hPB TB sB LB hdenB).completedTensor (Completion LA)
        (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)) :=
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
  letI := isHuberRing_completion_locTopology PD TD sD LD hdenD
  let e := Pair.completedTensorRationalEquiv
    PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
    PD TD sD LD hdenD hf hg hd
  { toRingHom := e.symm.toRingHom
    continuous_toRingHom := Pair.continuous_completedTensorRationalEquiv_symm
      PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
      PD TD sD LD hdenD hf hg hd
    map_mem_plus := fun z hz ↦ by
      rw [rationalLocalizationPair_plus] at hz
      exact (Pair.mem_completedTensor_plus_iff_completedTensorRationalEquiv
        PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
        PD TD sD LD hdenD hPB hPC hf hg hd (e.symm z)).mp (by simpa [e] using hz) }

/-- The underlying ring homomorphism of `Pair.completedTensor.toRationalLoc` is
`Pair.completedTensorRationalEquiv`. -/
@[simp]
theorem Pair.completedTensor.toRationalLoc_toRingHom
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
    letI := isHuberRing_completion_locTopology PD TD sD LD hdenD
    (Pair.completedTensor.toRationalLoc PA SA TA sA LA hdenA PB SB TB sB LB hdenB
      PC SC TC sC LC hdenC PD TD sD LD hdenD hPB hPC hPD hf hg hd).toRingHom =
      (Pair.completedTensorRationalEquiv PA SA TA sA LA hdenA PB SB TB sB LB hdenB
        PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd :
        CompletedTensor (Completion LA) (Completion LB) (Completion LC) →+* Completion LD) :=
  (rfl)

/-- The underlying ring homomorphism of `Pair.completedTensor.ofRationalLoc` is
`Pair.completedTensorRationalEquiv.symm`. -/
@[simp]
theorem Pair.completedTensor.ofRationalLoc_toRingHom
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
    letI := isHuberRing_completion_locTopology PD TD sD LD hdenD
    (Pair.completedTensor.ofRationalLoc PA SA TA sA LA hdenA PB SB TB sB LB hdenB
      PC SC TC sC LC hdenC PD TD sD LD hdenD hPB hPC hPD hf hg hd).toRingHom =
      ((Pair.completedTensorRationalEquiv PA SA TA sA LA hdenA PB SB TB sB LB hdenB
        PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd).symm :
        Completion LD →+* CompletedTensor (Completion LA) (Completion LB) (Completion LC)) :=
  (rfl)

/-- `Pair.completedTensor.toRationalLoc` and `Pair.completedTensor.ofRationalLoc` compose to the
identity on `O_D(d)`. -/
@[simp]
theorem Pair.completedTensor.toRationalLoc_comp_ofRationalLoc
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
    letI := isHuberRing_completion_locTopology PD TD sD LD hdenD
    (Pair.completedTensor.toRationalLoc PA SA TA sA LA hdenA PB SB TB sB LB hdenB
        PC SC TC sC LC hdenC PD TD sD LD hdenD hPB hPC hPD hf hg hd).comp
      (Pair.completedTensor.ofRationalLoc PA SA TA sA LA hdenA PB SB TB sB LB hdenB
        PC SC TC sC LC hdenC PD TD sD LD hdenD hPB hPC hPD hf hg hd) =
      Pair.Hom.id (PD.rationalLocalizationPair (SB.completedTensor A SC) hPD TD sD LD hdenD) := by
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
  have _ := isHuberRing_completion_locTopology PD TD sD LD hdenD
  ext1
  simp

/-- `Pair.completedTensor.ofRationalLoc` and `Pair.completedTensor.toRationalLoc` compose to the
identity on `O_B(U) ⊗̂_{O_A(W)} O_C(V)`. -/
@[simp]
theorem Pair.completedTensor.ofRationalLoc_comp_toRationalLoc
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
    letI := isHuberRing_completion_locTopology PD TD sD LD hdenD
    (Pair.completedTensor.ofRationalLoc PA SA TA sA LA hdenA PB SB TB sB LB hdenB
        PC SC TC sC LC hdenC PD TD sD LD hdenD hPB hPC hPD hf hg hd).comp
      (Pair.completedTensor.toRationalLoc PA SA TA sA LA hdenA PB SB TB sB LB hdenB
        PC SC TC sC LC hdenC PD TD sD LD hdenD hPB hPC hPD hf hg hd) =
      Pair.Hom.id
        ((PB.rationalLocalizationPair SB hPB TB sB LB hdenB).completedTensor (Completion LA)
          (PC.rationalLocalizationPair SC hPC TC sC LC hdenC)) := by
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
  have _ := isHuberRing_completion_locTopology PD TD sD LD hdenD
  ext1
  simp

end RationalPair

/-! ### Plus-ring compatibility for `CompletedTensor.completionLocEquiv` -/

section UnlocalisedBase

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  [DecidableEq (CompletedTensor A B C)]
  (P : PairOfDefinition B) (SB : Pair B) (hP : P.ringOfDefinition ≤ SB.plus)
  (T : Finset B) (s : B) (S : Type*) [CommRing S] [Algebra B S]
  [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
  (P' : PairOfDefinition C) (SC : Pair C) (hP' : P'.ringOfDefinition ≤ SC.plus)
  (T' : Finset C) (s' : C) (S' : Type*) [CommRing S'] [Algebra C S']
  [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P' T' s' S')
  (Q : PairOfDefinition (CompletedTensor A B C)) (S'' : Type*) [CommRing S'']
  [Algebra (CompletedTensor A B C) S'']
  [IsLocalization.Away (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') S'']
  (hden'' : HasDenominatorPower Q
    (insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
      insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C)) : Finset _)
    (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') S'')

/-- Over an unlocalised base `A`, `CompletedTensor.completionLocEquiv` also carries the completed
tensor plus ring onto `completedPlusSubring`. -/
theorem Pair.map_plus_completionLocEquiv :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstance : IsAdicHom (algebraMap A B))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstance : IsAdicHom (algebraMap A C))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    ((P.rationalLocalizationPair SB hP T s S hden).completedTensor A
      (P'.rationalLocalizationPair SC hP' T' s' S' hden')).plus.map
      (CompletedTensor.completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'' :
        CompletedTensor A (Completion S) (Completion S') →+* Completion S'') =
      completedPlusSubring Q (SB.completedTensor A SC).plus
        (insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
          insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C)) : Finset _)
        (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') S'' hden'' := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  let _ : Algebra A (Completion S) :=
    ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
  let _ : Algebra A (Completion S') :=
    ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion S)) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
      (inferInstance : IsAdicHom (algebraMap A B))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
      (inferInstance : IsAdicHom (algebraMap A C))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  let OU := P.rationalLocalizationPair SB hP T s S hden
  let OV := P'.rationalLocalizationPair SC hP' T' s' S' hden'
  let SD := SB.completedTensor A SC
  let T'' : Finset (CompletedTensor A B C) :=
    insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
      insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C))
  let s'' : CompletedTensor A B C := CompletedTensor.inl A B C s * CompletedTensor.inr A B C s'
  let ODplus := completedPlusSubring Q SD.plus T'' s'' S'' hden''
  let e := CompletedTensor.completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
  have he : Continuous e :=
    CompletedTensor.continuous_completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
  have he' : Continuous e.symm :=
    CompletedTensor.continuous_completionLocEquiv_symm P T s S hden P' T' s' S' hden' Q S'' hden''
  have hd : Subtype.val ⁻¹' rationalSubset SD.plus T'' s'' =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus T s)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus T' s')) := by
    convert (Pair.completedTensor.inter_preimage_rationalSubset
      (A := A) SB SC T s T' s').symm
  have hOD_ring : IsRingOfIntegralElements ODplus :=
    isRingOfIntegralElements_completedPlusSubring Q SD.plus
      (fun _ hj ↦ SD.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
        (Q.isTopologicallyNilpotent_of_mem_idealOfDefinition hj))
      SD.isRingOfIntegralElements.isPowerBounded_of_mem T'' s'' S'' hden''
  have _ := hOD_ring.isIntegrallyClosedIn
  have hOD_closed : IsClosed (ODplus : Set (Completion S'')) :=
    ODplus.toAddSubgroup.isClosed_of_isOpen hOD_ring.isOpen
  have hfwd : (OU.completedTensor A OV).plus ≤ ODplus.comap (e : _ →+* _) := by
    refine OU.completedTensor_plus_le_comap OV hOD_closed he (fun u hu ↦ ?_) (fun v hv ↦ ?_)
    · have hL := eq_ringHomOfMapsToRationalSubset P SB.plus T s S hden Q SD.plus
        SD.isRingOfIntegralElements.isPowerBounded_of_mem T'' s'' S'' hden''
        (CompletedTensor.continuous_inl A B C).continuousAt
        (Pair.completedTensor.mapsTo_inl_of_inter_eq hd)
        ((e : _ →+* _).comp (CompletedTensor.inl A (Completion S) (Completion S')))
        (he.comp (CompletedTensor.continuous_inl _ _ _))
        (RingHom.ext fun b ↦ by simp [e, toCompletionLoc_apply])
      have hu' : u ∈ completedPlusSubring P SB.plus T s S hden := by
        simpa only [OU, rationalLocalizationPair_plus] using hu
      rw [← RingHom.comp_apply, hL]
      exact ringHomOfMapsToRationalSubset_mem_completedPlusSubring P SB.plus T s S hden Q SD.plus
        (fun _ hj ↦ SD.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
          (Q.isTopologicallyNilpotent_of_mem_idealOfDefinition hj))
        SD.isRingOfIntegralElements.isPowerBounded_of_mem T'' s'' S'' hden''
        (CompletedTensor.continuous_inl A B C).continuousAt
        (Pair.completedTensor.mapsTo_inl_of_inter_eq hd) u hu'
    · have hR := eq_ringHomOfMapsToRationalSubset P' SC.plus T' s' S' hden' Q SD.plus
        SD.isRingOfIntegralElements.isPowerBounded_of_mem T'' s'' S'' hden''
        (CompletedTensor.continuous_inr A B C).continuousAt
        (Pair.completedTensor.mapsTo_inr_of_inter_eq hd)
        ((e : _ →+* _).comp (CompletedTensor.inr A (Completion S) (Completion S')))
        (he.comp (CompletedTensor.continuous_inr _ _ _))
        (RingHom.ext fun c ↦ by simp [e, toCompletionLoc_apply])
      have hv' : v ∈ completedPlusSubring P' SC.plus T' s' S' hden' := by
        simpa only [OV, rationalLocalizationPair_plus] using hv
      rw [← RingHom.comp_apply, hR]
      exact ringHomOfMapsToRationalSubset_mem_completedPlusSubring P' SC.plus T' s' S' hden'
        Q SD.plus
        (fun _ hj ↦ SD.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
          (Q.isTopologicallyNilpotent_of_mem_idealOfDefinition hj))
        SD.isRingOfIntegralElements.isPowerBounded_of_mem T'' s'' S'' hden''
        (CompletedTensor.continuous_inr A B C).continuousAt
        (Pair.completedTensor.mapsTo_inr_of_inter_eq hd) v hv'
  let g : CompletedTensor A B C →+* CompletedTensor A (Completion S) (Completion S') :=
    (e.symm : _ →+* _).comp (toCompletionLoc Q T'' s'' S'' hden'')
  have hg_cont : Continuous g := he'.comp (continuous_toCompletionLoc Q T'' s'' S'' hden'')
  have hgB : g.comp (CompletedTensor.inl A B C) =
      (CompletedTensor.inl A (Completion S) (Completion S')).comp
        (toCompletionLoc P T s S hden) :=
    RingHom.ext fun b ↦ by simp [g, e, toCompletionLoc_apply]
  have hgC : g.comp (CompletedTensor.inr A B C) =
      (CompletedTensor.inr A (Completion S) (Completion S')).comp
        (toCompletionLoc P' T' s' S' hden') :=
    RingHom.ext fun c ↦ by simp [g, e, toCompletionLoc_apply]
  have _ := (OU.completedTensor A OV).isRingOfIntegralElements.isIntegrallyClosedIn
  have hE_closed : IsClosed ((OU.completedTensor A OV).plus :
      Set (CompletedTensor A (Completion S) (Completion S'))) :=
    (OU.completedTensor A OV).plus.toAddSubgroup.isClosed_of_isOpen
      (OU.completedTensor A OV).isRingOfIntegralElements.isOpen
  have hg_plus : SD.plus ≤ (OU.completedTensor A OV).plus.comap g := by
    refine SB.completedTensor_plus_le_comap SC hE_closed hg_cont
      (fun b hb ↦ ?_) (fun c hc ↦ ?_)
    · have hb' : toCompletionLoc P T s S hden b ∈ OU.plus := by
        rw [rationalLocalizationPair_plus]
        exact toCompletionLoc_mem_completedPlusSubring P SB.plus T s S hden hb
      have hinl := OU.inl_mem_completedTensor_plus (A := A) OV hb'
      rwa [← RingHom.comp_apply, ← hgB, RingHom.comp_apply] at hinl
    · have hc' : toCompletionLoc P' T' s' S' hden' c ∈ OV.plus := by
        rw [rationalLocalizationPair_plus]
        exact toCompletionLoc_mem_completedPlusSubring P' SC.plus T' s' S' hden' hc
      have hinr := OU.inr_mem_completedTensor_plus (A := A) OV hc'
      rwa [← RingHom.comp_apply, ← hgC, RingHom.comp_apply] at hinr
  ext z
  rw [Subring.mem_map]
  refine ⟨fun ⟨x, hx, hxz⟩ ↦ hxz ▸ hfwd hx, fun hz ↦ ⟨e.symm z, ?_, e.apply_symm_apply z⟩⟩
  refine (OU.completedTensor A OV).isRingOfIntegralElements.mem_of_forall_vle_one fun w hw ↦ ?_
  let gHom : Pair.Hom SD (OU.completedTensor A OV) := ⟨g, hg_cont, fun d hd' ↦ hg_plus hd'⟩
  have hmemD : gHom.spaComap ⟨w, hw⟩ ∈ Subtype.val ⁻¹' rationalSubset SD.plus T'' s'' := by
    rw [hd]
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_preimage, Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inl]
      rw [← Function.comp_apply (f := comap (CompletedTensor.inl A B C)), ← comap_comp,
        hgB, comap_comp, Function.comp_apply]
      have hwB : comap (CompletedTensor.inl A (Completion S) (Completion S')) w ∈
          spa (completedPlusSubring P SB.plus T s S hden) := by
        rw [← rationalLocalizationPair_plus P SB hP T s S hden]
        simpa only [Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inl] using
          ((Pair.completedTensor.inl A OU OV).spaComap ⟨w, hw⟩).2
      simpa only [spaComapLoc_val] using
        spaComapLoc_mem_rationalSubset P SB.plus T s S hden ⟨_, hwB⟩
    · simp only [Set.mem_preimage, Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inr]
      rw [← Function.comp_apply (f := comap (CompletedTensor.inr A B C)), ← comap_comp,
        hgC, comap_comp, Function.comp_apply]
      have hwC : comap (CompletedTensor.inr A (Completion S) (Completion S')) w ∈
          spa (completedPlusSubring P' SC.plus T' s' S' hden') := by
        rw [← rationalLocalizationPair_plus P' SC hP' T' s' S' hden']
        simpa only [Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inr] using
          ((Pair.completedTensor.inr A OU OV).spaComap ⟨w, hw⟩).2
      simpa only [spaComapLoc_val] using
        spaComapLoc_mem_rationalSubset P' SC.plus T' s' S' hden' ⟨_, hwC⟩
  have hcomap := comap_mem_spa_completedPlusSubring Q SD.plus T'' s'' S'' hden''
    (e.symm : _ →+* _) he' ((mem_spa_iff _ _).mp hw).1
    (by simpa only [Set.mem_preimage, Pair.Hom.spaComap_val] using hmemD)
  simpa only [comap_vle, map_one, RingEquiv.coe_toRingHom] using
    ((mem_spa_iff _ _).mp hcomap).2 z hz

/-- Membership in the completed tensor plus ring over an unlocalised base `A` is equivalent to
membership of the image under `CompletedTensor.completionLocEquiv` in `completedPlusSubring` (not
`@[simp]` because `mem_completedPlusSubring_iff` already rewrites the right-hand side). -/
theorem Pair.mem_completedTensor_plus_iff_completionLocEquiv :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstance : IsAdicHom (algebraMap A B))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstance : IsAdicHom (algebraMap A C))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    ∀ x : CompletedTensor A (Completion S) (Completion S'),
      CompletedTensor.completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'' x ∈
          completedPlusSubring Q (SB.completedTensor A SC).plus
            (insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
              insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C)) :
                Finset _)
            (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') S'' hden'' ↔
        x ∈ ((P.rationalLocalizationPair SB hP T s S hden).completedTensor A
          (P'.rationalLocalizationPair SC hP' T' s' S' hden')).plus := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  let _ : Algebra A (Completion S) :=
    ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
  let _ : Algebra A (Completion S') :=
    ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion S)) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
      (inferInstance : IsAdicHom (algebraMap A B))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
      (inferInstance : IsAdicHom (algebraMap A C))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  intro x
  rw [← Pair.map_plus_completionLocEquiv P SB hP T s S hden P' SC hP' T' s' S' hden' Q S'' hden'']
  simp only [Subring.mem_map_equiv, RingEquiv.symm_apply_apply]

end UnlocalisedBase

end TauCeti.Huber

end
