/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Map
public import TauCeti.RingTheory.Huber.TensorProduct.Pair

/-!
# Topological ring isomorphism for completed tensor products of rational localisations

Let `(A, A⁺)`, `(B, B⁺)` and `(C, C⁺)` be Huber pairs with adic structure homomorphisms `A → B` and
`A → C`, and write `(D, D⁺) = (B, B⁺) ⊗̂_A (C, C⁺)` for their completed tensor Huber pair with
projections `p_B : Spa (D, D⁺) → Spa (B, B⁺)` and `p_C : Spa (D, D⁺) → Spa (C, C⁺)`. Let
`W = R(T_A/s_A) ⊆ Spa (A, A⁺)`, `U = R(T_B/s_B) ⊆ Spa (B, B⁺)` and `V = R(T_C/s_C) ⊆ Spa (C, C⁺)`
be rational subsets such that `U` and `V` map into `W`, and let `d = (T_D, s_D)` be any rational
presentation of `p_B⁻¹(U) ∩ p_C⁻¹(V)` in `Spa (D, D⁺)`.

Endowing `O_B(U) = B⟨T_B/s_B⟩` and `O_C(V) = C⟨T_C/s_C⟩` with their adic `O_A(W)`-algebra
structures via `ringHomOfMapsToRationalSubset` and `isAdicHom_ringHomOfMapsToRationalSubset`, this
file constructs the topological ring isomorphism

```text
Pair.completedTensorRationalEquiv : O_B(U) ⊗̂_{O_A(W)} O_C(V) ≃+* O_D(d)
```

and proves its continuity, homeomorphism property, action on the factor coprojections `inl` and
`inr`, and pure-tensor coefficient formula `e(ρ_B(b) ⊗ ρ_C(c)) = ρ_D(b ⊗ c)`. Plus-ring
compatibility and the induced morphisms of Huber pairs are established in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Rational.Pair`.

## Main definitions

* `TauCeti.Huber.Pair.completedTensorRationalEquiv`: the ring isomorphism
  `O_B(U) ⊗̂_{O_A(W)} O_C(V) ≃+* O_D(d)`.

## Main results

* `TauCeti.Huber.Pair.continuous_completedTensorRationalEquiv`,
  `TauCeti.Huber.Pair.continuous_completedTensorRationalEquiv_symm`,
  `TauCeti.Huber.Pair.isHomeomorph_completedTensorRationalEquiv`:
  `completedTensorRationalEquiv` is a homeomorphism.
* `TauCeti.Huber.Pair.completedTensorRationalEquiv_inl_toCompletionLoc`,
  `TauCeti.Huber.Pair.completedTensorRationalEquiv_inr_toCompletionLoc`,
  `TauCeti.Huber.Pair.completedTensorRationalEquiv_symm_toCompletionLoc_inl`,
  `TauCeti.Huber.Pair.completedTensorRationalEquiv_symm_toCompletionLoc_inr`:
  action of `completedTensorRationalEquiv` and its inverse on `inl` and `inr`.
* `TauCeti.Huber.Pair.completedTensorRationalEquiv_toCompletion_tmul`:
  pure-tensor coefficient formula `e(ρ_B(b) ⊗ ρ_C(c)) = ρ_D(b ⊗ c)`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  §3, proof of Proposition 3.7.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, after Definition 2.4.12.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.1 and Proposition 8.2(2).
-/

public section

open TensorProduct
open UniformSpace (Completion)

namespace TauCeti.Huber

open PairOfDefinition TauCeti.ValuationSpectrum

/-- Internal helper building the completed rational localisation `Pair` without requiring
`P.ringOfDefinition ≤ SR.plus`: every ring of integral elements already contains the ideal of
definition via topological nilpotence. -/
private noncomputable def locPairAux {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsHuberRing R] (P : PairOfDefinition R) (SR : Pair R)
    (T : Finset R) (s : R) (L : Type*) [CommRing L] [Algebra R L]
    [IsLocalization.Away s L] (hden : HasDenominatorPower P T s L) :
    letI := locUniformSpace P T s L hden
    letI := isUniformAddGroup_locUniformSpace P T s L hden
    letI := isTopologicalRing_locUniformSpace P T s L hden
    letI := isHuberRing_completion_locTopology P T s L hden
    Pair (Completion L) :=
  letI := locUniformSpace P T s L hden
  letI := isUniformAddGroup_locUniformSpace P T s L hden
  letI := isTopologicalRing_locUniformSpace P T s L hden
  letI := isHuberRing_completion_locTopology P T s L hden
  ⟨completedPlusSubring P SR.plus T s L hden,
    isRingOfIntegralElements_completedPlusSubring P SR.plus
      (fun _ hj ↦ SR.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
        (P.isTopologicallyNilpotent_of_mem_idealOfDefinition hj))
      SR.isRingOfIntegralElements.isPowerBounded_of_mem T s L hden⟩

private noncomputable def locPairHomAux {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsHuberRing R] (P : PairOfDefinition R) (SR : Pair R)
    (T : Finset R) (s : R) (L : Type*) [CommRing L] [Algebra R L]
    [IsLocalization.Away s L] (hden : HasDenominatorPower P T s L) :
    letI := locUniformSpace P T s L hden
    letI := isUniformAddGroup_locUniformSpace P T s L hden
    letI := isTopologicalRing_locUniformSpace P T s L hden
    letI := isHuberRing_completion_locTopology P T s L hden
    Pair.Hom SR (locPairAux P SR T s L hden) :=
  letI := locUniformSpace P T s L hden
  letI := isUniformAddGroup_locUniformSpace P T s L hden
  letI := isTopologicalRing_locUniformSpace P T s L hden
  letI := isHuberRing_completion_locTopology P T s L hden
  ⟨toCompletionLoc P T s L hden, continuous_toCompletionLoc P T s L hden,
    fun _ hr ↦ toCompletionLoc_mem_completedPlusSubring P SR.plus T s L hden hr⟩

section RationalEquiv

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- If `R(T_D/s_D)` cuts out `p_B⁻¹(U) ∩ p_C⁻¹(V)` inside `Spa ((B, B⁺) ⊗̂_A (C, C⁺))`, then
pullback along `CompletedTensor.inl A B C` maps `R(T_D/s_D)` into `R(T_B/s_B)`. -/
theorem Pair.completedTensor.mapsTo_inl_of_inter_eq
    {SB : Pair B} {TB : Finset B} {sB : B} {SC : Pair C} {TC : Finset C} {sC : C}
    {TD : Finset (CompletedTensor A B C)} {sD : CompletedTensor A B C}
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC))) :
    Set.MapsTo (comap (CompletedTensor.inl A B C))
      (rationalSubset (SB.completedTensor A SC).plus TD sD) (rationalSubset SB.plus TB sB) := by
  rw [← Pair.completedTensor.toRingHom_inl (S := SB) (T := SC),
    ← Pair.Hom.mapsTo_spaComap_rationalSubset_iff]
  intro v hv; rw [hd] at hv; exact hv.1

/-- If `R(T_D/s_D)` cuts out `p_B⁻¹(U) ∩ p_C⁻¹(V)` inside `Spa ((B, B⁺) ⊗̂_A (C, C⁺))`, then
pullback along `CompletedTensor.inr A B C` maps `R(T_D/s_D)` into `R(T_C/s_C)`. -/
theorem Pair.completedTensor.mapsTo_inr_of_inter_eq
    {SB : Pair B} {TB : Finset B} {sB : B} {SC : Pair C} {TC : Finset C} {sC : C}
    {TD : Finset (CompletedTensor A B C)} {sD : CompletedTensor A B C}
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC))) :
    Set.MapsTo (comap (CompletedTensor.inr A B C))
      (rationalSubset (SB.completedTensor A SC).plus TD sD) (rationalSubset SC.plus TC sC) := by
  rw [← Pair.completedTensor.toRingHom_inr (S := SB) (T := SC),
    ← Pair.Hom.mapsTo_spaComap_rationalSubset_iff]
  intro v hv; rw [hd] at hv; exact hv.2

variable [IsHuberRing A]
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

private noncomputable def leftToRationalLocAux
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC))) :
    letI := locUniformSpace PB TB sB LB hdenB
    letI := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
    letI := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
    letI := locUniformSpace PD TD sD LD hdenD
    letI := isUniformAddGroup_locUniformSpace PD TD sD LD hdenD
    letI := isTopologicalRing_locUniformSpace PD TD sD LD hdenD
    Completion LB →+* Completion LD :=
  ringHomOfMapsToRationalSubset PB SB.plus TB sB LB hdenB PD (SB.completedTensor A SC).plus
    (SB.completedTensor A SC).isRingOfIntegralElements.isPowerBounded_of_mem TD sD LD hdenD
    (CompletedTensor.continuous_inl A B C).continuousAt
    (Pair.completedTensor.mapsTo_inl_of_inter_eq hd)

private noncomputable def rightToRationalLocAux
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC))) :
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
    letI := locUniformSpace PD TD sD LD hdenD
    letI := isUniformAddGroup_locUniformSpace PD TD sD LD hdenD
    letI := isTopologicalRing_locUniformSpace PD TD sD LD hdenD
    Completion LC →+* Completion LD :=
  ringHomOfMapsToRationalSubset PC SC.plus TC sC LC hdenC PD (SB.completedTensor A SC).plus
    (SB.completedTensor A SC).isRingOfIntegralElements.isPowerBounded_of_mem TD sD LD hdenD
    (CompletedTensor.continuous_inr A B C).continuousAt
    (Pair.completedTensor.mapsTo_inr_of_inter_eq hd)

private noncomputable def toRationalLocHomAux
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
      ((locPairAux PB SB TB sB LB hdenB).completedTensor (Completion LA)
        (locPairAux PC SC TC sC LC hdenC))
      (locPairAux PD (SB.completedTensor A SC) TD sD LD hdenD) :=
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
  Pair.completedTensor.lift
    ⟨leftToRationalLocAux PB SB TB sB LB hdenB SC TC sC PD TD sD LD hdenD hd,
      continuous_ringHomOfMapsToRationalSubset _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      fun x hx ↦ ringHomOfMapsToRationalSubset_mem_completedPlusSubring
        PB SB.plus TB sB LB hdenB PD (SB.completedTensor A SC).plus
        (fun _ hj ↦ (SB.completedTensor A SC).isRingOfIntegralElements
          |>.mem_of_isTopologicallyNilpotent
          (PD.isTopologicallyNilpotent_of_mem_idealOfDefinition hj))
        (SB.completedTensor A SC).isRingOfIntegralElements.isPowerBounded_of_mem
        TD sD LD hdenD (CompletedTensor.continuous_inl A B C).continuousAt
        (Pair.completedTensor.mapsTo_inl_of_inter_eq hd) x hx⟩
    ⟨rightToRationalLocAux SB TB sB PC SC TC sC LC hdenC PD TD sD LD hdenD hd,
      continuous_ringHomOfMapsToRationalSubset _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      fun y hy ↦ ringHomOfMapsToRationalSubset_mem_completedPlusSubring
        PC SC.plus TC sC LC hdenC PD (SB.completedTensor A SC).plus
        (fun _ hj ↦ (SB.completedTensor A SC).isRingOfIntegralElements
          |>.mem_of_isTopologicallyNilpotent
          (PD.isTopologicallyNilpotent_of_mem_idealOfDefinition hj))
        (SB.completedTensor A SC).isRingOfIntegralElements.isPowerBounded_of_mem
        TD sD LD hdenD (CompletedTensor.continuous_inr A B C).continuousAt
        (Pair.completedTensor.mapsTo_inr_of_inter_eq hd) y hy⟩
    (by
      have hLcont : Continuous (leftToRationalLocAux
          PB SB TB sB LB hdenB SC TC sC PD TD sD LD hdenD hd) :=
        continuous_ringHomOfMapsToRationalSubset _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      have hRcont : Continuous (rightToRationalLocAux
          SB TB sB PC SC TC sC LC hdenC PD TD sD LD hdenD hd) :=
        continuous_ringHomOfMapsToRationalSubset _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      have hAB : Continuous (algebraMap (Completion LA) (Completion LB)) :=
        (inferInstance : IsAdicHom (algebraMap (Completion LA) (Completion LB))).continuous
      have hAC : Continuous (algebraMap (Completion LA) (Completion LC)) :=
        (inferInstance : IsAdicHom (algebraMap (Completion LA) (Completion LC))).continuous
      refine completion_locTopology_ringHom_ext_of_continuous PA TA sA LA hdenA _ _
        (hLcont.comp hAB) (hRcont.comp hAC) ?_
      ext a
      change leftToRationalLocAux PB SB TB sB LB hdenB SC TC sC PD TD sD LD hdenD hd
          (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PB SB.plus
            SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
            (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf
            (toCompletionLoc PA TA sA LA hdenA a)) =
        rightToRationalLocAux SB TB sB PC SC TC sC LC hdenC PD TD sD LD hdenD hd
          (ringHomOfMapsToRationalSubset PA SA.plus TA sA LA hdenA PC SC.plus
            SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
            (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg
            (toCompletionLoc PA TA sA LA hdenA a))
      simp only [toCompletionLoc_apply, leftToRationalLocAux, rightToRationalLocAux,
        ringHomOfMapsToRationalSubset_algebraMap_coe, CompletedTensor.inl_algebraMap,
        CompletedTensor.inr_algebraMap])

private noncomputable def baseToTensorLocHomAux
    (hf : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset SB.plus TB sB) (rationalSubset SA.plus TA sA))
    (hg : Set.MapsTo (comap (algebraMap A C))
      (rationalSubset SC.plus TC sC) (rationalSubset SA.plus TA sA)) :
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
    Pair.Hom (SB.completedTensor A SC)
      ((locPairAux PB SB TB sB LB hdenB).completedTensor (Completion LA)
        (locPairAux PC SC TC sC LC hdenC)) :=
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
  Pair.completedTensor.lift
    ((Pair.completedTensor.inl (Completion LA) (locPairAux PB SB TB sB LB hdenB)
      (locPairAux PC SC TC sC LC hdenC)).comp (locPairHomAux PB SB TB sB LB hdenB))
    ((Pair.completedTensor.inr (Completion LA) (locPairAux PB SB TB sB LB hdenB)
      (locPairAux PC SC TC sC LC hdenC)).comp (locPairHomAux PC SC TC sC LC hdenC))
    (by
      have hB : (toCompletionLoc PB TB sB LB hdenB).comp (algebraMap A B) =
          (algebraMap (Completion LA) (Completion LB)).comp
            (toCompletionLoc PA TA sA LA hdenA) :=
        (ringHomOfMapsToRationalSubset_comp_toCompletionLoc PA SA.plus TA sA LA hdenA PB SB.plus
          SB.isRingOfIntegralElements.isPowerBounded_of_mem TB sB LB hdenB
          (inferInstance : IsAdicHom (algebraMap A B)).continuous.continuousAt hf).symm
      have hC : (toCompletionLoc PC TC sC LC hdenC).comp (algebraMap A C) =
          (algebraMap (Completion LA) (Completion LC)).comp
            (toCompletionLoc PA TA sA LA hdenA) :=
        (ringHomOfMapsToRationalSubset_comp_toCompletionLoc PA SA.plus TA sA LA hdenA PC SC.plus
          SC.isRingOfIntegralElements.isPowerBounded_of_mem TC sC LC hdenC
          (inferInstance : IsAdicHom (algebraMap A C)).continuous.continuousAt hg).symm
      simp only [Pair.Hom.toRingHom_comp, Pair.completedTensor.toRingHom_inl,
        Pair.completedTensor.toRingHom_inr, locPairHomAux, RingHom.comp_assoc]
      rw [hB, ← RingHom.comp_assoc, CompletedTensor.inl_comp_algebraMap, RingHom.comp_assoc, ← hC])

private theorem baseToTensorLoc_comap_mem_rationalSubset
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
    ∀ w ∈ spa ((locPairAux PB SB TB sB LB hdenB).completedTensor (Completion LA)
        (locPairAux PC SC TC sC LC hdenC)).plus,
      comap (baseToTensorLocHomAux PA SA TA sA LA hdenA PB SB TB sB LB hdenB
        PC SC TC sC LC hdenC hf hg).toRingHom w ∈
        rationalSubset (SB.completedTensor A SC).plus TD sD := by
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
  let OU := locPairAux PB SB TB sB LB hdenB
  let OV := locPairAux PC SC TC sC LC hdenC
  let δ := baseToTensorLocHomAux PA SA TA sA LA hdenA PB SB TB sB LB hdenB
    PC SC TC sC LC hdenC hf hg
  have hB : δ.toRingHom.comp (CompletedTensor.inl A B C) =
      (CompletedTensor.inl (Completion LA) (Completion LB) (Completion LC)).comp
        (toCompletionLoc PB TB sB LB hdenB) := by
    simp only [δ, baseToTensorLocHomAux, Pair.completedTensor.toRingHom_lift,
      CompletedTensor.lift_comp_inl, Pair.Hom.toRingHom_comp, Pair.completedTensor.toRingHom_inl,
      locPairHomAux]
  have hC : δ.toRingHom.comp (CompletedTensor.inr A B C) =
      (CompletedTensor.inr (Completion LA) (Completion LB) (Completion LC)).comp
        (toCompletionLoc PC TC sC LC hdenC) := by
    simp only [δ, baseToTensorLocHomAux, Pair.completedTensor.toRingHom_lift,
      CompletedTensor.lift_comp_inr, Pair.Hom.toRingHom_comp, Pair.completedTensor.toRingHom_inr,
      locPairHomAux]
  intro w hw
  have hmem : δ.spaComap ⟨w, hw⟩ ∈
      Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD := by
    rw [hd]
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_preimage, Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inl]
      rw [← Function.comp_apply (f := comap (CompletedTensor.inl A B C)), ← comap_comp,
        hB, comap_comp, Function.comp_apply]
      simpa only [spaComapLoc_val, Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inl] using
        spaComapLoc_mem_rationalSubset PB SB.plus TB sB LB hdenB
          ⟨_, ((Pair.completedTensor.inl (Completion LA) OU OV).spaComap ⟨w, hw⟩).2⟩
    · simp only [Set.mem_preimage, Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inr]
      rw [← Function.comp_apply (f := comap (CompletedTensor.inr A B C)), ← comap_comp,
        hC, comap_comp, Function.comp_apply]
      simpa only [spaComapLoc_val, Pair.Hom.spaComap_val, Pair.completedTensor.toRingHom_inr] using
        spaComapLoc_mem_rationalSubset PC SC.plus TC sC LC hdenC
          ⟨_, ((Pair.completedTensor.inr (Completion LA) OU OV).spaComap ⟨w, hw⟩).2⟩
  simpa only [Set.mem_preimage, Pair.Hom.spaComap_val] using hmem

private noncomputable def ofRationalLocHomAux
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
      (locPairAux PD (SB.completedTensor A SC) TD sD LD hdenD)
      ((locPairAux PB SB TB sB LB hdenB).completedTensor (Completion LA)
        (locPairAux PC SC TC sC LC hdenC)) :=
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
  let huniq := existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset
    PD (SB.completedTensor A SC).plus TD sD LD hdenD
    ((locPairAux PB SB TB sB LB hdenB).completedTensor (Completion LA)
      (locPairAux PC SC TC sC LC hdenC)).plus
    ((locPairAux PB SB TB sB LB hdenB).completedTensor (Completion LA)
      (locPairAux PC SC TC sC LC hdenC)).isRingOfIntegralElements
    (baseToTensorLocHomAux PA SA TA sA LA hdenA PB SB TB sB LB hdenB
      PC SC TC sC LC hdenC hf hg).continuous_toRingHom.continuousAt
    (baseToTensorLoc_comap_mem_rationalSubset PA SA TA sA LA hdenA PB SB TB sB LB hdenB
      PC SC TC sC LC hdenC TD sD hf hg hd)
  { toRingHom := huniq.choose
    continuous_toRingHom := huniq.choose_spec.1.1
    map_mem_plus := fun z hz ↦
      ((locPairAux PB SB TB sB LB hdenB).completedTensor (Completion LA)
        (locPairAux PC SC TC sC LC hdenC)).isRingOfIntegralElements.mem_of_forall_vle_one
        fun w hw ↦ by
          have hcomap := comap_mem_spa_completedPlusSubring
            PD (SB.completedTensor A SC).plus TD sD LD hdenD huniq.choose huniq.choose_spec.1.1
            ((mem_spa_iff _ _).mp hw).1
            (by
              rw [huniq.choose_spec.1.2]
              exact baseToTensorLoc_comap_mem_rationalSubset PA SA TA sA LA hdenA
                PB SB TB sB LB hdenB PC SC TC sC LC hdenC TD sD hf hg hd w hw)
          simpa only [comap_vle, map_one] using ((mem_spa_iff _ _).mp hcomap).2 z hz }

private theorem toRationalLocHomAux_and_ofRationalLocHomAux_comp
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
    ((toRationalLocHomAux PA SA TA sA LA hdenA PB SB TB sB LB hdenB
          PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd).toRingHom.comp
        (ofRationalLocHomAux PA SA TA sA LA hdenA PB SB TB sB LB hdenB
          PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd).toRingHom =
        RingHom.id (Completion LD)) ∧
      ((ofRationalLocHomAux PA SA TA sA LA hdenA PB SB TB sB LB hdenB
          PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd).toRingHom.comp
        (toRationalLocHomAux PA SA TA sA LA hdenA PB SB TB sB LB hdenB
          PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd).toRingHom =
        RingHom.id (CompletedTensor (Completion LA) (Completion LB) (Completion LC))) := by
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
  let φ := toRationalLocHomAux PA SA TA sA LA hdenA PB SB TB sB LB hdenB
    PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd
  let ψ := ofRationalLocHomAux PA SA TA sA LA hdenA PB SB TB sB LB hdenB
    PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd
  let δ := baseToTensorLocHomAux PA SA TA sA LA hdenA PB SB TB sB LB hdenB
    PC SC TC sC LC hdenC hf hg
  have hψρ : ψ.toRingHom.comp (toCompletionLoc PD TD sD LD hdenD) = δ.toRingHom :=
    (existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset
      PD (SB.completedTensor A SC).plus TD sD LD hdenD
      ((locPairAux PB SB TB sB LB hdenB).completedTensor (Completion LA)
        (locPairAux PC SC TC sC LC hdenC)).plus
      ((locPairAux PB SB TB sB LB hdenB).completedTensor (Completion LA)
        (locPairAux PC SC TC sC LC hdenC)).isRingOfIntegralElements
      δ.continuous_toRingHom.continuousAt
      (baseToTensorLoc_comap_mem_rationalSubset PA SA TA sA LA hdenA PB SB TB sB LB hdenB
        PC SC TC sC LC hdenC TD sD hf hg hd)).choose_spec.1.2
  have hφL : φ.toRingHom.comp
      (CompletedTensor.inl (Completion LA) (Completion LB) (Completion LC)) =
      leftToRationalLocAux PB SB TB sB LB hdenB SC TC sC PD TD sD LD hdenD hd := by
    simp only [φ, toRationalLocHomAux, Pair.completedTensor.toRingHom_lift,
      CompletedTensor.lift_comp_inl]
  have hφR : φ.toRingHom.comp
      (CompletedTensor.inr (Completion LA) (Completion LB) (Completion LC)) =
      rightToRationalLocAux SB TB sB PC SC TC sC LC hdenC PD TD sD LD hdenD hd := by
    simp only [φ, toRationalLocHomAux, Pair.completedTensor.toRingHom_lift,
      CompletedTensor.lift_comp_inr]
  have hδL : δ.toRingHom.comp (CompletedTensor.inl A B C) =
      (CompletedTensor.inl (Completion LA) (Completion LB) (Completion LC)).comp
        (toCompletionLoc PB TB sB LB hdenB) := by
    simp only [δ, baseToTensorLocHomAux, Pair.completedTensor.toRingHom_lift,
      CompletedTensor.lift_comp_inl, Pair.Hom.toRingHom_comp, Pair.completedTensor.toRingHom_inl,
      locPairHomAux]
  have hδR : δ.toRingHom.comp (CompletedTensor.inr A B C) =
      (CompletedTensor.inr (Completion LA) (Completion LB) (Completion LC)).comp
        (toCompletionLoc PC TC sC LC hdenC) := by
    simp only [δ, baseToTensorLocHomAux, Pair.completedTensor.toRingHom_lift,
      CompletedTensor.lift_comp_inr, Pair.Hom.toRingHom_comp, Pair.completedTensor.toRingHom_inr,
      locPairHomAux]
  refine ⟨?_, ?_⟩
  · refine eq_id_of_comp_toCompletionLoc_eq_self PD TD sD LD hdenD _
      (φ.continuous_toRingHom.comp ψ.continuous_toRingHom) ?_
    rw [RingHom.comp_assoc, hψρ]
    refine CompletedTensor.hom_ext
      (φ.continuous_toRingHom.comp δ.continuous_toRingHom)
      (continuous_toCompletionLoc PD TD sD LD hdenD) ?_ ?_
    · rw [RingHom.comp_assoc, hδL, ← RingHom.comp_assoc, hφL]
      exact ringHomOfMapsToRationalSubset_comp_toCompletionLoc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · rw [RingHom.comp_assoc, hδR, ← RingHom.comp_assoc, hφR]
      exact ringHomOfMapsToRationalSubset_comp_toCompletionLoc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · have hc := ψ.continuous_toRingHom.comp φ.continuous_toRingHom
    refine CompletedTensor.hom_ext hc continuous_id ?_ ?_
    · refine completion_locTopology_ringHom_ext_of_continuous PB TB sB LB hdenB _ _
        (hc.comp (CompletedTensor.continuous_inl _ _ _))
        (continuous_id.comp (CompletedTensor.continuous_inl _ _ _)) ?_
      ext b
      have hφLb := RingHom.congr_fun hφL (toCompletionLoc PB TB sB LB hdenB b)
      have hψρd := RingHom.congr_fun hψρ (CompletedTensor.inl A B C b)
      have hδLb := RingHom.congr_fun hδL b
      have hloc := RingHom.congr_fun
        (ringHomOfMapsToRationalSubset_comp_toCompletionLoc PB SB.plus TB sB LB hdenB PD
          (SB.completedTensor A SC).plus
          (SB.completedTensor A SC).isRingOfIntegralElements.isPowerBounded_of_mem TD sD LD hdenD
          (CompletedTensor.continuous_inl A B C).continuousAt
          (Pair.completedTensor.mapsTo_inl_of_inter_eq hd)) b
      simp only [RingHom.comp_apply, RingHom.id_apply] at hφLb hψρd hδLb hloc ⊢
      rw [hφLb, leftToRationalLocAux, hloc, hψρd, hδLb]
    · refine completion_locTopology_ringHom_ext_of_continuous PC TC sC LC hdenC _ _
        (hc.comp (CompletedTensor.continuous_inr _ _ _))
        (continuous_id.comp (CompletedTensor.continuous_inr _ _ _)) ?_
      ext c
      have hφRc := RingHom.congr_fun hφR (toCompletionLoc PC TC sC LC hdenC c)
      have hψρd := RingHom.congr_fun hψρ (CompletedTensor.inr A B C c)
      have hδRc := RingHom.congr_fun hδR c
      have hloc := RingHom.congr_fun
        (ringHomOfMapsToRationalSubset_comp_toCompletionLoc PC SC.plus TC sC LC hdenC PD
          (SB.completedTensor A SC).plus
          (SB.completedTensor A SC).isRingOfIntegralElements.isPowerBounded_of_mem TD sD LD hdenD
          (CompletedTensor.continuous_inr A B C).continuousAt
          (Pair.completedTensor.mapsTo_inr_of_inter_eq hd)) c
      simp only [RingHom.comp_apply, RingHom.id_apply] at hφRc hψρd hδRc hloc ⊢
      rw [hφRc, rightToRationalLocAux, hloc, hψρd, hδRc]

/-- **Completed rational localisation commutes with completed tensor products of Huber pairs.**
Given rational subsets `W = R(T_A/s_A) ⊆ Spa (A, A⁺)`, `U = R(T_B/s_B) ⊆ Spa (B, B⁺)` and
`V = R(T_C/s_C) ⊆ Spa (C, C⁺)` with `U` and `V` mapping into `W`, and any rational presentation
`d = (T_D, s_D)` of `p_B⁻¹(U) ∩ p_C⁻¹(V)` in `Spa ((B, B⁺) ⊗̂_A (C, C⁺))`, the completed tensor
product `O_B(U) ⊗̂_{O_A(W)} O_C(V)` is isomorphic as a topological ring to `O_D(d)`. -/
noncomputable def Pair.completedTensorRationalEquiv
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
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
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
    CompletedTensor (Completion LA) (Completion LB) (Completion LC) ≃+* Completion LD :=
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
  let hcomp := toRationalLocHomAux_and_ofRationalLocHomAux_comp
    PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd
  RingEquiv.ofRingHom
    (toRationalLocHomAux PA SA TA sA LA hdenA PB SB TB sB LB hdenB
      PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd).toRingHom
    (ofRationalLocHomAux PA SA TA sA LA hdenA PB SB TB sB LB hdenB
      PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd).toRingHom
    hcomp.1 hcomp.2

/-- `Pair.completedTensorRationalEquiv` is continuous. -/
@[fun_prop]
theorem Pair.continuous_completedTensorRationalEquiv
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
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
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
    Continuous (Pair.completedTensorRationalEquiv
      PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd) :=
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
  (toRationalLocHomAux PA SA TA sA LA hdenA PB SB TB sB LB hdenB
    PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd).continuous_toRingHom

/-- The inverse of `Pair.completedTensorRationalEquiv` is continuous. -/
@[fun_prop]
theorem Pair.continuous_completedTensorRationalEquiv_symm
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
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
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
    Continuous (Pair.completedTensorRationalEquiv
      PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
      PD TD sD LD hdenD hf hg hd).symm :=
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
  (ofRationalLocHomAux PA SA TA sA LA hdenA PB SB TB sB LB hdenB
    PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd).continuous_toRingHom

/-- `Pair.completedTensorRationalEquiv` is a homeomorphism. -/
theorem Pair.isHomeomorph_completedTensorRationalEquiv
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
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
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
    IsHomeomorph (Pair.completedTensorRationalEquiv
      PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd) :=
  letI := locUniformSpace PA TA sA LA hdenA
  letI := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
  letI := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
  letI := locUniformSpace PB TB sB LB hdenB
  letI := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
  letI := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
  letI := locUniformSpace PC TC sC LC hdenC
  letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
  letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
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
  (Pair.completedTensorRationalEquiv
    PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
    PD TD sD LD hdenD hf hg hd).toEquiv.isHomeomorph_iff.mpr
    ⟨Pair.continuous_completedTensorRationalEquiv
        PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd,
      Pair.continuous_completedTensorRationalEquiv_symm
        PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd⟩

/-- `Pair.completedTensorRationalEquiv` maps `inl(ρ_B(b))` to `ρ_D(inl(b))`. -/
@[simp]
theorem Pair.completedTensorRationalEquiv_inl_toCompletionLoc
    (hf : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset SB.plus TB sB) (rationalSubset SA.plus TA sA))
    (hg : Set.MapsTo (comap (algebraMap A C))
      (rationalSubset SC.plus TC sC) (rationalSubset SA.plus TA sA))
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC)))
    (b : B) :
    letI := locUniformSpace PA TA sA LA hdenA
    letI := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
    letI := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
    letI := locUniformSpace PB TB sB LB hdenB
    letI := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
    letI := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
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
    Pair.completedTensorRationalEquiv
        PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd
        (CompletedTensor.inl (Completion LA) (Completion LB) (Completion LC)
          (algebraMap B LB b : Completion LB)) =
      (algebraMap (CompletedTensor A B C) LD (CompletedTensor.inl A B C b) : Completion LD) := by
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
  simp only [Pair.completedTensorRationalEquiv, RingEquiv.ofRingHom_apply, toRationalLocHomAux,
    Pair.completedTensor.toRingHom_lift, CompletedTensor.lift_inl, leftToRationalLocAux,
    ringHomOfMapsToRationalSubset_algebraMap_coe]

/-- `Pair.completedTensorRationalEquiv` maps `inr(ρ_C(c))` to `ρ_D(inr(c))`. -/
@[simp]
theorem Pair.completedTensorRationalEquiv_inr_toCompletionLoc
    (hf : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset SB.plus TB sB) (rationalSubset SA.plus TA sA))
    (hg : Set.MapsTo (comap (algebraMap A C))
      (rationalSubset SC.plus TC sC) (rationalSubset SA.plus TA sA))
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC)))
    (c : C) :
    letI := locUniformSpace PA TA sA LA hdenA
    letI := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
    letI := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
    letI := locUniformSpace PB TB sB LB hdenB
    letI := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
    letI := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
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
    Pair.completedTensorRationalEquiv
        PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd
        (CompletedTensor.inr (Completion LA) (Completion LB) (Completion LC)
          (algebraMap C LC c : Completion LC)) =
      (algebraMap (CompletedTensor A B C) LD (CompletedTensor.inr A B C c) : Completion LD) := by
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
  simp only [Pair.completedTensorRationalEquiv, RingEquiv.ofRingHom_apply, toRationalLocHomAux,
    Pair.completedTensor.toRingHom_lift, CompletedTensor.lift_inr, rightToRationalLocAux,
    ringHomOfMapsToRationalSubset_algebraMap_coe]

/-- The inverse of `Pair.completedTensorRationalEquiv` sends `ρ_D(inl(b))` to `inl(ρ_B(b))`. -/
@[simp]
theorem Pair.completedTensorRationalEquiv_symm_toCompletionLoc_inl
    (hf : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset SB.plus TB sB) (rationalSubset SA.plus TA sA))
    (hg : Set.MapsTo (comap (algebraMap A C))
      (rationalSubset SC.plus TC sC) (rationalSubset SA.plus TA sA))
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC)))
    (b : B) :
    letI := locUniformSpace PA TA sA LA hdenA
    letI := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
    letI := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
    letI := locUniformSpace PB TB sB LB hdenB
    letI := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
    letI := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
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
    (Pair.completedTensorRationalEquiv
        PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
        PD TD sD LD hdenD hf hg hd).symm
        (algebraMap (CompletedTensor A B C) LD (CompletedTensor.inl A B C b) : Completion LD) =
      CompletedTensor.inl (Completion LA) (Completion LB) (Completion LC)
        (algebraMap B LB b : Completion LB) :=
  (Pair.completedTensorRationalEquiv
    PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
    PD TD sD LD hdenD hf hg hd).toEquiv.symm_apply_eq.mpr
    (Pair.completedTensorRationalEquiv_inl_toCompletionLoc
      PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
      PD TD sD LD hdenD hf hg hd b).symm

/-- The inverse of `Pair.completedTensorRationalEquiv` sends `ρ_D(inr(c))` to `inr(ρ_C(c))`. -/
@[simp]
theorem Pair.completedTensorRationalEquiv_symm_toCompletionLoc_inr
    (hf : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset SB.plus TB sB) (rationalSubset SA.plus TA sA))
    (hg : Set.MapsTo (comap (algebraMap A C))
      (rationalSubset SC.plus TC sC) (rationalSubset SA.plus TA sA))
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC)))
    (c : C) :
    letI := locUniformSpace PA TA sA LA hdenA
    letI := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
    letI := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
    letI := locUniformSpace PB TB sB LB hdenB
    letI := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
    letI := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
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
    (Pair.completedTensorRationalEquiv
        PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
        PD TD sD LD hdenD hf hg hd).symm
        (algebraMap (CompletedTensor A B C) LD (CompletedTensor.inr A B C c) : Completion LD) =
      CompletedTensor.inr (Completion LA) (Completion LB) (Completion LC)
        (algebraMap C LC c : Completion LC) :=
  (Pair.completedTensorRationalEquiv
    PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
    PD TD sD LD hdenD hf hg hd).toEquiv.symm_apply_eq.mpr
    (Pair.completedTensorRationalEquiv_inr_toCompletionLoc
      PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC
      PD TD sD LD hdenD hf hg hd c).symm

/-- **Pure-tensor coefficient formula for `Pair.completedTensorRationalEquiv`**:
`e(ρ_B(b) ⊗ ρ_C(c)) = ρ_D(b ⊗ c)`. -/
theorem Pair.completedTensorRationalEquiv_toCompletion_tmul
    (hf : Set.MapsTo (comap (algebraMap A B))
      (rationalSubset SB.plus TB sB) (rationalSubset SA.plus TA sA))
    (hg : Set.MapsTo (comap (algebraMap A C))
      (rationalSubset SC.plus TC sC) (rationalSubset SA.plus TA sA))
    (hd : Subtype.val ⁻¹' rationalSubset (SB.completedTensor A SC).plus TD sD =
      ((Pair.completedTensor.inl A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SB.plus TB sB)) ∩
      ((Pair.completedTensor.inr A SB SC).spaComap ⁻¹'
        (Subtype.val ⁻¹' rationalSubset SC.plus TC sC)))
    (b : B) (c : C) :
    letI := locUniformSpace PA TA sA LA hdenA
    letI := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
    letI := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
    letI := locUniformSpace PB TB sB LB hdenB
    letI := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
    letI := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
    letI := locUniformSpace PC TC sC LC hdenC
    letI := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
    letI := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
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
    Pair.completedTensorRationalEquiv
        PA SA TA sA LA hdenA PB SB TB sB LB hdenB PC SC TC sC LC hdenC PD TD sD LD hdenD hf hg hd
        (CompletedTensor.toCompletion (Completion LA) (Completion LB) (Completion LC)
          (toCompletionLoc PB TB sB LB hdenB b ⊗ₜ[Completion LA]
            toCompletionLoc PC TC sC LC hdenC c)) =
      toCompletionLoc PD TD sD LD hdenD (CompletedTensor.toCompletion A B C (b ⊗ₜ[A] c)) := by
  let _ := locUniformSpace PA TA sA LA hdenA
  have _ := isUniformAddGroup_locUniformSpace PA TA sA LA hdenA
  have _ := isTopologicalRing_locUniformSpace PA TA sA LA hdenA
  let _ := locUniformSpace PB TB sB LB hdenB
  have _ := isUniformAddGroup_locUniformSpace PB TB sB LB hdenB
  have _ := isTopologicalRing_locUniformSpace PB TB sB LB hdenB
  let _ := locUniformSpace PC TC sC LC hdenC
  have _ := isUniformAddGroup_locUniformSpace PC TC sC LC hdenC
  have _ := isTopologicalRing_locUniformSpace PC TC sC LC hdenC
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
  rw [CompletedTensor.toCompletion_tmul, CompletedTensor.toCompletion_tmul, map_mul, map_mul,
    toCompletionLoc_apply, toCompletionLoc_apply,
    Pair.completedTensorRationalEquiv_inl_toCompletionLoc,
    Pair.completedTensorRationalEquiv_inr_toCompletionLoc,
    ← toCompletionLoc_apply PD TD sD LD hdenD, ← toCompletionLoc_apply PD TD sD LD hdenD]

end RationalEquiv

end TauCeti.Huber

end
