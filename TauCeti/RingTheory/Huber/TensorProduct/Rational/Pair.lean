/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Pushout
public import TauCeti.RingTheory.Huber.TensorProduct.Rational.Base
public import TauCeti.RingTheory.Huber.TensorProduct.Rational.Basic
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Completed tensor products of rational localisation Huber pairs

Let `A → B` and `A → C` be adic homomorphisms of Huber rings, `(B, B⁺)` and `(C, C⁺)` Huber pairs,
and `(D, D⁺) = (B, B⁺) ⊗̂_A (C, C⁺)` their completed tensor product. In
`TauCeti.RingTheory.Huber.TensorProduct.Rational.Basic`, the topological ring equivalence
`TauCeti.Huber.CompletedTensor.completionLocEquiv` identifies the completed tensor product
`B⟨T/s⟩ ⊗̂_A C⟨T'/s'⟩` of completed rational localisations with the completed localisation
`D⟨T''/(inl(s) · inr(s'))⟩`, where `T'' = ({inl(s)} ∪ inl(T)) · ({inr(s')} ∪ inr(T'))`.

This file upgrades `completionLocEquiv` to Huber pairs without completeness, Hausdorffness, Tate or
sheafiness hypotheses on `A`, `B`, `C`: it shows that `completionLocEquiv` carries the completed
tensor plus ring of `(B⟨T/s⟩, B_U⁺)` and `(C⟨T'/s'⟩, C_V⁺)` onto the rational localisation plus ring
`D_W⁺` of `(D, D⁺)`, constructs the mutually inverse morphisms of Huber pairs
`toRationalLocalization` and `ofRationalLocalization`, and combines them with
`TauCeti.RingTheory.Huber.TensorProduct.Rational.Base` to exhibit
`(D⟨T''/(inl(s) · inr(s'))⟩, D_W⁺)` as a completed pushout (`TauCeti.Huber.IsCompletedPushout`)
over any compatible rational localisation `(A⟨T₀/s₀⟩, A_0⁺)` of the base.

## Main definitions

* `TauCeti.Huber.Pair.completedTensor.toRationalLocalization`,
  `TauCeti.Huber.Pair.completedTensor.ofRationalLocalization`: mutually inverse morphisms of Huber
  pairs between `(B⟨T/s⟩, B_U⁺) ⊗̂_A (C⟨T'/s'⟩, C_V⁺)` and `(D⟨T''/s''⟩, D_W⁺)`.

## Main results

* `TauCeti.Huber.PairOfDefinition.completedPlusSubring_le_comap`: a continuous homomorphism out of
  `A⟨T/s⟩` sending `A⁺` and each `t/s` (`t ∈ T`) into a closed integrally closed subring carries
  `completedPlusSubring` into it.
* `TauCeti.Huber.CompletedTensor.completionLocEquiv_toCompletion_tmul`,
  `TauCeti.Huber.CompletedTensor.completionLocEquiv_inl_divBy`,
  `TauCeti.Huber.CompletedTensor.completionLocEquiv_inr_divBy`: action of `completionLocEquiv` on
  pure tensors and distinguished fractions.
* `TauCeti.Huber.Pair.completedTensor.map_completedPlusSubring_completionLocEquiv`,
  `TauCeti.Huber.Pair.completedTensor.map_plus_completionLocEquiv`: `completionLocEquiv` carries
  the completed tensor plus ring onto `completedPlusSubring` of `(B, B⁺) ⊗̂_A (C, C⁺)`.
* `TauCeti.Huber.Pair.completedTensor.isCompletedPushout_rationalLocalizationPair`: the localised
  completed tensor pair is a `TauCeti.Huber.IsCompletedPushout` of the rational localisation pairs
  over `(A⟨T₀/s₀⟩, A_0⁺)`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, after Definition 2.4.12.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  §3, proof of Proposition 3.7.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition and Definition 5.51,
  §7.5 and §8.1.
-/

public section

open TensorProduct UniformSpace TauCeti.Localization
open scoped Pointwise

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Rings of integral elements of targets bound the image of `A_U⁺`.** A continuous ring
homomorphism out of `A⟨T/s⟩` which carries `A⁺` and each distinguished fraction `t/s` (`t ∈ T`)
into a closed subring `R⁺` integrally closed in `R` carries `completedPlusSubring` into `R⁺`. -/
theorem completedPlusSubring_le_comap (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) {R : Type*} [CommRing R] [TopologicalSpace R]
    {Rplus : Subring R} (hclosed : IsClosed (Rplus : Set R)) [IsIntegrallyClosedIn Rplus R] :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ {φ : Completion S →+* R}, Continuous φ →
      (∀ a ∈ Aplus, φ (toCompletionLoc P T s S hden a) ∈ Rplus) →
      (∀ t ∈ T, φ ((divBy t s : S) : Completion S) ∈ Rplus) →
      completedPlusSubring P Aplus T s S hden ≤ Rplus.comap φ := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro φ hφ hA hT
  refine (completedPlusSubring_le_iff P Aplus T s S hden (hclosed.preimage hφ)).mpr ?_
  let g := φ.comp Completion.coeRingHom
  have hle : (Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S))).toSubring ≤
      Rplus.comap g := by
    rw [Algebra.adjoin_eq_ring_closure, Subring.closure_le]
    rintro w (⟨⟨a, ha⟩, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap]
      have hga : g (algebraMap Aplus S ⟨a, ha⟩) = φ (toCompletionLoc P T s S hden a) := by
        rw [toCompletionLoc_apply]; rfl
      rw [hga]
      exact hA a ha
    · exact hT t ht
  intro x hx
  exact (Subring.integralClosure_subring_le_iff
    (S := Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S)))
    (T := Rplus.comap g)).mpr hle hx

/-- For any Huber pair `U` on `A` and any pair of definition `P` of `A`, `completedPlusSubring` is a
ring of integral elements of `A⟨T/s⟩`, even without assuming `P.ringOfDefinition ≤ U.plus`: elements
of `P.idealOfDefinition` are topologically nilpotent and therefore belong to `U.plus`. -/
theorem isRingOfIntegralElements_completedPlusSubring_of_pair [IsHuberRing A]
    (P : PairOfDefinition A) (U : Pair A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    IsRingOfIntegralElements (completedPlusSubring P U.plus T s S hden) :=
  isRingOfIntegralElements_completedPlusSubring P U.plus
    (fun _ hj ↦ U.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
      (P.isTopologicallyNilpotent_of_mem_idealOfDefinition hj))
    U.isRingOfIntegralElements.isPowerBounded_of_mem T s S hden

end TauCeti.Huber.PairOfDefinition

namespace TauCeti.Huber.CompletedTensor

open PairOfDefinition

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)] [DecidableEq (CompletedTensor A B C)]
  (P : PairOfDefinition B) (T : Finset B) (s : B) (S : Type*) [CommRing S] [Algebra B S]
  [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
  (P' : PairOfDefinition C) (T' : Finset C) (s' : C) (S' : Type*) [CommRing S'] [Algebra C S']
  [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P' T' s' S')
  (Q : PairOfDefinition (CompletedTensor A B C)) (S'' : Type*) [CommRing S'']
  [Algebra (CompletedTensor A B C) S''] [IsLocalization.Away (inl A B C s * inr A B C s') S'']
  (hden'' : HasDenominatorPower Q
    (insert (inl A B C s) (T.image (inl A B C)) *
      insert (inr A B C s') (T'.image (inr A B C)) : Finset _)
    (inl A B C s * inr A B C s') S'')

/-- On pure tensors of images of `b ∈ B` and `c ∈ C`, `completionLocEquiv` sends
`ρ_B(b) ⊗ ρ_C(c)` to `ρ_D(b ⊗ c)`. -/
theorem completionLocEquiv_toCompletion_tmul (b : B) (c : C) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
        (toCompletion A (Completion S) (Completion S')
          (toCompletionLoc P T s S hden b ⊗ₜ[A] toCompletionLoc P' T' s' S' hden' c)) =
      toCompletionLoc Q _ _ S'' hden'' (toCompletion A B C (b ⊗ₜ[A] c)) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  let _ : Algebra A (Completion S) :=
    ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
  let _ : Algebra A (Completion S') :=
    ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion S)) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  simp only [toCompletion_tmul, map_mul, toCompletionLoc_apply,
    completionLocEquiv_inl_toCompletionLoc, completionLocEquiv_inr_toCompletionLoc,
    ← Completion.coe_mul]

/-- `completionLocEquiv` sends `(b/s) ⊗ 1` to `(inl(b) · inr(s')) / (inl(s) · inr(s'))` in
`D⟨T''/s''⟩`. -/
@[simp] theorem completionLocEquiv_inl_divBy (b : B) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
        (inl A (Completion S) (Completion S') ((divBy b s : S) : Completion S)) =
      ((divBy (inl A B C b * inr A B C s') (inl A B C s * inr A B C s') : S'') :
        Completion S'') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  let _ : Algebra A (Completion S) :=
    ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
  let _ : Algebra A (Completion S') :=
    ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion S)) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have hu := isUnit_toCompletionLoc_of_dvd Q _ _ S'' hden''
    (dvd_refl (inl A B C s * inr A B C s'))
  rw [toCompletionLoc_apply] at hu
  refine hu.mul_left_inj.mp ?_
  calc
    completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
          (inl A (Completion S) (Completion S') ((divBy b s : S) : Completion S)) *
        (algebraMap (CompletedTensor A B C) S'' (inl A B C s * inr A B C s') : Completion S'')
      = (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
            (inl A (Completion S) (Completion S') ((divBy b s : S) : Completion S)) *
          completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
            (inl A (Completion S) (Completion S') (algebraMap B S s : Completion S))) *
        (algebraMap (CompletedTensor A B C) S'' (inr A B C s') : Completion S'') := by
      rw [completionLocEquiv_inl_toCompletionLoc, map_mul, Completion.coe_mul, mul_assoc]
    _ = (algebraMap (CompletedTensor A B C) S'' (inl A B C b * inr A B C s') : Completion S'') := by
      rw [← map_mul, ← map_mul, ← Completion.coe_mul, divBy_mul_algebraMap,
        completionLocEquiv_inl_toCompletionLoc, ← Completion.coe_mul, ← map_mul]
    _ = ((divBy (inl A B C b * inr A B C s') (inl A B C s * inr A B C s') : S'') :
          Completion S'') *
        (algebraMap (CompletedTensor A B C) S'' (inl A B C s * inr A B C s') : Completion S'') := by
      rw [← Completion.coe_mul, divBy_mul_algebraMap]

/-- `completionLocEquiv` sends `1 ⊗ (c/s')` to `(inl(s) · inr(c)) / (inl(s) · inr(s'))` in
`D⟨T''/s''⟩`. -/
@[simp] theorem completionLocEquiv_inr_divBy (c : C) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI : Algebra A (Completion S) :=
      ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
    letI : Algebra A (Completion S') :=
      ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
    haveI : IsAdicHom (algebraMap A (Completion S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
        (inr A (Completion S) (Completion S') ((divBy c s' : S') : Completion S')) =
      ((divBy (inl A B C s * inr A B C c) (inl A B C s * inr A B C s') : S'') :
        Completion S'') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  let _ : Algebra A (Completion S) :=
    ((toCompletionLoc P T s S hden).comp (algebraMap A B)).toAlgebra
  let _ : Algebra A (Completion S') :=
    ((toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)).toAlgebra
  have _ : IsAdicHom (algebraMap A (Completion S)) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have hu := isUnit_toCompletionLoc_of_dvd Q _ _ S'' hden''
    (dvd_refl (inl A B C s * inr A B C s'))
  rw [toCompletionLoc_apply] at hu
  refine hu.mul_left_inj.mp ?_
  calc
    completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
          (inr A (Completion S) (Completion S') ((divBy c s' : S') : Completion S')) *
        (algebraMap (CompletedTensor A B C) S'' (inl A B C s * inr A B C s') : Completion S'')
      = (algebraMap (CompletedTensor A B C) S'' (inl A B C s) : Completion S'') *
          (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
            (inr A (Completion S) (Completion S') ((divBy c s' : S') : Completion S')) *
          completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
            (inr A (Completion S) (Completion S') (algebraMap C S' s' : Completion S'))) := by
      rw [completionLocEquiv_inr_toCompletionLoc, map_mul, Completion.coe_mul]
      ring
    _ = (algebraMap (CompletedTensor A B C) S'' (inl A B C s * inr A B C c) : Completion S'') := by
      rw [← map_mul, ← map_mul, ← Completion.coe_mul, divBy_mul_algebraMap,
        completionLocEquiv_inr_toCompletionLoc, ← Completion.coe_mul, ← map_mul]
    _ = ((divBy (inl A B C s * inr A B C c) (inl A B C s * inr A B C s') : S'') :
          Completion S'') *
        (algebraMap (CompletedTensor A B C) S'' (inl A B C s * inr A B C s') : Completion S'') := by
      rw [← Completion.coe_mul, divBy_mul_algebraMap]

end TauCeti.Huber.CompletedTensor

namespace TauCeti.Huber.Pair.completedTensor

open CompletedTensor PairOfDefinition

section FixedBase

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)] [DecidableEq (CompletedTensor A B C)]
  (P : PairOfDefinition B) (UB : Pair B) (T : Finset B) (s : B) (S : Type*) [CommRing S]
  [Algebra B S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
  (P' : PairOfDefinition C) (UC : Pair C) (T' : Finset C) (s' : C) (S' : Type*) [CommRing S']
  [Algebra C S'] [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P' T' s' S')
  (Q : PairOfDefinition (CompletedTensor A B C)) (S'' : Type*) [CommRing S'']
  [Algebra (CompletedTensor A B C) S'']
  [IsLocalization.Away (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') S'']
  (hden'' : HasDenominatorPower Q
    (insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
      insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C)) : Finset _)
    (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') S'')

private theorem completionLocEquiv_plus_le :
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
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    ((⟨completedPlusSubring P UB.plus T s S hden,
        isRingOfIntegralElements_completedPlusSubring_of_pair P UB T s S hden⟩ :
          Pair (Completion S)).completedTensor A
      ⟨completedPlusSubring P' UC.plus T' s' S' hden',
        isRingOfIntegralElements_completedPlusSubring_of_pair P' UC T' s' S' hden'⟩).plus ≤
      (completedPlusSubring Q (UB.completedTensor A UC).plus _ _ S'' hden'').comap
        (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').toRingHom := by
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
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  let O_U : Pair (Completion S) :=
    ⟨completedPlusSubring P UB.plus T s S hden,
      isRingOfIntegralElements_completedPlusSubring_of_pair P UB T s S hden⟩
  let O_V : Pair (Completion S') :=
    ⟨completedPlusSubring P' UC.plus T' s' S' hden',
      isRingOfIntegralElements_completedPlusSubring_of_pair P' UC T' s' S' hden'⟩
  let hD := isRingOfIntegralElements_completedPlusSubring_of_pair Q (UB.completedTensor A UC)
    _ _ S'' hden''
  have _ := hD.isIntegrallyClosedIn
  have hclosed := isClosed_completedPlusSubring Q (UB.completedTensor A UC).plus _ _ S'' hden''
  refine O_U.completedTensor_plus_le_comap O_V hclosed
    (f := (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').toRingHom)
    (continuous_completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'') ?_ ?_
  · refine completedPlusSubring_le_comap P UB.plus T s S hden hclosed
      (φ := (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').toRingHom.comp
        (CompletedTensor.inl A (Completion S) (Completion S')))
      ((continuous_completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').comp
        (CompletedTensor.continuous_inl _ _ _)) (fun b hb ↦ ?_) (fun t ht ↦ ?_)
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        toCompletionLoc_apply, completionLocEquiv_inl_toCompletionLoc]
      rw [← toCompletionLoc_apply Q _ _ S'' hden'']
      exact toCompletionLoc_mem_completedPlusSubring Q (UB.completedTensor A UC).plus
        _ _ S'' hden'' (UB.inl_mem_completedTensor_plus UC hb)
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        completionLocEquiv_inl_divBy]
      exact divBy_mem_completedPlusSubring Q (UB.completedTensor A UC).plus _ _ S'' hden''
        (Finset.mul_mem_mul (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ht))
          (Finset.mem_insert_self _ _))
  · refine completedPlusSubring_le_comap P' UC.plus T' s' S' hden' hclosed
      (φ := (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').toRingHom.comp
        (CompletedTensor.inr A (Completion S) (Completion S')))
      ((continuous_completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').comp
        (CompletedTensor.continuous_inr _ _ _)) (fun c hc ↦ ?_) (fun t' ht' ↦ ?_)
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        toCompletionLoc_apply, completionLocEquiv_inr_toCompletionLoc]
      rw [← toCompletionLoc_apply Q _ _ S'' hden'']
      exact toCompletionLoc_mem_completedPlusSubring Q (UB.completedTensor A UC).plus
        _ _ S'' hden'' (UB.inr_mem_completedTensor_plus UC hc)
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        completionLocEquiv_inr_divBy]
      exact divBy_mem_completedPlusSubring Q (UB.completedTensor A UC).plus _ _ S'' hden''
        (Finset.mul_mem_mul (Finset.mem_insert_self _ _)
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ht')))

private theorem completionLocEquiv_symm_plus_le :
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
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    completedPlusSubring Q (UB.completedTensor A UC).plus _ _ S'' hden'' ≤
      ((⟨completedPlusSubring P UB.plus T s S hden,
          isRingOfIntegralElements_completedPlusSubring_of_pair P UB T s S hden⟩ :
            Pair (Completion S)).completedTensor A
        ⟨completedPlusSubring P' UC.plus T' s' S' hden',
          isRingOfIntegralElements_completedPlusSubring_of_pair P' UC T' s' S' hden'⟩).plus.comap
        (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm.toRingHom := by
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
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  let O_U : Pair (Completion S) :=
    ⟨completedPlusSubring P UB.plus T s S hden,
      isRingOfIntegralElements_completedPlusSubring_of_pair P UB T s S hden⟩
  let O_V : Pair (Completion S') :=
    ⟨completedPlusSubring P' UC.plus T' s' S' hden',
      isRingOfIntegralElements_completedPlusSubring_of_pair P' UC T' s' S' hden'⟩
  let W := O_U.completedTensor A O_V
  have _ := W.isRingOfIntegralElements.isIntegrallyClosedIn
  have hWclosed := W.plus.toAddSubgroup.isClosed_of_isOpen W.isRingOfIntegralElements.isOpen
  let e := completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
  refine completedPlusSubring_le_comap Q (UB.completedTensor A UC).plus _ _ S'' hden'' hWclosed
    (φ := e.symm.toRingHom)
    (continuous_completionLocEquiv_symm P T s S hden P' T' s' S' hden' Q S'' hden'')
    (fun d hd ↦ ?_) (fun x hx ↦ ?_)
  · refine UB.completedTensor_plus_le_comap UC hWclosed
      (f := e.symm.toRingHom.comp (toCompletionLoc Q _ _ S'' hden''))
      ((continuous_completionLocEquiv_symm P T s S hden P' T' s' S' hden' Q S'' hden'').comp
        (continuous_toCompletionLoc Q _ _ S'' hden''))
      (fun b hb ↦ ?_) (fun c hc ↦ ?_) hd
    · dsimp only [e]
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        toCompletionLoc_apply, completionLocEquiv_symm_toCompletionLoc_inl]
      rw [← toCompletionLoc_apply P T s S hden]
      exact O_U.inl_mem_completedTensor_plus (A := A) O_V
        (toCompletionLoc_mem_completedPlusSubring P UB.plus T s S hden hb)
    · dsimp only [e]
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        toCompletionLoc_apply, completionLocEquiv_symm_toCompletionLoc_inr]
      rw [← toCompletionLoc_apply P' T' s' S' hden']
      exact O_U.inr_mem_completedTensor_plus (A := A) O_V
        (toCompletionLoc_mem_completedPlusSubring P' UC.plus T' s' S' hden' hc)
  · obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hx
    have hleft : ∃ y ∈ O_U.plus,
        e.symm (toCompletionLoc Q _ _ S'' hden'' a) =
          CompletedTensor.inl A (Completion S) (Completion S') y *
            e.symm (toCompletionLoc Q _ _ S'' hden'' (CompletedTensor.inl A B C s)) := by
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact ⟨1, O_U.plus.one_mem, by simp⟩
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
      refine ⟨((divBy t s : S) : Completion S),
        divBy_mem_completedPlusSubring P UB.plus T s S hden ht, ?_⟩
      dsimp only [e]
      simp only [toCompletionLoc_apply, completionLocEquiv_symm_toCompletionLoc_inl,
        ← map_mul, ← Completion.coe_mul, divBy_mul_algebraMap]
    have hright : ∃ z ∈ O_V.plus,
        e.symm (toCompletionLoc Q _ _ S'' hden'' b) =
          CompletedTensor.inr A (Completion S) (Completion S') z *
            e.symm (toCompletionLoc Q _ _ S'' hden'' (CompletedTensor.inr A B C s')) := by
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨1, O_V.plus.one_mem, by simp⟩
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hb
      refine ⟨((divBy t' s' : S') : Completion S'),
        divBy_mem_completedPlusSubring P' UC.plus T' s' S' hden' ht', ?_⟩
      dsimp only [e]
      simp only [toCompletionLoc_apply, completionLocEquiv_symm_toCompletionLoc_inr,
        ← map_mul, ← Completion.coe_mul, divBy_mul_algebraMap]
    obtain ⟨y, hy, hay⟩ := hleft
    obtain ⟨z, hz, hbz⟩ := hright
    have hu := (isUnit_toCompletionLoc_of_dvd Q _ _ S'' hden''
      (dvd_refl (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s'))).map e.symm.toRingHom
    have heq : e.symm ((divBy (a * b)
        (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') : S'') : Completion S'') =
        CompletedTensor.inl A (Completion S) (Completion S') y *
          CompletedTensor.inr A (Completion S) (Completion S') z := by
      refine hu.mul_left_inj.mp ?_
      calc
        e.symm ((divBy (a * b)
            (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') : S'') : Completion S'') *
            e.symm.toRingHom (toCompletionLoc Q _ _ S'' hden''
              (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s'))
          = e.symm (toCompletionLoc Q _ _ S'' hden'' (a * b)) := by
          rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, ← map_mul,
            toCompletionLoc_apply, toCompletionLoc_apply, ← Completion.coe_mul,
            divBy_mul_algebraMap]
        _ = (CompletedTensor.inl A (Completion S) (Completion S') y *
              CompletedTensor.inr A (Completion S) (Completion S') z) *
            e.symm.toRingHom (toCompletionLoc Q _ _ S'' hden''
              (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s')) := by
          rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_mul, map_mul, map_mul,
            map_mul, hay, hbz]
          ring
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, heq]
    exact mul_mem (O_U.inl_mem_completedTensor_plus (A := A) O_V hy)
      (O_U.inr_mem_completedTensor_plus (A := A) O_V hz)

/-- **`completionLocEquiv` identifies the completed tensor plus ring with `completedPlusSubring`**,
requiring no ring-of-definition containment hypotheses on `P`, `P'`, `Q`. -/
theorem map_completedPlusSubring_completionLocEquiv :
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
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    ((⟨completedPlusSubring P UB.plus T s S hden,
        isRingOfIntegralElements_completedPlusSubring_of_pair P UB T s S hden⟩ :
          Pair (Completion S)).completedTensor A
      ⟨completedPlusSubring P' UC.plus T' s' S' hden',
        isRingOfIntegralElements_completedPlusSubring_of_pair P' UC T' s' S' hden'⟩).plus.map
        (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').toRingHom =
      completedPlusSubring Q (UB.completedTensor A UC).plus _ _ S'' hden'' := by
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
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  refine le_antisymm
    (Subring.map_le_iff_le_comap.mpr
      (completionLocEquiv_plus_le P UB T s S hden P' UC T' s' S' hden' Q S'' hden''))
    fun y hy ↦ ⟨(completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm y,
      completionLocEquiv_symm_plus_le P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hy,
      (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').apply_symm_apply y⟩

section RationalLocalizationPair

variable (hP : P.ringOfDefinition ≤ UB.plus) (hP' : P'.ringOfDefinition ≤ UC.plus)
  (hQ : Q.ringOfDefinition ≤ (UB.completedTensor A UC).plus)

/-- **`completionLocEquiv` maps the plus ring of `(B⟨T/s⟩, B_U⁺) ⊗̂_A (C⟨T'/s'⟩, C_V⁺)` onto the
plus ring of `D⟨T''/s''⟩`.** -/
theorem map_plus_completionLocEquiv :
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
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    letI := isHuberRing_completion_locTopology Q _ _ S'' hden''
    (((rationalLocalizationPair P UB hP T s S hden).completedTensor A
        (rationalLocalizationPair P' UC hP' T' s' S' hden')).plus.map
        (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').toRingHom) =
      (rationalLocalizationPair Q (UB.completedTensor A UC) hQ _ _ S'' hden'').plus := by
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
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  have hUB : rationalLocalizationPair P UB hP T s S hden =
      ⟨completedPlusSubring P UB.plus T s S hden,
        isRingOfIntegralElements_completedPlusSubring_of_pair P UB T s S hden⟩ :=
    Pair.ext (rationalLocalizationPair_plus P UB hP T s S hden)
  have hUC : rationalLocalizationPair P' UC hP' T' s' S' hden' =
      ⟨completedPlusSubring P' UC.plus T' s' S' hden',
        isRingOfIntegralElements_completedPlusSubring_of_pair P' UC T' s' S' hden'⟩ :=
    Pair.ext (rationalLocalizationPair_plus P' UC hP' T' s' S' hden')
  rw [hUB, hUC, rationalLocalizationPair_plus]
  exact map_completedPlusSubring_completionLocEquiv
    P UB T s S hden P' UC T' s' S' hden' Q S'' hden''

/-- Membership in the plus ring of `(B⟨T/s⟩, B_U⁺) ⊗̂_A (C⟨T'/s'⟩, C_V⁺)` is tested in the plus
ring of `D⟨T''/s''⟩` via `completionLocEquiv`. -/
theorem mem_completedTensor_plus_iff_completionLocEquiv :
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
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    letI := isHuberRing_completion_locTopology Q _ _ S'' hden''
    ∀ x : CompletedTensor A (Completion S) (Completion S'),
      x ∈ ((rationalLocalizationPair P UB hP T s S hden).completedTensor A
          (rationalLocalizationPair P' UC hP' T' s' S' hden')).plus ↔
        completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'' x ∈
          (rationalLocalizationPair Q (UB.completedTensor A UC) hQ _ _ S'' hden'').plus := by
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
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  intro x
  rw [← map_plus_completionLocEquiv P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ]
  exact (completionLocEquiv P T s S hden P' T' s' S' hden'
    Q S'' hden'').injective.mem_set_image.symm

/-- The forward rational-localisation comparison
`(B⟨T/s⟩, B_U⁺) ⊗̂_A (C⟨T'/s'⟩, C_V⁺) → (D⟨T''/s''⟩, D_W⁺)` as a morphism of Huber pairs. -/
noncomputable def toRationalLocalization :
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
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    letI := isHuberRing_completion_locTopology Q _ _ S'' hden''
    Hom ((rationalLocalizationPair P UB hP T s S hden).completedTensor A
        (rationalLocalizationPair P' UC hP' T' s' S' hden'))
      (rationalLocalizationPair Q (UB.completedTensor A UC) hQ _ _ S'' hden'') :=
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
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  { toRingHom := (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').toRingHom
    continuous_toRingHom :=
      continuous_completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
    map_mem_plus := fun x hx ↦
      (mem_completedTensor_plus_iff_completionLocEquiv
        P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ x).mp hx }

/-- The inverse rational-localisation comparison
`(D⟨T''/s''⟩, D_W⁺) → (B⟨T/s⟩, B_U⁺) ⊗̂_A (C⟨T'/s'⟩, C_V⁺)` as a morphism of Huber pairs. -/
noncomputable def ofRationalLocalization :
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
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    letI := isHuberRing_completion_locTopology Q _ _ S'' hden''
    Hom (rationalLocalizationPair Q (UB.completedTensor A UC) hQ _ _ S'' hden'')
      ((rationalLocalizationPair P UB hP T s S hden).completedTensor A
        (rationalLocalizationPair P' UC hP' T' s' S' hden')) :=
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
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  { toRingHom := (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm.toRingHom
    continuous_toRingHom :=
      continuous_completionLocEquiv_symm P T s S hden P' T' s' S' hden' Q S'' hden''
    map_mem_plus := fun y hy ↦
      (mem_completedTensor_plus_iff_completionLocEquiv
        P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ _).mpr (by simpa using hy) }

/-- The underlying ring homomorphism of `toRationalLocalization`. -/
@[simp] theorem toRingHom_toRationalLocalization :
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
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    letI := isHuberRing_completion_locTopology Q _ _ S'' hden''
    (toRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ).toRingHom =
      (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').toRingHom := (rfl)

/-- The underlying ring homomorphism of `ofRationalLocalization`. -/
@[simp] theorem toRingHom_ofRationalLocalization :
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
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    letI := isHuberRing_completion_locTopology Q _ _ S'' hden''
    (ofRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ).toRingHom =
      (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm.toRingHom := (rfl)

/-- `ofRationalLocalization` is a left inverse to `toRationalLocalization`. -/
@[simp] theorem ofRationalLocalization_comp_toRationalLocalization :
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
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    letI := isHuberRing_completion_locTopology Q _ _ S'' hden''
    (ofRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ).comp
        (toRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ) =
      Hom.id _ := by
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
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  ext x; simp

/-- `toRationalLocalization` is a left inverse to `ofRationalLocalization`. -/
@[simp] theorem toRationalLocalization_comp_ofRationalLocalization :
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
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    letI := isHuberRing_completion_locTopology Q _ _ S'' hden''
    (toRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ).comp
        (ofRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ) =
      Hom.id _ := by
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
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  ext x; simp

end RationalLocalizationPair

end FixedBase

section Pushout

universe u

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing A] [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)] [DecidableEq (CompletedTensor A B C)]

/-- **The localised completed tensor pair is a completed pushout of the localised factor pairs.**
Given morphisms `f₀ : (A⟨T₀/s₀⟩, A_0⁺) → (B⟨T/s⟩, B_U⁺)` and
`g₀ : (A⟨T₀/s₀⟩, A_0⁺) → (C⟨T'/s'⟩, C_V⁺)` compatible with `A → B` and `A → C`, `(D⟨T''/s''⟩, D_W⁺)`
forms a `TauCeti.Huber.IsCompletedPushout` square with `f₀` and `g₀`. -/
theorem isCompletedPushout_rationalLocalizationPair
    (P₀ : PairOfDefinition A) (UA : Pair A) (hP₀ : P₀.ringOfDefinition ≤ UA.plus)
    (T₀ : Finset A) (s₀ : A) (S₀ : Type u) [CommRing S₀] [Algebra A S₀]
    [IsLocalization.Away s₀ S₀] (hden₀ : HasDenominatorPower P₀ T₀ s₀ S₀)
    (P : PairOfDefinition B) (UB : Pair B) (hP : P.ringOfDefinition ≤ UB.plus)
    (T : Finset B) (s : B) (S : Type u) [CommRing S] [Algebra B S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition C) (UC : Pair C) (hP' : P'.ringOfDefinition ≤ UC.plus)
    (T' : Finset C) (s' : C) (S' : Type u) [CommRing S'] [Algebra C S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P' T' s' S')
    (Q : PairOfDefinition (CompletedTensor A B C))
    (hQ : Q.ringOfDefinition ≤ (UB.completedTensor A UC).plus) (S'' : Type u) [CommRing S'']
    [Algebra (CompletedTensor A B C) S'']
    [IsLocalization.Away (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') S'']
    (hden'' : HasDenominatorPower Q
      (insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
        insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C)) : Finset _)
      (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') S'') :
    letI := locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
    letI := isHuberRing_completion_locTopology P₀ T₀ s₀ S₀ hden₀
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
        (inferInstanceAs (IsAdicHom (algebraMap A B)))
    haveI : IsAdicHom (algebraMap A (Completion S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C)))
    letI := locUniformSpace Q _ _ S'' hden''
    letI := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
    letI := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
    letI := isHuberRing_completion_locTopology Q _ _ S'' hden''
    ∀ (f₀ : Hom (rationalLocalizationPair P₀ UA hP₀ T₀ s₀ S₀ hden₀)
          (rationalLocalizationPair P UB hP T s S hden))
      (g₀ : Hom (rationalLocalizationPair P₀ UA hP₀ T₀ s₀ S₀ hden₀)
          (rationalLocalizationPair P' UC hP' T' s' S' hden'))
      (hf₀ : f₀.toRingHom.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) =
        (toCompletionLoc P T s S hden).comp (algebraMap A B))
      (hg₀ : g₀.toRingHom.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) =
        (toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)),
      letI : Algebra (Completion S₀) (Completion S) := f₀.toRingHom.toAlgebra
      letI : Algebra (Completion S₀) (Completion S') := g₀.toRingHom.toAlgebra
      haveI : IsAdicHom (algebraMap (Completion S₀) (Completion S)) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ f₀.continuous_toRingHom
          (hf₀.symm ▸ IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
            (inferInstanceAs (IsAdicHom (algebraMap A B))))
      haveI : IsAdicHom (algebraMap (Completion S₀) (Completion S')) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ g₀.continuous_toRingHom
          (hg₀.symm ▸ IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
            (inferInstanceAs (IsAdicHom (algebraMap A C))))
      let fwd := (toRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden''
          hP hP' hQ).comp
        (toBaseLocalization P₀ T₀ s₀ S₀ hden₀
          (rationalLocalizationPair P UB hP T s S hden)
          (rationalLocalizationPair P' UC hP' T' s' S' hden')
          f₀.toRingHom g₀.toRingHom f₀.continuous_toRingHom g₀.continuous_toRingHom hf₀ hg₀)
      IsCompletedPushout f₀ g₀
        (fwd.comp (inl (Completion S₀) _ _)) (fwd.comp (inr (Completion S₀) _ _)) := by
  let _ := locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isUniformAddGroup_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isTopologicalRing_locUniformSpace P₀ T₀ s₀ S₀ hden₀
  have _ := isHuberRing_completion_locTopology P₀ T₀ s₀ S₀ hden₀
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
      (inferInstanceAs (IsAdicHom (algebraMap A B)))
  have _ : IsAdicHom (algebraMap A (Completion S')) :=
    IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
      (inferInstanceAs (IsAdicHom (algebraMap A C)))
  let _ := locUniformSpace Q _ _ S'' hden''
  have _ := isUniformAddGroup_locUniformSpace Q _ _ S'' hden''
  have _ := isTopologicalRing_locUniformSpace Q _ _ S'' hden''
  have _ := isHuberRing_completion_locTopology Q _ _ S'' hden''
  intro f₀ g₀ hf₀ hg₀
  let _ : Algebra (Completion S₀) (Completion S) := f₀.toRingHom.toAlgebra
  let _ : Algebra (Completion S₀) (Completion S') := g₀.toRingHom.toAlgebra
  have _ : IsAdicHom (algebraMap (Completion S₀) (Completion S)) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ f₀.continuous_toRingHom
      (hf₀.symm ▸ IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
        (inferInstanceAs (IsAdicHom (algebraMap A B))))
  have _ : IsAdicHom (algebraMap (Completion S₀) (Completion S')) :=
    isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ g₀.continuous_toRingHom
      (hg₀.symm ▸ IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
        (inferInstanceAs (IsAdicHom (algebraMap A C))))
  let fwd := (toRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden''
      hP hP' hQ).comp
    (toBaseLocalization P₀ T₀ s₀ S₀ hden₀
      (rationalLocalizationPair P UB hP T s S hden)
      (rationalLocalizationPair P' UC hP' T' s' S' hden')
      f₀.toRingHom g₀.toRingHom f₀.continuous_toRingHom g₀.continuous_toRingHom hf₀ hg₀)
  let inv := (ofBaseLocalization P₀ T₀ s₀ S₀ hden₀
      (rationalLocalizationPair P UB hP T s S hden)
      (rationalLocalizationPair P' UC hP' T' s' S' hden')
      f₀.toRingHom g₀.toRingHom f₀.continuous_toRingHom g₀.continuous_toRingHom hf₀ hg₀).comp
    (ofRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ)
  have hinv_fwd : inv.comp fwd = Hom.id _ := by
    dsimp only [fwd, inv]
    rw [Hom.comp_assoc, ← Hom.comp_assoc (ofRationalLocalization ..),
      ofRationalLocalization_comp_toRationalLocalization, Hom.id_comp,
      ofBaseLocalization_comp_toBaseLocalization]
  have hfwd_inv : fwd.comp inv = Hom.id _ := by
    dsimp only [fwd, inv]
    rw [Hom.comp_assoc, ← Hom.comp_assoc (toBaseLocalization ..),
      toBaseLocalization_comp_ofBaseLocalization, Hom.id_comp,
      toRationalLocalization_comp_ofRationalLocalization]
  have hpush := isCompletedPushout f₀ g₀ (RingHom.algebraMap_toAlgebra f₀.toRingHom)
    (RingHom.algebraMap_toAlgebra g₀.toRingHom)
  refine ⟨by rw [Hom.comp_assoc, hpush.condition, ← Hom.comp_assoc],
    fun D _ _ _ _ _ _ _ V a b hab ↦ ?_⟩
  obtain ⟨h₀, ⟨hh₀l, hh₀r⟩, hh₀uniq⟩ := hpush.existsUnique_desc D V a b hab
  refine ⟨h₀.comp inv,
    ⟨by rw [Hom.comp_assoc, ← Hom.comp_assoc inv fwd, hinv_fwd, Hom.id_comp, hh₀l],
      by rw [Hom.comp_assoc, ← Hom.comp_assoc inv fwd, hinv_fwd, Hom.id_comp, hh₀r]⟩,
    fun k ⟨hkl, hkr⟩ ↦ ?_⟩
  have hk : k.comp fwd = h₀ :=
    hh₀uniq (k.comp fwd) ⟨by rwa [Hom.comp_assoc], by rwa [Hom.comp_assoc]⟩
  calc
    k = k.comp (fwd.comp inv) := by rw [hfwd_inv, Hom.comp_id]
    _ = (k.comp fwd).comp inv := (Hom.comp_assoc k fwd inv).symm
    _ = h₀.comp inv := by rw [hk]

end Pushout

end TauCeti.Huber.Pair.completedTensor
