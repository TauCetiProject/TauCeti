/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Adic
public import TauCeti.RingTheory.Huber.Restricted.Adic
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Kernel
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
import TauCeti.Topology.Algebra.Nonarchimedean.Quotient
import TauCeti.Topology.Algebra.Module.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Polynomial reductions of adic restricted power series

Reduction of restricted power series modulo an open ideal `J` is polynomial, both on the
uncompleted restricted-series subring (`Ideal.restrictedReduction`) and on the separated
completion `A⟨X₁, …, Xₖ⟩` (`Ideal.restrictedReductionCompletion`), without completeness or
Hausdorffness hypotheses on `A`: `A ⧸ J` is discrete, so the induced completed coefficient map
lands in a discrete polynomial ring.

For a finitely generated ideal of definition `I`, the kernel on either carrier is the extended
ideal `I · A⟨X⟩`, giving `A`-algebra isomorphisms `A⟨X⟩ ⧸ I · A⟨X⟩ ≃ₐ[A] (A ⧸ I)[X]` and, for
every `m > 0`, `A⟨X⟩ ⧸ (I · A⟨X⟩) ^ m ≃ₐ[A] (A ⧸ I ^ m)[X]`. Reduction commutes with continuous
coefficient maps and turns topological series evaluation into algebraic polynomial evaluation
`MvPolynomial.eval₂` modulo open ideals.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.1, 7.5.3.
* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §§5.1.1–5.1.3.
-/

public section

open Topology UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {k : ℕ} {I : Ideal A}

namespace TauCeti.Huber

/-- Membership in the extension of a finitely generated ideal of definition to restricted
series is coefficientwise. -/
theorem mem_map_weightedC_iff_of_isAdic (hI : IsAdic I) (hfg : I.FG)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    f ∈ I.map (weightedC _ isWeightFamily_one_weight) ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ I := by
  constructor
  · exact fun hf ↦ Ideal.coeff_mem_of_mem_map_weightedC hf
  · intro hf
    let P := PairOfDefinition.adic I hI hfg
    let Q := P.weighted (k := k) isWeightFamily_one_weight
    have htop : Q.ringOfDefinition = ⊤ :=
      P.weighted_ringOfDefinition_one_weight_eq_top
        (PairOfDefinition.adic_ringOfDefinition I hI hfg)
    let g : Q.ringOfDefinition := ⟨f, htop ▸ Subring.mem_top f⟩
    have hg : g ∈ Q.idealOfDefinition := by
      rw [PairOfDefinition.mem_weighted_idealOfDefinition]
      simpa [PairOfDefinition.mem_weightedIdeal, mem_weightedNhd,
        weightMul_one_weight, P, g] using hf
    have hext := P.weighted_extendedIdealOfDefinition (k := k) isWeightFamily_one_weight
    rw [PairOfDefinition.adic_extendedIdealOfDefinition,
      algebraMap_weightedRestrictedSubring] at hext
    rw [← hext, PairOfDefinition.extendedIdealOfDefinition_def]
    exact Ideal.mem_map_of_mem _ hg

end TauCeti.Huber

namespace Ideal

open TauCeti.Huber

/-- Reduction of restricted series modulo an open ideal is polynomial, since only finitely
many coefficients survive. -/
noncomputable def restrictedReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight →+*
      MvPolynomial (Fin k) (A ⧸ J) := by
  letI : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  exact (weightedPolynomialEquivOfDiscrete (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
    isWeightFamily_one_weight).symm.toRingHom.comp
      (weightedMap (φ := Ideal.Quotient.mk J) (QuotientRing.isOpenQuotientMap_mk J).continuous
        isWeightFamily_one_weight isWeightFamily_one_weight (by simp))

/-- Polynomial reduction reduces each coefficient modulo the given ideal. -/
@[simp]
theorem coeff_restrictedReduction (J : Ideal A) (hJ : IsOpen (J : Set A))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) (ν : Fin k →₀ ℕ) :
    (restrictedReduction J hJ f).coeff ν =
      Ideal.Quotient.mk J (MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)) := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  dsimp only [restrictedReduction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  rw [coeff_weightedPolynomialEquivOfDiscrete_symm]
  simp

/-- On polynomials, reduction of restricted series is the usual coefficient map. -/
@[simp]
theorem restrictedReduction_weightedPolynomialHom (J : Ideal A) (hJ : IsOpen (J : Set A))
    (p : MvPolynomial (Fin k) A) :
    restrictedReduction J hJ (weightedPolynomialHom _ isWeightFamily_one_weight p) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  ext ν
  simp [MvPolynomial.coeff_map]

/-- Reduction sends a constant series to the corresponding constant polynomial. -/
@[simp]
theorem restrictedReduction_weightedC (J : Ideal A) (hJ : IsOpen (J : Set A)) (a : A) :
    restrictedReduction (k := k) J hJ (weightedC _ isWeightFamily_one_weight a) =
      MvPolynomial.C (Ideal.Quotient.mk J a) := by
  simpa using restrictedReduction_weightedPolynomialHom J hJ (MvPolynomial.C a)

/-- Reduction preserves the coordinate variables. -/
@[simp]
theorem restrictedReduction_weightedX (J : Ideal A) (hJ : IsOpen (J : Set A)) (i : Fin k) :
    restrictedReduction J hJ (weightedX _ isWeightFamily_one_weight i) = MvPolynomial.X i := by
  simpa using restrictedReduction_weightedPolynomialHom J hJ (MvPolynomial.X i)

/-- Every polynomial over the quotient lifts to a restricted series, already to a polynomial. -/
theorem restrictedReduction_surjective (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    Function.Surjective (restrictedReduction (k := k) J hJ) := by
  intro p
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective p
  exact ⟨weightedPolynomialHom _ isWeightFamily_one_weight q, by simp⟩

/-- **Base-change naturality of polynomial reduction**: along a continuous ring homomorphism
`φ : A →+* B` mapping an open ideal `J` into an open ideal `K`, reduction commutes with
`weightedMap` and `MvPolynomial.map (Ideal.quotientMap K φ hJK)`. -/
theorem restrictedReduction_weightedMap {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] (J : Ideal A) (hJ : IsOpen (J : Set A)) (K : Ideal B)
    (hK : IsOpen (K : Set B)) {φ : A →+* B} (hφ : Continuous φ) (hJK : J ≤ K.comap φ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    K.restrictedReduction hK
        (weightedMap hφ isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f) =
      MvPolynomial.map (Ideal.quotientMap K φ hJK) (J.restrictedReduction hJ f) := by
  ext ν
  simp [MvPolynomial.coeff_map]

/-- Reduction of the completed restricted power-series algebra `A⟨X₁, …, Xₖ⟩` modulo an open ideal
`J` of `A`, with no completeness or Hausdorffness hypothesis on `A`. Because `A ⧸ J` is discrete,
its restricted-series ring is already discrete and complete, and identifies with
`MvPolynomial (Fin k) (A ⧸ J)`. -/
noncomputable def restrictedReductionCompletion (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    restrictedMvPowerSeriesCompletion k A →+* MvPolynomial (Fin k) (A ⧸ J) := by
  letI : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  haveI : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  haveI : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := IsRightUniformAddGroup.discreteUniformity
  exact (weightedPolynomialEquivOfDiscrete (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
    isWeightFamily_one_weight).symm.toRingHom.comp
      ((restrictedMvPowerSeriesCompletionEquiv k (A ⧸ J)).toRingHom.comp
        (weightedMapCompletion (φ := Ideal.Quotient.mk J)
          (QuotientRing.isOpenQuotientMap_mk J).continuous
          isWeightFamily_one_weight isWeightFamily_one_weight (by simp)))

/-- Any map out of `MvPolynomial (Fin k) (A ⧸ J)` into a topological space becomes continuous
after precomposing with `restrictedReduction`, since `restrictedReduction` factors through the
discrete restricted-series ring over `A ⧸ J`. -/
private theorem continuous_comp_restrictedReduction {X : Type*} [TopologicalSpace X]
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (g : MvPolynomial (Fin k) (A ⧸ J) → X) :
    Continuous (g ∘ J.restrictedReduction hJ) := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  have hg : Continuous (g ∘ (weightedPolynomialEquivOfDiscrete
      (fun _ : Fin k ↦ ({1} : Set (A ⧸ J))) isWeightFamily_one_weight).symm) :=
    continuous_of_discreteTopology
  exact hg.comp
    (continuous_weightedMap (QuotientRing.isOpenQuotientMap_mk J).continuous
      isWeightFamily_one_weight isWeightFamily_one_weight (by simp))

/-- Any map out of `MvPolynomial (Fin k) (A ⧸ J)` into a topological space becomes continuous
after precomposing with `restrictedReductionCompletion`. -/
private theorem continuous_comp_restrictedReductionCompletion {X : Type*} [TopologicalSpace X]
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (g : MvPolynomial (Fin k) (A ⧸ J) → X) :
    Continuous (g ∘ J.restrictedReductionCompletion hJ) := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  have : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := IsRightUniformAddGroup.discreteUniformity
  have hg : Continuous (g ∘ (weightedPolynomialEquivOfDiscrete
      (fun _ : Fin k ↦ ({1} : Set (A ⧸ J))) isWeightFamily_one_weight).symm) :=
    continuous_of_discreteTopology
  exact hg.comp
    (uniformContinuous_restrictedMvPowerSeriesCompletionEquiv.continuous.comp
      (continuous_weightedMapCompletion (QuotientRing.isOpenQuotientMap_mk J).continuous
        isWeightFamily_one_weight isWeightFamily_one_weight (by simp)))

/-- On a represented restricted series, `restrictedReductionCompletion` agrees with
`restrictedReduction`. -/
@[simp]
theorem restrictedReductionCompletion_coe (J : Ideal A) (hJ : IsOpen (J : Set A))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    J.restrictedReductionCompletion hJ (f : restrictedMvPowerSeriesCompletion k A) =
      J.restrictedReduction hJ f := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  have : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := IsRightUniformAddGroup.discreteUniformity
  simp [restrictedReductionCompletion, restrictedReduction]

/-- Completed reduction sends a scalar `algebraMap A _ a` to the constant polynomial
`C (mk J a)`. -/
theorem restrictedReductionCompletion_algebraMap (J : Ideal A) (hJ : IsOpen (J : Set A)) (a : A) :
    J.restrictedReductionCompletion (k := k) hJ
        (algebraMap A (restrictedMvPowerSeriesCompletion k A) a) =
      MvPolynomial.C (Ideal.Quotient.mk J a) := by
  simp

/-- Completed reduction preserves the coordinate variables. -/
theorem restrictedReductionCompletion_weightedX (J : Ideal A) (hJ : IsOpen (J : Set A))
    (i : Fin k) :
    J.restrictedReductionCompletion hJ
        ((weightedX _ isWeightFamily_one_weight i :
          weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
            restrictedMvPowerSeriesCompletion k A) =
      MvPolynomial.X i := by
  simp

/-- Completed reduction modulo an open ideal is surjective. -/
theorem restrictedReductionCompletion_surjective (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    Function.Surjective (J.restrictedReductionCompletion (k := k) hJ) := fun p ↦ by
  obtain ⟨f, rfl⟩ := J.restrictedReduction_surjective (k := k) hJ p
  exact ⟨f, by simp⟩

/-- **Base-change naturality of completed polynomial reduction**: along a continuous ring
homomorphism `φ : A →+* B` mapping an open ideal `J` into an open ideal `K`, completed reduction
commutes with `weightedMapCompletion` and `MvPolynomial.map (Ideal.quotientMap K φ hJK)`. -/
theorem restrictedReductionCompletion_weightedMapCompletion {B : Type*} [CommRing B]
    [TopologicalSpace B] [NonarchimedeanRing B] (J : Ideal A) (hJ : IsOpen (J : Set A))
    (K : Ideal B) (hK : IsOpen (K : Set B)) {φ : A →+* B} (hφ : Continuous φ)
    (hJK : J ≤ K.comap φ) (x : restrictedMvPowerSeriesCompletion k A) :
    K.restrictedReductionCompletion hK
        (weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) x) =
      MvPolynomial.map (Ideal.quotientMap K φ hJK) (J.restrictedReductionCompletion hJ x) := by
  let _ : TopologicalSpace (MvPolynomial (Fin k) (B ⧸ K)) := ⊥
  have _ := discreteTopology_bot (MvPolynomial (Fin k) (B ⧸ K))
  refine Completion.induction_on x (isClosed_eq
    ((K.continuous_comp_restrictedReductionCompletion hK id).comp
      (continuous_weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight
        (by simp)))
    (J.continuous_comp_restrictedReductionCompletion hJ
      (MvPolynomial.map (Ideal.quotientMap K φ hJK)))) fun f ↦ ?_
  rw [weightedMapCompletion_coe, restrictedReductionCompletion_coe,
    restrictedReductionCompletion_coe, J.restrictedReduction_weightedMap hJ K hK hφ hJK f]

end Ideal

namespace TauCeti.Huber

open Ideal (restrictedReduction restrictedReduction_surjective
  restrictedReductionCompletion restrictedReductionCompletion_surjective)

/-- Reduction modulo a finitely generated ideal of definition has exactly the extended ideal
as its kernel. -/
theorem ker_restrictedReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedReduction (k := k) I (by simpa only [pow_one] using hI.isOpen_pow 1)) =
      I.map (weightedC _ isWeightFamily_one_weight) := by
  ext f
  rw [RingHom.mem_ker, mem_map_weightedC_iff_of_isAdic hI hfg, MvPolynomial.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

/-- The infinitesimal reduction of restricted power series is a polynomial algebra. -/
noncomputable def quotientRestrictedEquivMvPolynomialQuotient (hI : IsAdic I) (hfg : I.FG) :
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
      I.map (weightedC _ isWeightFamily_one_weight)) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I) := by
  let e := (Ideal.quotEquivOfEq (ker_restrictedReduction (k := k) hI hfg).symm).trans
    ((restrictedReduction I (by simpa using hI.isOpen_pow 1)).quotientKerEquivOfSurjective
      (restrictedReduction_surjective I (by simpa only [pow_one] using hI.isOpen_pow 1)))
  refine AlgEquiv.ofRingEquiv (f := e) fun a ↦ ?_
  have he : e (algebraMap A _ a) =
      restrictedReduction I (by simpa only [pow_one] using hI.isOpen_pow 1) (algebraMap A _ a) := by
    rw [← Ideal.Quotient.mk_algebraMap]
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [he]
  simp [algebraMap_weightedRestrictedSubring]

/-- On a represented series the quotient comparison computes its polynomial reduction. -/
@[simp]
theorem quotientRestrictedEquivMvPolynomialQuotient_mk (hI : IsAdic I) (hfg : I.FG)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    quotientRestrictedEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ f) =
      restrictedReduction I (by simpa only [pow_one] using hI.isOpen_pow 1) f := by
  simp [quotientRestrictedEquivMvPolynomialQuotient]

/-- For every positive power `I ^ m` of a finitely generated ideal of definition, the quotient of
restricted power series by `(I · A⟨X⟩) ^ m` is the polynomial algebra `(A ⧸ I ^ m)[X]`. -/
noncomputable def quotientRestrictedPowEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : 0 < m) :
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
      (I.map (weightedC _ isWeightFamily_one_weight)) ^ m) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I ^ m) :=
  (Ideal.quotientEquivAlgOfEq A
    (I.map_pow (weightedC _ isWeightFamily_one_weight) m).symm).trans
    (quotientRestrictedEquivMvPolynomialQuotient (is_ideal_adic_pow hI hm) hfg.pow)

/-- On a represented series, `quotientRestrictedPowEquivMvPolynomialQuotient` computes reduction
modulo `I ^ m`. -/
@[simp]
theorem quotientRestrictedPowEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : 0 < m)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    quotientRestrictedPowEquivMvPolynomialQuotient hI hfg hm (Ideal.Quotient.mk _ f) =
      restrictedReduction (I ^ m) (hI.isOpen_pow m) f := by
  simp [quotientRestrictedPowEquivMvPolynomialQuotient]

/-- Reduction is compatible with passing to a larger open ideal. -/
@[simp]
theorem map_restrictedReduction {J : Ideal A} (hJ : IsOpen (J : Set A))
    (hI : IsOpen (I : Set A)) (hJI : J ≤ I)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    MvPolynomial.map (Ideal.Quotient.factor hJI) (restrictedReduction J hJ f) =
      restrictedReduction I hI f := by
  ext ν
  simp [MvPolynomial.coeff_map]

/-- Completed reduction is compatible with passing to a larger open ideal. -/
@[simp]
theorem map_restrictedReductionCompletion {J : Ideal A} (hJ : IsOpen (J : Set A))
    (hI : IsOpen (I : Set A)) (hJI : J ≤ I)
    (x : restrictedMvPowerSeriesCompletion k A) :
    MvPolynomial.map (Ideal.Quotient.factor hJI) (restrictedReductionCompletion J hJ x) =
      restrictedReductionCompletion I hI x := by
  let _ : TopologicalSpace (MvPolynomial (Fin k) (A ⧸ I)) := ⊥
  have _ := discreteTopology_bot (MvPolynomial (Fin k) (A ⧸ I))
  refine Completion.induction_on x (isClosed_eq
    (J.continuous_comp_restrictedReductionCompletion hJ
      (MvPolynomial.map (Ideal.Quotient.factor hJI)))
    (I.continuous_comp_restrictedReductionCompletion hI id)) fun f ↦ ?_
  simp [map_restrictedReduction hJ hI hJI f]

/-- When the restricted-series ring is already complete and Hausdorff,
`restrictedReductionCompletion` agrees with `restrictedReduction` across
`restrictedMvPowerSeriesCompletionEquiv`. -/
theorem restrictedReductionCompletion_eq_restrictedReduction_completionEquiv
    [CompleteSpace (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight)]
    [T0Space (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight)]
    {J : Ideal A} (hJ : IsOpen (J : Set A))
    (x : restrictedMvPowerSeriesCompletion k A) :
    restrictedReductionCompletion J hJ x =
      restrictedReduction J hJ (restrictedMvPowerSeriesCompletionEquiv k A x) := by
  let _ : TopologicalSpace (MvPolynomial (Fin k) (A ⧸ J)) := ⊥
  have _ := discreteTopology_bot (MvPolynomial (Fin k) (A ⧸ J))
  refine Completion.induction_on x (isClosed_eq
    (J.continuous_comp_restrictedReductionCompletion hJ id)
    ((J.continuous_comp_restrictedReduction hJ id).comp
      uniformContinuous_restrictedMvPowerSeriesCompletionEquiv.continuous)) fun f ↦ ?_
  simp

/-- Completed reduction modulo a finitely generated ideal of definition has the extended ideal
`I · A⟨X₁, …, Xₖ⟩` as its kernel, with no completeness or Hausdorffness hypothesis on `A`. -/
theorem ker_restrictedReductionCompletion (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedReductionCompletion (k := k) I
        (by simpa only [pow_one] using hI.isOpen_pow 1)) =
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) := by
  set hI₁ : IsOpen (I : Set A) := by simpa only [pow_one] using hI.isOpen_pow 1
  set IC := I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))
  have hle : IC ≤ RingHom.ker (restrictedReductionCompletion (k := k) I hI₁) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  refine le_antisymm ?_ hle
  intro x hx
  have hIC_open : IsOpen (IC : Set (restrictedMvPowerSeriesCompletion k A)) := by
    simpa only [pow_one] using
      (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg).isOpen_pow 1
  have hmem : {y : restrictedMvPowerSeriesCompletion k A | x - y ∈ IC} ∈ 𝓝 x := by
    have hcont : Continuous (fun y : restrictedMvPowerSeriesCompletion k A ↦ x - y) :=
      continuous_const.sub continuous_id
    exact (hIC_open.preimage hcont).mem_nhds (by simp [IC.zero_mem])
  obtain ⟨f, hf⟩ := Completion.denseRange_coe.mem_nhds hmem
  have hf_ker : f ∈ RingHom.ker (restrictedReduction (k := k) I hI₁) := by
    rw [RingHom.mem_ker, ← Ideal.restrictedReductionCompletion_coe]
    have hfx : (f : restrictedMvPowerSeriesCompletion k A) = x - (x - f) :=
      (sub_sub_cancel x f).symm
    rw [hfx]
    exact RingHom.mem_ker.mp (sub_mem hx (hle hf))
  rw [ker_restrictedReduction hI hfg] at hf_ker
  have hf_IC : (f : restrictedMvPowerSeriesCompletion k A) ∈ IC := by
    have hmap : (I.map (weightedC _ isWeightFamily_one_weight)).map Completion.coeRingHom =
        IC := by
      rw [Ideal.map_map]
      congr 1
    rw [← hmap]
    exact Ideal.mem_map_of_mem Completion.coeRingHom hf_ker
  simpa only [sub_add_cancel] using add_mem hf hf_IC

/-- The reduction modulo a finitely generated ideal of definition of the completed
restricted-series algebra is the polynomial algebra over the quotient of the coefficients,
with no completeness or Hausdorffness hypothesis on the base ring `A`. -/
noncomputable def quotientRestrictedCompletionEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) :
    (restrictedMvPowerSeriesCompletion k A ⧸
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I) := by
  set hI₁ : IsOpen (I : Set A) := by simpa only [pow_one] using hI.isOpen_pow 1
  let e := (Ideal.quotEquivOfEq (ker_restrictedReductionCompletion (k := k) hI hfg).symm).trans
    ((restrictedReductionCompletion I hI₁).quotientKerEquivOfSurjective
      (restrictedReductionCompletion_surjective I hI₁))
  refine AlgEquiv.ofRingEquiv (f := e) fun a ↦ ?_
  have he : e (algebraMap A _ a) =
      restrictedReductionCompletion I hI₁ (algebraMap A _ a) := by
    rw [← Ideal.Quotient.mk_algebraMap]
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [he]
  simp

/-- On an arbitrary completion element, the quotient comparison computes its completed polynomial
reduction. -/
@[simp]
theorem quotientRestrictedCompletionEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) (x : restrictedMvPowerSeriesCompletion k A) :
    quotientRestrictedCompletionEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ x) =
      restrictedReductionCompletion I (by simpa only [pow_one] using hI.isOpen_pow 1) x := by
  simp [quotientRestrictedCompletionEquivMvPolynomialQuotient]

/-- For every positive power `I ^ m` of a finitely generated ideal of definition, the quotient of
`A⟨X₁, …, Xₖ⟩` by `(I · A⟨X₁, …, Xₖ⟩) ^ m` is `(A ⧸ I ^ m)[X₁, …, Xₖ]`. -/
noncomputable def quotientRestrictedCompletionPowEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : 0 < m) :
    (restrictedMvPowerSeriesCompletion k A ⧸
      (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))) ^ m) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I ^ m) :=
  (Ideal.quotientEquivAlgOfEq A
    (I.map_pow (algebraMap A (restrictedMvPowerSeriesCompletion k A)) m).symm).trans
    (quotientRestrictedCompletionEquivMvPolynomialQuotient (is_ideal_adic_pow hI hm) hfg.pow)

/-- On an arbitrary completion element, `quotientRestrictedCompletionPowEquivMvPolynomialQuotient`
computes completed polynomial reduction modulo `I ^ m`. -/
@[simp]
theorem quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : 0 < m)
    (x : restrictedMvPowerSeriesCompletion k A) :
    quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg hm (Ideal.Quotient.mk _ x) =
      restrictedReductionCompletion (I ^ m) (hI.isOpen_pow m) x := by
  simp [quotientRestrictedCompletionPowEquivMvPolynomialQuotient]

/-! ### Compatibility of evaluation with polynomial reduction -/

section EvalReduction

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [NonarchimedeanRing B] [CompleteSpace B] [T3Space B]

/-- **Evaluation commutes with reduction modulo open ideals**: reducing an evaluated restricted
series modulo an open ideal `K` of `B` equals evaluating its polynomial reduction modulo an open
ideal `J` of `A` with `J ≤ K.comap φ` via `MvPolynomial.eval₂`. -/
theorem mk_weightedEvalHom_eq_eval₂_restrictedReduction {φ : A →+* B} (hφ : ContinuousAt φ 0)
    {b : Fin k → B} (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b)
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (K : Ideal B) (hK : IsOpen (K : Set B))
    (hJK : J ≤ K.comap φ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    Ideal.Quotient.mk K (weightedEvalHom isWeightFamily_one_weight hφ hb f) =
      MvPolynomial.eval₂ (Ideal.quotientMap K φ hJK) (Ideal.Quotient.mk K ∘ b)
        (J.restrictedReduction hJ f) := by
  let : DiscreteTopology (B ⧸ K) := Submodule.Quotient.discreteTopology_of_isOpen K hK
  have h := weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    (f := (Ideal.Quotient.mk K).comp (weightedEvalHom isWeightFamily_one_weight hφ hb))
    (g := (MvPolynomial.eval₂Hom (Ideal.quotientMap K φ hJK)
      (Ideal.Quotient.mk K ∘ b)).comp (J.restrictedReduction hJ))
    ((QuotientRing.isOpenQuotientMap_mk K).continuous.comp
      (continuous_weightedEvalHom isWeightFamily_one_weight hφ hb))
    (J.continuous_comp_restrictedReduction hJ
      (MvPolynomial.eval₂Hom (Ideal.quotientMap K φ hJK) (Ideal.Quotient.mk K ∘ b)))
    (fun _ ↦ by simp)
    (fun _ ↦ by simp)
  exact congr($h f)

/-- **Completed evaluation commutes with polynomial reduction modulo open ideals**: reducing a
completed evaluation modulo `K` equals evaluating `J.restrictedReductionCompletion` via
`MvPolynomial.eval₂`. -/
theorem mk_weightedEvalHomCompletion_eq_eval₂_restrictedReductionCompletion
    {φ : A →+* B} (hφ : ContinuousAt φ 0)
    {b : Fin k → B} (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b)
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (K : Ideal B) (hK : IsOpen (K : Set B))
    (hJK : J ≤ K.comap φ) (x : restrictedMvPowerSeriesCompletion k A) :
    Ideal.Quotient.mk K (weightedEvalHomCompletion isWeightFamily_one_weight hφ hb x) =
      MvPolynomial.eval₂ (Ideal.quotientMap K φ hJK) (Ideal.Quotient.mk K ∘ b)
        (J.restrictedReductionCompletion hJ x) := by
  let : DiscreteTopology (B ⧸ K) := Submodule.Quotient.discreteTopology_of_isOpen K hK
  refine Completion.induction_on x (isClosed_eq
    ((QuotientRing.isOpenQuotientMap_mk K).continuous.comp
      (continuous_weightedEvalHomCompletion isWeightFamily_one_weight hφ hb))
    (J.continuous_comp_restrictedReductionCompletion hJ
      (MvPolynomial.eval₂ (Ideal.quotientMap K φ hJK) (Ideal.Quotient.mk K ∘ b)))) fun f ↦ ?_
  rw [weightedEvalHomCompletion_coe, Ideal.restrictedReductionCompletion_coe,
    mk_weightedEvalHom_eq_eval₂_restrictedReduction hφ hb J hJ K hK hJK f]

end EvalReduction

section LinearEvalReduction

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsLinearTopology B B] [CompleteSpace B] [T2Space B]

/-- For a linearly topologised target `B` (such as an adic ring), reducing
`restrictedCompletionEvalLinear` at arbitrary `b : Fin k → B` modulo an open ideal `K` equals
polynomial evaluation of `J.restrictedReductionCompletion`. -/
theorem mk_restrictedCompletionEvalLinear_eq_eval₂_restrictedReductionCompletion
    {φ : A →+* B} (hφ : Continuous φ) (b : Fin k → B)
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (K : Ideal B) (hK : IsOpen (K : Set B))
    (hJK : J ≤ K.comap φ) (x : restrictedMvPowerSeriesCompletion k A) :
    Ideal.Quotient.mk K (restrictedCompletionEvalLinear hφ b x) =
      MvPolynomial.eval₂ (Ideal.quotientMap K φ hJK) (Ideal.Quotient.mk K ∘ b)
        (J.restrictedReductionCompletion hJ x) := by
  let _ := IsLinearTopology.isTopologicalRing (R := B)
  let _ := IsLinearTopology.nonarchimedeanRing B
  rw [restrictedCompletionEvalLinear_eq_weightedEvalHomCompletion]
  exact mk_weightedEvalHomCompletion_eq_eval₂_restrictedReductionCompletion hφ.continuousAt
    (isWeightBounded_of_isLinearTopology φ _ b) J hJ K hK hJK x

/-- For a linearly topologised `A`-algebra `B` with a continuous structure map, reducing
`restrictedCompletionLiftLinear` at arbitrary `b : Fin k → B` modulo an open ideal `K` equals
polynomial evaluation of `J.restrictedReductionCompletion`. -/
theorem mk_restrictedCompletionLiftLinear_eq_eval₂_restrictedReductionCompletion
    [Algebra A B] (hA : Continuous (algebraMap A B)) (b : Fin k → B)
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (K : Ideal B) (hK : IsOpen (K : Set B))
    (hJK : J ≤ K.comap (algebraMap A B)) (x : restrictedMvPowerSeriesCompletion k A) :
    Ideal.Quotient.mk K (restrictedCompletionLiftLinear hA b x) =
      MvPolynomial.eval₂ (Ideal.quotientMap K (algebraMap A B) hJK) (Ideal.Quotient.mk K ∘ b)
        (J.restrictedReductionCompletion hJ x) := by
  rw [coe_restrictedCompletionLiftLinear]
  exact mk_restrictedCompletionEvalLinear_eq_eval₂_restrictedReductionCompletion hA b
    J hJ K hK hJK x

end LinearEvalReduction

end TauCeti.Huber
