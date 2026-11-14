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
public import TauCeti.Topology.Algebra.Group.LocallyConstant
import TauCeti.Topology.Algebra.Nonarchimedean.Quotient
import TauCeti.Topology.Algebra.Module.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Polynomial reductions and linear-target maps of adic restricted power series

Reduction of restricted power series modulo an open ideal `J` of `A` lands in the polynomial ring
`MvPolynomial (Fin k) (A ⧸ J)`, because only finitely many coefficients lie outside `J`. Because
the quotient `A ⧸ J` is discrete, the coefficientwise map extends across separated completion to
`Ideal.restrictedCompletionReduction : A⟨X₁, …, Xₖ⟩ →+* (A ⧸ J)[X₁, …, Xₖ]` without assuming
completeness or separatedness of `A` itself.

For a finitely generated ideal of definition `I` and every `m : ℕ`, the kernel of reduction modulo
`I ^ m` is `I.map _ ^ m`, giving `A`-algebra isomorphisms
`A⟨X⟩ ⧸ (I · A⟨X⟩) ^ m ≃ₐ[A] (A ⧸ I ^ m)[X]` on both the uncompleted subring and the completed
carrier `restrictedMvPowerSeriesCompletion k A`. At `m = 0` both sides are the zero ring; for
`0 < m`, `I ^ m` is again a finitely generated ideal of definition.

Reduction is natural under continuous coefficient maps `φ : A →+* B` carrying `J` into `K` and
commutes with topological evaluation `weightedEvalHom` and `weightedEvalHomCompletion` modulo an
open ideal of the target. When the target `B` is a complete separated linearly topologised
`A`-algebra with continuous structure map, ideal neighbourhoods of zero make every element of `B`
power-bounded (`isWeightBounded_of_isLinearTopology`), so arbitrary choices `b : Fin k → B` of the
variables determine a unique continuous `A`-algebra homomorphism `A⟨X₁, …, Xₖ⟩ →ₐ[A] B`—in
contrast to general nonarchimedean or normed targets, where power-boundedness or norm bounds on
the evaluation point are essential.

## Main definitions

* `Ideal.restrictedReduction`: open-ideal polynomial reduction on `weightedRestrictedSubring`.
* `Ideal.restrictedCompletionReduction`: open-ideal polynomial reduction on
  `restrictedMvPowerSeriesCompletion k A`.
* `TauCeti.Huber.quotientRestrictedEquivMvPolynomialQuotient` and
  `TauCeti.Huber.quotientPowRestrictedEquivMvPolynomialQuotient`: quotient comparisons modulo `I`
  and `I ^ m` on `weightedRestrictedSubring`.
* `TauCeti.Huber.quotientRestrictedCompletionEquivMvPolynomialQuotient` and
  `TauCeti.Huber.quotientPowRestrictedCompletionEquivMvPolynomialQuotient`: quotient comparisons
  modulo `I` and `I ^ m` on `restrictedMvPowerSeriesCompletion`.
* `TauCeti.Huber.restrictedLinearEvalAlgHom`: continuous `A`-algebra evaluation out of
  `restrictedMvPowerSeriesCompletion k A` into a complete separated linearly topologised
  `A`-algebra at arbitrary points.

## Main results

* `Ideal.isOpen_ker_restrictedReduction` and `Ideal.isOpen_ker_restrictedCompletionReduction`:
  kernels of open-ideal polynomial reductions are open, making both maps locally constant.
* `Ideal.restrictedReduction_weightedMap` and
  `Ideal.restrictedCompletionReduction_weightedMapCompletion`: naturality under continuous
  coefficient homomorphisms.
* `TauCeti.Huber.mem_pow_map_weightedC_iff_of_isAdic`,
  `TauCeti.Huber.ker_restrictedReduction_pow`, and
  `TauCeti.Huber.ker_restrictedCompletionReduction_pow`: kernels of reduction modulo `I ^ m`.
* `TauCeti.Huber.quotientMk_weightedEvalHom` and
  `TauCeti.Huber.quotientMk_weightedEvalHomCompletion`: evaluation commutes with polynomial
  reduction modulo open ideals.
* `existsUnique_continuous_algHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology`:
  `A`-algebra form of the linear-target universal property of `A⟨X₁, …, Xₖ⟩`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.1–7.5.4.
* T. Wedhorn, *Adic Spaces*, §5.6, Proposition 5.50.
-/

public section

open Topology

namespace TauCeti.Huber

section AdicMembership

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {k : ℕ} {I : Ideal A}

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

/-- Membership in every power `(I · A⟨T⟩) ^ m` of the extended ideal of definition is
coefficientwise, including the degenerate case `m = 0` where both sides are the unit ideal. -/
theorem mem_pow_map_weightedC_iff_of_isAdic (hI : IsAdic I) (hfg : I.FG) (m : ℕ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    f ∈ I.map (weightedC _ isWeightFamily_one_weight) ^ m ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ I ^ m := by
  rw [← Ideal.map_pow]
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [Ideal.map_top]
  · exact mem_map_weightedC_iff_of_isAdic (is_ideal_adic_pow hI hm) hfg.pow f

end AdicMembership

end TauCeti.Huber

namespace Ideal

open TauCeti.Huber

section Reduction

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] {k : ℕ}

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

/-- A restricted series lies in the kernel of open-ideal reduction exactly when all of its
coefficients lie in the ideal. -/
theorem mem_ker_restrictedReduction (J : Ideal A) (hJ : IsOpen (J : Set A))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    f ∈ RingHom.ker (restrictedReduction J hJ) ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ J := by
  rw [RingHom.mem_ker, MvPolynomial.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

/-- The kernel of polynomial reduction modulo an open ideal is an open ideal of `A⟨X⟩`: it is the
basic neighbourhood subgroup cut out by `J`. -/
theorem isOpen_ker_restrictedReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    IsOpen (RingHom.ker (restrictedReduction (k := k) J hJ) :
      Set (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight)) := by
  have hset : (RingHom.ker (restrictedReduction (k := k) J hJ) :
      Set (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight)) =
      (weightedNhd (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight J.toAddSubgroup :
        Set (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
          isWeightFamily_one_weight)) := by
    ext f
    rw [SetLike.mem_coe, mem_ker_restrictedReduction, SetLike.mem_coe]
    simp [mem_weightedNhd, weightMul_one_weight]
  rw [hset]
  exact isOpen_weightedNhd isWeightFamily_one_weight hJ

/-- Open-ideal polynomial reduction is locally constant on `A⟨X₁, …, Xₖ⟩`. -/
theorem isLocallyConstant_restrictedReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    IsLocallyConstant (J.restrictedReduction (k := k) hJ) :=
  (J.restrictedReduction (k := k) hJ).toAddMonoidHom.isLocallyConstant_of_isOpen_ker
    (J.isOpen_ker_restrictedReduction hJ)

/-- Open-ideal polynomial reduction commutes with continuous coefficient maps. -/
theorem restrictedReduction_weightedMap {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] (J : Ideal A) (hJ : IsOpen (J : Set A)) (K : Ideal B)
    (hK : IsOpen (K : Set B)) {φ : A →+* B} (hφ : Continuous φ) (hJK : J ≤ K.comap φ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    K.restrictedReduction hK
        (weightedMap hφ isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f) =
      MvPolynomial.map (Ideal.quotientMap K φ hJK) (J.restrictedReduction hJ f) := by
  ext ν
  simp [MvPolynomial.coeff_map]

/-- Reduction of the completed restricted-series algebra `A⟨X₁, …, Xₖ⟩` modulo an open ideal `J`
of `A`, obtained by functoriality of completion into the discrete quotient `A ⧸ J`. Neither
completeness nor separatedness of `A` is needed. -/
noncomputable def restrictedCompletionReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    restrictedMvPowerSeriesCompletion k A →+* MvPolynomial (Fin k) (A ⧸ J) := by
  letI : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  exact (weightedPolynomialEquivOfDiscrete (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
    isWeightFamily_one_weight).symm.toRingHom.comp
      ((restrictedMvPowerSeriesCompletionEquiv k (A ⧸ J)).toRingHom.comp
        (weightedMapCompletion (φ := Ideal.Quotient.mk J)
          (QuotientRing.isOpenQuotientMap_mk J).continuous
          isWeightFamily_one_weight isWeightFamily_one_weight (by simp)))

/-- On the canonical image of a restricted series, completed reduction agrees with
`Ideal.restrictedReduction`. -/
@[simp]
theorem restrictedCompletionReduction_coe (J : Ideal A) (hJ : IsOpen (J : Set A))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    J.restrictedCompletionReduction hJ (f : restrictedMvPowerSeriesCompletion k A) =
      J.restrictedReduction hJ f := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  simp [restrictedCompletionReduction, restrictedReduction]

/-- Completed reduction sends a constant from `A` to the corresponding constant polynomial over
`A ⧸ J`. -/
theorem restrictedCompletionReduction_algebraMap (J : Ideal A) (hJ : IsOpen (J : Set A)) (a : A) :
    J.restrictedCompletionReduction (k := k) hJ
        (algebraMap A (restrictedMvPowerSeriesCompletion k A) a) =
      MvPolynomial.C (Ideal.Quotient.mk J a) := by
  rw [algebraMap_completion_weightedRestrictedSubring_apply, restrictedCompletionReduction_coe,
    restrictedReduction_weightedC]

/-- Completed reduction sends each coordinate variable to the corresponding polynomial variable. -/
theorem restrictedCompletionReduction_weightedX (J : Ideal A) (hJ : IsOpen (J : Set A))
    (i : Fin k) :
    J.restrictedCompletionReduction hJ
        ((weightedX _ isWeightFamily_one_weight i :
          weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
            restrictedMvPowerSeriesCompletion k A) =
      MvPolynomial.X i := by
  rw [restrictedCompletionReduction_coe, restrictedReduction_weightedX]

/-- Completed open-ideal reduction is surjective, already on embedded polynomials. -/
theorem restrictedCompletionReduction_surjective (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    Function.Surjective (J.restrictedCompletionReduction (k := k) hJ) := fun p ↦ by
  obtain ⟨f, rfl⟩ := J.restrictedReduction_surjective hJ p
  exact ⟨f, J.restrictedCompletionReduction_coe hJ f⟩

/-- The kernel of completed open-ideal reduction is open in `A⟨X₁, …, Xₖ⟩`. -/
theorem isOpen_ker_restrictedCompletionReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    IsOpen (RingHom.ker (J.restrictedCompletionReduction (k := k) hJ) :
      Set (restrictedMvPowerSeriesCompletion k A)) := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  let g := (restrictedMvPowerSeriesCompletionEquiv k (A ⧸ J)).toRingHom.comp
    (weightedMapCompletion (φ := Ideal.Quotient.mk J)
      (QuotientRing.isOpenQuotientMap_mk J).continuous
      isWeightFamily_one_weight isWeightFamily_one_weight (by simp))
  have hg : Continuous g :=
    uniformContinuous_restrictedMvPowerSeriesCompletionEquiv.continuous.comp
      (continuous_weightedMapCompletion ..)
  have hker : (RingHom.ker (J.restrictedCompletionReduction (k := k) hJ) :
      Set (restrictedMvPowerSeriesCompletion k A)) =
      g ⁻¹' {(0 : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
        isWeightFamily_one_weight)} := by
    ext x
    simp [restrictedCompletionReduction, g, RingHom.mem_ker]
  rw [hker]
  exact (isOpen_discrete _).preimage hg

/-- Completed open-ideal polynomial reduction is locally constant on `A⟨X₁, …, Xₖ⟩`. -/
theorem isLocallyConstant_restrictedCompletionReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    IsLocallyConstant (J.restrictedCompletionReduction (k := k) hJ) :=
  (J.restrictedCompletionReduction (k := k) hJ).toAddMonoidHom.isLocallyConstant_of_isOpen_ker
    (J.isOpen_ker_restrictedCompletionReduction hJ)

/-- Completed open-ideal polynomial reduction commutes with continuous coefficient maps on
completions. -/
theorem restrictedCompletionReduction_weightedMapCompletion {B : Type*} [CommRing B]
    [TopologicalSpace B] [NonarchimedeanRing B] (J : Ideal A) (hJ : IsOpen (J : Set A))
    (K : Ideal B) (hK : IsOpen (K : Set B)) {φ : A →+* B} (hφ : Continuous φ)
    (hJK : J ≤ K.comap φ) (x : restrictedMvPowerSeriesCompletion k A) :
    K.restrictedCompletionReduction hK
        (weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) x) =
      MvPolynomial.map (Ideal.quotientMap K φ hJK) (J.restrictedCompletionReduction hJ x) := by
  let : TopologicalSpace (MvPolynomial (Fin k) (B ⧸ K)) := ⊥
  have : DiscreteTopology (MvPolynomial (Fin k) (B ⧸ K)) := ⟨rfl⟩
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq
      ((K.isLocallyConstant_restrictedCompletionReduction hK).continuous.comp
        (continuous_weightedMapCompletion ..))
      ((J.isLocallyConstant_restrictedCompletionReduction hJ).comp
        (MvPolynomial.map (Ideal.quotientMap K φ hJK))).continuous)
    fun f ↦ ?_
  simpa only [weightedMapCompletion_coe, restrictedCompletionReduction_coe] using
    J.restrictedReduction_weightedMap hJ K hK hφ hJK f

/-- When the uncompleted restricted-series ring is complete and Hausdorff, completed reduction
factors through `restrictedMvPowerSeriesCompletionAlgEquiv`. -/
@[simp]
theorem restrictedCompletionReduction_eq_restrictedReduction_algEquiv
    [CompleteSpace (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight)]
    [T0Space (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight)]
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (x : restrictedMvPowerSeriesCompletion k A) :
    J.restrictedCompletionReduction hJ x =
      J.restrictedReduction hJ (restrictedMvPowerSeriesCompletionAlgEquiv k A x) := by
  obtain ⟨f, rfl⟩ := (restrictedMvPowerSeriesCompletionEquiv k A).symm.surjective x
  simp

end Reduction

end Ideal

namespace TauCeti.Huber

open Ideal (restrictedReduction restrictedReduction_surjective
  restrictedCompletionReduction restrictedCompletionReduction_surjective)

section QuotientComparison

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {k : ℕ} {I : Ideal A}

/-- Reduction modulo a finitely generated ideal of definition has exactly the extended ideal
as its kernel. -/
theorem ker_restrictedReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedReduction (k := k) I (by simpa only [pow_one] using hI.isOpen_pow 1)) =
      I.map (weightedC _ isWeightFamily_one_weight) := by
  ext f
  rw [Ideal.mem_ker_restrictedReduction, mem_map_weightedC_iff_of_isAdic hI hfg]

/-- Reduction modulo any power `I ^ m` of a finitely generated ideal of definition has kernel
`(I · A⟨T⟩) ^ m`. -/
theorem ker_restrictedReduction_pow (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    RingHom.ker (restrictedReduction (k := k) (I ^ m) (hI.isOpen_pow m)) =
      I.map (weightedC _ isWeightFamily_one_weight) ^ m := by
  ext f
  rw [Ideal.mem_ker_restrictedReduction, mem_pow_map_weightedC_iff_of_isAdic hI hfg m]

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

/-- Reduction of restricted power series modulo any power `(I · A⟨T⟩) ^ m` of a finitely generated
ideal of definition is the polynomial algebra `(A ⧸ I ^ m)[T]`. -/
noncomputable def quotientPowRestrictedEquivMvPolynomialQuotient (hI : IsAdic I) (hfg : I.FG)
    (m : ℕ) :
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
      I.map (weightedC _ isWeightFamily_one_weight) ^ m) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I ^ m) := by
  let e := (Ideal.quotEquivOfEq (ker_restrictedReduction_pow (k := k) hI hfg m).symm).trans
    ((restrictedReduction (I ^ m) (hI.isOpen_pow m)).quotientKerEquivOfSurjective
      (restrictedReduction_surjective (I ^ m) (hI.isOpen_pow m)))
  refine AlgEquiv.ofRingEquiv (f := e) fun a ↦ ?_
  have he : e (algebraMap A _ a) =
      restrictedReduction (I ^ m) (hI.isOpen_pow m) (algebraMap A _ a) := by
    rw [← Ideal.Quotient.mk_algebraMap]
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [he]
  simp [algebraMap_weightedRestrictedSubring]

/-- On a represented series, `quotientPowRestrictedEquivMvPolynomialQuotient` computes its
reduction modulo `I ^ m`. -/
@[simp]
theorem quotientPowRestrictedEquivMvPolynomialQuotient_mk (hI : IsAdic I) (hfg : I.FG) (m : ℕ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    quotientPowRestrictedEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ f) =
      restrictedReduction (I ^ m) (hI.isOpen_pow m) f := by
  simp [quotientPowRestrictedEquivMvPolynomialQuotient]

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
theorem map_restrictedCompletionReduction {J : Ideal A} (hJ : IsOpen (J : Set A))
    (hI : IsOpen (I : Set A)) (hJI : J ≤ I) (x : restrictedMvPowerSeriesCompletion k A) :
    MvPolynomial.map (Ideal.Quotient.factor hJI) (J.restrictedCompletionReduction hJ x) =
      I.restrictedCompletionReduction hI x := by
  have hfac : Ideal.Quotient.factor hJI =
      Ideal.quotientMap I (RingHom.id A) (by simpa using hJI) :=
    RingHom.ext fun y ↦ by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      rfl
  rw [hfac, ← J.restrictedCompletionReduction_weightedMapCompletion hJ I hI
    (by simpa only [RingHom.coe_id] using continuous_id) (by simpa using hJI) x]
  simp

/-- On the completed restricted-series algebra `A⟨X₁, …, Xₖ⟩`, reduction modulo `I ^ m` has kernel
`(I · A⟨X₁, …, Xₖ⟩) ^ m` for every `m : ℕ`, without assuming completeness or separatedness of
`A`. -/
theorem ker_restrictedCompletionReduction_pow (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    RingHom.ker (restrictedCompletionReduction (k := k) (I ^ m) (hI.isOpen_pow m)) =
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) ^ m := by
  let S := weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
  let J := I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))
  have hle : J ^ m ≤
      RingHom.ker (restrictedCompletionReduction (k := k) (I ^ m) (hI.isOpen_pow m)) := by
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro a ha
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  refine le_antisymm ?_ hle
  intro x hx
  have hJ : IsAdic J := isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg
  obtain ⟨f, hf⟩ := (UniformSpace.Completion.denseRange_coe (α := S)).exists_mem_open
    ((hJ.isOpen_pow m).preimage (continuous_sub_left x))
    ⟨x, by simp⟩
  have hxf : x - (f : restrictedMvPowerSeriesCompletion k A) ∈ J ^ m := hf
  have hfker : (f : restrictedMvPowerSeriesCompletion k A) ∈
      RingHom.ker (restrictedCompletionReduction (k := k) (I ^ m) (hI.isOpen_pow m)) := by
    simpa [sub_sub_cancel] using Ideal.sub_mem _ hx (hle hxf)
  rw [RingHom.mem_ker, Ideal.restrictedCompletionReduction_coe, ← RingHom.mem_ker,
    ker_restrictedReduction_pow hI hfg m] at hfker
  have hfJ : (f : restrictedMvPowerSeriesCompletion k A) ∈ J ^ m := by
    have hcomp : (UniformSpace.Completion.coeRingHom :
          S →+* restrictedMvPowerSeriesCompletion k A).comp
        (weightedC (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) =
        algebraMap A (restrictedMvPowerSeriesCompletion k A) :=
      RingHom.ext fun a ↦ (algebraMap_completion_weightedRestrictedSubring_apply k A
        isWeightFamily_one_weight a).symm
    have hmap :
        (I.map (weightedC (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) ^ m).map
          (UniformSpace.Completion.coeRingHom : S →+* restrictedMvPowerSeriesCompletion k A) =
          J ^ m := by
      rw [Ideal.map_pow, Ideal.map_map, hcomp]
    exact hmap ▸ Ideal.mem_map_of_mem _ hfker
  simpa [sub_add_cancel] using Ideal.add_mem _ hxf hfJ

/-- Reduction of the completed restricted-series algebra modulo `(I · A⟨X⟩) ^ m` is the polynomial
algebra `(A ⧸ I ^ m)[X]` for every `m : ℕ`, with no completeness or separatedness assumption on
`A`. -/
noncomputable def quotientPowRestrictedCompletionEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    (restrictedMvPowerSeriesCompletion k A ⧸
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) ^ m) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I ^ m) := by
  let e := (Ideal.quotEquivOfEq
      (ker_restrictedCompletionReduction_pow (k := k) hI hfg m).symm).trans
    ((restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m)).quotientKerEquivOfSurjective
      (restrictedCompletionReduction_surjective (I ^ m) (hI.isOpen_pow m)))
  refine AlgEquiv.ofRingEquiv (f := e) fun a ↦ ?_
  have he : e (algebraMap A _ a) =
      restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m) (algebraMap A _ a) := by
    rw [← Ideal.Quotient.mk_algebraMap]
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [he]
  simp [Ideal.Quotient.algebraMap_eq]

/-- On the class of an element of `A⟨X₁, …, Xₖ⟩`,
`quotientPowRestrictedCompletionEquivMvPolynomialQuotient` computes its completed reduction modulo
`I ^ m`. -/
@[simp]
theorem quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) (x : restrictedMvPowerSeriesCompletion k A) :
    quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ x) =
      restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m) x := by
  simp [quotientPowRestrictedCompletionEquivMvPolynomialQuotient]

end QuotientComparison

section Completion

variable {k : ℕ} {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [NonarchimedeanRing R] [T2Space R] [CompleteSpace R] {J : Ideal R}

/-- The reduction modulo a finitely generated ideal of definition of the completed
restricted-series algebra is the polynomial algebra over the quotient of the coefficients. -/
noncomputable def quotientRestrictedCompletionEquivMvPolynomialQuotient
    (hJ : IsAdic J) (hfg : J.FG) :
    (restrictedMvPowerSeriesCompletion k R ⧸
      J.map (algebraMap R (restrictedMvPowerSeriesCompletion k R))) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ J) :=
  (Ideal.quotientEquivAlg _ _ (restrictedMvPowerSeriesCompletionAlgEquiv k R) (by
    rw [Ideal.map_map]
    congr 1
    rw [← algebraMap_weightedRestrictedSubring]
    exact (restrictedMvPowerSeriesCompletionAlgEquiv k R).toAlgHom.comp_algebraMap.symm)).trans
      (quotientRestrictedEquivMvPolynomialQuotient hJ hfg)

/-- On an arbitrary completion element, the quotient comparison reduces its associated
restricted series coefficientwise. -/
@[simp]
theorem quotientRestrictedCompletionEquivMvPolynomialQuotient_mk
    (hJ : IsAdic J) (hfg : J.FG) (x : restrictedMvPowerSeriesCompletion k R) :
    quotientRestrictedCompletionEquivMvPolynomialQuotient hJ hfg (Ideal.Quotient.mk _ x) =
      restrictedReduction J (by simpa only [pow_one] using hJ.isOpen_pow 1)
        (restrictedMvPowerSeriesCompletionAlgEquiv k R x) := by
  simp [quotientRestrictedCompletionEquivMvPolynomialQuotient]

end Completion

section Evaluation

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] {k : ℕ}

/-- Reducing a topologically evaluated restricted series modulo an open ideal `K` of the target
agrees with evaluating its polynomial reduction modulo an open ideal `J ≤ K.comap φ` at the
reduced point. -/
theorem quotientMk_weightedEvalHom {B : Type*} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
    {φ : A →+* B} (hφ : ContinuousAt φ 0) {b : Fin k → B}
    (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b)
    {J : Ideal A} (hJ : IsOpen (J : Set A)) {K : Ideal B} (hK : IsOpen (K : Set B))
    (hJK : J ≤ K.comap φ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    Ideal.Quotient.mk K (weightedEvalHom isWeightFamily_one_weight hφ hb f) =
      (J.restrictedReduction hJ f).eval₂ (Ideal.quotientMap K φ hJK)
        (Ideal.Quotient.mk K ∘ b) := by
  let : DiscreteTopology (B ⧸ K) := Submodule.Quotient.discreteTopology_of_isOpen K hK
  have hcont₁ : Continuous ((Ideal.Quotient.mk K).comp
      (weightedEvalHom isWeightFamily_one_weight hφ hb)) :=
    (QuotientRing.isOpenQuotientMap_mk K).continuous.comp
      (continuous_weightedEvalHom isWeightFamily_one_weight hφ hb)
  let rhs := (MvPolynomial.eval₂Hom (Ideal.quotientMap K φ hJK)
    (Ideal.Quotient.mk K ∘ b)).comp (J.restrictedReduction hJ)
  have hcont₂ : Continuous rhs :=
    ((J.isLocallyConstant_restrictedReduction hJ).comp
      (MvPolynomial.eval₂Hom (Ideal.quotientMap K φ hJK) (Ideal.Quotient.mk K ∘ b))).continuous
  have heq := weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    hcont₁ hcont₂ (fun a ↦ by simp [rhs]) (fun i ↦ by simp [rhs])
  exact congr($heq f)

/-- Reducing an evaluated element of the completed restricted-series algebra `A⟨X₁, …, Xₖ⟩`
modulo an open ideal `K` of the target agrees with evaluating its completed polynomial reduction
at the reduced point. -/
theorem quotientMk_weightedEvalHomCompletion {B : Type*} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
    {φ : A →+* B} (hφ : ContinuousAt φ 0) {b : Fin k → B}
    (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b)
    {J : Ideal A} (hJ : IsOpen (J : Set A)) {K : Ideal B} (hK : IsOpen (K : Set B))
    (hJK : J ≤ K.comap φ) (x : restrictedMvPowerSeriesCompletion k A) :
    Ideal.Quotient.mk K (weightedEvalHomCompletion isWeightFamily_one_weight hφ hb x) =
      (J.restrictedCompletionReduction hJ x).eval₂ (Ideal.quotientMap K φ hJK)
        (Ideal.Quotient.mk K ∘ b) := by
  let : DiscreteTopology (B ⧸ K) := Submodule.Quotient.discreteTopology_of_isOpen K hK
  have hcont₁ : Continuous ((Ideal.Quotient.mk K).comp
      (weightedEvalHomCompletion isWeightFamily_one_weight hφ hb)) :=
    (QuotientRing.isOpenQuotientMap_mk K).continuous.comp
      (continuous_weightedEvalHomCompletion isWeightFamily_one_weight hφ hb)
  let rhs := (MvPolynomial.eval₂Hom (Ideal.quotientMap K φ hJK)
    (Ideal.Quotient.mk K ∘ b)).comp (J.restrictedCompletionReduction hJ)
  have hcont₂ : Continuous rhs :=
    ((J.isLocallyConstant_restrictedCompletionReduction hJ).comp
      (MvPolynomial.eval₂Hom (Ideal.quotientMap K φ hJK) (Ideal.Quotient.mk K ∘ b))).continuous
  have heq := completion_weightedRestrictedSubring_ringHom_ext_of_continuous
    isWeightFamily_one_weight hcont₁ hcont₂
    (fun a ↦ by simp [rhs])
    (fun i ↦ by simp [rhs])
  exact congr($heq x)

end Evaluation

section LinearAlgebra

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsLinearTopology B B]
  [CompleteSpace B] [T0Space B] [Algebra A B] {k : ℕ}

/-- **Evaluation of `A⟨X₁, …, Xₖ⟩` in a complete separated linearly topologised `A`-algebra.**
Because `B` has a neighbourhood basis of ideals, every element of `B` is power-bounded, so
arbitrary values `b : Fin k → B` define a continuous `A`-algebra homomorphism out of
`restrictedMvPowerSeriesCompletion k A`. -/
noncomputable def restrictedLinearEvalAlgHom (hA : Continuous (algebraMap A B)) (b : Fin k → B) :
    restrictedMvPowerSeriesCompletion k A →ₐ[A] B :=
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  { weightedEvalHomCompletion isWeightFamily_one_weight hA.continuousAt
      (isWeightBounded_of_isLinearTopology (algebraMap A B) _ b) with
    commutes' a := by
      change weightedEvalHomCompletion _ _ _ _ = _
      rw [algebraMap_completion_weightedRestrictedSubring_apply, weightedEvalHomCompletion_coe,
        weightedEvalHom_weightedC] }

/-- `restrictedLinearEvalAlgHom` agrees with `weightedEvalHomCompletion` on elements. -/
theorem restrictedLinearEvalAlgHom_apply (hA : Continuous (algebraMap A B)) (b : Fin k → B)
    (x : restrictedMvPowerSeriesCompletion k A) :
    restrictedLinearEvalAlgHom hA b x =
      (have := IsLinearTopology.isTopologicalRing (R := B)
       have := IsLinearTopology.nonarchimedeanRing B
       weightedEvalHomCompletion isWeightFamily_one_weight hA.continuousAt
         (isWeightBounded_of_isLinearTopology (algebraMap A B) _ b) x) := by
  rfl

/-- `restrictedLinearEvalAlgHom` is continuous. -/
theorem continuous_restrictedLinearEvalAlgHom (hA : Continuous (algebraMap A B)) (b : Fin k → B) :
    Continuous (restrictedLinearEvalAlgHom hA b) := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  exact continuous_weightedEvalHomCompletion isWeightFamily_one_weight hA.continuousAt
    (isWeightBounded_of_isLinearTopology (algebraMap A B) _ b)

/-- `restrictedLinearEvalAlgHom` sends each coordinate variable `Xᵢ` to `bᵢ`. -/
@[simp]
theorem restrictedLinearEvalAlgHom_weightedX (hA : Continuous (algebraMap A B)) (b : Fin k → B)
    (i : Fin k) :
    restrictedLinearEvalAlgHom hA b
        ((weightedX _ isWeightFamily_one_weight i :
          weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
            restrictedMvPowerSeriesCompletion k A) =
      b i := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  simp [restrictedLinearEvalAlgHom]

/-- Reducing `restrictedLinearEvalAlgHom` modulo an open ideal `K` of `B` agrees with polynomial
evaluation of the completed reduction modulo an open ideal `J ≤ K.comap (algebraMap A B)`. -/
theorem quotientMk_restrictedLinearEvalAlgHom (hA : Continuous (algebraMap A B)) (b : Fin k → B)
    {J : Ideal A} (hJ : IsOpen (J : Set A)) {K : Ideal B} (hK : IsOpen (K : Set B))
    (hJK : J ≤ K.comap (algebraMap A B)) (x : restrictedMvPowerSeriesCompletion k A) :
    Ideal.Quotient.mk K (restrictedLinearEvalAlgHom hA b x) =
      (J.restrictedCompletionReduction hJ x).eval₂ (Ideal.quotientMap K (algebraMap A B) hJK)
        (Ideal.Quotient.mk K ∘ b) := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  exact quotientMk_weightedEvalHomCompletion hA.continuousAt
    (isWeightBounded_of_isLinearTopology (algebraMap A B) _ b) hJ hK hJK x

/-- **Universal property of `A⟨X₁, …, Xₖ⟩` for linearly topologised `A`-algebras.** For a complete
separated linearly topologised commutative `A`-algebra `B` with continuous structure map, arbitrary
choices `b : Fin k → B` of the variables determine a unique continuous `A`-algebra homomorphism
`A⟨X₁, …, Xₖ⟩ →ₐ[A] B`; compare
`existsUnique_continuous_ringHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology` for the
underlying ring-homomorphism form. -/
theorem existsUnique_continuous_algHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology
    (hA : Continuous (algebraMap A B)) (b : Fin k → B) :
    ∃! ψ : restrictedMvPowerSeriesCompletion k A →ₐ[A] B, Continuous ψ ∧
      ∀ i, ψ ((weightedX _ isWeightFamily_one_weight i :
        weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion k A) = b i := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  refine ⟨restrictedLinearEvalAlgHom hA b,
    ⟨continuous_restrictedLinearEvalAlgHom hA b, restrictedLinearEvalAlgHom_weightedX hA b⟩,
    fun ψ ⟨hψ, hX⟩ ↦ AlgHom.toRingHom_injective ?_⟩
  exact completion_weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    hψ (continuous_restrictedLinearEvalAlgHom hA b)
    (fun a ↦ by
      rw [RingHom.coe_coe, RingHom.coe_coe, ← algebraMap_completion_weightedRestrictedSubring_apply,
        ψ.commutes, (restrictedLinearEvalAlgHom hA b).commutes])
    (fun i ↦ (hX i).trans (restrictedLinearEvalAlgHom_weightedX hA b i).symm)

end LinearAlgebra

end TauCeti.Huber
