/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Quotient
public import TauCeti.RingTheory.AdicCompletion.UniformCompletion
public import TauCeti.RingTheory.Huber.Adic
public import TauCeti.RingTheory.Huber.Restricted.Adic
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Kernel
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
import TauCeti.RingTheory.AdicCompletion.AlgHom
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.Topology.Algebra.Nonarchimedean.Quotient
import TauCeti.Topology.Algebra.Module.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Polynomial reductions of adic restricted power series

Reduction of restricted power series modulo an open ideal is polynomial, both on the restricted
series subring (`Ideal.restrictedReduction`) and on its separated completion
(`Ideal.restrictedCompletionReduction`), without requiring completeness or separatedness of the
coefficient ring. For a finitely generated ideal of definition `I`, the kernel is the extended
ideal `I·A⟨T⟩`, giving `A⟨T⟩/I·A⟨T⟩ ≃ₐ[A] (A/I)[T]` on both the uncompleted and completed carriers.
Since every positive power `Iᵐ` (`m ≠ 0`) is again a finitely generated ideal of definition
(`is_ideal_adic_pow`), this yields `A⟨T⟩/(I·A⟨T⟩)ᵐ ≃ₐ[A] (A/Iᵐ)[T]` on both carriers and identifies
the separated completion `A⟨T⟩` as a topological `A`-algebra with the `(I·A[T])`-adic inverse-limit
completion `AdicCompletion (I.map MvPolynomial.C) (MvPolynomial (Fin k) A)`
whose `m`-th projection (`m ≠ 0`) computes polynomial reduction modulo `Iᵐ`.

Reduction is continuous into any topology on `MvPolynomial (Fin k) (A ⧸ J)`, natural under
continuous coefficient homomorphisms mapping an open ideal of the source into an open ideal of the
target, and commutes with topological evaluation (`weightedEvalHom` and
`weightedEvalHomCompletion`) modulo any open ideal of the target ring: ideal neighbourhoods
annihilate higher-order terms regardless of the values substituted for the variables.

## Main definitions

* `Ideal.restrictedReduction` and `Ideal.restrictedCompletionReduction`: polynomial reduction of
  uncompleted and completed restricted power series modulo an open ideal.
* `TauCeti.Huber.quotientRestrictedEquivMvPolynomialQuotient` and
  `TauCeti.Huber.quotientRestrictedCompletionEquivMvPolynomialQuotient`: the `A`-algebra
  equivalences modulo `I·A⟨T⟩` on the uncompleted and completed carriers.
* `TauCeti.Huber.quotientPowRestrictedEquivMvPolynomialQuotient` and
  `TauCeti.Huber.quotientPowRestrictedCompletionEquivMvPolynomialQuotient`: the `A`-algebra
  equivalences modulo `(I·A⟨T⟩)ᵐ` for `m ≠ 0`.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionEquivAdicCompletion`: the topological `A`-algebra
  equivalence from the completed restricted-series algebra to the `(I·A[T])`-adic completion of
  `MvPolynomial (Fin k) A`.

## Main results

* `Ideal.continuous_restrictedReduction` and `Ideal.continuous_restrictedCompletionReduction`:
  continuity of uncompleted and completed polynomial reduction.
* `TauCeti.Huber.restrictedReduction_weightedMap` and
  `TauCeti.Huber.restrictedCompletionReduction_weightedMapCompletion`: naturality of polynomial
  reduction along continuous coefficient maps.
* `TauCeti.Huber.mk_weightedEvalHom_eq_eval₂_restrictedReduction` and
  `TauCeti.Huber.mk_weightedEvalHomCompletion_eq_eval₂_restrictedCompletionReduction`: reducing an
  evaluated restricted series modulo an open ideal agrees with polynomial evaluation of its
  reduction.
* `TauCeti.Huber.evalₐ_restrictedMvPowerSeriesCompletionEquivAdicCompletion`: for `m ≠ 0`, the
  `m`-th inverse-limit projection computes polynomial reduction modulo `Iᵐ`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.1–7.5.4.
* T. Wedhorn, *Adic Spaces*, §5.6, Proposition 5.50.
-/

public section

open Topology

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

/-- A restricted series reduces to `0` modulo an open ideal `J` if and only if all of its
coefficients belong to `J`. -/
theorem restrictedReduction_eq_zero_iff {J : Ideal A} (hJ : IsOpen (J : Set A))
    {f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight} :
    restrictedReduction J hJ f = 0 ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ J := by
  simp [MvPolynomial.ext_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- On polynomials, reduction of restricted series is the usual coefficient map. -/
@[simp]
theorem restrictedReduction_weightedPolynomialHom (J : Ideal A) (hJ : IsOpen (J : Set A))
    (p : MvPolynomial (Fin k) A) :
    restrictedReduction J hJ (weightedPolynomialHom _ isWeightFamily_one_weight p) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  ext ν; simp [MvPolynomial.coeff_map]

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
    Function.Surjective (restrictedReduction (k := k) J hJ) := fun p ↦ by
  obtain ⟨q, rfl⟩ :=
    MvPolynomial.map_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective p
  exact ⟨weightedPolynomialHom _ isWeightFamily_one_weight q, by simp⟩

/-- Reduction of completed restricted series modulo an open ideal is polynomial. Because `A ⧸ J`
is discrete, its restricted-series ring is already discrete, hence complete and separated; no
completeness or separatedness assumption on `A` is needed. -/
noncomputable def restrictedCompletionReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    restrictedMvPowerSeriesCompletion k A →+* MvPolynomial (Fin k) (A ⧸ J) :=
  letI : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  haveI : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
    isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  haveI : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
    isWeightFamily_one_weight) := IsRightUniformAddGroup.discreteUniformity
  (weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).symm.toRingHom.comp
    ((restrictedMvPowerSeriesCompletionEquiv k (A ⧸ J)).toRingHom.comp
      (weightedMapCompletion (φ := Ideal.Quotient.mk J)
        (QuotientRing.isOpenQuotientMap_mk J).continuous
        isWeightFamily_one_weight isWeightFamily_one_weight (by simp)))

/-- Any post-composition of `restrictedReduction` into a topological space is continuous, since it
factors through the discrete ring of restricted series over `A ⧸ J`. -/
theorem continuous_comp_restrictedReduction {Z : Type*} [TopologicalSpace Z]
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (g : MvPolynomial (Fin k) (A ⧸ J) → Z) :
    Continuous (fun f ↦ g (restrictedReduction (k := k) J hJ f)) := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
    isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  exact (continuous_of_discreteTopology (f := fun y ↦
    g ((weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).symm y))).comp
      (continuous_weightedMap _ _ _ _)

/-- `restrictedReduction` is continuous into any topology on `MvPolynomial (Fin k) (A ⧸ J)`. -/
theorem continuous_restrictedReduction (J : Ideal A)
    [TopologicalSpace (MvPolynomial (Fin k) (A ⧸ J))] (hJ : IsOpen (J : Set A)) :
    Continuous (restrictedReduction (k := k) J hJ) :=
  continuous_comp_restrictedReduction J hJ id

/-- Any post-composition of `restrictedCompletionReduction` into a topological space is continuous,
since it factors through the discrete ring of restricted series over `A ⧸ J`. -/
theorem continuous_comp_restrictedCompletionReduction {Z : Type*} [TopologicalSpace Z]
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (g : MvPolynomial (Fin k) (A ⧸ J) → Z) :
    Continuous (fun x ↦ g (restrictedCompletionReduction (k := k) J hJ x)) := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
    isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  have : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
    isWeightFamily_one_weight) := IsRightUniformAddGroup.discreteUniformity
  exact (continuous_of_discreteTopology (f := fun y ↦
    g ((weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).symm y))).comp
      (uniformContinuous_restrictedMvPowerSeriesCompletionEquiv.continuous.comp
        (continuous_weightedMapCompletion _ _ _ _))

/-- `restrictedCompletionReduction` is continuous into any topology on
`MvPolynomial (Fin k) (A ⧸ J)`. -/
theorem continuous_restrictedCompletionReduction (J : Ideal A)
    [TopologicalSpace (MvPolynomial (Fin k) (A ⧸ J))] (hJ : IsOpen (J : Set A)) :
    Continuous (restrictedCompletionReduction (k := k) J hJ) :=
  continuous_comp_restrictedCompletionReduction J hJ id

/-- On the canonical image of a restricted series, completed reduction agrees with uncompleted
reduction. -/
@[simp]
theorem restrictedCompletionReduction_coe (J : Ideal A) (hJ : IsOpen (J : Set A))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    restrictedCompletionReduction J hJ (f : restrictedMvPowerSeriesCompletion k A) =
      restrictedReduction J hJ f := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
    isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  have : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
    isWeightFamily_one_weight) := IsRightUniformAddGroup.discreteUniformity
  simp [restrictedCompletionReduction, restrictedReduction]

/-- Completed reduction sends a constant to the corresponding constant polynomial. -/
theorem restrictedCompletionReduction_algebraMap (J : Ideal A) (hJ : IsOpen (J : Set A)) (a : A) :
    restrictedCompletionReduction (k := k) J hJ
        (algebraMap A (restrictedMvPowerSeriesCompletion k A) a) =
      MvPolynomial.C (Ideal.Quotient.mk J a) := by
  rw [algebraMap_completion_weightedRestrictedSubring_apply, restrictedCompletionReduction_coe,
    restrictedReduction_weightedC]

/-- Completed reduction preserves each coordinate variable. -/
theorem restrictedCompletionReduction_weightedX (J : Ideal A) (hJ : IsOpen (J : Set A))
    (i : Fin k) :
    restrictedCompletionReduction J hJ
        ((weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i :
          weightedRestrictedSubring _ isWeightFamily_one_weight) :
            restrictedMvPowerSeriesCompletion k A) = MvPolynomial.X i := by
  rw [restrictedCompletionReduction_coe, restrictedReduction_weightedX]

/-- On embedded polynomials, completed reduction reduces coefficients modulo `J`. -/
theorem restrictedCompletionReduction_weightedPolynomialHom
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (p : MvPolynomial (Fin k) A) :
    restrictedCompletionReduction J hJ
        ((weightedPolynomialHom (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight p :
          weightedRestrictedSubring _ isWeightFamily_one_weight) :
            restrictedMvPowerSeriesCompletion k A) = MvPolynomial.map (Ideal.Quotient.mk J) p := by
  rw [restrictedCompletionReduction_coe, restrictedReduction_weightedPolynomialHom]

/-- Every polynomial over `A ⧸ J` lifts to the completed restricted-series algebra. -/
theorem restrictedCompletionReduction_surjective (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    Function.Surjective (restrictedCompletionReduction (k := k) J hJ) := fun p ↦ by
  obtain ⟨f, rfl⟩ := restrictedReduction_surjective (k := k) J hJ p
  exact ⟨f, restrictedCompletionReduction_coe J hJ f⟩

end Ideal

namespace TauCeti.Huber

open Ideal (restrictedReduction restrictedReduction_surjective restrictedCompletionReduction)

/-- Polynomial reduction is natural along a continuous coefficient homomorphism carrying an open
ideal of the source into an open ideal of the target. -/
theorem restrictedReduction_weightedMap {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ) {I : Ideal A} {J : Ideal B}
    (hI : IsOpen (I : Set A)) (hJ : IsOpen (J : Set B)) (hIJ : I ≤ J.comap φ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    restrictedReduction J hJ
        (weightedMap hφ isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (restrictedReduction I hI f) := by
  ext ν; simp [MvPolynomial.coeff_map]

/-- Completed polynomial reduction is natural along a continuous coefficient homomorphism carrying
an open ideal of the source into an open ideal of the target. -/
theorem restrictedCompletionReduction_weightedMapCompletion
    {B : Type*} [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]
    {φ : A →+* B} (hφ : Continuous φ) {I : Ideal A} {J : Ideal B}
    (hI : IsOpen (I : Set A)) (hJ : IsOpen (J : Set B)) (hIJ : I ≤ J.comap φ)
    (x : restrictedMvPowerSeriesCompletion k A) :
    restrictedCompletionReduction J hJ
        (weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) x) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (restrictedCompletionReduction I hI x) := by
  let : TopologicalSpace (MvPolynomial (Fin k) (B ⧸ J)) := ⊥
  have : DiscreteTopology (MvPolynomial (Fin k) (B ⧸ J)) := ⟨rfl⟩
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    ((Ideal.continuous_restrictedCompletionReduction J hJ).comp
      (continuous_weightedMapCompletion _ _ _ _))
    (Ideal.continuous_comp_restrictedCompletionReduction I hI _)) fun f ↦ ?_
  simp [restrictedReduction_weightedMap hφ hI hJ hIJ]

/-- Reduction modulo a finitely generated ideal of definition has the extended ideal as its
kernel. -/
theorem ker_restrictedReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedReduction (k := k) I (pow_one I ▸ hI.isOpen_pow 1)) =
      I.map (weightedC _ isWeightFamily_one_weight) := by
  ext f
  rw [RingHom.mem_ker, Ideal.restrictedReduction_eq_zero_iff,
    mem_map_weightedC_iff_of_isAdic hI hfg]

/-- Reduction modulo the `m`-th power (`m ≠ 0`) of a finitely generated ideal of definition has
kernel `(I · A⟨T⟩) ^ m`. -/
theorem ker_restrictedReduction_pow (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0) :
    RingHom.ker (restrictedReduction (k := k) (I ^ m) (hI.isOpen_pow m)) =
      I.map (weightedC _ isWeightFamily_one_weight) ^ m :=
  Ideal.map_pow (weightedC (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) I m ▸
    ker_restrictedReduction (is_ideal_adic_pow hI (Nat.pos_of_ne_zero hm)) hfg.pow

/-- The infinitesimal reduction of restricted power series is a polynomial algebra. -/
noncomputable def quotientRestrictedEquivMvPolynomialQuotient (hI : IsAdic I) (hfg : I.FG) :
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
      I.map (weightedC _ isWeightFamily_one_weight)) ≃ₐ[A] MvPolynomial (Fin k) (A ⧸ I) := by
  let e := (Ideal.quotEquivOfEq (ker_restrictedReduction (k := k) hI hfg).symm).trans
    ((restrictedReduction I (pow_one I ▸ hI.isOpen_pow 1)).quotientKerEquivOfSurjective
      (restrictedReduction_surjective I (pow_one I ▸ hI.isOpen_pow 1)))
  refine AlgEquiv.ofRingEquiv (f := e) fun a ↦ ?_
  rw [← Ideal.Quotient.mk_algebraMap]; simp [e, algebraMap_weightedRestrictedSubring]

/-- On a represented series the quotient comparison computes its polynomial reduction. -/
@[simp]
theorem quotientRestrictedEquivMvPolynomialQuotient_mk (hI : IsAdic I) (hfg : I.FG)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    quotientRestrictedEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ f) =
      restrictedReduction I (pow_one I ▸ hI.isOpen_pow 1) f := by
  simp [quotientRestrictedEquivMvPolynomialQuotient]

/-- Infinitesimal thickening of order `m` (`m ≠ 0`): reducing restricted power series modulo
`(I · A⟨T⟩) ^ m` gives the polynomial algebra `(A ⧸ I ^ m)[T]`. -/
noncomputable def quotientPowRestrictedEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0) :
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
      I.map (weightedC _ isWeightFamily_one_weight) ^ m) ≃ₐ[A] MvPolynomial (Fin k) (A ⧸ I ^ m) :=
  (Ideal.quotientEquivAlgOfEq A (Ideal.map_pow _ I m).symm).trans
    (quotientRestrictedEquivMvPolynomialQuotient
      (is_ideal_adic_pow hI (Nat.pos_of_ne_zero hm)) hfg.pow)

/-- On a represented series, the order-`m` quotient comparison computes reduction modulo `I ^ m`. -/
@[simp]
theorem quotientPowRestrictedEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    quotientPowRestrictedEquivMvPolynomialQuotient hI hfg hm (Ideal.Quotient.mk _ f) =
      restrictedReduction (I ^ m) (hI.isOpen_pow m) f := by
  simp [quotientPowRestrictedEquivMvPolynomialQuotient]

/-- Reduction is compatible with passing to a larger open ideal. -/
@[simp]
theorem map_restrictedReduction {J : Ideal A} (hJ : IsOpen (J : Set A))
    (hI : IsOpen (I : Set A)) (hJI : J ≤ I)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    MvPolynomial.map (Ideal.Quotient.factor hJI) (restrictedReduction J hJ f) =
      restrictedReduction I hI f := by
  ext ν; simp [MvPolynomial.coeff_map]

/-- Completed reduction is compatible with passing to a larger open ideal. -/
@[simp]
theorem map_restrictedCompletionReduction {J : Ideal A} (hJ : IsOpen (J : Set A))
    (hI : IsOpen (I : Set A)) (hJI : J ≤ I) (x : restrictedMvPowerSeriesCompletion k A) :
    MvPolynomial.map (Ideal.Quotient.factor hJI) (restrictedCompletionReduction J hJ x) =
      restrictedCompletionReduction I hI x := by
  have hfac : Ideal.quotientMap I (RingHom.id A) hJI = Ideal.Quotient.factor hJI :=
    RingHom.ext fun q ↦ by obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q; rfl
  simpa [hfac] using
    (restrictedCompletionReduction_weightedMapCompletion (φ := RingHom.id A)
      continuous_id hJ hI hJI x).symm

section EvalCompatibility

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [NonarchimedeanRing B] [CompleteSpace B] [T3Space B] {φ : A →+* B} {b : Fin k → B}

/-- **Polynomial reduction commutes with topological evaluation.** Modulo an open ideal `J` of `B`,
evaluating a restricted series along `φ` at weight-bounded arguments `b` agrees with evaluating its
reduction modulo `I` in `B ⧸ J`, whenever `φ` carries `I` into `J`. Because `J` is an ideal, no
additional bound on the residues of `b` is needed. -/
theorem mk_weightedEvalHom_eq_eval₂_restrictedReduction
    (hφ : ContinuousAt φ 0) (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b)
    {J : Ideal B} (hI : IsOpen (I : Set A)) (hJ : IsOpen (J : Set B)) (hIJ : I ≤ J.comap φ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    Ideal.Quotient.mk J (weightedEvalHom isWeightFamily_one_weight hφ hb f) =
      (restrictedReduction I hI f).eval₂ (Ideal.quotientMap J φ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (b i)) := by
  let : DiscreteTopology (B ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  let ev := MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (fun i ↦ Ideal.Quotient.mk J (b i))
  have hcomp := weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    (f := (Ideal.Quotient.mk J).comp (weightedEvalHom isWeightFamily_one_weight hφ hb))
    (g := ev.comp (restrictedReduction I hI))
    ((QuotientRing.isOpenQuotientMap_mk J).continuous.comp (continuous_weightedEvalHom _ hφ hb))
    (Ideal.continuous_comp_restrictedReduction I hI ev) (fun _ ↦ by simp [ev])
    (fun _ ↦ by simp [ev])
  exact congr($hcomp f)

/-- **Completed polynomial reduction commutes with completed topological evaluation.** Modulo an
open ideal `J` of `B`, evaluating a completed restricted series at weight-bounded arguments `b`
agrees with polynomial evaluation of its reduction modulo `I`. -/
theorem mk_weightedEvalHomCompletion_eq_eval₂_restrictedCompletionReduction
    (hφ : ContinuousAt φ 0) (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b)
    {J : Ideal B} (hI : IsOpen (I : Set A)) (hJ : IsOpen (J : Set B)) (hIJ : I ≤ J.comap φ)
    (x : restrictedMvPowerSeriesCompletion k A) :
    Ideal.Quotient.mk J (weightedEvalHomCompletion isWeightFamily_one_weight hφ hb x) =
      (restrictedCompletionReduction I hI x).eval₂ (Ideal.quotientMap J φ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (b i)) := by
  let : DiscreteTopology (B ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    ((QuotientRing.isOpenQuotientMap_mk J).continuous.comp
      (continuous_weightedEvalHomCompletion _ hφ hb))
    (Ideal.continuous_comp_restrictedCompletionReduction I hI
      (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (b i))))) fun f ↦ ?_
  rw [weightedEvalHomCompletion_coe, Ideal.restrictedCompletionReduction_coe]
  exact mk_weightedEvalHom_eq_eval₂_restrictedReduction hφ hb hI hJ hIJ f

end EvalCompatibility

section CompletedQuotient

/-- Completed reduction modulo a finitely generated ideal of definition has kernel `I · A⟨T⟩`,
without requiring completeness or separatedness of `A`. -/
theorem ker_restrictedCompletionReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedCompletionReduction (k := k) I (pow_one I ▸ hI.isOpen_pow 1)) =
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) := by
  let K : Ideal (restrictedMvPowerSeriesCompletion k A) :=
    I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))
  have hIopen : IsOpen (I : Set A) := pow_one I ▸ hI.isOpen_pow 1
  have hKopen : IsOpen (K : Set (restrictedMvPowerSeriesCompletion k A)) :=
    pow_one K ▸ (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg).isOpen_pow 1
  have hKle : K ≤ RingHom.ker (restrictedCompletionReduction (k := k) I hIopen) :=
    Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
      rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.restrictedCompletionReduction_algebraMap,
        Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  refine le_antisymm (fun x hx ↦ ?_) hKle
  -- Approximate `x` modulo the open ideal `K` by an uncompleted restricted series `f`.
  obtain ⟨f, hfx⟩ := UniformSpace.Completion.denseRange_coe.exists_mem_open
    (hKopen.preimage (f := (· - x)) (continuous_id.sub continuous_const)) ⟨x, by simp⟩
  have hfker : f ∈ I.map (weightedC (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) := by
    rw [← ker_restrictedReduction hI hfg, RingHom.mem_ker]
    have hsub : restrictedCompletionReduction I hIopen
        ((f : restrictedMvPowerSeriesCompletion k A) - x) = 0 := hKle hfx
    rwa [map_sub, Ideal.restrictedCompletionReduction_coe, RingHom.mem_ker.mp hx, sub_zero] at hsub
  have hfK : (f : restrictedMvPowerSeriesCompletion k A) ∈ K := by
    have hmap : (I.map (weightedC (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight)).map UniformSpace.Completion.coeRingHom = K := by
      rw [Ideal.map_map]; exact congrArg (Ideal.map · I) (RingHom.ext fun _ ↦ by simp)
    exact hmap ▸ Ideal.mem_map_of_mem UniformSpace.Completion.coeRingHom hfker
  simpa only [Set.mem_preimage, SetLike.mem_coe, sub_sub_cancel] using K.sub_mem hfK hfx

/-- Completed reduction modulo the `m`-th power (`m ≠ 0`) of a finitely generated ideal of
definition has kernel `(I · A⟨T⟩) ^ m`, without requiring completeness or separatedness of `A`. -/
theorem ker_restrictedCompletionReduction_pow (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0) :
    RingHom.ker (restrictedCompletionReduction (k := k) (I ^ m) (hI.isOpen_pow m)) =
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) ^ m :=
  Ideal.map_pow (algebraMap A (restrictedMvPowerSeriesCompletion k A)) I m ▸
    ker_restrictedCompletionReduction (is_ideal_adic_pow hI (Nat.pos_of_ne_zero hm)) hfg.pow

/-- The reduction modulo a finitely generated ideal of definition of the completed
restricted-series algebra is the polynomial algebra over the quotient of the coefficients, without
requiring completeness or separatedness of `A`. -/
noncomputable def quotientRestrictedCompletionEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) :
    (restrictedMvPowerSeriesCompletion k A ⧸
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I) := by
  let hopen : IsOpen (I : Set A) := pow_one I ▸ hI.isOpen_pow 1
  let e := (Ideal.quotEquivOfEq (ker_restrictedCompletionReduction (k := k) hI hfg).symm).trans
    ((restrictedCompletionReduction I hopen).quotientKerEquivOfSurjective
      (Ideal.restrictedCompletionReduction_surjective I hopen))
  refine AlgEquiv.ofRingEquiv (f := e) fun a ↦ ?_
  rw [← Ideal.Quotient.mk_algebraMap]; simp [e]

/-- On an arbitrary completion element, the quotient comparison computes completed polynomial
reduction modulo `I`. -/
@[simp]
theorem quotientRestrictedCompletionEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) (x : restrictedMvPowerSeriesCompletion k A) :
    quotientRestrictedCompletionEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ x) =
      restrictedCompletionReduction I (pow_one I ▸ hI.isOpen_pow 1) x := by
  simp [quotientRestrictedCompletionEquivMvPolynomialQuotient]

/-- Infinitesimal thickening of order `m` (`m ≠ 0`) on the completed carrier: reducing modulo
`(I · A⟨T⟩) ^ m` gives `(A ⧸ I ^ m)[T]`, without requiring completeness or separatedness of `A`. -/
noncomputable def quotientPowRestrictedCompletionEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0) :
    (restrictedMvPowerSeriesCompletion k A ⧸
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) ^ m) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I ^ m) :=
  (Ideal.quotientEquivAlgOfEq A (Ideal.map_pow _ I m).symm).trans
    (quotientRestrictedCompletionEquivMvPolynomialQuotient
      (is_ideal_adic_pow hI (Nat.pos_of_ne_zero hm)) hfg.pow)

/-- On an element of the completed carrier, the order-`m` quotient comparison computes completed
polynomial reduction modulo `I ^ m`. -/
@[simp]
theorem quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (x : restrictedMvPowerSeriesCompletion k A) :
    quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg hm (Ideal.Quotient.mk _ x) =
      restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m) x := by
  simp [quotientPowRestrictedCompletionEquivMvPolynomialQuotient]

end CompletedQuotient

section AdicLimit

/-- `A`-algebra inclusion of polynomials into uncompleted restricted power series. -/
private noncomputable def weightedPolynomialAlgHom :
    MvPolynomial (Fin k) A →ₐ[A]
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  { weightedPolynomialHom _ isWeightFamily_one_weight with
    commutes' a := by simp [algebraMap_weightedRestrictedSubring] }

omit [TopologicalSpace A] [NonarchimedeanRing A] in
private theorem quotientEquivQuotientMvPolynomial_symm_mk (J : Ideal A)
    (p : MvPolynomial (Fin k) A) :
    (MvPolynomial.quotientEquivQuotientMvPolynomial J).symm
        (Ideal.Quotient.mk (Ideal.map MvPolynomial.C J) p) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]; rfl

private theorem map_weightedPolynomialAlgHom_le (I : Ideal A) :
    I.map (MvPolynomial.C (σ := Fin k)) ≤
      (I.map (algebraMap A (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight))).comap (weightedPolynomialAlgHom (k := k) (A := A)) :=
  Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
    rw [← MvPolynomial.algebraMap_eq]
    simpa only [Ideal.mem_comap, AlgHom.coe_ofClass, AlgHom.commutes] using
      Ideal.mem_map_of_mem _ ha

private theorem bijective_mapₐ_weightedPolynomialAlgHom (hI : IsAdic I) (hfg : I.FG) :
    Function.Bijective (AdicCompletion.mapₐ (weightedPolynomialAlgHom (k := k) (A := A))
      (map_weightedPolynomialAlgHom_le I)) := by
  refine AdicCompletion.mapₐ_bijective _ _ fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have h1 := Submodule.Quotient.subsingleton_iff.mpr
      ((pow_zero (I.map (MvPolynomial.C (σ := Fin k)))).trans Ideal.one_eq_top)
    have h2 := Submodule.Quotient.subsingleton_iff.mpr ((pow_zero
      (I.map (algebraMap A (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight)))).trans Ideal.one_eq_top)
    exact ⟨fun _ _ _ ↦ h1.elim _ _, fun _ ↦ ⟨0, h2.elim _ _⟩⟩
  · let e₁ := (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).toRingEquiv.trans
      (Ideal.quotEquivOfEq (Ideal.map_pow (MvPolynomial.C (σ := Fin k)) I n))
    have halg : I.map (algebraMap A (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight)) ^ n =
        I.map (weightedC _ isWeightFamily_one_weight) ^ n := by
      rw [algebraMap_weightedRestrictedSubring]
    let e₂ := (Ideal.quotEquivOfEq halg).trans
      (quotientPowRestrictedEquivMvPolynomialQuotient (k := k) hI hfg hn).toRingEquiv
    let qmap := Ideal.quotientMap _ (weightedPolynomialAlgHom (k := k) (A := A)).toRingHom
      ((Ideal.pow_right_mono (map_weightedPolynomialAlgHom_le I) n).trans (Ideal.le_comap_pow _ n))
    have hcomp : (e₂ ∘ (qmap ∘ e₁)) = id := funext fun q ↦ by
      obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective q
      have he₁ : e₁ (MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p) = Ideal.Quotient.mk _ p := by
        rw [← quotientEquivQuotientMvPolynomial_symm_mk]; simp [e₁]
      simp [Function.comp_apply, he₁, qmap, e₂, weightedPolynomialAlgHom]
    exact (e₁.bijective.of_comp_iff qmap).mp
      ((e₂.bijective.of_comp_iff' (qmap ∘ e₁)).mp (hcomp.symm ▸ Function.bijective_id))

/-- **Inverse-limit description of completed restricted power series** (EGA I, Ch. 0, §7.5.1).
When `A` has a finitely generated ideal of definition `I`, the completed restricted-series algebra
`A⟨T₁, …, Tₖ⟩` is isomorphic as an `A`-algebra to the `(I · A[T])`-adic completion of the
polynomial algebra `MvPolynomial (Fin k) A`. -/
noncomputable def restrictedMvPowerSeriesCompletionEquivAdicCompletion
    (hI : IsAdic I) (hfg : I.FG) :
    restrictedMvPowerSeriesCompletion k A ≃ₐ[A]
      AdicCompletion (I.map (MvPolynomial.C (σ := Fin k))) (MvPolynomial (Fin k) A) :=
  let hAdic := isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg
  (AlgEquiv.ofRingEquiv (f := hAdic.completionEquivAdicCompletion (hfg.map _)) fun a ↦ by
    rw [algebraMap_completion_weightedRestrictedSubring_apply,
      IsAdic.completionEquivAdicCompletion_coe, ← algebraMap_weightedRestrictedSubring,
      ← IsScalarTower.algebraMap_apply]).trans
    (AlgEquiv.ofBijective (AdicCompletion.mapₐ (weightedPolynomialAlgHom (k := k) (A := A))
      (map_weightedPolynomialAlgHom_le I)) (bijective_mapₐ_weightedPolynomialAlgHom hI hfg)).symm

/-- On an embedded polynomial, `restrictedMvPowerSeriesCompletionEquivAdicCompletion` agrees with
the canonical `algebraMap` from `MvPolynomial (Fin k) A` into its adic completion. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionEquivAdicCompletion_weightedPolynomialHom
    (hI : IsAdic I) (hfg : I.FG) (p : MvPolynomial (Fin k) A) :
    restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg
        ((weightedPolynomialHom (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight p :
          weightedRestrictedSubring _ isWeightFamily_one_weight) :
            restrictedMvPowerSeriesCompletion k A) =
      algebraMap (MvPolynomial (Fin k) A) _ p := by
  let ePoly := AlgEquiv.ofBijective
    (AdicCompletion.mapₐ (weightedPolynomialAlgHom (k := k) (A := A))
      (map_weightedPolynomialAlgHom_le I)) (bijective_mapₐ_weightedPolynomialAlgHom hI hfg)
  apply ePoly.injective
  dsimp only [restrictedMvPowerSeriesCompletionEquivAdicCompletion]
  rw [AlgEquiv.trans_apply, ePoly.apply_symm_apply, AlgEquiv.ofRingEquiv_apply,
    IsAdic.completionEquivAdicCompletion_coe]
  simp [ePoly, AdicCompletion.algebraMap_apply, weightedPolynomialAlgHom]

/-- The inverse of `restrictedMvPowerSeriesCompletionEquivAdicCompletion` sends an embedded
polynomial in `AdicCompletion` to its image in `restrictedMvPowerSeriesCompletion k A`. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionEquivAdicCompletion_symm_algebraMap
    (hI : IsAdic I) (hfg : I.FG) (p : MvPolynomial (Fin k) A) :
    (restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg).symm
        (algebraMap (MvPolynomial (Fin k) A) _ p) =
      ((weightedPolynomialHom (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight p :
        weightedRestrictedSubring _ isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion k A) := by
  rw [AlgEquiv.symm_apply_eq,
    restrictedMvPowerSeriesCompletionEquivAdicCompletion_weightedPolynomialHom]

/-- `restrictedMvPowerSeriesCompletionEquivAdicCompletion` is a homeomorphism when `AdicCompletion`
carries the adic topology of the extended ideal. -/
theorem isHomeomorph_restrictedMvPowerSeriesCompletionEquivAdicCompletion
    (hI : IsAdic I) (hfg : I.FG) :
    @IsHomeomorph _ _ _
      ((I.map (MvPolynomial.C (σ := Fin k))).map (algebraMap _ _)).adicTopology
      (restrictedMvPowerSeriesCompletionEquivAdicCompletion (k := k) hI hfg) := by
  let P := MvPolynomial (Fin k) A
  let IP : Ideal P := I.map MvPolynomial.C
  let C := AdicCompletion IP P
  let : WithIdeal C := ⟨IP.map (algebraMap P C)⟩
  have hAdicB := isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg
  have hAdicC : IsAdic (I.map (algebraMap A C)) :=
    (show IP.map (algebraMap P C) = I.map (algebraMap A C) by
      dsimp only [IP]
      rw [← MvPolynomial.algebraMap_eq, Ideal.map_map, ← IsScalarTower.algebraMap_eq]) ▸
      (rfl : IsAdic (IP.map (algebraMap P C)))
  let e := restrictedMvPowerSeriesCompletionEquivAdicCompletion (k := k) hI hfg
  have he : (I.map (algebraMap A _)).map e.toRingHom = I.map (algebraMap A C) := by
    rw [Ideal.map_map]; exact congrArg (Ideal.map · I) (RingHom.ext e.commutes)
  have hesymm : (I.map (algebraMap A C)).map e.symm.toRingHom = I.map (algebraMap A _) := by
    rw [Ideal.map_map]; exact congrArg (Ideal.map · I) (RingHom.ext e.symm.commutes)
  exact e.toEquiv.isHomeomorph_iff.mpr
    ⟨hAdicB.continuous_of_map_le_radical hAdicC (hfg.map _) (he.le.trans Ideal.le_radical),
     hAdicC.continuous_of_map_le_radical hAdicB (hfg.map _) (hesymm.le.trans Ideal.le_radical)⟩

/-- Under `restrictedMvPowerSeriesCompletionEquivAdicCompletion`, the `m`-th inverse-limit
projection (`m ≠ 0`) identifies with completed polynomial reduction modulo `I ^ m` via
`MvPolynomial.quotientEquivQuotientMvPolynomial`. -/
theorem evalₐ_restrictedMvPowerSeriesCompletionEquivAdicCompletion
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (x : restrictedMvPowerSeriesCompletion k A) :
    AdicCompletion.evalₐ _ m (restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg x) =
      Ideal.quotEquivOfEq (Ideal.map_pow (MvPolynomial.C (σ := Fin k)) I m)
        (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ m)
          (restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m) x)) := by
  let P := MvPolynomial (Fin k) A
  let IP : Ideal P := I.map MvPolynomial.C
  let e := restrictedMvPowerSeriesCompletionEquivAdicCompletion (k := k) hI hfg
  obtain ⟨p, hp⟩ := AdicCompletion.exists_sub_algebraMap_mem_map_pow (I := IP) (hfg.map _) m (e x)
  have heval : AdicCompletion.evalₐ IP m (e x) = Ideal.Quotient.mk (IP ^ m) p := by
    have hker : e x - algebraMap P (AdicCompletion IP P) p ∈
        RingHom.ker (AdicCompletion.evalₐ IP m).toRingHom :=
      (AdicCompletion.ker_evalₐ_eq_map_pow (R := P) (I := IP) (hfg.map _) m).symm ▸ hp
    simpa [sub_eq_zero, AdicCompletion.algebraMap_apply] using RingHom.mem_ker.mp hker
  have hmap : ((IP ^ m).map (algebraMap P (AdicCompletion IP P))).map e.symm.toRingHom =
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) ^ m := by
    rw [show IP ^ m = (I ^ m).map (MvPolynomial.C (σ := Fin k)) from (Ideal.map_pow _ I m).symm,
      Ideal.map_map, Ideal.map_map, ← Ideal.map_pow]
    exact congrArg (Ideal.map · (I ^ m)) (RingHom.ext fun a ↦ by
      have hCa : algebraMap P (AdicCompletion IP P) (MvPolynomial.C a) =
          algebraMap A (AdicCompletion IP P) a := by
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply A P]
      exact (congrArg e.symm hCa).trans (e.symm.commutes a))
  have hred : restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m) x =
      MvPolynomial.map (Ideal.Quotient.mk (I ^ m)) p := by
    have hxker : e.symm (e x - algebraMap P (AdicCompletion IP P) p) ∈
        RingHom.ker (restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m)) := by
      rw [ker_restrictedCompletionReduction_pow hI hfg hm, ← hmap]
      exact Ideal.mem_map_of_mem e.symm.toRingHom hp
    have hx0 := RingHom.mem_ker.mp hxker
    dsimp only [P, IP, e] at hx0
    rw [map_sub, AlgEquiv.symm_apply_apply,
      restrictedMvPowerSeriesCompletionEquivAdicCompletion_symm_algebraMap, map_sub,
      Ideal.restrictedCompletionReduction_coe, Ideal.restrictedReduction_weightedPolynomialHom,
      sub_eq_zero] at hx0
    exact hx0
  rw [heval, hred, ← quotientEquivQuotientMvPolynomial_symm_mk, AlgEquiv.apply_symm_apply,
    Ideal.quotEquivOfEq_mk]

end AdicLimit

section Completion

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [NonarchimedeanRing R] [T2Space R] [CompleteSpace R] {J : Ideal R}

/-- Over a complete separated coefficient ring, completed polynomial reduction agrees with
uncompleted reduction through `restrictedMvPowerSeriesCompletionEquiv`. -/
theorem restrictedCompletionReduction_eq_restrictedReduction
    (hJ : IsOpen (J : Set R)) (x : restrictedMvPowerSeriesCompletion k R) :
    restrictedCompletionReduction J hJ x =
      restrictedReduction J hJ (restrictedMvPowerSeriesCompletionEquiv k R x) := by
  conv_lhs => rw [← (restrictedMvPowerSeriesCompletionEquiv k R).symm_apply_apply x]
  rw [restrictedMvPowerSeriesCompletionEquiv_symm_apply, Ideal.restrictedCompletionReduction_coe]

end Completion

end TauCeti.Huber
