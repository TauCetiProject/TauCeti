/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.UniformCompletion
public import TauCeti.RingTheory.Huber.Adic
public import TauCeti.RingTheory.Huber.Restricted.Adic
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Kernel
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
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
ideal `I·A⟨T⟩`, which equals the set of series whose coefficients lie in `I`. Thus
`A⟨T⟩/I·A⟨T⟩ ≃ₐ[A] (A/I)[T]`, also on the completed carrier when `A` is complete and Hausdorff.
Every positive power `Iᵐ` is again a finitely generated ideal of definition (`IsAdic.pow`), giving
`A⟨T⟩/(I·A⟨T⟩)ᵐ ≃ₐ[A] (A/Iᵐ)[T]` on both carriers and identifying the separated completion
`A⟨T⟩` with the inverse-limit adic completion `AdicCompletion (I·A⟨T⟩) A⟨T⟩` whose `m`-th
projection computes polynomial reduction modulo `Iᵐ`.

Reduction is natural under continuous coefficient homomorphisms mapping an open ideal of the source
into an open ideal of the target, and commutes with topological evaluation (`weightedEvalHom` and
`weightedEvalHomCompletion`) modulo any open ideal of the target ring: ideal neighbourhoods
annihilate higher-order terms regardless of the values substituted for the variables.

## Main definitions

* `Ideal.restrictedReduction` and `Ideal.restrictedCompletionReduction`: polynomial reduction of
  uncompleted and completed restricted power series modulo an open ideal.
* `TauCeti.Huber.quotientRestrictedEquivMvPolynomialQuotient` and
  `TauCeti.Huber.quotientRestrictedCompletionEquivMvPolynomialQuotient`: the `A`-algebra
  equivalences modulo `I·A⟨T⟩`.
* `TauCeti.Huber.quotientPowRestrictedEquivMvPolynomialQuotient` and
  `TauCeti.Huber.quotientPowRestrictedCompletionEquivMvPolynomialQuotient`: the `A`-algebra
  equivalences modulo `(I·A⟨T⟩)ᵐ` for `m ≠ 0`.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionEquivAdicCompletion`: the ring isomorphism from
  the completed restricted-series algebra to the inverse-limit adic completion.

## Main results

* `Ideal.restrictedReduction_weightedMap` and
  `Ideal.restrictedCompletionReduction_weightedMapCompletion`: naturality of polynomial reduction
  along continuous coefficient maps.
* `TauCeti.Huber.mk_weightedEvalHom_eq_eval₂_restrictedReduction` and
  `TauCeti.Huber.mk_weightedEvalHomCompletion_eq_eval₂_restrictedCompletionReduction`: reducing an
  evaluated restricted series modulo an open ideal agrees with polynomial evaluation of its
  reduction.
* `TauCeti.Huber.quotientPowRestrictedEquiv_evalₐ_completionEquivAdicCompletion`: the `m`-th
  projection of the adic completion computes polynomial reduction modulo `Iᵐ`.

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

/-- Polynomial reduction is natural along a continuous coefficient homomorphism carrying an open
ideal of the source into an open ideal of the target. -/
theorem restrictedReduction_weightedMap {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ) {I : Ideal A} {J : Ideal B}
    (hI : IsOpen (I : Set A)) (hJ : IsOpen (J : Set B)) (hIJ : I ≤ J.comap φ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    restrictedReduction J hJ
        (weightedMap hφ isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (restrictedReduction I hI f) := by
  ext ν
  simp [MvPolynomial.coeff_map]

/-- Reduction of completed restricted series modulo an open ideal is polynomial. Because `A ⧸ J`
is discrete, its restricted-series ring is already discrete, hence complete and separated; no
completeness or separatedness assumption on `A` is needed. -/
noncomputable def restrictedCompletionReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
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

/-- Any post-composition of `restrictedReduction` into a topological space is continuous, since it
factors through the discrete ring of restricted series over `A ⧸ J`. -/
private theorem continuous_comp_restrictedReduction {Z : Type*} [TopologicalSpace Z]
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (g : MvPolynomial (Fin k) (A ⧸ J) → Z) :
    Continuous (fun f ↦ g (restrictedReduction (k := k) J hJ f)) := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  dsimp only [restrictedReduction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  exact (continuous_of_discreteTopology (f := fun y ↦
    g ((weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).symm y))).comp
      (continuous_weightedMap _ _ _ _)

/-- Any post-composition of `restrictedCompletionReduction` into a topological space is continuous,
since it factors through the discrete ring of restricted series over `A ⧸ J`. -/
private theorem continuous_comp_restrictedCompletionReduction {Z : Type*} [TopologicalSpace Z]
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (g : MvPolynomial (Fin k) (A ⧸ J) → Z) :
    Continuous (fun x ↦ g (restrictedCompletionReduction (k := k) J hJ x)) := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  have : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := IsRightUniformAddGroup.discreteUniformity
  dsimp only [restrictedCompletionReduction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  exact (continuous_of_discreteTopology (f := fun y ↦
    g ((weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).symm y))).comp
      (uniformContinuous_restrictedMvPowerSeriesCompletionEquiv.continuous.comp
        (continuous_weightedMapCompletion _ _ _ _))

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
  dsimp only [restrictedCompletionReduction, restrictedReduction, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [weightedMapCompletion_coe, restrictedMvPowerSeriesCompletionEquiv_coe]

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
        ((weightedX _ isWeightFamily_one_weight i :
          weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
            restrictedMvPowerSeriesCompletion k A) =
      MvPolynomial.X i := by
  rw [restrictedCompletionReduction_coe, restrictedReduction_weightedX]

/-- On embedded polynomials, completed reduction reduces coefficients modulo `J`. -/
theorem restrictedCompletionReduction_weightedPolynomialHom
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (p : MvPolynomial (Fin k) A) :
    restrictedCompletionReduction J hJ
        ((weightedPolynomialHom _ isWeightFamily_one_weight p :
          weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
            restrictedMvPowerSeriesCompletion k A) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  rw [restrictedCompletionReduction_coe, restrictedReduction_weightedPolynomialHom]

/-- Every polynomial over `A ⧸ J` lifts to the completed restricted-series algebra. -/
theorem restrictedCompletionReduction_surjective (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    Function.Surjective (restrictedCompletionReduction (k := k) J hJ) := by
  intro p
  obtain ⟨f, rfl⟩ := restrictedReduction_surjective (k := k) J hJ p
  exact ⟨f, restrictedCompletionReduction_coe J hJ f⟩

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
  let : DiscreteTopology (B ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (B ⧸ J)))
      isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  let eJ := weightedPolynomialEquivOfDiscrete (fun _ : Fin k ↦ ({1} : Set (B ⧸ J)))
    isWeightFamily_one_weight
  apply eJ.injective
  have hcomp :
      eJ.toRingHom.comp ((restrictedCompletionReduction (k := k) J hJ).comp
          (weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight
            (by simp))) =
        eJ.toRingHom.comp ((MvPolynomial.map (Ideal.quotientMap J φ hIJ)).comp
          (restrictedCompletionReduction I hI)) :=
    UniformSpace.Completion.ringHom_ext_of_continuous
      ((continuous_comp_restrictedCompletionReduction J hJ eJ).comp
        (continuous_weightedMapCompletion _ _ _ _))
      (continuous_comp_restrictedCompletionReduction I hI
        (fun p ↦ eJ (MvPolynomial.map (Ideal.quotientMap J φ hIJ) p)))
      (RingHom.ext fun f ↦ by
        simp [restrictedReduction_weightedMap hφ hI hJ hIJ])
  exact congr($hcomp x)

end Ideal

namespace TauCeti.Huber

open Ideal (restrictedReduction restrictedReduction_surjective restrictedCompletionReduction)

/-- Reduction modulo a finitely generated ideal of definition has exactly the extended ideal
as its kernel. -/
theorem ker_restrictedReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedReduction (k := k) I (by simpa only [pow_one] using hI.isOpen_pow 1)) =
      I.map (weightedC _ isWeightFamily_one_weight) := by
  ext f
  rw [RingHom.mem_ker, mem_map_weightedC_iff_of_isAdic hI hfg, MvPolynomial.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

/-- Reduction modulo the `m`-th power (`m ≠ 0`) of a finitely generated ideal of definition has
kernel `(I · A⟨T⟩) ^ m`. -/
theorem ker_restrictedReduction_pow (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0) :
    RingHom.ker (restrictedReduction (k := k) (I ^ m) (hI.isOpen_pow m)) =
      I.map (weightedC _ isWeightFamily_one_weight) ^ m := by
  rw [← Ideal.map_pow]
  exact ker_restrictedReduction (hI.pow hm) hfg.pow

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

/-- Infinitesimal thickening of order `m` (`m ≠ 0`): reducing restricted power series modulo
`(I · A⟨T⟩) ^ m` gives the polynomial algebra `(A ⧸ I ^ m)[T]`. -/
noncomputable def quotientPowRestrictedEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0) :
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
      I.map (weightedC _ isWeightFamily_one_weight) ^ m) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I ^ m) :=
  (Ideal.quotientEquivAlgOfEq A (Ideal.map_pow _ I m).symm).trans
    (quotientRestrictedEquivMvPolynomialQuotient (hI.pow hm) hfg.pow)

/-- On a represented series, the order-`m` quotient comparison computes reduction modulo `I ^ m`. -/
@[simp]
theorem quotientPowRestrictedEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    quotientPowRestrictedEquivMvPolynomialQuotient hI hfg hm (Ideal.Quotient.mk _ f) =
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
    (hI : IsOpen (I : Set A)) (hJI : J ≤ I)
    (x : restrictedMvPowerSeriesCompletion k A) :
    MvPolynomial.map (Ideal.Quotient.factor hJI) (restrictedCompletionReduction J hJ x) =
      restrictedCompletionReduction I hI x := by
  have hfac : Ideal.quotientMap I (RingHom.id A) hJI = Ideal.Quotient.factor hJI :=
    RingHom.ext fun q ↦ by obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q; rfl
  simpa [hfac] using
    (Ideal.restrictedCompletionReduction_weightedMapCompletion (φ := RingHom.id A)
      continuous_id hJ hI hJI x).symm

section EvalCompatibility

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [NonarchimedeanRing B] [CompleteSpace B] [T3Space B]
  {φ : A →+* B} {b : Fin k → B}

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
  have hcomp :
      (Ideal.Quotient.mk J).comp (weightedEvalHom isWeightFamily_one_weight hφ hb) =
        (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ)
          (fun i ↦ Ideal.Quotient.mk J (b i))).comp (restrictedReduction I hI) :=
    weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
      ((QuotientRing.isOpenQuotientMap_mk J).continuous.comp
        (continuous_weightedEvalHom _ hφ hb))
      (Ideal.continuous_comp_restrictedReduction I hI
        (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (fun i ↦ Ideal.Quotient.mk J (b i))))
      (fun a ↦ by simp)
      (fun i ↦ by simp)
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
  have hcomp :
      (Ideal.Quotient.mk J).comp (weightedEvalHomCompletion isWeightFamily_one_weight hφ hb) =
        (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ)
          (fun i ↦ Ideal.Quotient.mk J (b i))).comp (restrictedCompletionReduction I hI) :=
    completion_weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
      ((QuotientRing.isOpenQuotientMap_mk J).continuous.comp
        (continuous_weightedEvalHomCompletion _ hφ hb))
      (Ideal.continuous_comp_restrictedCompletionReduction I hI
        (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (fun i ↦ Ideal.Quotient.mk J (b i))))
      (fun a ↦ by
        rw [RingHom.comp_apply, RingHom.comp_apply, weightedEvalHomCompletion_coe,
          weightedEvalHom_weightedC, Ideal.restrictedCompletionReduction_coe,
          Ideal.restrictedReduction_weightedC, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
          Ideal.quotientMap_mk])
      (fun i ↦ by simp)
  exact congr($hcomp x)

end EvalCompatibility

section AdicLimit

/-- **Inverse-limit description of completed restricted power series.** When `A` has a finitely
generated ideal of definition `I`, the completed restricted-series algebra `A⟨T₁, …, Tₖ⟩` is
isomorphic to the algebraic adic completion of the restricted-series subring with respect to the
extended ideal `I · A⟨T⟩`. -/
noncomputable def restrictedMvPowerSeriesCompletionEquivAdicCompletion
    (hI : IsAdic I) (hfg : I.FG) :
    restrictedMvPowerSeriesCompletion k A ≃+*
      AdicCompletion
        (I.map (algebraMap A (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
          isWeightFamily_one_weight)))
        (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :=
  let hAdic := isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg
  hAdic.completionEquivAdicCompletion (hfg.map _)

/-- On a restricted series in the dense subring, the adic-completion isomorphism is `algebraMap`. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionEquivAdicCompletion_coe
    (hI : IsAdic I) (hfg : I.FG)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg
        (f : restrictedMvPowerSeriesCompletion k A) =
      algebraMap _ _ f :=
  IsAdic.completionEquivAdicCompletion_coe _ _ f

/-- The adic-completion comparison is a homeomorphism when `AdicCompletion` carries the adic
topology of the extended ideal. -/
theorem isHomeomorph_restrictedMvPowerSeriesCompletionEquivAdicCompletion
    (hI : IsAdic I) (hfg : I.FG) :
    @IsHomeomorph _ _ _
      ((I.map (algebraMap A (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight))).map (algebraMap _ _)).adicTopology
      (restrictedMvPowerSeriesCompletionEquivAdicCompletion (k := k) hI hfg) :=
  IsAdic.isHomeomorph_completionEquivAdicCompletion _ _

/-- The `m`-th inverse-limit projection (`m ≠ 0`) of the adic completion computes polynomial
reduction modulo `I ^ m`. -/
theorem quotientPowRestrictedEquiv_evalₐ_completionEquivAdicCompletion
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (x : restrictedMvPowerSeriesCompletion k A) :
    quotientPowRestrictedEquivMvPolynomialQuotient hI hfg hm
        (AdicCompletion.evalₐ _ m
          (restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg x)) =
      restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m) x := by
  let S := weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
  let K : Ideal S := I.map (weightedC _ isWeightFamily_one_weight)
  let e := restrictedMvPowerSeriesCompletionEquivAdicCompletion (k := k) hI hfg
  have hfgK : K.FG := hfg.map _
  obtain ⟨f, hf⟩ := AdicCompletion.exists_sub_algebraMap_mem_map_pow hfgK m (e x)
  have heval : AdicCompletion.evalₐ K m (e x) = Ideal.Quotient.mk (K ^ m) f := by
    have hker :
        e x - algebraMap S (AdicCompletion K S) f ∈ RingHom.ker (AdicCompletion.evalₐ K m) :=
      (AdicCompletion.ker_evalₐ_eq_map_pow hfgK m).symm ▸ hf
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, AdicCompletion.algebraMap_apply,
      AdicCompletion.evalₐ_of] at hker
    exact hker
  have hred : restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m) x =
      restrictedReduction (I ^ m) (hI.isOpen_pow m) f := by
    have hzero : restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m)
        (e.symm (e x - algebraMap S (AdicCompletion K S) f)) = 0 := by
      refine Submodule.span_induction (fun y hy ↦ ?_) (by simp)
        (fun _ _ _ _ hx hy ↦ by simp [hx, hy])
        (fun c y _ hy ↦ by
          rw [Algebra.smul_def, map_mul, map_mul, hy, mul_zero]) hf
      obtain ⟨s, hs, rfl⟩ := hy
      have hsymm : e.symm (algebraMap S (AdicCompletion K S) s) =
          (s : restrictedMvPowerSeriesCompletion k A) :=
        IsAdic.completionEquivAdicCompletion_symm_algebraMap _ _ s
      rw [hsymm, Ideal.restrictedCompletionReduction_coe]
      exact RingHom.mem_ker.mp ((ker_restrictedReduction_pow hI hfg hm).symm ▸ hs)
    have hsub : e.symm (e x - algebraMap S (AdicCompletion K S) f) =
        x - (f : restrictedMvPowerSeriesCompletion k A) := by
      rw [map_sub, e.symm_apply_apply]
      congr 1
      exact IsAdic.completionEquivAdicCompletion_symm_algebraMap _ _ f
    rw [hsub, map_sub, Ideal.restrictedCompletionReduction_coe, sub_eq_zero] at hzero
    exact hzero
  change quotientPowRestrictedEquivMvPolynomialQuotient hI hfg hm (AdicCompletion.evalₐ K m (e x)) =
    restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m) x
  rw [heval, hred]
  exact quotientPowRestrictedEquivMvPolynomialQuotient_mk hI hfg hm f

/-- Completed reduction modulo the `m`-th power (`m ≠ 0`) of a finitely generated ideal of
definition has kernel `(I · A⟨T⟩) ^ m`, without requiring completeness or separatedness of `A`. -/
theorem ker_restrictedCompletionReduction_pow (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0) :
    RingHom.ker (restrictedCompletionReduction (k := k) (I ^ m) (hI.isOpen_pow m)) =
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) ^ m := by
  let S := weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
  let K : Ideal S := I.map (weightedC _ isWeightFamily_one_weight)
  let e := restrictedMvPowerSeriesCompletionEquivAdicCompletion (k := k) hI hfg
  ext x
  rw [RingHom.mem_ker, ← quotientPowRestrictedEquiv_evalₐ_completionEquivAdicCompletion hI hfg hm,
    map_eq_zero_iff _ (quotientPowRestrictedEquivMvPolynomialQuotient hI hfg hm).injective]
  change e x ∈ RingHom.ker (AdicCompletion.evalₐ K m) ↔ _
  rw [AdicCompletion.ker_evalₐ_eq_map_pow (hfg.map _) m]
  have hmap : (K ^ m).map (algebraMap S (AdicCompletion K S)) =
      (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) ^ m).map e.toRingHom := by
    have halg : algebraMap S (AdicCompletion K S) =
        e.toRingHom.comp UniformSpace.Completion.coeRingHom :=
      RingHom.ext fun s ↦ (restrictedMvPowerSeriesCompletionEquivAdicCompletion_coe hI hfg s).symm
    have hcoe : UniformSpace.Completion.coeRingHom.comp (weightedC _ isWeightFamily_one_weight) =
        algebraMap A (restrictedMvPowerSeriesCompletion k A) :=
      RingHom.ext fun a ↦ by simp
    rw [halg, ← Ideal.map_map, Ideal.map_pow, Ideal.map_map, hcoe]
  rw [hmap]
  exact Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective
    |>.trans ⟨fun ⟨y, hy, hyx⟩ ↦ e.injective hyx ▸ hy, fun hx ↦ ⟨x, hx, rfl⟩⟩

/-- Completed reduction modulo a finitely generated ideal of definition has kernel `I · A⟨T⟩`. -/
theorem ker_restrictedCompletionReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedCompletionReduction (k := k) I
        (by simpa only [pow_one] using hI.isOpen_pow 1)) =
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) := by
  have h1 : ∀ (J : Ideal A) (_ : J = I) (hJ : IsOpen (J : Set A)) (hI' : IsOpen (I : Set A)),
      RingHom.ker (restrictedCompletionReduction (k := k) I hI') =
        RingHom.ker (restrictedCompletionReduction (k := k) J hJ) := by
    rintro _ rfl _ _; rfl
  rw [h1 (I ^ 1) (pow_one I) (hI.isOpen_pow 1),
    ker_restrictedCompletionReduction_pow (k := k) hI hfg one_ne_zero, pow_one]

/-- Infinitesimal thickening of order `m` (`m ≠ 0`) on the completed carrier: reducing modulo
`(I · A⟨T⟩) ^ m` gives `(A ⧸ I ^ m)[T]`, without requiring completeness or separatedness of `A`. -/
noncomputable def quotientPowRestrictedCompletionEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0) :
    (restrictedMvPowerSeriesCompletion k A ⧸
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) ^ m) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I ^ m) := by
  let hker := (ker_restrictedCompletionReduction_pow (k := k) hI hfg hm).symm
  let e := (Ideal.quotEquivOfEq hker).trans
    ((restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m)).quotientKerEquivOfSurjective
      (Ideal.restrictedCompletionReduction_surjective (I ^ m) (hI.isOpen_pow m)))
  refine AlgEquiv.ofRingEquiv (f := e) fun a ↦ ?_
  rw [← Ideal.Quotient.mk_algebraMap]
  simp [e]

/-- On an element of the completed carrier, the order-`m` quotient comparison computes completed
polynomial reduction modulo `I ^ m`. -/
@[simp]
theorem quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : m ≠ 0)
    (x : restrictedMvPowerSeriesCompletion k A) :
    quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg hm (Ideal.Quotient.mk _ x) =
      restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m) x := by
  simp [quotientPowRestrictedCompletionEquivMvPolynomialQuotient]

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

end TauCeti.Huber
