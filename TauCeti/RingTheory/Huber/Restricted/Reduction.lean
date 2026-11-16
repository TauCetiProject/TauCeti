/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Adic
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Kernel
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Huber.Restricted.Adic
import TauCeti.Topology.Algebra.Nonarchimedean.Quotient
import TauCeti.Topology.Algebra.Module.Quotient
import Mathlib.RingTheory.AdicCompletion.RingHom

/-!
# Polynomial reductions of adic restricted power series

Reduction of restricted power series modulo an open ideal is polynomial on both the restricted
subring and its separated completion `A⟨X₁, …, Xₖ⟩`. For a finitely generated ideal of definition
`I`, the kernel is `I · A⟨X⟩`, giving `A⟨X⟩ ⧸ (I · A⟨X⟩)ᵐ ≃ₐ[A] (A ⧸ Iᵐ)[X]` for every `m : ℕ`
without assuming `A` complete or Hausdorff, and agreeing with the subring quotient when the
restricted subring is complete and Hausdorff. Together with adic completeness of `A⟨X⟩`, these
compatible reductions identify `A⟨X⟩` as the inverse limit of `(A ⧸ Iⁿ⁺¹)[X₁, …, Xₖ]`
(`liftCompatibleRestrictedReductionCompletion`,
`existsUnique_ringHom_restrictedReductionCompletion_pow_succ_comp_eq`, and
`existsUnique_restrictedReductionCompletion_pow_succ_eq`, via
`IsAdicComplete.StrictMono.liftRingHom`).

Polynomial reduction commutes with continuous coefficient homomorphisms (`weightedMap` and
`weightedMapCompletion`, without flatness) and with topological evaluation (`weightedEvalHom`,
`weightedEvalHomCompletion`, and `weightedEvalHomCompletionOfIsLinearTopology`).

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.1–7.5.3.
* T. Wedhorn, *Adic Spaces*, §5.6, Proposition 5.50.
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

/-- Composing `restrictedReduction` with any map into a topological space is continuous. -/
theorem continuous_comp_restrictedReduction {X : Type*} [TopologicalSpace X]
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (g : MvPolynomial (Fin k) (A ⧸ J) → X) :
    Continuous (g ∘ restrictedReduction (k := k) J hJ) := by
  have : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  exact (continuous_of_discreteTopology (f := g ∘ (weightedPolynomialEquivOfDiscrete
    (fun _ : Fin k ↦ ({1} : Set (A ⧸ J))) isWeightFamily_one_weight).symm)).comp
    (continuous_weightedMap (QuotientRing.isOpenQuotientMap_mk J).continuous _ _ (by simp))

/-- Polynomial reduction reduces each coefficient modulo the given ideal. -/
@[simp]
theorem coeff_restrictedReduction (J : Ideal A) (hJ : IsOpen (J : Set A))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) (ν : Fin k →₀ ℕ) :
    (restrictedReduction J hJ f).coeff ν =
      Ideal.Quotient.mk J (MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)) := by
  have : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
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

/-- Polynomial reduction `A⟨X₁, …, Xₖ⟩ →+* (A ⧸ J)[X₁, …, Xₖ]` continuously extending
`Ideal.restrictedReduction` to the completed restricted-series algebra modulo an open ideal `J` of
`A`, defined without assuming `A` complete or Hausdorff. -/
noncomputable def restrictedReductionCompletion (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    restrictedMvPowerSeriesCompletion k A →+* MvPolynomial (Fin k) (A ⧸ J) := by
  letI : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  exact (weightedPolynomialEquivOfDiscrete (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
    isWeightFamily_one_weight).symm.toRingHom.comp
      ((restrictedMvPowerSeriesCompletionEquiv k (A ⧸ J)).toRingHom.comp
        (weightedMapCompletion (φ := Ideal.Quotient.mk J)
          (QuotientRing.isOpenQuotientMap_mk J).continuous _ _ (by simp)))

/-- Composing `restrictedReductionCompletion` with any map into a topological space is
continuous. -/
theorem continuous_comp_restrictedReductionCompletion {X : Type*} [TopologicalSpace X]
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (g : MvPolynomial (Fin k) (A ⧸ J) → X) :
    Continuous (g ∘ restrictedReductionCompletion (k := k) J hJ) := by
  have : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  exact (continuous_of_discreteTopology (f := g ∘ (weightedPolynomialEquivOfDiscrete
    (fun _ : Fin k ↦ ({1} : Set (A ⧸ J))) isWeightFamily_one_weight).symm)).comp
    ((uniformContinuous_restrictedMvPowerSeriesCompletionEquiv (k := k) (A := A ⧸ J)).continuous
      |>.comp (continuous_weightedMapCompletion (QuotientRing.isOpenQuotientMap_mk J).continuous
        _ _ (by simp)))

/-- On a restricted series, completed reduction agrees with `restrictedReduction`. -/
@[simp]
theorem restrictedReductionCompletion_coe (J : Ideal A) (hJ : IsOpen (J : Set A))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    J.restrictedReductionCompletion hJ (f : restrictedMvPowerSeriesCompletion k A) =
      J.restrictedReduction hJ f := by
  have : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  simp [restrictedReductionCompletion, restrictedReduction]

/-- Completed reduction sends a constant in `A` to the corresponding constant polynomial. -/
theorem restrictedReductionCompletion_algebraMap (J : Ideal A) (hJ : IsOpen (J : Set A)) (a : A) :
    J.restrictedReductionCompletion hJ (algebraMap A (restrictedMvPowerSeriesCompletion k A) a) =
      MvPolynomial.C (Ideal.Quotient.mk J a) := by
  rw [algebraMap_completion_weightedRestrictedSubring_apply, restrictedReductionCompletion_coe,
    restrictedReduction_weightedC]

/-- Completed polynomial reduction is surjective. -/
theorem restrictedReductionCompletion_surjective (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    Function.Surjective (J.restrictedReductionCompletion (k := k) hJ) := fun p ↦ by
  obtain ⟨f, rfl⟩ := J.restrictedReduction_surjective hJ p
  exact ⟨f, J.restrictedReductionCompletion_coe hJ f⟩

end Ideal

namespace TauCeti.Huber

open Ideal (restrictedReduction restrictedReduction_surjective
  restrictedReductionCompletion restrictedReductionCompletion_surjective)

/-- **Base-change functoriality of polynomial reduction.** Along a continuous ring homomorphism
`φ : A →+* B` carrying an open ideal `I` into an open ideal `J`, reducing the coefficientwise image
of a restricted series equals mapping its polynomial reduction along `A ⧸ I →+* B ⧸ J`. No
flatness or completeness hypothesis is needed. -/
theorem restrictedReduction_weightedMap {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ) {I : Ideal A}
    (hI : IsOpen (I : Set A)) (J : Ideal B) (hJ : IsOpen (J : Set B)) (hIJ : I ≤ J.comap φ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    J.restrictedReduction hJ
        (weightedMap hφ isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (I.restrictedReduction hI f) := by
  ext ν
  simp [MvPolynomial.coeff_map]

/-- **Polynomial reduction commutes with topological evaluation.** Let `φ : A →+* B` be continuous
at `0` into a complete Hausdorff nonarchimedean ring `B`, let `b : Fin k → B` be weight-bounded
(for instance arbitrary when `B` is linearly topologised), and let `I ⊆ A` and `J ⊆ B` be open
ideals with `φ(I) ⊆ J`. Reducing `weightedEvalHom` modulo `J` evaluates the polynomial reduction
of the series at the residue classes of `b`. -/
theorem mk_weightedEvalHom {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [NonarchimedeanRing B] [CompleteSpace B] [T3Space B] {φ : A →+* B} {b : Fin k → B}
    (hφ : ContinuousAt φ 0) (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b)
    {I : Ideal A} (hI : IsOpen (I : Set A)) (J : Ideal B) (hJ : IsOpen (J : Set B))
    (hIJ : I ≤ J.comap φ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    Ideal.Quotient.mk J (weightedEvalHom isWeightFamily_one_weight hφ hb f) =
      MvPolynomial.eval₂ (Ideal.quotientMap J φ hIJ) (fun i ↦ Ideal.Quotient.mk J (b i))
        (I.restrictedReduction hI f) := by
  have : DiscreteTopology (B ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  let ev := MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) fun i ↦ Ideal.Quotient.mk J (b i)
  exact congr($(weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    (f := (Ideal.Quotient.mk J).comp (weightedEvalHom isWeightFamily_one_weight hφ hb))
    (g := ev.comp (I.restrictedReduction hI))
    ((QuotientRing.isOpenQuotientMap_mk J).continuous.comp
      (continuous_weightedEvalHom isWeightFamily_one_weight hφ hb))
    (I.continuous_comp_restrictedReduction hI ev) (fun _ ↦ by simp [ev]) (fun _ ↦ by simp [ev])) f)

/-- **Base-change functoriality of completed polynomial reduction.** Along a continuous ring
homomorphism `φ : A →+* B` carrying an open ideal `I` into an open ideal `J`, completed reduction
commutes with `weightedMapCompletion`. -/
theorem restrictedReductionCompletion_weightedMapCompletion {B : Type*} [CommRing B]
    [TopologicalSpace B] [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ)
    {I : Ideal A} (hI : IsOpen (I : Set A)) (J : Ideal B) (hJ : IsOpen (J : Set B))
    (hIJ : I ≤ J.comap φ) (x : restrictedMvPowerSeriesCompletion k A) :
    J.restrictedReductionCompletion hJ
        (weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) x) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (I.restrictedReductionCompletion hI x) := by
  have : DiscreteTopology (B ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  let e := weightedPolynomialEquivOfDiscrete (fun _ : Fin k ↦ ({1} : Set (B ⧸ J)))
    isWeightFamily_one_weight
  exact e.injective <| congr($(completion_weightedRestrictedSubring_ringHom_ext_of_continuous
    isWeightFamily_one_weight
    (f := e.toRingHom.comp ((J.restrictedReductionCompletion hJ).comp
      (weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight (by simp))))
    (g := e.toRingHom.comp ((MvPolynomial.map (Ideal.quotientMap J φ hIJ)).comp
      (I.restrictedReductionCompletion hI)))
    ((J.continuous_comp_restrictedReductionCompletion hJ e.toRingHom).comp
      (continuous_weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight _))
    (I.continuous_comp_restrictedReductionCompletion hI
      (e.toRingHom.comp (MvPolynomial.map (Ideal.quotientMap J φ hIJ))))
    (fun _ ↦ by simp) (fun _ ↦ by simp)) x)

/-- Completed reduction is compatible with passing to a larger open ideal. -/
@[simp]
theorem map_restrictedReductionCompletion {J : Ideal A} (hJ : IsOpen (J : Set A))
    (hI : IsOpen (I : Set A)) (hJI : J ≤ I) (x : restrictedMvPowerSeriesCompletion k A) :
    MvPolynomial.map (Ideal.Quotient.factor hJI) (J.restrictedReductionCompletion hJ x) =
      I.restrictedReductionCompletion hI x := by
  have hfac : Ideal.quotientMap I (RingHom.id A) hJI = Ideal.Quotient.factor hJI :=
    Ideal.Quotient.ringHom_ext rfl
  simpa [hfac] using
    (restrictedReductionCompletion_weightedMapCompletion (φ := RingHom.id A) continuous_id
      hJ I hI hJI x).symm

/-- **Completed polynomial reduction commutes with completed topological evaluation.** In
particular, when `B` is a complete Hausdorff linearly topologised ring, this holds for arbitrary
variable images `b : Fin k → B` (`mk_weightedEvalHomCompletionOfIsLinearTopology`). -/
theorem mk_weightedEvalHomCompletion {B : Type*} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T3Space B]
    {φ : A →+* B} {b : Fin k → B} (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b)
    {I : Ideal A} (hI : IsOpen (I : Set A)) (J : Ideal B) (hJ : IsOpen (J : Set B))
    (hIJ : I ≤ J.comap φ) (x : restrictedMvPowerSeriesCompletion k A) :
    Ideal.Quotient.mk J (weightedEvalHomCompletion isWeightFamily_one_weight hφ hb x) =
      MvPolynomial.eval₂ (Ideal.quotientMap J φ hIJ) (fun i ↦ Ideal.Quotient.mk J (b i))
        (I.restrictedReductionCompletion hI x) := by
  have : DiscreteTopology (B ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  let ev := MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) fun i ↦ Ideal.Quotient.mk J (b i)
  exact congr($(completion_weightedRestrictedSubring_ringHom_ext_of_continuous
    isWeightFamily_one_weight
    (f := (Ideal.Quotient.mk J).comp (weightedEvalHomCompletion isWeightFamily_one_weight hφ hb))
    (g := ev.comp (I.restrictedReductionCompletion hI))
    ((QuotientRing.isOpenQuotientMap_mk J).continuous.comp
      (continuous_weightedEvalHomCompletion isWeightFamily_one_weight hφ hb))
    (I.continuous_comp_restrictedReductionCompletion hI ev)
    (fun _ ↦ by simp [ev]) (fun _ ↦ by simp [ev])) x)

/-- Completed polynomial reduction commutes with `weightedEvalHomCompletionOfIsLinearTopology` into
a complete Hausdorff linearly topologised ring at arbitrary variable images `b : Fin k → B`. -/
theorem mk_weightedEvalHomCompletionOfIsLinearTopology {B : Type*} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [IsLinearTopology B B] [CompleteSpace B] [T2Space B]
    {φ : A →+* B} (hφ : Continuous φ) (b : Fin k → B)
    {I : Ideal A} (hI : IsOpen (I : Set A)) (J : Ideal B) (hJ : IsOpen (J : Set B))
    (hIJ : I ≤ J.comap φ) (x : restrictedMvPowerSeriesCompletion k A) :
    Ideal.Quotient.mk J (weightedEvalHomCompletionOfIsLinearTopology hφ b x) =
      MvPolynomial.eval₂ (Ideal.quotientMap J φ hIJ) (fun i ↦ Ideal.Quotient.mk J (b i))
        (I.restrictedReductionCompletion hI x) := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  rw [weightedEvalHomCompletionOfIsLinearTopology_eq_weightedEvalHomCompletion]
  exact mk_weightedEvalHomCompletion hφ.continuousAt
    (isWeightBounded_of_isLinearTopology φ _ b) hI J hJ hIJ x

/-- Reduction modulo a finitely generated ideal of definition has exactly the extended ideal
as its kernel. -/
theorem ker_restrictedReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedReduction (k := k) I hI.isOpen) =
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
    ((restrictedReduction I hI.isOpen).quotientKerEquivOfSurjective
      (restrictedReduction_surjective I hI.isOpen))
  refine AlgEquiv.ofRingEquiv (f := e) fun a ↦ ?_
  have he : e (algebraMap A _ a) =
      restrictedReduction I hI.isOpen (algebraMap A _ a) := by
    rw [← Ideal.Quotient.mk_algebraMap]
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [he]
  simp

/-- On a represented series the quotient comparison computes its polynomial reduction. -/
@[simp]
theorem quotientRestrictedEquivMvPolynomialQuotient_mk (hI : IsAdic I) (hfg : I.FG)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    quotientRestrictedEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ f) =
      restrictedReduction I hI.isOpen f := by
  simp [quotientRestrictedEquivMvPolynomialQuotient]

section SubringQuotient

variable (hI : IsAdic I) (hfg : I.FG)

/-- The inverse of `quotientRestrictedEquivMvPolynomialQuotient` maps a polynomial reduction back
to its quotient class. -/
@[simp]
theorem quotientRestrictedEquivMvPolynomialQuotient_symm_restrictedReduction
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    (quotientRestrictedEquivMvPolynomialQuotient hI hfg).symm (restrictedReduction I hI.isOpen f) =
      Ideal.Quotient.mk _ f := by
  rw [← quotientRestrictedEquivMvPolynomialQuotient_mk hI hfg, AlgEquiv.symm_apply_apply]

/-- The inverse of `quotientRestrictedEquivMvPolynomialQuotient` sends `Xᵢ` to the class of
`weightedX i`. -/
@[simp]
theorem quotientRestrictedEquivMvPolynomialQuotient_symm_X (i : Fin k) :
    (quotientRestrictedEquivMvPolynomialQuotient hI hfg).symm (MvPolynomial.X i) =
      Ideal.Quotient.mk _ (weightedX _ isWeightFamily_one_weight i) := by
  rw [← Ideal.restrictedReduction_weightedX I hI.isOpen i,
    quotientRestrictedEquivMvPolynomialQuotient_symm_restrictedReduction]

/-- The inverse of `quotientRestrictedEquivMvPolynomialQuotient` sends `C (a mod I)` to
`algebraMap A _ a`. -/
@[simp]
theorem quotientRestrictedEquivMvPolynomialQuotient_symm_C_mk (a : A) :
    (quotientRestrictedEquivMvPolynomialQuotient (k := k) hI hfg).symm
        (MvPolynomial.C (Ideal.Quotient.mk I a)) =
      algebraMap A _ a := by
  simpa [MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq] using
    (quotientRestrictedEquivMvPolynomialQuotient (k := k) hI hfg).symm.commutes a

section Pow

variable (m : ℕ)

/-- For every exponent `m : ℕ`, the quotient of the restricted-series subring by the `m`-th power
of the extended ideal is the polynomial algebra `(A ⧸ Iᵐ)[X₁, …, Xₖ]`. -/
noncomputable def quotientRestrictedPowEquivMvPolynomialQuotient :
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
      (I.map (weightedC _ isWeightFamily_one_weight)) ^ m) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I ^ m) :=
  if hm : 0 < m then
    (Ideal.quotientEquivAlgOfEq A
      (Ideal.map_pow (weightedC _ isWeightFamily_one_weight) I m).symm).trans
        (quotientRestrictedEquivMvPolynomialQuotient (is_ideal_adic_pow hI hm) hfg.pow)
  else by
    obtain rfl := Nat.eq_zero_of_not_pos hm
    have : Subsingleton (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight ⧸ (I.map (weightedC _ isWeightFamily_one_weight)) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    have : Subsingleton (A ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact default

/-- On a represented series, `quotientRestrictedPowEquivMvPolynomialQuotient` reduces coefficients
modulo `Iᵐ`. -/
@[simp]
theorem quotientRestrictedPowEquivMvPolynomialQuotient_mk
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    quotientRestrictedPowEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ f) =
      (I ^ m).restrictedReduction (hI.isOpen_pow m) f := by
  rcases m.eq_zero_or_pos with rfl | hm
  · have : Subsingleton (A ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact Subsingleton.elim _ _
  · simp [quotientRestrictedPowEquivMvPolynomialQuotient, hm]

/-- The inverse of `quotientRestrictedPowEquivMvPolynomialQuotient` maps a polynomial reduction
modulo `Iᵐ` back to its quotient class. -/
@[simp]
theorem quotientRestrictedPowEquivMvPolynomialQuotient_symm_restrictedReduction
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    (quotientRestrictedPowEquivMvPolynomialQuotient hI hfg m).symm
        ((I ^ m).restrictedReduction (hI.isOpen_pow m) f) =
      Ideal.Quotient.mk _ f := by
  rw [← quotientRestrictedPowEquivMvPolynomialQuotient_mk hI hfg m, AlgEquiv.symm_apply_apply]

/-- The inverse of `quotientRestrictedPowEquivMvPolynomialQuotient` sends `Xᵢ` to the class of
`weightedX i`. -/
@[simp]
theorem quotientRestrictedPowEquivMvPolynomialQuotient_symm_X (i : Fin k) :
    (quotientRestrictedPowEquivMvPolynomialQuotient hI hfg m).symm (MvPolynomial.X i) =
      Ideal.Quotient.mk _ (weightedX _ isWeightFamily_one_weight i) := by
  rw [← Ideal.restrictedReduction_weightedX (I ^ m) (hI.isOpen_pow m) i,
    quotientRestrictedPowEquivMvPolynomialQuotient_symm_restrictedReduction]

/-- The inverse of `quotientRestrictedPowEquivMvPolynomialQuotient` sends `C (a mod Iᵐ)` to
`algebraMap A _ a`. -/
@[simp]
theorem quotientRestrictedPowEquivMvPolynomialQuotient_symm_C_mk (a : A) :
    (quotientRestrictedPowEquivMvPolynomialQuotient (k := k) hI hfg m).symm
        (MvPolynomial.C (Ideal.Quotient.mk (I ^ m) a)) =
      algebraMap A _ a := by
  simpa [MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq] using
    (quotientRestrictedPowEquivMvPolynomialQuotient (k := k) hI hfg m).symm.commutes a

end Pow

end SubringQuotient

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

section CompletionQuotient

variable (hI : IsAdic I) (hfg : I.FG)

include hfg in
/-- On the completed restricted-series algebra, reduction modulo a finitely generated ideal of
definition has kernel equal to the extended ideal `I · A⟨X₁, …, Xₖ⟩`, without assuming `A`
complete or Hausdorff. -/
theorem ker_restrictedReductionCompletion :
    RingHom.ker (I.restrictedReductionCompletion (k := k) hI.isOpen) =
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) := by
  set S₀ := weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
  set S := restrictedMvPowerSeriesCompletion k A
  set M := I.map (algebraMap A S)
  have hMle : M ≤ RingHom.ker (I.restrictedReductionCompletion (k := k) hI.isOpen) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.restrictedReductionCompletion_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  refine le_antisymm (fun x hx ↦ ?_) hMle
  -- `M` is open in the completion, so `x` can be approximated modulo `M` by an element of `S₀`.
  have hMopen : IsOpen (M : Set S) :=
    (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg).isOpen
  obtain ⟨f, hfx⟩ := (Completion.denseRange_coe (α := S₀)).exists_mem_open
    (hMopen.preimage (continuous_sub_right x)) ⟨x, by simp [M.zero_mem]⟩
  have hfx' : (f : S) - x ∈ M := hfx
  have hfker : f ∈ RingHom.ker (I.restrictedReduction (k := k) hI.isOpen) := by
    simpa [RingHom.mem_ker, S, S₀, Ideal.restrictedReductionCompletion_coe] using
      add_mem (hMle hfx') hx
  rw [ker_restrictedReduction hI hfg] at hfker
  have hmap : (I.map (weightedC _ isWeightFamily_one_weight)).map
      (Completion.coeRingHom : S₀ →+* S) = M := by
    rw [Ideal.map_map]
    exact congrArg (Ideal.map · I)
      (RingHom.ext fun a ↦ (algebraMap_completion_weightedRestrictedSubring_apply ..).symm)
  have hfM : (f : S) ∈ M := hmap ▸ Ideal.mem_map_of_mem (Completion.coeRingHom : S₀ →+* S) hfker
  simpa using sub_mem hfM hfx'

/-- The reduction modulo a finitely generated ideal of definition of the completed
restricted-series algebra is the polynomial algebra over the quotient of the coefficients. -/
noncomputable def quotientRestrictedCompletionEquivMvPolynomialQuotient :
    (restrictedMvPowerSeriesCompletion k A ⧸
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I) := by
  let e := (Ideal.quotEquivOfEq (ker_restrictedReductionCompletion (k := k) hI hfg).symm).trans
    ((I.restrictedReductionCompletion hI.isOpen).quotientKerEquivOfSurjective
      (I.restrictedReductionCompletion_surjective hI.isOpen))
  refine AlgEquiv.ofRingEquiv (f := e) fun a ↦ ?_
  rw [← Ideal.Quotient.mk_algebraMap]
  simp [e]

/-- On an arbitrary completion element, the quotient comparison computes its completed polynomial
reduction. -/
@[simp]
theorem quotientRestrictedCompletionEquivMvPolynomialQuotient_mk
    (x : restrictedMvPowerSeriesCompletion k A) :
    quotientRestrictedCompletionEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ x) =
      I.restrictedReductionCompletion hI.isOpen x := by
  simp [quotientRestrictedCompletionEquivMvPolynomialQuotient]

/-- The inverse of `quotientRestrictedCompletionEquivMvPolynomialQuotient` maps a completed
polynomial reduction back to its quotient class. -/
@[simp]
theorem quotientRestrictedCompletionEquivMvPolynomialQuotient_symm_restrictedReductionCompletion
    (x : restrictedMvPowerSeriesCompletion k A) :
    (quotientRestrictedCompletionEquivMvPolynomialQuotient hI hfg).symm
        (I.restrictedReductionCompletion hI.isOpen x) =
      Ideal.Quotient.mk _ x := by
  rw [← quotientRestrictedCompletionEquivMvPolynomialQuotient_mk hI hfg, AlgEquiv.symm_apply_apply]

/-- The inverse of `quotientRestrictedCompletionEquivMvPolynomialQuotient` sends `Xᵢ` to the class
of the canonical image of `weightedX i`. -/
@[simp]
theorem quotientRestrictedCompletionEquivMvPolynomialQuotient_symm_X (i : Fin k) :
    (quotientRestrictedCompletionEquivMvPolynomialQuotient hI hfg).symm (MvPolynomial.X i) =
      Ideal.Quotient.mk _ (Completion.coe' (weightedX _ isWeightFamily_one_weight i)) := by
  rw [← Ideal.restrictedReduction_weightedX I hI.isOpen i,
    ← Ideal.restrictedReductionCompletion_coe,
    quotientRestrictedCompletionEquivMvPolynomialQuotient_symm_restrictedReductionCompletion]

/-- The inverse of `quotientRestrictedCompletionEquivMvPolynomialQuotient` sends `C (a mod I)` to
`algebraMap A _ a`. -/
@[simp]
theorem quotientRestrictedCompletionEquivMvPolynomialQuotient_symm_C_mk (a : A) :
    (quotientRestrictedCompletionEquivMvPolynomialQuotient (k := k) hI hfg).symm
        (MvPolynomial.C (Ideal.Quotient.mk I a)) =
      algebraMap A _ a := by
  simpa [MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq] using
    (quotientRestrictedCompletionEquivMvPolynomialQuotient (k := k) hI hfg).symm.commutes a

section Pow

variable (m : ℕ)

/-- For every exponent `m : ℕ`, the quotient of `A⟨X₁, …, Xₖ⟩` by `(I · A⟨X⟩)ᵐ` is the polynomial
algebra `(A ⧸ Iᵐ)[X₁, …, Xₖ]`. -/
noncomputable def quotientRestrictedCompletionPowEquivMvPolynomialQuotient :
    (restrictedMvPowerSeriesCompletion k A ⧸
      (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))) ^ m) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I ^ m) :=
  if hm : 0 < m then
    (Ideal.quotientEquivAlgOfEq A
      (Ideal.map_pow (algebraMap A (restrictedMvPowerSeriesCompletion k A)) I m).symm).trans
        (quotientRestrictedCompletionEquivMvPolynomialQuotient (is_ideal_adic_pow hI hm) hfg.pow)
  else by
    obtain rfl := Nat.eq_zero_of_not_pos hm
    have : Subsingleton (_ ⧸ (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    have : Subsingleton (A ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact default

/-- On a completion element, `quotientRestrictedCompletionPowEquivMvPolynomialQuotient` computes
completed reduction modulo `Iᵐ`. -/
@[simp]
theorem quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk
    (x : restrictedMvPowerSeriesCompletion k A) :
    quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ x) =
      (I ^ m).restrictedReductionCompletion (hI.isOpen_pow m) x := by
  rcases m.eq_zero_or_pos with rfl | hm
  · have : Subsingleton (A ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact Subsingleton.elim _ _
  · simp [quotientRestrictedCompletionPowEquivMvPolynomialQuotient, hm]

/-- The inverse of `quotientRestrictedCompletionPowEquivMvPolynomialQuotient` maps a completed
polynomial reduction modulo `Iᵐ` back to its quotient class. -/
@[simp]
theorem quotientRestrictedCompletionPowEquivMvPolynomialQuotient_symm_restrictedReductionCompletion
    (x : restrictedMvPowerSeriesCompletion k A) :
    (quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg m).symm
        ((I ^ m).restrictedReductionCompletion (hI.isOpen_pow m) x) =
      Ideal.Quotient.mk _ x := by
  rw [← quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk hI hfg m,
    AlgEquiv.symm_apply_apply]

/-- The inverse of `quotientRestrictedCompletionPowEquivMvPolynomialQuotient` sends `Xᵢ` to the
class of the canonical image of `weightedX i`. -/
@[simp]
theorem quotientRestrictedCompletionPowEquivMvPolynomialQuotient_symm_X (i : Fin k) :
    (quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg m).symm (MvPolynomial.X i) =
      Ideal.Quotient.mk _ (Completion.coe' (weightedX _ isWeightFamily_one_weight i)) := by
  rw [← Ideal.restrictedReduction_weightedX (I ^ m) (hI.isOpen_pow m) i,
    ← Ideal.restrictedReductionCompletion_coe,
    quotientRestrictedCompletionPowEquivMvPolynomialQuotient_symm_restrictedReductionCompletion]

/-- The inverse of `quotientRestrictedCompletionPowEquivMvPolynomialQuotient` sends `C (a mod Iᵐ)`
to `algebraMap A _ a`. -/
@[simp]
theorem quotientRestrictedCompletionPowEquivMvPolynomialQuotient_symm_C_mk (a : A) :
    (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg m).symm
        (MvPolynomial.C (Ideal.Quotient.mk (I ^ m) a)) =
      algebraMap A _ a := by
  simpa [MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq] using
    (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg m).symm.commutes a

end Pow

end CompletionQuotient

section InverseLimit

/-! ### Inverse-limit description of `A⟨X₁, …, Xₖ⟩`

Because `I · A⟨X₁, …, Xₖ⟩` defines the complete Hausdorff topology of `A⟨X₁, …, Xₖ⟩`
(`isAdicComplete_map_algebraMap_restrictedMvPowerSeriesCompletion`), the algebra is complete and
separated for the powers `(I · A⟨X⟩)ⁿ⁺¹`, whose quotients are the polynomial rings
`(A ⧸ Iⁿ⁺¹)[X₁, …, Xₖ]`. Compatible families of ring homomorphisms (or elements) into those
polynomial rings therefore lift uniquely to `A⟨X₁, …, Xₖ⟩`. -/

variable (hI : IsAdic I) (hfg : I.FG)

include hfg in
/-- Ring homomorphisms into `A⟨X₁, …, Xₖ⟩` are determined by their polynomial reductions modulo
`Iⁿ⁺¹` for all `n : ℕ`. -/
theorem restrictedReductionCompletion_pow_succ_ext
    {D : Type*} [NonAssocSemiring D] {f g : D →+* restrictedMvPowerSeriesCompletion k A}
    (h : ∀ n : ℕ, ((I ^ (n + 1)).restrictedReductionCompletion (hI.isOpen_pow (n + 1))).comp f =
      ((I ^ (n + 1)).restrictedReductionCompletion (hI.isOpen_pow (n + 1))).comp g) :
    f = g := by
  have := isAdicComplete_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg
  apply DFunLike.coe_injective
  refine IsHausdorff.StrictMono.funext'
      (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
      (fun _ _ h ↦ Nat.add_lt_add_right h 1) fun n d ↦ ?_
  apply (quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg (n + 1)).injective
  simpa only [quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk, RingHom.comp_apply]
    using congr($(h n) d)

section RingHomLift

variable {D : Type*} [NonAssocSemiring D]
  (φ : ∀ n : ℕ, D →+* MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))
  (hφ : ∀ n : ℕ, (MvPolynomial.map (Ideal.Quotient.factorPowSucc I (n + 1))).comp
    (φ (n + 1)) = φ n)

include hφ in
private theorem factorPow_comp_quotientRestrictedCompletionPowEquiv_symm {n : ℕ} :
    (Ideal.Quotient.factorPow (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
        (Nat.le_succ (n + 1))).comp
      ((quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg
        (n + 1 + 1)).symm.toRingHom.comp (φ (n + 1))) =
      (quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg
        (n + 1)).symm.toRingHom.comp (φ n) := by
  let e (m : ℕ) := quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg (m + 1)
  refine RingHom.ext fun d ↦ (e n).injective ?_
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective ((e (n + 1)).symm (φ (n + 1) d))
  have hx' : φ (n + 1) d = (I ^ (n + 1 + 1)).restrictedReductionCompletion
      (hI.isOpen_pow (n + 1 + 1)) x := by simpa [e] using congrArg (e (n + 1)) hx.symm
  calc (e n) ((Ideal.Quotient.factorPow
        (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
        (Nat.le_succ (n + 1))) ((e (n + 1)).symm (φ (n + 1) d)))
    _ = (I ^ (n + 1)).restrictedReductionCompletion (hI.isOpen_pow (n + 1)) x := by
        rw [← hx]; simp [e, Ideal.Quotient.factorPow]
    _ = MvPolynomial.map (Ideal.Quotient.factorPowSucc I (n + 1))
          ((I ^ (n + 1 + 1)).restrictedReductionCompletion (hI.isOpen_pow (n + 1 + 1)) x) :=
        (map_restrictedReductionCompletion (hI.isOpen_pow (n + 1 + 1))
          (hI.isOpen_pow (n + 1)) (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) x).symm
    _ = φ n d := by rw [← hx']; exact congr($(hφ n) d)
    _ = (e n) ((e n).symm (φ n d)) := ((e n).apply_symm_apply _).symm

/-- **Inverse-limit lift into `A⟨X₁, …, Xₖ⟩`.** A compatible family of ring homomorphisms
`φₙ : D →+* (A ⧸ Iⁿ⁺¹)[X₁, …, Xₖ]` lifts to a ring homomorphism `D →+* A⟨X₁, …, Xₖ⟩`. -/
noncomputable def liftCompatibleRestrictedReductionCompletion :
    D →+* restrictedMvPowerSeriesCompletion k A :=
  letI := isAdicComplete_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg
  IsAdicComplete.StrictMono.liftRingHom
    (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
    (fun _ _ h ↦ Nat.add_lt_add_right h 1)
    (fun n ↦ (quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg
      (n + 1)).symm.toRingHom.comp (φ n))
    (factorPow_comp_quotientRestrictedCompletionPowEquiv_symm hI hfg φ hφ)

/-- Reducing `liftCompatibleRestrictedReductionCompletion` modulo `Iⁿ⁺¹` recovers `φ n`. -/
@[simp]
theorem restrictedReductionCompletion_comp_liftCompatibleRestrictedReductionCompletion (n : ℕ) :
    ((I ^ (n + 1)).restrictedReductionCompletion (hI.isOpen_pow (n + 1))).comp
        (liftCompatibleRestrictedReductionCompletion hI hfg φ hφ) = φ n := by
  have := isAdicComplete_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg
  let e := quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg (n + 1)
  refine RingHom.ext fun d ↦ ?_
  have hmk := IsAdicComplete.StrictMono.mk_liftRingHom (n := n)
    (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
    (fun _ _ h ↦ Nat.add_lt_add_right h 1)
    (fun m ↦ (quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg
      (m + 1)).symm.toRingHom.comp (φ m))
    (factorPow_comp_quotientRestrictedCompletionPowEquiv_symm hI hfg φ hφ) d
  rw [RingHom.comp_apply, ← quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk hI hfg]
  exact (congrArg e hmk).trans (e.apply_symm_apply (φ n d))

/-- Elementwise form of
`restrictedReductionCompletion_comp_liftCompatibleRestrictedReductionCompletion`. -/
@[simp]
theorem restrictedReductionCompletion_liftCompatibleRestrictedReductionCompletion (n : ℕ) (d : D) :
    (I ^ (n + 1)).restrictedReductionCompletion (hI.isOpen_pow (n + 1))
        (liftCompatibleRestrictedReductionCompletion hI hfg φ hφ d) = φ n d :=
  congr($(restrictedReductionCompletion_comp_liftCompatibleRestrictedReductionCompletion
    hI hfg φ hφ n) d)

include hfg hφ in
/-- **Universal property of `A⟨X₁, …, Xₖ⟩` as the inverse limit of `(A ⧸ Iⁿ⁺¹)[X₁, …, Xₖ]`.** -/
theorem existsUnique_ringHom_restrictedReductionCompletion_pow_succ_comp_eq :
    ∃! ψ : D →+* restrictedMvPowerSeriesCompletion k A, ∀ n : ℕ,
      ((I ^ (n + 1)).restrictedReductionCompletion (hI.isOpen_pow (n + 1))).comp ψ = φ n :=
  ⟨liftCompatibleRestrictedReductionCompletion hI hfg φ hφ,
    restrictedReductionCompletion_comp_liftCompatibleRestrictedReductionCompletion hI hfg φ hφ,
    fun _ hψ ↦ restrictedReductionCompletion_pow_succ_ext hI hfg fun n ↦
      (hψ n).trans (restrictedReductionCompletion_comp_liftCompatibleRestrictedReductionCompletion
        hI hfg φ hφ n).symm⟩

end RingHomLift

include hfg in
/-- **Elementwise inverse-limit description of `A⟨X₁, …, Xₖ⟩`.** Every compatible sequence of
polynomials `pₙ ∈ (A ⧸ Iⁿ⁺¹)[X₁, …, Xₖ]` is the sequence of reductions of a unique element of
`A⟨X₁, …, Xₖ⟩`. -/
theorem existsUnique_restrictedReductionCompletion_pow_succ_eq
    (p : ∀ n : ℕ, MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)))
    (hp : ∀ n : ℕ,
      MvPolynomial.map (Ideal.Quotient.factorPowSucc I (n + 1)) (p (n + 1)) = p n) :
    ∃! x : restrictedMvPowerSeriesCompletion k A, ∀ n : ℕ,
      (I ^ (n + 1)).restrictedReductionCompletion (hI.isOpen_pow (n + 1)) x = p n := by
  let φ (n : ℕ) : Polynomial ℤ →+* MvPolynomial (Fin k) (A ⧸ I ^ (n + 1)) :=
    Polynomial.eval₂RingHom (Int.castRingHom _) (p n)
  have hφ (n : ℕ) : (MvPolynomial.map (Ideal.Quotient.factorPowSucc I (n + 1))).comp
      (φ (n + 1)) = φ n :=
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simpa [φ] using hp n)
  refine ⟨liftCompatibleRestrictedReductionCompletion hI hfg φ hφ Polynomial.X,
    fun n ↦ by simp [φ], fun y hy ↦ ?_⟩
  have huniq := restrictedReductionCompletion_pow_succ_ext hI hfg
    (f := Polynomial.eval₂RingHom (Int.castRingHom _) y)
    (g := liftCompatibleRestrictedReductionCompletion hI hfg φ hφ) fun n ↦
      Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp [φ, hy n])
  simpa using congr($huniq Polynomial.X)

end InverseLimit

section CompleteBase

variable [CompleteSpace (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
    isWeightFamily_one_weight)]
  [T0Space (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)]

/-- When the restricted-series subring is complete and Hausdorff, applying `restrictedReduction`
after `restrictedMvPowerSeriesCompletionEquiv` computes `restrictedReductionCompletion`. -/
@[simp]
theorem _root_.Ideal.restrictedReduction_restrictedMvPowerSeriesCompletionEquiv (J : Ideal A)
    (hJ : IsOpen (J : Set A)) (x : restrictedMvPowerSeriesCompletion k A) :
    J.restrictedReduction hJ (restrictedMvPowerSeriesCompletionEquiv k A x) =
      J.restrictedReductionCompletion hJ x := by
  conv_rhs => rw [← (restrictedMvPowerSeriesCompletionEquiv k A).symm_apply_apply x]
  rw [restrictedMvPowerSeriesCompletionEquiv_symm_apply, Ideal.restrictedReductionCompletion_coe]

/-- When the restricted-series subring is complete and Hausdorff,
`quotientRestrictedCompletionEquivMvPolynomialQuotient` agrees with transporting
`quotientRestrictedEquivMvPolynomialQuotient` along `restrictedMvPowerSeriesCompletionAlgEquiv`. -/
theorem quotientRestrictedCompletionEquivMvPolynomialQuotient_eq_trans {J : Ideal A}
    (hJ : IsAdic J) (hfg : J.FG) :
    quotientRestrictedCompletionEquivMvPolynomialQuotient (k := k) hJ hfg =
      (Ideal.quotientEquivAlg _ _ (restrictedMvPowerSeriesCompletionAlgEquiv k A) (by
        rw [Ideal.map_map, ← algebraMap_weightedRestrictedSubring]
        exact congrArg (Ideal.map · J)
          (restrictedMvPowerSeriesCompletionAlgEquiv k A).toAlgHom.comp_algebraMap.symm)).trans
        (quotientRestrictedEquivMvPolynomialQuotient hJ hfg) := by
  ext x; obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x; simp

/-- When the restricted-series subring is complete and Hausdorff,
`quotientRestrictedCompletionPowEquivMvPolynomialQuotient` agrees for every `m : ℕ` with
transporting `quotientRestrictedPowEquivMvPolynomialQuotient` along
`restrictedMvPowerSeriesCompletionAlgEquiv`. -/
theorem quotientRestrictedCompletionPowEquivMvPolynomialQuotient_eq_trans {J : Ideal A}
    (hJ : IsAdic J) (hfg : J.FG) (m : ℕ) :
    quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hJ hfg m =
      (Ideal.quotientEquivAlg _ _ (restrictedMvPowerSeriesCompletionAlgEquiv k A) (by
        rw [← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map, ← algebraMap_weightedRestrictedSubring]
        exact congrArg (Ideal.map · (J ^ m))
          (restrictedMvPowerSeriesCompletionAlgEquiv k A).toAlgHom.comp_algebraMap.symm)).trans
        (quotientRestrictedPowEquivMvPolynomialQuotient hJ hfg m) := by
  ext x; obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x; simp

end CompleteBase

end TauCeti.Huber
