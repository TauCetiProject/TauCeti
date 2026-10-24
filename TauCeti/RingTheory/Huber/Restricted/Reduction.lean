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
import TauCeti.Topology.Algebra.Nonarchimedean.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Polynomial reductions of adic restricted power series

For a finitely generated ideal of definition `I`, reduction modulo `Iⁿ` identifies restricted
power series with polynomials over `A/Iⁿ`. The kernel is the extended ideal `Iⁿ`, rather than
merely the set of series whose coefficients lie in `Iⁿ`: the coefficient decomposition for
adic restricted series supplies this equality. These comparisons describe the infinitesimal
thickenings of affine formal space.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.5.1.
-/

public section

open Topology

namespace TauCeti.Huber

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

/-- Reduction of restricted series modulo an open ideal is polynomial, since only finitely
many coefficients survive. -/
noncomputable def restrictedReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight →+*
      MvPolynomial (Fin k) (A ⧸ J) := by
  letI : DiscreteTopology (A ⧸ J) := QuotientAddGroup.discreteTopology hJ
  exact (weightedPolynomialEquiv (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
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
  let : DiscreteTopology (A ⧸ J) := QuotientAddGroup.discreteTopology hJ
  dsimp only [restrictedReduction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  -- `QuotientAddGroup.discreteTopology hJ` has type `DiscreteTopology (A ⧸ J.toAddSubgroup)`,
  -- while `weightedPolynomialEquiv` expects `DiscreteTopology (A ⧸ J)`. The additive and ring
  -- quotient presentations agree only after unfolding, so `rw` cannot match the instance.
  erw [coeff_weightedPolynomialEquiv_symm]
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

section Completion

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
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

end TauCeti.Huber
