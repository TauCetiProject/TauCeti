/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import TauCeti.RingTheory.Huber.Adic
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Kernel
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Huber.Restricted.Adic
import TauCeti.Topology.Algebra.Module.Quotient
import TauCeti.Topology.Algebra.Nonarchimedean.Quotient
import TauCeti.Topology.UniformSpace.DiscreteUniformity

/-!
# Polynomial reductions of adic restricted power series

Reduction of restricted power series modulo an open ideal is polynomial, both on the uncompleted
subring (`Ideal.restrictedReduction`) and on its separated completion
(`Ideal.restrictedCompletionReduction`), with no completeness or separation assumption on the
coefficient ring in either case.

For a finitely generated ideal of definition `I`, the kernel of reduction modulo `I ^ m` is the
power `(I · A⟨T⟩) ^ m` of the extended ideal, yielding `A`-algebra isomorphisms
`A⟨T⟩ ⧸ (I · A⟨T⟩) ^ m ≃ₐ[A] (A ⧸ I ^ m)[T]` on both carriers. Reduction is functorial in the
coefficient ring without any flatness assumption, commutes with topological evaluation, and gives
the inverse-limit description of restricted power series from compatible families of polynomials
modulo `I ^ (m + 1)`:

* on `weightedRestrictedSubring`, assuming `IsAdic I` and `[IsAdicComplete I A]` (with no finite
  generation assumption on `I`);
* on `restrictedMvPowerSeriesCompletion k A`, assuming `IsAdic I` and `I.FG` (with no completeness
  or Hausdorffness assumption on `A`).

This module also packages the `A`-algebra universal property of restricted power series into
complete Hausdorff linearly topologised `A`-algebras (`weightedEvalLinearAlgHom` and
`weightedEvalCompletionLinearAlgHom`), where open-ideal neighbourhoods make every element
power-bounded so no boundedness hypothesis on the substituted tuple is needed.

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

/-- A restricted series lies in the kernel of reduction modulo an open ideal `J` if and only if
all of its coefficients lie in `J`. -/
theorem mem_ker_restrictedReduction (J : Ideal A) (hJ : IsOpen (J : Set A))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    f ∈ RingHom.ker (restrictedReduction J hJ) ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ J := by
  rw [RingHom.mem_ker, MvPolynomial.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

/-- Any function out of `MvPolynomial (Fin k) (A ⧸ J)` becomes continuous after precomposing with
`restrictedReduction J hJ`, since `restrictedReduction J hJ` factors through the discrete
restricted-series ring over `A ⧸ J`. -/
theorem continuous_comp_restrictedReduction {X : Type*} [TopologicalSpace X]
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (g : MvPolynomial (Fin k) (A ⧸ J) → X) :
    Continuous (g ∘ restrictedReduction (k := k) J hJ) := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  exact (continuous_of_discreteTopology (f := fun y ↦
    g ((weightedPolynomialEquivOfDiscrete (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight).symm y))).comp
    (continuous_weightedMap (QuotientRing.isOpenQuotientMap_mk J).continuous
      isWeightFamily_one_weight isWeightFamily_one_weight (by simp))

/-- The kernel of polynomial reduction modulo an open ideal is open: it coincides as a set with the
open neighbourhood subgroup `J⟨X⟩`. -/
theorem isOpen_ker_restrictedReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    IsOpen (RingHom.ker (restrictedReduction (k := k) J hJ) : Set
      (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight)) := by
  refine AddSubgroup.isOpen_mono
    (H₁ := weightedNhd (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight J.toAddSubgroup)
    (H₂ := (RingHom.ker (restrictedReduction (k := k) J hJ)).toAddSubgroup)
    (fun f hf ↦ ?_) (isOpen_weightedNhd isWeightFamily_one_weight hJ)
  rw [Submodule.mem_toAddSubgroup, mem_ker_restrictedReduction]
  simpa only [mem_weightedNhd, weightMul_one_weight, Submodule.mem_toAddSubgroup] using hf

/-- **Functoriality of polynomial reduction in the coefficient ring.** For a continuous ring
homomorphism `φ : A →+* B` carrying an open ideal `I` into an open ideal `J`, polynomial reduction
commutes with `weightedMap`. No flatness assumption is needed. -/
theorem restrictedReduction_weightedMap {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ) (I : Ideal A)
    (hI : IsOpen (I : Set A)) (J : Ideal B) (hJ : IsOpen (J : Set B)) (hIJ : I ≤ J.comap φ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    restrictedReduction J hJ
        (weightedMap hφ isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (restrictedReduction I hI f) := by
  ext ν
  simp [MvPolynomial.coeff_map]

/-- Reduction of completed restricted series modulo an open ideal of the coefficient ring is
polynomial. Because `A ⧸ J` is discrete, its restricted-series ring is already complete and
Hausdorff, so the reduction extends across `UniformSpace.Completion` with no completeness or
separation assumption on `A`. -/
noncomputable def restrictedCompletionReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    restrictedMvPowerSeriesCompletion k A →+* MvPolynomial (Fin k) (A ⧸ J) := by
  letI : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  haveI : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  haveI : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := IsRightUniformAddGroup.discreteUniformity
  exact (weightedPolynomialEquivOfDiscrete (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
    isWeightFamily_one_weight).symm.toRingHom.comp
      (Completion.extensionHom
        (weightedMap (φ := Ideal.Quotient.mk J) (QuotientRing.isOpenQuotientMap_mk J).continuous
          isWeightFamily_one_weight isWeightFamily_one_weight (by simp))
        (continuous_weightedMap (QuotientRing.isOpenQuotientMap_mk J).continuous
          isWeightFamily_one_weight isWeightFamily_one_weight (by simp)))

/-- On the image of the uncompleted restricted-series subring, `restrictedCompletionReduction`
agrees with `restrictedReduction`. -/
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
  simp [restrictedCompletionReduction, restrictedReduction, Completion.extensionHom_coe]

/-- Completed reduction sends a constant series from `A` to the corresponding constant polynomial
over `A ⧸ J`. -/
theorem restrictedCompletionReduction_algebraMap (J : Ideal A) (hJ : IsOpen (J : Set A)) (a : A) :
    restrictedCompletionReduction (k := k) J hJ
        (algebraMap A (restrictedMvPowerSeriesCompletion k A) a) =
      MvPolynomial.C (Ideal.Quotient.mk J a) := by
  rw [algebraMap_completion_weightedRestrictedSubring_apply, restrictedCompletionReduction_coe,
    restrictedReduction_weightedC]

/-- Completed reduction preserves the coordinate variables. -/
theorem restrictedCompletionReduction_weightedX (J : Ideal A) (hJ : IsOpen (J : Set A))
    (i : Fin k) :
    restrictedCompletionReduction J hJ
        ((weightedX _ isWeightFamily_one_weight i :
          weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion k A) =
      MvPolynomial.X i := by
  rw [restrictedCompletionReduction_coe, restrictedReduction_weightedX]

/-- Completed polynomial reduction is surjective: every polynomial over `A ⧸ J` lifts already to a
polynomial over `A`. -/
theorem restrictedCompletionReduction_surjective (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    Function.Surjective (restrictedCompletionReduction (k := k) J hJ) := fun p ↦ by
  obtain ⟨f, rfl⟩ := restrictedReduction_surjective (k := k) J hJ p
  exact ⟨f, restrictedCompletionReduction_coe J hJ f⟩

/-- Any function out of `MvPolynomial (Fin k) (A ⧸ J)` becomes continuous after precomposing with
`restrictedCompletionReduction J hJ`. -/
theorem continuous_comp_restrictedCompletionReduction {X : Type*} [TopologicalSpace X]
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (g : MvPolynomial (Fin k) (A ⧸ J) → X) :
    Continuous (g ∘ restrictedCompletionReduction (k := k) J hJ) := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  have : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := IsRightUniformAddGroup.discreteUniformity
  exact (continuous_of_discreteTopology (f := fun y ↦
    g ((weightedPolynomialEquivOfDiscrete (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight).symm y))).comp Completion.continuous_extension

/-- The kernel of `restrictedCompletionReduction` is an open ideal of
`restrictedMvPowerSeriesCompletion k A`. -/
theorem isOpen_ker_restrictedCompletionReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    IsOpen (RingHom.ker (restrictedCompletionReduction (k := k) J hJ) :
      Set (restrictedMvPowerSeriesCompletion k A)) := by
  let : TopologicalSpace (MvPolynomial (Fin k) (A ⧸ J)) := ⊥
  have : DiscreteTopology (MvPolynomial (Fin k) (A ⧸ J)) := ⟨rfl⟩
  exact (isOpen_discrete ({0} : Set (MvPolynomial (Fin k) (A ⧸ J)))).preimage
    (continuous_comp_restrictedCompletionReduction J hJ id)

/-- Completed reduction is compatible with passing to a larger open ideal. -/
@[simp]
theorem map_restrictedCompletionReduction {J : Ideal A} (hJ : IsOpen (J : Set A))
    (hI : IsOpen (I : Set A)) (hJI : J ≤ I) (x : restrictedMvPowerSeriesCompletion k A) :
    MvPolynomial.map (Ideal.Quotient.factor hJI) (restrictedCompletionReduction J hJ x) =
      restrictedCompletionReduction I hI x := by
  let : TopologicalSpace (MvPolynomial (Fin k) (A ⧸ I)) := ⊥
  have : DiscreteTopology (MvPolynomial (Fin k) (A ⧸ I)) := ⟨rfl⟩
  have h := completion_weightedRestrictedSubring_ringHom_ext_of_continuous
    isWeightFamily_one_weight
    (f := (MvPolynomial.map (Ideal.Quotient.factor hJI)).comp
      (restrictedCompletionReduction (k := k) J hJ))
    (g := restrictedCompletionReduction (k := k) I hI)
    (continuous_comp_restrictedCompletionReduction J hJ
      (MvPolynomial.map (Ideal.Quotient.factor hJI)))
    (continuous_comp_restrictedCompletionReduction I hI id)
    (fun a ↦ by simp)
    (fun i ↦ by simp)
  exact RingHom.congr_fun h x

/-- **Functoriality of completed polynomial reduction in the coefficient ring.** No completeness,
separation, or flatness assumption is required on either ring. -/
theorem restrictedCompletionReduction_weightedMapCompletion {B : Type*} [CommRing B]
    [TopologicalSpace B] [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ)
    (I : Ideal A) (hI : IsOpen (I : Set A)) (J : Ideal B) (hJ : IsOpen (J : Set B))
    (hIJ : I ≤ J.comap φ) (x : restrictedMvPowerSeriesCompletion k A) :
    restrictedCompletionReduction J hJ
        (weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight (by simp) x) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (restrictedCompletionReduction I hI x) := by
  let : TopologicalSpace (MvPolynomial (Fin k) (B ⧸ J)) := ⊥
  have : DiscreteTopology (MvPolynomial (Fin k) (B ⧸ J)) := ⟨rfl⟩
  have h := completion_weightedRestrictedSubring_ringHom_ext_of_continuous
    isWeightFamily_one_weight
    (f := (restrictedCompletionReduction (k := k) J hJ).comp
      (weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight (by simp)))
    (g := (MvPolynomial.map (Ideal.quotientMap J φ hIJ)).comp
      (restrictedCompletionReduction (k := k) I hI))
    ((continuous_comp_restrictedCompletionReduction J hJ id).comp
      (continuous_weightedMapCompletion hφ _ _ _))
    (continuous_comp_restrictedCompletionReduction I hI
      (MvPolynomial.map (Ideal.quotientMap J φ hIJ)))
    (fun a ↦ by simp)
    (fun i ↦ by simp)
  exact RingHom.congr_fun h x

/-- Over a complete Hausdorff base, `restrictedCompletionReduction` agrees with
`restrictedReduction` across `restrictedMvPowerSeriesCompletionAlgEquiv`. -/
theorem restrictedCompletionReduction_eq_restrictedReduction {R : Type*} [CommRing R]
    [UniformSpace R] [IsUniformAddGroup R] [NonarchimedeanRing R] [T2Space R] [CompleteSpace R]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (x : restrictedMvPowerSeriesCompletion k R) :
    restrictedCompletionReduction J hJ x =
      restrictedReduction J hJ (restrictedMvPowerSeriesCompletionAlgEquiv k R x) := by
  rw [coe_restrictedMvPowerSeriesCompletionAlgEquiv]
  let : TopologicalSpace (MvPolynomial (Fin k) (R ⧸ J)) := ⊥
  have : DiscreteTopology (MvPolynomial (Fin k) (R ⧸ J)) := ⟨rfl⟩
  have h := completion_weightedRestrictedSubring_ringHom_ext_of_continuous
    isWeightFamily_one_weight
    (f := restrictedCompletionReduction (k := k) J hJ)
    (g := (restrictedReduction (k := k) J hJ).comp
      (restrictedMvPowerSeriesCompletionEquiv k R).toRingHom)
    (continuous_comp_restrictedCompletionReduction J hJ id)
    ((continuous_comp_restrictedReduction J hJ id).comp
      uniformContinuous_restrictedMvPowerSeriesCompletionEquiv.continuous)
    (fun a ↦ by simp)
    (fun i ↦ by simp)
  exact RingHom.congr_fun h x

end Ideal

namespace TauCeti.Huber

open Ideal (restrictedReduction restrictedReduction_surjective mem_ker_restrictedReduction
  continuous_comp_restrictedReduction restrictedCompletionReduction
  restrictedCompletionReduction_coe restrictedCompletionReduction_algebraMap
  restrictedCompletionReduction_surjective continuous_comp_restrictedCompletionReduction)

/-- Reduction modulo a finitely generated ideal of definition has exactly the extended ideal
as its kernel. -/
theorem ker_restrictedReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedReduction (k := k) I (by simpa only [pow_one] using hI.isOpen_pow 1)) =
      I.map (weightedC _ isWeightFamily_one_weight) := by
  ext f
  rw [mem_ker_restrictedReduction, mem_map_weightedC_iff_of_isAdic hI hfg]

/-- Reduction modulo any power `I ^ m` of a finitely generated ideal of definition has kernel
`(I · A⟨T⟩) ^ m`. -/
theorem ker_restrictedReduction_pow (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    RingHom.ker (restrictedReduction (k := k) (I ^ m) (hI.isOpen_pow m)) =
      I.map (weightedC _ isWeightFamily_one_weight) ^ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · ext f
    simp only [Ideal.mem_ker_restrictedReduction, pow_zero, Ideal.one_eq_top, Submodule.mem_top,
      implies_true]
  · rw [← Ideal.map_pow]
    exact ker_restrictedReduction (is_ideal_adic_pow hI (Nat.pos_of_ne_zero hm)) hfg.pow

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

/-- Reduction of restricted power series modulo `(I · A⟨T⟩) ^ m` is the polynomial algebra over
`A ⧸ I ^ m`, for every `m : ℕ`. -/
noncomputable def quotientRestrictedPowEquivMvPolynomialQuotient (hI : IsAdic I) (hfg : I.FG)
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

/-- On a represented series, `quotientRestrictedPowEquivMvPolynomialQuotient` computes its
polynomial reduction modulo `I ^ m`. -/
@[simp]
theorem quotientRestrictedPowEquivMvPolynomialQuotient_mk (hI : IsAdic I) (hfg : I.FG) (m : ℕ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    quotientRestrictedPowEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ f) =
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

/-! ### Completed reductions modulo powers of an ideal of definition -/

/-- General kernel transfer from `restrictedReduction` to `restrictedCompletionReduction` for an
open ideal whose extension to `restrictedMvPowerSeriesCompletion k A` is open. -/
private theorem ker_restrictedCompletionReduction_of_isOpen {K : Ideal A}
    (hK : IsOpen (K : Set A))
    (hker : RingHom.ker (restrictedReduction (k := k) K hK) =
      K.map (weightedC _ isWeightFamily_one_weight))
    (hKopen : IsOpen ((K.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) :
      Ideal (restrictedMvPowerSeriesCompletion k A)) :
      Set (restrictedMvPowerSeriesCompletion k A))) :
    RingHom.ker (restrictedCompletionReduction (k := k) K hK) =
      K.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) := by
  let S := restrictedMvPowerSeriesCompletion k A
  let JK := K.map (algebraMap A S)
  have hle : JK ≤ RingHom.ker (restrictedCompletionReduction (k := k) K hK) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.restrictedCompletionReduction_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  refine le_antisymm ?_ hle
  intro x hx
  have hnhds : {y : S | x - y ∈ JK} ∈ nhds x := by
    have hcont : Continuous (fun y : S ↦ x - y) := continuous_const.sub continuous_id
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hKopen.mem_nhds (zero_mem JK))
  obtain ⟨f, hf⟩ := Completion.denseRange_coe.mem_nhds hnhds
  have hfker : f ∈ RingHom.ker (restrictedReduction (k := k) K hK) := by
    rw [RingHom.mem_ker, ← restrictedCompletionReduction_coe, ← RingHom.mem_ker]
    have hsub := (RingHom.ker (restrictedCompletionReduction (k := k) K hK)).sub_mem hx (hle hf)
    simpa only [sub_sub_cancel] using hsub
  rw [hker] at hfker
  have hfJK : (f : S) ∈ JK := by
    have hmap : JK = (K.map (weightedC _ isWeightFamily_one_weight)).map Completion.coeRingHom := by
      dsimp only [JK, S]
      rw [Ideal.map_map]
      exact congrArg (Ideal.map · K) (RingHom.ext fun a ↦
        algebraMap_completion_weightedRestrictedSubring_apply k A isWeightFamily_one_weight a)
    rw [hmap]
    exact Ideal.mem_map_of_mem _ hfker
  simpa only [sub_add_cancel] using JK.add_mem hf hfJK

/-- Reduction modulo a finitely generated ideal of definition on the completed restricted-series
algebra has kernel `I · A⟨T⟩`. -/
theorem ker_restrictedCompletionReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedCompletionReduction (k := k) I
        (by simpa only [pow_one] using hI.isOpen_pow 1)) =
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) :=
  ker_restrictedCompletionReduction_of_isOpen _ (ker_restrictedReduction hI hfg)
    (by
      simpa only [pow_one] using
        (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg).isOpen_pow 1)

/-- On the completed restricted-series algebra, reduction modulo `I ^ m` has kernel
`(I · A⟨T⟩) ^ m` for every finitely generated ideal of definition `I` and every `m : ℕ`. No
completeness or separation assumption on `A` is needed. -/
theorem ker_restrictedCompletionReduction_pow (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    RingHom.ker (restrictedCompletionReduction (k := k) (I ^ m) (hI.isOpen_pow m)) =
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) ^ m := by
  rw [← Ideal.map_pow]
  refine ker_restrictedCompletionReduction_of_isOpen (hI.isOpen_pow m) ?_ ?_
  · rw [Ideal.map_pow]
    exact ker_restrictedReduction_pow hI hfg m
  · rw [Ideal.map_pow]
    exact (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg).isOpen_pow m

/-- The reduction modulo `(I · A⟨T⟩) ^ m` of the completed restricted-series algebra is the
polynomial algebra over `A ⧸ I ^ m`, for every `m : ℕ` and with no completeness or separation
assumption on `A`. -/
noncomputable def quotientRestrictedCompletionPowEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    (restrictedMvPowerSeriesCompletion k A ⧸
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) ^ m) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I ^ m) := by
  let hker := ker_restrictedCompletionReduction_pow (k := k) hI hfg m
  let e := (Ideal.quotEquivOfEq hker.symm).trans
    ((restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m)).quotientKerEquivOfSurjective
      (restrictedCompletionReduction_surjective (I ^ m) (hI.isOpen_pow m)))
  refine AlgEquiv.ofRingEquiv (f := e) fun a ↦ ?_
  have he : e (algebraMap A _ a) =
      restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m) (algebraMap A _ a) := by
    rw [← Ideal.Quotient.mk_algebraMap]
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [he, restrictedCompletionReduction_algebraMap]
  rfl

/-- On a represented completion element,
`quotientRestrictedCompletionPowEquivMvPolynomialQuotient` computes its completed polynomial
reduction modulo `I ^ m`. -/
@[simp]
theorem quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) (x : restrictedMvPowerSeriesCompletion k A) :
    quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ x) =
      restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m) x := by
  simp [quotientRestrictedCompletionPowEquivMvPolynomialQuotient]

section Completion

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [NonarchimedeanRing R] [T2Space R] [CompleteSpace R] {J : Ideal R}

/-- The reduction modulo a finitely generated ideal of definition of the completed
restricted-series algebra is the polynomial algebra over the quotient of the coefficients.
(See `quotientRestrictedCompletionPowEquivMvPolynomialQuotient` for the power generalization with
no completeness or separation assumption on the base ring.) -/
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

/-! ### Compatibility with evaluation and the linearly topologised universal property -/

section Evaluation

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T2Space B]

/-- **Evaluation commutes with polynomial reduction modulo open ideals.** Reducing the value of a
restricted series at `b` modulo an open ideal `J` of `B` agrees with evaluating its polynomial
reduction modulo `I` at `b mod J`. -/
theorem mk_weightedEvalHom_eq_eval₂_restrictedReduction {φ : A →+* B} (hφ : ContinuousAt φ 0)
    {b : Fin k → B} (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b)
    (I : Ideal A) (hI : IsOpen (I : Set A)) (J : Ideal B) (hJ : IsOpen (J : Set B))
    (hIJ : I ≤ J.comap φ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    Ideal.Quotient.mk J (weightedEvalHom isWeightFamily_one_weight hφ hb f) =
      (restrictedReduction I hI f).eval₂ (Ideal.quotientMap J φ hIJ) (Ideal.Quotient.mk J ∘ b) := by
  let : DiscreteTopology (B ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have h := weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    (f := (Ideal.Quotient.mk J).comp (weightedEvalHom isWeightFamily_one_weight hφ hb))
    (g := (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (Ideal.Quotient.mk J ∘ b)).comp
      (restrictedReduction (k := k) I hI))
    (continuous_quot_mk.comp (continuous_weightedEvalHom isWeightFamily_one_weight hφ hb))
    (continuous_comp_restrictedReduction I hI
      (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (Ideal.Quotient.mk J ∘ b)))
    (fun a ↦ by simp)
    (fun i ↦ by simp)
  exact RingHom.congr_fun h f

/-- **Completed evaluation commutes with polynomial reduction modulo open ideals.** -/
theorem mk_weightedEvalHomCompletion_eq_eval₂_restrictedCompletionReduction {φ : A →+* B}
    (hφ : ContinuousAt φ 0) {b : Fin k → B}
    (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b)
    (I : Ideal A) (hI : IsOpen (I : Set A)) (J : Ideal B) (hJ : IsOpen (J : Set B))
    (hIJ : I ≤ J.comap φ) (x : restrictedMvPowerSeriesCompletion k A) :
    Ideal.Quotient.mk J (weightedEvalHomCompletion isWeightFamily_one_weight hφ hb x) =
      (restrictedCompletionReduction I hI x).eval₂
        (Ideal.quotientMap J φ hIJ) (Ideal.Quotient.mk J ∘ b) := by
  let : DiscreteTopology (B ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have h := completion_weightedRestrictedSubring_ringHom_ext_of_continuous
    isWeightFamily_one_weight
    (f := (Ideal.Quotient.mk J).comp (weightedEvalHomCompletion isWeightFamily_one_weight hφ hb))
    (g := (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (Ideal.Quotient.mk J ∘ b)).comp
      (restrictedCompletionReduction (k := k) I hI))
    (continuous_quot_mk.comp (continuous_weightedEvalHomCompletion isWeightFamily_one_weight hφ hb))
    (continuous_comp_restrictedCompletionReduction I hI
      (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (Ideal.Quotient.mk J ∘ b)))
    (fun a ↦ by simp)
    (fun i ↦ by simp)
  exact RingHom.congr_fun h x

end Evaluation

section LinearTopology

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsLinearTopology B B] [CompleteSpace B] [T2Space B]

/-- **The universal property of the uncompleted restricted-series ring into a linearly topologised
ring.** Because open ideals form a neighbourhood basis of zero in `B`, every subset of `B` is
bounded and every element is power-bounded, so any ring homomorphism `φ : A →+* B` continuous at `0`
extends uniquely to a continuous ring homomorphism sending the variables to arbitrary prescribed
elements `b : Fin k → B`. -/
theorem existsUnique_continuous_ringHom_weightedRestrictedSubring_of_isLinearTopology
    {φ : A →+* B} (hφ : ContinuousAt φ 0) (b : Fin k → B) :
    ∃! ψ : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight →+* B,
      Continuous ψ ∧ (∀ a, ψ (weightedC _ isWeightFamily_one_weight a) = φ a) ∧
        ∀ i, ψ (weightedX _ isWeightFamily_one_weight i) = b i := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  exact existsUnique_continuous_ringHom_weightedRestrictedSubring isWeightFamily_one_weight hφ
    (isWeightBounded_of_isLinearTopology φ _ b)

variable [Algebra A B]

/-- Evaluation of uncompleted restricted series in a complete Hausdorff linearly topologised
`A`-algebra at an arbitrary tuple `b : Fin k → B`, bundled as an `A`-algebra homomorphism. No
boundedness or power-boundedness hypothesis on `b` is required. -/
noncomputable def weightedEvalLinearAlgHom (hA : ContinuousAt (algebraMap A B) 0)
    (b : Fin k → B) :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight →ₐ[A]
      B := by
  haveI := IsLinearTopology.isTopologicalRing (R := B)
  haveI := IsLinearTopology.nonarchimedeanRing B
  let φ := weightedEvalHom isWeightFamily_one_weight hA
    (isWeightBounded_of_isLinearTopology (algebraMap A B) _ b)
  exact
    { __ := φ
      toFun := φ
      commutes' := fun a ↦ by
        dsimp only [φ]
        rw [algebraMap_weightedRestrictedSubring, weightedEvalHom_weightedC] }

/-- Underlying ring homomorphism of `weightedEvalLinearAlgHom`. -/
@[simp]
theorem coe_weightedEvalLinearAlgHom (hA : ContinuousAt (algebraMap A B) 0) (b : Fin k → B) :
    (weightedEvalLinearAlgHom hA b :
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight →+* B) =
      letI := IsLinearTopology.isTopologicalRing (R := B)
      letI := IsLinearTopology.nonarchimedeanRing B
      weightedEvalHom isWeightFamily_one_weight hA
        (isWeightBounded_of_isLinearTopology (algebraMap A B) _ b) := by
  ext x
  rfl

/-- `weightedEvalLinearAlgHom` sends each coordinate variable `Xᵢ` to `bᵢ`. -/
@[simp]
theorem weightedEvalLinearAlgHom_weightedX (hA : ContinuousAt (algebraMap A B) 0)
    (b : Fin k → B) (i : Fin k) :
    weightedEvalLinearAlgHom hA b (weightedX _ isWeightFamily_one_weight i) = b i := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  exact weightedEvalHom_weightedX isWeightFamily_one_weight hA
    (isWeightBounded_of_isLinearTopology (algebraMap A B) _ b) i

/-- `weightedEvalLinearAlgHom` is continuous. -/
theorem continuous_weightedEvalLinearAlgHom (hA : ContinuousAt (algebraMap A B) 0)
    (b : Fin k → B) : Continuous (weightedEvalLinearAlgHom hA b) := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  exact continuous_weightedEvalHom isWeightFamily_one_weight hA
    (isWeightBounded_of_isLinearTopology (algebraMap A B) _ b)

/-- **Universal property of `weightedRestrictedSubring` for linearly topologised `A`-algebras.**
For any `b : Fin k → B` (with no norm or power-boundedness restriction), `weightedEvalLinearAlgHom`
is the unique continuous `A`-algebra homomorphism sending each `Xᵢ` to `bᵢ`. -/
theorem existsUnique_continuous_algHom_weightedRestrictedSubring_of_isLinearTopology
    (hA : ContinuousAt (algebraMap A B) 0) (b : Fin k → B) :
    ∃! ψ : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight →ₐ[A] B,
      Continuous ψ ∧ ∀ i, ψ (weightedX _ isWeightFamily_one_weight i) = b i := by
  refine ⟨weightedEvalLinearAlgHom hA b,
    ⟨continuous_weightedEvalLinearAlgHom hA b, weightedEvalLinearAlgHom_weightedX hA b⟩,
    fun ψ ⟨hψ, hX⟩ ↦ AlgHom.toRingHom_injective ?_⟩
  exact (existsUnique_continuous_ringHom_weightedRestrictedSubring_of_isLinearTopology hA b).unique
    ⟨hψ, fun a ↦ by rw [← algebraMap_weightedRestrictedSubring]; exact ψ.commutes a, hX⟩
    ⟨continuous_weightedEvalLinearAlgHom hA b, fun a ↦ by simp,
      weightedEvalLinearAlgHom_weightedX hA b⟩

/-- Evaluation of completed restricted series in a complete Hausdorff linearly topologised
`A`-algebra at an arbitrary tuple `b : Fin k → B`, bundled as an `A`-algebra homomorphism
(EGA I, Ch. 0, §7.5.3). -/
noncomputable def weightedEvalCompletionLinearAlgHom (hA : ContinuousAt (algebraMap A B) 0)
    (b : Fin k → B) : restrictedMvPowerSeriesCompletion k A →ₐ[A] B := by
  haveI := IsLinearTopology.isTopologicalRing (R := B)
  haveI := IsLinearTopology.nonarchimedeanRing B
  let φ := weightedEvalHomCompletion isWeightFamily_one_weight hA
    (isWeightBounded_of_isLinearTopology (algebraMap A B) _ b)
  exact
    { __ := φ
      toFun := φ
      commutes' := fun a ↦ by
        dsimp only [φ]
        rw [algebraMap_completion_weightedRestrictedSubring_apply,
          weightedEvalHomCompletion_coe, weightedEvalHom_weightedC] }

/-- Underlying ring homomorphism of `weightedEvalCompletionLinearAlgHom`. -/
@[simp]
theorem coe_weightedEvalCompletionLinearAlgHom (hA : ContinuousAt (algebraMap A B) 0)
    (b : Fin k → B) :
    (weightedEvalCompletionLinearAlgHom hA b : restrictedMvPowerSeriesCompletion k A →+* B) =
      letI := IsLinearTopology.isTopologicalRing (R := B)
      letI := IsLinearTopology.nonarchimedeanRing B
      weightedEvalHomCompletion isWeightFamily_one_weight hA
        (isWeightBounded_of_isLinearTopology (algebraMap A B) _ b) := by
  ext x
  rfl

/-- On the uncompleted subring, `weightedEvalCompletionLinearAlgHom` agrees with
`weightedEvalLinearAlgHom`. -/
@[simp]
theorem weightedEvalCompletionLinearAlgHom_coe (hA : ContinuousAt (algebraMap A B) 0)
    (b : Fin k → B)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    weightedEvalCompletionLinearAlgHom hA b (f : restrictedMvPowerSeriesCompletion k A) =
      weightedEvalLinearAlgHom hA b f := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  exact weightedEvalHomCompletion_coe isWeightFamily_one_weight hA
    (isWeightBounded_of_isLinearTopology (algebraMap A B) _ b) f

/-- `weightedEvalCompletionLinearAlgHom` sends each coordinate variable `Xᵢ` to `bᵢ`. -/
theorem weightedEvalCompletionLinearAlgHom_weightedX (hA : ContinuousAt (algebraMap A B) 0)
    (b : Fin k → B) (i : Fin k) :
    weightedEvalCompletionLinearAlgHom hA b
        ((weightedX _ isWeightFamily_one_weight i :
          weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion k A) = b i := by
  rw [weightedEvalCompletionLinearAlgHom_coe, weightedEvalLinearAlgHom_weightedX]

/-- `weightedEvalCompletionLinearAlgHom` is continuous. -/
theorem continuous_weightedEvalCompletionLinearAlgHom (hA : ContinuousAt (algebraMap A B) 0)
    (b : Fin k → B) : Continuous (weightedEvalCompletionLinearAlgHom hA b) := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  exact continuous_weightedEvalHomCompletion isWeightFamily_one_weight hA
    (isWeightBounded_of_isLinearTopology (algebraMap A B) _ b)

/-- **Universal property of `restrictedMvPowerSeriesCompletion` for linearly topologised
`A`-algebras** (EGA I, Ch. 0, §7.5.3). Every tuple `b : Fin k → B` in a complete Hausdorff linearly
topologised `A`-algebra (with `algebraMap A B` continuous at `0`) determines a unique continuous
`A`-algebra homomorphism `A⟨X₁, …, Xₖ⟩ →ₐ[A] B` sending each `Xᵢ` to `bᵢ`, with no boundedness
condition on `b`. -/
theorem existsUnique_continuous_algHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology
    (hA : ContinuousAt (algebraMap A B) 0) (b : Fin k → B) :
    ∃! ψ : restrictedMvPowerSeriesCompletion k A →ₐ[A] B,
      Continuous ψ ∧ ∀ i, ψ ((weightedX _ isWeightFamily_one_weight i :
        weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion k A) = b i := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  refine ⟨weightedEvalCompletionLinearAlgHom hA b,
    ⟨continuous_weightedEvalCompletionLinearAlgHom hA b,
      weightedEvalCompletionLinearAlgHom_weightedX hA b⟩,
    fun ψ ⟨hψ, hX⟩ ↦ AlgHom.toRingHom_injective ?_⟩
  exact (existsUnique_continuous_ringHom_completion_weightedRestrictedSubring
    isWeightFamily_one_weight hA (isWeightBounded_of_isLinearTopology (algebraMap A B) _ b)).unique
      ⟨hψ, fun a ↦ by
        rw [← algebraMap_completion_weightedRestrictedSubring_apply]
        exact ψ.commutes a, hX⟩
      ⟨continuous_weightedEvalCompletionLinearAlgHom hA b,
        fun a ↦ by
          rw [← algebraMap_completion_weightedRestrictedSubring_apply]
          exact (weightedEvalCompletionLinearAlgHom hA b).commutes a,
        weightedEvalCompletionLinearAlgHom_weightedX hA b⟩

end LinearTopology

/-! ### Inverse-limit description from compatible polynomial reductions -/

section InverseLimit

private theorem strictMono_add_one : StrictMono (· + 1 : ℕ → ℕ) :=
  fun _ _ h ↦ Nat.add_lt_add_right h 1

/-- Over an `I`-adically separated ring carrying the `I`-adic topology, a restricted power series is
uniquely determined by its sequence of polynomial reductions modulo `I ^ (m + 1)`. -/
theorem restrictedReduction_pow_succ_injective (hI : IsAdic I) [IsHausdorff I A] :
    Function.Injective (fun (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight) (m : ℕ) ↦
      restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1)) f) := by
  intro f g hfg
  apply Subtype.ext
  ext ν
  have hfun : (fun _ : Unit ↦ MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)) =
      fun _ : Unit ↦ MvPowerSeries.coeff ν (g : MvPowerSeries (Fin k) A) :=
    IsHausdorff.StrictMono.funext' I strictMono_add_one fun m _ ↦ by
      simpa only [Ideal.coeff_restrictedReduction] using
        congrArg (fun p : MvPolynomial (Fin k) _ ↦ p.coeff ν) (congrFun hfg m)
  exact congrFun hfun ()

/-- **Inverse-limit characterisation of adic restricted power series**
(EGA I, Ch. 0, §7.5.1). Over an `I`-adically complete ring carrying the `I`-adic topology (with no
finite generation assumption on `I`), every compatible sequence of polynomials in
`(A ⧸ I ^ (m + 1))[X₁, …, Xₖ]` is the reduction sequence of a unique restricted power series in
`A⟨X₁, …, Xₖ⟩`. -/
theorem existsUnique_restrictedReduction_pow_succ_eq (hI : IsAdic I) [IsAdicComplete I A]
    (p : ∀ m : ℕ, MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hp : ∀ m : ℕ,
      MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))
        (p (m + 1)) = p m) :
    ∃! f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight,
      ∀ m : ℕ, restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1)) f = p m := by
  have compat (ν : Fin k →₀ ℕ) {m : ℕ} :
      (Ideal.Quotient.factorPow I (strictMono_add_one.monotone m.le_succ)).comp
        (MvPolynomial.eval₂Hom (Int.castRingHom _) fun _ : Unit ↦ (p (m + 1)).coeff ν) =
      MvPolynomial.eval₂Hom (Int.castRingHom _) fun _ : Unit ↦ (p m).coeff ν :=
    MvPolynomial.ringHom_ext (fun z ↦ by simp) fun _ ↦ by
      simpa [MvPolynomial.coeff_map] using
        congrArg (fun q : MvPolynomial (Fin k) _ ↦ q.coeff ν) (hp m)
  let c (ν : Fin k →₀ ℕ) : A :=
    IsAdicComplete.StrictMono.liftRingHom I strictMono_add_one
      (fun m ↦ MvPolynomial.eval₂Hom (Int.castRingHom _) fun _ : Unit ↦ (p m).coeff ν)
      (fun {m} ↦ compat ν) (MvPolynomial.X ())
  have hc (ν : Fin k →₀ ℕ) (m : ℕ) : Ideal.Quotient.mk (I ^ (m + 1)) (c ν) = (p m).coeff ν := by
    simpa only [c, MvPolynomial.eval₂Hom_X'] using
      IsAdicComplete.StrictMono.mk_liftRingHom (n := m) I strictMono_add_one
        (fun m ↦ MvPolynomial.eval₂Hom (Int.castRingHom _) fun _ : Unit ↦ (p m).coeff ν)
        (fun {m} ↦ compat ν) (MvPolynomial.X ())
  let F : MvPowerSeries (Fin k) A := fun ν ↦ c ν
  have hF : IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) F := by
    rw [isWeightedRestricted_iff]
    intro U
    obtain ⟨n, -, hn⟩ := hI.hasBasis_nhds_zero.mem_iff.mp (U.isOpen.mem_nhds U.zero_mem)
    rw [Filter.eventually_cofinite]
    refine (p n).support.finite_toSet.subset fun ν hν ↦ ?_
    simp only [Set.mem_ofPred_eq, weightMul_one_weight] at hν
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff]
    intro hzero
    apply hν
    refine hn (Ideal.pow_le_pow_right n.le_succ ?_)
    rw [← Ideal.Quotient.eq_zero_iff_mem, MvPowerSeries.coeff_apply, hc ν n]
    exact hzero
  let f₀ : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
    ⟨F, mem_weightedRestrictedSubring.mpr hF⟩
  have hf₀ (m : ℕ) : restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1)) f₀ = p m := by
    ext ν
    rw [Ideal.coeff_restrictedReduction]
    exact (congrArg _ (MvPowerSeries.coeff_apply F ν)).trans (hc ν m)
  exact ⟨f₀, hf₀, fun g hg ↦ restrictedReduction_pow_succ_injective hI <|
    funext fun m ↦ (hg m).trans (hf₀ m).symm⟩

/-- **Universal property of adic restricted power series as the inverse limit of polynomial
reductions.** Over an `I`-adically complete ring carrying the `I`-adic topology (with no finite
generation assumption on `I`), any compatible family of ring homomorphisms
`S →+* (A ⧸ I ^ (m + 1))[X₁, …, Xₖ]` lifts to a ring homomorphism into the restricted-series
ring. -/
noncomputable def liftRestrictedReductionPowSucc {S : Type*} [NonAssocSemiring S] (hI : IsAdic I)
    [IsAdicComplete I A] (φ : ∀ m : ℕ, S →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ,
      (MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp
        (φ (m + 1)) = φ m) :
    S →+* weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight := by
  let liftElem (s : S) :=
    (existsUnique_restrictedReduction_pow_succ_eq hI (fun m ↦ φ m s)
      fun m ↦ RingHom.congr_fun (hφ m) s).choose
  have hlift (s : S) (m : ℕ) :
      restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1)) (liftElem s) = φ m s :=
    (existsUnique_restrictedReduction_pow_succ_eq hI (fun m ↦ φ m s)
      fun m ↦ RingHom.congr_fun (hφ m) s).choose_spec.1 m
  refine
    { toFun := liftElem
      map_one' := restrictedReduction_pow_succ_injective hI <| funext fun m ↦ by simp [hlift]
      map_mul' := fun x y ↦
        restrictedReduction_pow_succ_injective hI <| funext fun m ↦ by simp [hlift]
      map_zero' := restrictedReduction_pow_succ_injective hI <| funext fun m ↦ by simp [hlift]
      map_add' := fun x y ↦
        restrictedReduction_pow_succ_injective hI <| funext fun m ↦ by simp [hlift] }

/-- Reducing `liftRestrictedReductionPowSucc hI φ hφ s` modulo `I ^ (m + 1)` recovers `φ m s`. -/
@[simp]
theorem restrictedReduction_pow_succ_liftRestrictedReductionPowSucc {S : Type*}
    [NonAssocSemiring S] (hI : IsAdic I) [IsAdicComplete I A]
    (φ : ∀ m : ℕ, S →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ,
      (MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp
        (φ (m + 1)) = φ m)
    (m : ℕ) (s : S) :
    restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1))
        (liftRestrictedReductionPowSucc hI φ hφ s) = φ m s :=
  (existsUnique_restrictedReduction_pow_succ_eq hI (fun n ↦ φ n s)
    fun n ↦ RingHom.congr_fun (hφ n) s).choose_spec.1 m

/-- Uniqueness of `liftRestrictedReductionPowSucc`. -/
theorem eq_liftRestrictedReductionPowSucc {S : Type*} [NonAssocSemiring S] (hI : IsAdic I)
    [IsAdicComplete I A] (φ : ∀ m : ℕ, S →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ,
      (MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp
        (φ (m + 1)) = φ m)
    {ψ : S →+* weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight}
    (hψ : ∀ m : ℕ, (restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1))).comp ψ = φ m) :
    ψ = liftRestrictedReductionPowSucc hI φ hφ := by
  ext1 s
  refine restrictedReduction_pow_succ_injective hI (funext fun m ↦ ?_)
  dsimp only
  rw [restrictedReduction_pow_succ_liftRestrictedReductionPowSucc]
  exact RingHom.congr_fun (hψ m) s

/-- On the completed restricted-series algebra over a ring with finitely generated ideal of
definition `I` (with `A` not assumed complete or Hausdorff), every element is uniquely determined
by its sequence of polynomial reductions modulo `I ^ (m + 1)`. -/
theorem restrictedCompletionReduction_pow_succ_injective (hI : IsAdic I) (hfg : I.FG) :
    Function.Injective (fun (x : restrictedMvPowerSeriesCompletion k A) (m : ℕ) ↦
      restrictedCompletionReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1)) x) := by
  let S := restrictedMvPowerSeriesCompletion k A
  let J := I.map (algebraMap A S)
  have hJ : IsAdic J := isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg
  have : IsAdicComplete J S := hJ.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩
  intro x y hxy
  have hfun : (fun _ : Unit ↦ x) = fun _ : Unit ↦ y :=
    IsHausdorff.StrictMono.funext' J strictMono_add_one fun m _ ↦ by
      apply (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg
        (m + 1)).injective
      simpa [J, S] using congrFun hxy m
  exact congrFun hfun ()

private theorem factorPow_quotientRestrictedCompletionPowEquiv_symm (hI : IsAdic I) (hfg : I.FG)
    (φ : ∀ m : ℕ, MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ,
      MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))
        (φ (m + 1)) = φ m)
    (m : ℕ) :
    Ideal.Quotient.factorPow (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
        (strictMono_add_one.monotone m.le_succ)
        ((quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg (m + 2)).symm
          (φ (m + 1))) =
      (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg (m + 1)).symm
        (φ m) := by
  let e₁ := quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg (m + 1)
  let e₂ := quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg (m + 2)
  apply e₁.injective
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e₂.symm (φ (m + 1)))
  rw [← hx]
  have hfac : Ideal.Quotient.factorPow
      (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
      (strictMono_add_one.monotone m.le_succ) (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ x := rfl
  rw [hfac]
  simp only [e₁, quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk,
    AlgEquiv.apply_symm_apply]
  rw [← hφ m, ← Ideal.map_restrictedCompletionReduction (hI.isOpen_pow (m + 2))
    (hI.isOpen_pow (m + 1)) (Ideal.pow_le_pow_right m.succ.le_succ) x]
  congr 1
  simpa [e₂] using congrArg e₂ hx

/-- **Universal property of `restrictedMvPowerSeriesCompletion` as the inverse limit of polynomial
reductions.** When `I` is a finitely generated ideal of definition of `A` (with no completeness or
Hausdorffness assumption on `A`), any compatible family of ring homomorphisms
`S →+* (A ⧸ I ^ (m + 1))[X₁, …, Xₖ]` lifts uniquely to `restrictedMvPowerSeriesCompletion k A`. -/
noncomputable def liftRestrictedCompletionReductionPowSucc {S : Type*} [NonAssocSemiring S]
    (hI : IsAdic I) (hfg : I.FG)
    (φ : ∀ m : ℕ, S →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ,
      (MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp
        (φ (m + 1)) = φ m) :
    S →+* restrictedMvPowerSeriesCompletion k A :=
  letI : IsAdicComplete (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
      (restrictedMvPowerSeriesCompletion k A) :=
    (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg).isAdicComplete_iff.mpr
      ⟨inferInstance, inferInstance⟩
  IsAdicComplete.StrictMono.liftRingHom
    (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
    strictMono_add_one
    (fun m ↦
      (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg
        (m + 1)).symm.toRingHom.comp (φ m))
    (fun {m} ↦ RingHom.ext fun s ↦ factorPow_quotientRestrictedCompletionPowEquiv_symm hI hfg
      (fun n ↦ φ n s) (fun n ↦ RingHom.congr_fun (hφ n) s) m)

/-- Reducing `liftRestrictedCompletionReductionPowSucc hI hfg φ hφ s` modulo `I ^ (m + 1)` recovers
`φ m s`. -/
@[simp]
theorem restrictedCompletionReduction_pow_succ_liftRestrictedCompletionReductionPowSucc
    {S : Type*} [NonAssocSemiring S] (hI : IsAdic I) (hfg : I.FG)
    (φ : ∀ m : ℕ, S →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ,
      (MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp
        (φ (m + 1)) = φ m)
    (m : ℕ) (s : S) :
    restrictedCompletionReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1))
        (liftRestrictedCompletionReductionPowSucc hI hfg φ hφ s) = φ m s := by
  have : IsAdicComplete (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
      (restrictedMvPowerSeriesCompletion k A) :=
    (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg).isAdicComplete_iff.mpr
      ⟨inferInstance, inferInstance⟩
  let e := quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg (m + 1)
  have hmk : Ideal.Quotient.mk
      (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) ^ (m + 1))
      (liftRestrictedCompletionReductionPowSucc hI hfg φ hφ s) = e.symm (φ m s) :=
    IsAdicComplete.StrictMono.mk_liftRingHom (n := m)
      (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))) strictMono_add_one _
      (fun {m} ↦ RingHom.ext fun t ↦ factorPow_quotientRestrictedCompletionPowEquiv_symm hI hfg
        (fun n ↦ φ n t) (fun n ↦ RingHom.congr_fun (hφ n) t) m) s
  simpa [e] using congrArg e hmk

/-- Uniqueness of `liftRestrictedCompletionReductionPowSucc`. -/
theorem eq_liftRestrictedCompletionReductionPowSucc {S : Type*} [NonAssocSemiring S]
    (hI : IsAdic I) (hfg : I.FG)
    (φ : ∀ m : ℕ, S →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ,
      (MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp
        (φ (m + 1)) = φ m)
    {ψ : S →+* restrictedMvPowerSeriesCompletion k A}
    (hψ : ∀ m : ℕ,
      (restrictedCompletionReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1))).comp ψ = φ m) :
    ψ = liftRestrictedCompletionReductionPowSucc hI hfg φ hφ := by
  ext1 s
  refine restrictedCompletionReduction_pow_succ_injective hI hfg (funext fun m ↦ ?_)
  dsimp only
  rw [restrictedCompletionReduction_pow_succ_liftRestrictedCompletionReductionPowSucc]
  exact RingHom.congr_fun (hψ m) s

/-- **Inverse-limit characterisation of `restrictedMvPowerSeriesCompletion`**
(EGA I, Ch. 0, §7.5.1). For any finitely generated ideal of definition `I` of `A` (with `A` not
assumed complete or Hausdorff), every compatible sequence of polynomials in
`(A ⧸ I ^ (m + 1))[X₁, …, Xₖ]` is the reduction sequence of a unique element of
`restrictedMvPowerSeriesCompletion k A`. -/
theorem existsUnique_restrictedCompletionReduction_pow_succ_eq (hI : IsAdic I) (hfg : I.FG)
    (p : ∀ m : ℕ, MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hp : ∀ m : ℕ,
      MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))
        (p (m + 1)) = p m) :
    ∃! x : restrictedMvPowerSeriesCompletion k A,
      ∀ m : ℕ, restrictedCompletionReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1)) x = p m := by
  let φ (m : ℕ) : MvPolynomial Unit ℤ →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)) :=
    MvPolynomial.eval₂Hom (Int.castRingHom _) fun _ ↦ p m
  have hφ (m : ℕ) :
      (MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp
        (φ (m + 1)) = φ m := by
    refine MvPolynomial.ringHom_ext (fun z ↦ by simp [φ]) fun _ ↦ ?_
    simpa [φ] using hp m
  let x := liftRestrictedCompletionReductionPowSucc hI hfg φ hφ (MvPolynomial.X ())
  have hx (m : ℕ) :
      restrictedCompletionReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1)) x = p m := by
    simp [x, φ]
  exact ⟨x, hx, fun y hy ↦ restrictedCompletionReduction_pow_succ_injective hI hfg <|
    funext fun m ↦ (hy m).trans (hx m).symm⟩

end InverseLimit

end TauCeti.Huber
