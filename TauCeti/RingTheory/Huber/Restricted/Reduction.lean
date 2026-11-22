/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.RingTheory.MvPolynomial.Quotient
public import TauCeti.RingTheory.AdicCompletion.UniformCompletion
public import Mathlib.RingTheory.AdicCompletion.Basic
public import TauCeti.RingTheory.Huber.Adic
public import TauCeti.RingTheory.Huber.Restricted.Adic
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Kernel
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Subring
import TauCeti.RingTheory.AdicCompletion.AlgHom
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.Ideal.Maps
import TauCeti.Topology.Algebra.Nonarchimedean.Quotient
import TauCeti.Topology.Algebra.Module.Quotient
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

Reduction of restricted power series modulo an open ideal is polynomial on both the restricted
subring (`Ideal.restrictedReduction`) and its separated completion
(`Ideal.restrictedCompletionReduction`), without completeness or separatedness of `A`. Both maps are
locally constant, natural under continuous coefficient homomorphisms, and commute with topological
evaluation (`weightedEvalHom` and `weightedEvalHomCompletion`) modulo any open ideal of the target.
For a finitely generated ideal of definition `I` and every `m : ℕ`, reducing modulo `(I·A⟨T⟩)ᵐ`
gives `A⟨T⟩/(I·A⟨T⟩)ᵐ ≃ₐ[A] (A/Iᵐ)[T]` on both carriers, and identifies the separated completion
`restrictedMvPowerSeriesCompletion k A` homeomorphically as a topological `A`-algebra with
`AdicCompletion (I.map MvPolynomial.C) (MvPolynomial (Fin k) A)`.

## Main definitions and results

* `Ideal.restrictedReduction`, `Ideal.weightedSubringReduction`,
  `Ideal.restrictedCompletionReduction`, `Ideal.isLocallyConstant_restrictedReduction`, and
  `Ideal.isLocallyConstant_restrictedCompletionReduction`.
* `TauCeti.Huber.quotientPowRestrictedEquivMvPolynomialQuotient`,
  `TauCeti.Huber.quotientPowRestrictedCompletionEquivMvPolynomialQuotient`, and
  `TauCeti.Huber.restrictedMvPowerSeriesCompletionEquivAdicCompletion` (with `m = 1` specializations
  and `evalₐ` comparison `evalₐ_restrictedMvPowerSeriesCompletionEquivAdicCompletion`).
* `TauCeti.Huber.mk_weightedEvalHom_eq_eval₂_restrictedReduction` and
  `TauCeti.Huber.mk_weightedEvalHomCompletion_eq_eval₂_restrictedCompletionReduction`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.1–7.5.4.
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

/-- Reduction of unit-bounded restricted series `R⟨X₁, …, Xₖ⟩` modulo an open ideal `J` of a
subring `R ≤ A` is polynomial, obtained via `weightedRestrictedSubringEquivWeightedSubring`. -/
noncomputable def weightedSubringReduction (R : Subring A) (J : Ideal R)
    (hJ : IsOpen (J : Set R)) :
    weightedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight R →+*
      MvPolynomial (Fin k) (R ⧸ J) :=
  (restrictedReduction J hJ).comp (weightedRestrictedSubringEquivWeightedSubring R).symm.toRingHom

/-- Unfolding equation for `weightedSubringReduction`. -/
theorem weightedSubringReduction_def (R : Subring A) (J : Ideal R)
    (hJ : IsOpen (J : Set R)) :
    weightedSubringReduction (k := k) R J hJ =
      (restrictedReduction J hJ).comp
        (weightedRestrictedSubringEquivWeightedSubring R).symm.toRingHom :=
  (rfl)

/-- Polynomial reduction on `R⟨X₁, …, Xₖ⟩` reduces each coefficient modulo `J`. -/
@[simp]
theorem coeff_weightedSubringReduction (R : Subring A) (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : weightedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight R)
    (ν : Fin k →₀ ℕ) :
    (weightedSubringReduction R J hJ f).coeff ν =
      Ideal.Quotient.mk J
        ⟨MvPowerSeries.coeff ν ((f.val : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
            isWeightFamily_one_weight) : MvPowerSeries (Fin k) A),
          by simpa only [weightMul_one_weight, Subring.mem_toAddSubgroup] using
            mem_weightedNhd.mp (mem_weightedSubring.mp f.property) ν⟩ := by
  simp only [weightedSubringReduction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, coeff_restrictedReduction]
  refine congrArg (Ideal.Quotient.mk J) (Subtype.ext ?_)
  exact coeff_weightedRestrictedSubringEquivWeightedSubring_symm R f ν

/-- A series in `R⟨X₁, …, Xₖ⟩` reduces to `0` modulo an open ideal `J` of `R` if and only if all
of its coefficients lie in `J`. -/
theorem weightedSubringReduction_eq_zero_iff (R : Subring A) {J : Ideal R}
    (hJ : IsOpen (J : Set R))
    {f : weightedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight R} :
    weightedSubringReduction R J hJ f = 0 ↔
      ∀ ν, ⟨MvPowerSeries.coeff ν ((f.val : weightedRestrictedSubring
          (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) : MvPowerSeries (Fin k) A),
        by simpa only [weightMul_one_weight, Subring.mem_toAddSubgroup] using
          mem_weightedNhd.mp (mem_weightedSubring.mp f.property) ν⟩ ∈ J := by
  simp [MvPolynomial.ext_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- On embedded polynomials with coefficients in `R`, `weightedSubringReduction` reduces
coefficients modulo `J`. -/
@[simp]
theorem weightedSubringReduction_weightedPolynomialHom (R : Subring A) (J : Ideal R)
    (hJ : IsOpen (J : Set R)) (p : MvPolynomial (Fin k) R) :
    weightedSubringReduction R J hJ
        ⟨weightedPolynomialHom (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
            (MvPolynomial.map R.subtype p),
          weightedPolynomialHom_map_mem_weightedSubring_one_weight R p⟩ =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  simp [weightedSubringReduction]

/-- `weightedSubringReduction` sends constant series in `R` to constant polynomials over `R ⧸ J`. -/
@[simp]
theorem weightedSubringReduction_weightedC (R : Subring A) (J : Ideal R) (hJ : IsOpen (J : Set R))
    (a : R) :
    weightedSubringReduction (k := k) R J hJ
        ⟨weightedC (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight (a : A),
          (weightedC_mem_weightedSubring isWeightFamily_one_weight).mpr a.property⟩ =
      MvPolynomial.C (Ideal.Quotient.mk J a) := by
  simp [weightedSubringReduction]

/-- `weightedSubringReduction` preserves the coordinate variables. -/
@[simp]
theorem weightedSubringReduction_weightedX (R : Subring A) (J : Ideal R) (hJ : IsOpen (J : Set R))
    (i : Fin k) :
    weightedSubringReduction R J hJ
        ⟨weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i,
          weightedX_mem_weightedSubring_one_weight R i⟩ =
      MvPolynomial.X i := by
  simp [weightedSubringReduction]

/-- Every polynomial over `R ⧸ J` lifts to `R⟨X₁, …, Xₖ⟩`. -/
theorem weightedSubringReduction_surjective (R : Subring A) (J : Ideal R)
    (hJ : IsOpen (J : Set R)) :
    Function.Surjective (weightedSubringReduction (k := k) R J hJ) :=
  (restrictedReduction_surjective J hJ).comp
    (weightedRestrictedSubringEquivWeightedSubring R).symm.surjective

local notation:max "WSub" k:max A:max =>
  weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
local notation:max "WPoly" k:max A:max =>
  weightedPolynomialHom (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
local notation:max "WX" k:max A:max =>
  weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
local notation:max "WComp" k:max A:max => restrictedMvPowerSeriesCompletion k A

/-- Reduction of completed restricted series modulo an open ideal is polynomial, without requiring
completeness or separatedness of `A`. -/
noncomputable def restrictedCompletionReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    WComp k A →+* MvPolynomial (Fin k) (A ⧸ J) :=
  letI : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  haveI : DiscreteTopology (WSub k (A ⧸ J)) := discreteTopology_weightedRestrictedSubring
  haveI : DiscreteUniformity (WSub k (A ⧸ J)) := IsRightUniformAddGroup.discreteUniformity
  (weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).symm.toRingHom.comp
    ((restrictedMvPowerSeriesCompletionEquiv k (A ⧸ J)).toRingHom.comp
      (weightedMapCompletion (φ := Ideal.Quotient.mk J)
        (QuotientRing.isOpenQuotientMap_mk J).continuous
        isWeightFamily_one_weight isWeightFamily_one_weight (by simp)))

/-- `restrictedReduction` is locally constant, factoring through the discrete ring over `A ⧸ J`. -/
theorem isLocallyConstant_restrictedReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    IsLocallyConstant (restrictedReduction (k := k) J hJ) :=
  letI : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  haveI : DiscreteTopology (WSub k (A ⧸ J)) := discreteTopology_weightedRestrictedSubring
  (IsLocallyConstant.of_discrete
    ((weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).symm : _ → _)).comp_continuous
    (continuous_weightedMap _ _ _ _)

/-- `restrictedReduction` is continuous into any topology on `MvPolynomial (Fin k) (A ⧸ J)`. -/
theorem continuous_restrictedReduction (J : Ideal A)
    [TopologicalSpace (MvPolynomial (Fin k) (A ⧸ J))] (hJ : IsOpen (J : Set A)) :
    Continuous (restrictedReduction (k := k) J hJ) :=
  (J.isLocallyConstant_restrictedReduction hJ).continuous

/-- `restrictedCompletionReduction` is locally constant, factoring through `WSub k (A ⧸ J)`. -/
theorem isLocallyConstant_restrictedCompletionReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    IsLocallyConstant (restrictedCompletionReduction (k := k) J hJ) :=
  letI : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  haveI : DiscreteTopology (WSub k (A ⧸ J)) := discreteTopology_weightedRestrictedSubring
  haveI : DiscreteUniformity (WSub k (A ⧸ J)) := IsRightUniformAddGroup.discreteUniformity
  (IsLocallyConstant.of_discrete
    ((weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).symm : _ → _)).comp_continuous
    (uniformContinuous_restrictedMvPowerSeriesCompletionEquiv.continuous.comp
      (continuous_weightedMapCompletion _ _ _ _))

/-- `restrictedCompletionReduction` is continuous into any topology on `(A ⧸ J)[T]`. -/
theorem continuous_restrictedCompletionReduction (J : Ideal A)
    [TopologicalSpace (MvPolynomial (Fin k) (A ⧸ J))] (hJ : IsOpen (J : Set A)) :
    Continuous (restrictedCompletionReduction (k := k) J hJ) :=
  (J.isLocallyConstant_restrictedCompletionReduction hJ).continuous

/-- Completed reduction agrees with `restrictedReduction` on coerced series. -/
@[simp] theorem restrictedCompletionReduction_coe (J : Ideal A) (hJ : IsOpen (J : Set A))
    (f : WSub k A) :
    restrictedCompletionReduction J hJ (f : WComp k A) = restrictedReduction J hJ f := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have : DiscreteTopology (WSub k (A ⧸ J)) := discreteTopology_weightedRestrictedSubring
  have : DiscreteUniformity (WSub k (A ⧸ J)) := IsRightUniformAddGroup.discreteUniformity
  simp [restrictedCompletionReduction, restrictedReduction]

/-- Completed reduction sends a constant to the corresponding constant polynomial. -/
theorem restrictedCompletionReduction_algebraMap (J : Ideal A) (hJ : IsOpen (J : Set A))
    (a : A) : restrictedCompletionReduction (k := k) J hJ (algebraMap A (WComp k A) a) =
      MvPolynomial.C (Ideal.Quotient.mk J a) := by
  rw [algebraMap_completion_weightedRestrictedSubring_apply, restrictedCompletionReduction_coe,
    restrictedReduction_weightedC]

/-- Completed reduction preserves each coordinate variable. -/
theorem restrictedCompletionReduction_weightedX (J : Ideal A) (hJ : IsOpen (J : Set A))
    (i : Fin k) :
    restrictedCompletionReduction J hJ ((WX k A i : WSub k A) : WComp k A) = MvPolynomial.X i := by
  rw [restrictedCompletionReduction_coe, restrictedReduction_weightedX]

/-- On embedded polynomials, completed reduction reduces coefficients modulo `J`. -/
theorem restrictedCompletionReduction_weightedPolynomialHom
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (p : MvPolynomial (Fin k) A) :
    restrictedCompletionReduction J hJ ((WPoly k A p : WSub k A) : WComp k A) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  rw [restrictedCompletionReduction_coe, restrictedReduction_weightedPolynomialHom]

/-- Every polynomial over `A ⧸ J` lifts to the completed restricted-series algebra. -/
theorem restrictedCompletionReduction_surjective (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    Function.Surjective (restrictedCompletionReduction (k := k) J hJ) := fun p ↦ by
  obtain ⟨f, rfl⟩ := restrictedReduction_surjective (k := k) J hJ p
  exact ⟨f, restrictedCompletionReduction_coe J hJ f⟩

/-- A restricted series lies in the kernel of reduction modulo an open ideal `J` if and only if
all of its coefficients lie in `J`. -/
theorem mem_ker_restrictedReduction (J : Ideal A) (hJ : IsOpen (J : Set A))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    f ∈ RingHom.ker (restrictedReduction J hJ) ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ J := by
  simp [RingHom.mem_ker, MvPolynomial.ext_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- Precomposing any map with `restrictedReduction J hJ` is continuous, since reduction factors
through the discrete restricted-series ring over `A ⧸ J`. -/
theorem continuous_comp_restrictedReduction {X : Type*} [TopologicalSpace X]
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (g : MvPolynomial (Fin k) (A ⧸ J) → X) :
    Continuous (g ∘ restrictedReduction (k := k) J hJ) := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  exact (continuous_of_discreteTopology (f := fun y ↦
    g ((weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).symm y))).comp
    (continuous_weightedMap (QuotientRing.isOpenQuotientMap_mk J).continuous
      isWeightFamily_one_weight isWeightFamily_one_weight (by simp))

/-- The kernel of polynomial reduction modulo an open ideal is open. -/
theorem isOpen_ker_restrictedReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    IsOpen (RingHom.ker (restrictedReduction (k := k) J hJ) : Set
      (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)) :=
  AddSubgroup.isOpen_mono (H₁ := weightedNhd _ isWeightFamily_one_weight J.toAddSubgroup)
    (H₂ := (RingHom.ker (restrictedReduction J hJ)).toAddSubgroup)
    (fun f hf ↦ (mem_ker_restrictedReduction J hJ f).mpr <| by
      simpa only [mem_weightedNhd, weightMul_one_weight, Submodule.mem_toAddSubgroup] using hf)
    (isOpen_weightedNhd isWeightFamily_one_weight hJ)

/-- Precomposing any map with `restrictedCompletionReduction J hJ` is continuous. -/
theorem continuous_comp_restrictedCompletionReduction {X : Type*} [TopologicalSpace X]
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (g : MvPolynomial (Fin k) (A ⧸ J) → X) :
    Continuous (g ∘ restrictedCompletionReduction (k := k) J hJ) :=
  ((J.isLocallyConstant_restrictedCompletionReduction hJ).comp g).continuous

/-- The kernel of `restrictedCompletionReduction` is an open ideal. -/
theorem isOpen_ker_restrictedCompletionReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    IsOpen (RingHom.ker (restrictedCompletionReduction (k := k) J hJ) :
      Set (restrictedMvPowerSeriesCompletion k A)) := by
  let : TopologicalSpace (MvPolynomial (Fin k) (A ⧸ J)) := ⊥
  have : DiscreteTopology (MvPolynomial (Fin k) (A ⧸ J)) := ⟨rfl⟩
  exact (isOpen_discrete ({0} : Set _)).preimage
    (continuous_comp_restrictedCompletionReduction J hJ id)

end Ideal

namespace TauCeti.Huber

open Ideal (restrictedReduction restrictedReduction_surjective restrictedCompletionReduction)

local notation:max "WSub" k:max A:max =>
  weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
local notation:max "WPoly" k:max A:max =>
  weightedPolynomialHom (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
local notation:max "WX" k:max A:max =>
  weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
local notation:max "WC" k:max A:max =>
  weightedC (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight
local notation:max "WComp" k:max A:max => restrictedMvPowerSeriesCompletion k A

/-- Polynomial reduction is natural along continuous maps compatible with open ideals. -/
theorem restrictedReduction_weightedMap {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ) {I : Ideal A} {J : Ideal B}
    (hI : IsOpen (I : Set A)) (hJ : IsOpen (J : Set B)) (hIJ : I ≤ J.comap φ) (f : WSub k A) :
    restrictedReduction J hJ
        (weightedMap hφ isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (restrictedReduction I hI f) := by
  ext ν; simp [MvPolynomial.coeff_map]

/-- Completed polynomial reduction is natural along continuous maps compatible with open ideals. -/
theorem restrictedCompletionReduction_weightedMapCompletion {B : Type*} [CommRing B]
    [TopologicalSpace B] [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ)
    {I : Ideal A} {J : Ideal B} (hI : IsOpen (I : Set A)) (hJ : IsOpen (J : Set B))
    (hIJ : I ≤ J.comap φ) (x : WComp k A) :
    restrictedCompletionReduction J hJ
        (weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) x) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (restrictedCompletionReduction I hI x) := by
  let : TopologicalSpace (MvPolynomial (Fin k) (B ⧸ J)) := ⊥
  have : DiscreteTopology (MvPolynomial (Fin k) (B ⧸ J)) := ⟨rfl⟩
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    ((J.continuous_restrictedCompletionReduction hJ).comp
      (continuous_weightedMapCompletion _ _ _ _))
    (((I.isLocallyConstant_restrictedCompletionReduction hI).comp _).continuous)) fun f ↦ ?_
  simp [restrictedReduction_weightedMap hφ hI hJ hIJ]

private theorem ker_pow_of_ker {B : Type*} [CommRing B] (c : A →+* B)
    (f : (J : Ideal A) → IsOpen (J : Set A) → B →+* MvPolynomial (Fin k) (A ⧸ J))
    (hker : ∀ {J : Ideal A} (hJ : IsAdic J), J.FG →
      RingHom.ker (f J (pow_one J ▸ hJ.isOpen_pow 1)) = J.map c)
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    RingHom.ker (f (I ^ m) (hI.isOpen_pow m)) = I.map c ^ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · have hsub : Subsingleton (A ⧸ (I ^ 0 : Ideal A)) :=
      Submodule.Quotient.subsingleton_iff.mpr ((pow_zero I).trans Ideal.one_eq_top)
    ext x
    simp only [RingHom.mem_ker, pow_zero, Ideal.one_eq_top, Submodule.mem_top, iff_true]
    ext ν; exact hsub.elim _ _
  · exact Ideal.map_pow c I m ▸
      hker (is_ideal_adic_pow hI (Nat.pos_of_ne_zero hm)) hfg.pow

private noncomputable def quotientEquivOfReduction {B : Type*} [CommRing B] [Algebra A B]
    {J : Ideal A} {K : Ideal B} (f : B →+* MvPolynomial (Fin k) (A ⧸ J))
    (hcomm : ∀ a, f (algebraMap A B a) = MvPolynomial.C (Ideal.Quotient.mk J a))
    (hker : RingHom.ker f = K) (hsurj : Function.Surjective f) :
    (B ⧸ K) ≃ₐ[A] MvPolynomial (Fin k) (A ⧸ J) :=
  let fₐ : B →ₐ[A] MvPolynomial (Fin k) (A ⧸ J) :=
    { f with
      commutes' a :=
        (hcomm a).trans (by rw [IsScalarTower.algebraMap_apply A (A ⧸ J)]; rfl) }
  have hker' : K = RingHom.ker fₐ := by rw [← hker]; ext x; rfl
  (Ideal.quotientEquivAlgOfEq A hker').trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := fₐ) hsurj)

omit [TopologicalSpace A] [NonarchimedeanRing A] in
private theorem quotientEquivOfReduction_mk {B : Type*} [CommRing B] [Algebra A B]
    {J : Ideal A} {K : Ideal B} (f : B →+* MvPolynomial (Fin k) (A ⧸ J))
    (hcomm : ∀ a, f (algebraMap A B a) = MvPolynomial.C (Ideal.Quotient.mk J a))
    (hker : RingHom.ker f = K) (hsurj : Function.Surjective f) (x : B) :
    quotientEquivOfReduction f hcomm hker hsurj (Ideal.Quotient.mk K x) = f x := by
  dsimp only [quotientEquivOfReduction]
  rw [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]
  rfl

private noncomputable def quotientOneEquivOfPow {B : Type*} [CommRing B] [Algebra A B]
    {K : Ideal B} (e : (B ⧸ K ^ 1) ≃ₐ[A] MvPolynomial (Fin k) (A ⧸ I ^ 1)) :
    (B ⧸ K) ≃ₐ[A] MvPolynomial (Fin k) (A ⧸ I) :=
  (Ideal.quotientEquivAlgOfEq A (pow_one K).symm).trans
    (e.trans (MvPolynomial.mapAlgEquiv (Fin k) (Ideal.quotientEquivAlgOfEq A (pow_one I))))

omit [TopologicalSpace A] [NonarchimedeanRing A] in
private theorem quotientOneEquivOfPow_mk {B : Type*} [CommRing B] [Algebra A B] {K : Ideal B}
    (e : (B ⧸ K ^ 1) ≃ₐ[A] MvPolynomial (Fin k) (A ⧸ I ^ 1)) (x : B) :
    quotientOneEquivOfPow e (Ideal.Quotient.mk K x) =
      MvPolynomial.map (Ideal.Quotient.factor (le_of_eq (pow_one I)))
        (e (Ideal.Quotient.mk (K ^ 1) x)) := by
  simp [quotientOneEquivOfPow]

omit [TopologicalSpace A] [NonarchimedeanRing A] in
private theorem quotientOneEquivOfPow_symm_map_mk {B : Type*} [CommRing B] [Algebra A B]
    {K : Ideal B} (e : (B ⧸ K ^ 1) ≃ₐ[A] MvPolynomial (Fin k) (A ⧸ I ^ 1))
    (p : MvPolynomial (Fin k) A) {x : B}
    (hx : e.symm (MvPolynomial.map (Ideal.Quotient.mk (I ^ 1)) p) = Ideal.Quotient.mk (K ^ 1) x) :
    (quotientOneEquivOfPow e).symm (MvPolynomial.map (Ideal.Quotient.mk I) p) =
      Ideal.Quotient.mk K x := by
  simp [quotientOneEquivOfPow, MvPolynomial.map_map, Ideal.Quotient.factor_comp_mk, hx]

omit [TopologicalSpace A] [NonarchimedeanRing A] in
private theorem quotientOneEquivOfPow_symm_X {B : Type*} [CommRing B] [Algebra A B]
    {K : Ideal B} (e : (B ⧸ K ^ 1) ≃ₐ[A] MvPolynomial (Fin k) (A ⧸ I ^ 1)) (i : Fin k) {x : B}
    (hx : e.symm (MvPolynomial.X i) = Ideal.Quotient.mk (K ^ 1) x) :
    (quotientOneEquivOfPow e).symm (MvPolynomial.X i) = Ideal.Quotient.mk K x := by
  simp [quotientOneEquivOfPow, hx]

omit [TopologicalSpace A] [NonarchimedeanRing A] in
private theorem quotientOneEquivOfPow_symm_C_mk {B : Type*} [CommRing B] [Algebra A B]
    {K : Ideal B} (e : (B ⧸ K ^ 1) ≃ₐ[A] MvPolynomial (Fin k) (A ⧸ I ^ 1)) (a : A)
    (ha : e.symm (MvPolynomial.C (Ideal.Quotient.mk (I ^ 1) a)) = algebraMap A _ a) :
    (quotientOneEquivOfPow e).symm (MvPolynomial.C (Ideal.Quotient.mk I a)) = algebraMap A _ a := by
  simp [quotientOneEquivOfPow, ha]

/-- Reduction modulo a finitely generated ideal of definition has the extended ideal as kernel. -/
theorem ker_restrictedReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedReduction (k := k) I (pow_one I ▸ hI.isOpen_pow 1)) =
      I.map (weightedC _ isWeightFamily_one_weight) := by
  ext f
  rw [RingHom.mem_ker, Ideal.restrictedReduction_eq_zero_iff,
    mem_map_weightedC_iff_of_isAdic hI hfg]

/-- Reduction modulo `I ^ m` for a finitely generated ideal of definition has kernel
`(I · A⟨T⟩) ^ m`. -/
theorem ker_restrictedReduction_pow (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    RingHom.ker (restrictedReduction (k := k) (I ^ m) (hI.isOpen_pow m)) =
      I.map (WC k A) ^ m :=
  ker_pow_of_ker (WC k A) (fun J hJ ↦ restrictedReduction J hJ)
    (fun hJ hJfg ↦ ker_restrictedReduction hJ hJfg) hI hfg m

/-- Infinitesimal thickening of order `m` modulo `(I · A⟨T⟩) ^ m` gives `(A ⧸ I ^ m)[T]`. -/
noncomputable def quotientPowRestrictedEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    (WSub k A ⧸ I.map (WC k A) ^ m) ≃ₐ[A] MvPolynomial (Fin k) (A ⧸ I ^ m) :=
  quotientEquivOfReduction (restrictedReduction (I ^ m) (hI.isOpen_pow m))
    (fun a ↦ by simp [algebraMap_weightedRestrictedSubring])
    (ker_restrictedReduction_pow hI hfg m)
    (restrictedReduction_surjective (I ^ m) (hI.isOpen_pow m))

/-- On a represented series, the order-`m` quotient comparison computes reduction modulo `I ^ m`. -/
@[simp] theorem quotientPowRestrictedEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) (f : WSub k A) :
    quotientPowRestrictedEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ f) =
      restrictedReduction (I ^ m) (hI.isOpen_pow m) f :=
  quotientEquivOfReduction_mk ..

/-- `quotientPowRestrictedEquivMvPolynomialQuotient.symm` lifts `map (mk (I ^ m)) p` to `WPoly`. -/
@[simp] theorem quotientPowRestrictedEquivMvPolynomialQuotient_symm_map_mk
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) (p : MvPolynomial (Fin k) A) :
    (quotientPowRestrictedEquivMvPolynomialQuotient hI hfg m).symm
      (MvPolynomial.map (Ideal.Quotient.mk (I ^ m)) p) = Ideal.Quotient.mk _ (WPoly k A p) := by
  rw [AlgEquiv.symm_apply_eq]; simp

/-- `quotientPowRestrictedEquivMvPolynomialQuotient.symm` sends `X i` to the class of `WX i`. -/
@[simp] theorem quotientPowRestrictedEquivMvPolynomialQuotient_symm_X (hI : IsAdic I) (hfg : I.FG)
    (m : ℕ) (i : Fin k) :
    (quotientPowRestrictedEquivMvPolynomialQuotient hI hfg m).symm (MvPolynomial.X i) =
      Ideal.Quotient.mk _ (WX k A i) := by rw [AlgEquiv.symm_apply_eq]; simp

/-- `quotientPowRestrictedEquivMvPolynomialQuotient.symm` sends `C (mk (I ^ m) a)` to scalars. -/
@[simp] theorem quotientPowRestrictedEquivMvPolynomialQuotient_symm_C_mk (hI : IsAdic I)
    (hfg : I.FG) (m : ℕ) (a : A) :
    (quotientPowRestrictedEquivMvPolynomialQuotient (k := k) hI hfg m).symm
      (MvPolynomial.C (Ideal.Quotient.mk (I ^ m) a)) = algebraMap A _ a := by
  rw [AlgEquiv.symm_apply_eq, ← Ideal.Quotient.mk_algebraMap]; simp

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

/-- The infinitesimal reduction of restricted power series is a polynomial algebra. -/
noncomputable def quotientRestrictedEquivMvPolynomialQuotient (hI : IsAdic I) (hfg : I.FG) :
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
      I.map (weightedC _ isWeightFamily_one_weight)) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I) :=
  quotientOneEquivOfPow (quotientPowRestrictedEquivMvPolynomialQuotient hI hfg 1)

/-- Reduction of restricted power series modulo `(I · A⟨T⟩) ^ m` is `(A ⧸ I ^ m)[T]`. -/
noncomputable def quotientRestrictedPowEquivMvPolynomialQuotient (hI : IsAdic I) (hfg : I.FG)
    (m : ℕ) :
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
      I.map (weightedC _ isWeightFamily_one_weight) ^ m) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I ^ m) :=
  AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq
    (ker_restrictedReduction_pow (k := k) hI hfg m).symm).trans
    ((restrictedReduction (I ^ m) (hI.isOpen_pow m)).quotientKerEquivOfSurjective
      (restrictedReduction_surjective (I ^ m) (hI.isOpen_pow m)))) fun a ↦ by
    rw [← Ideal.Quotient.mk_algebraMap]; simp [algebraMap_weightedRestrictedSubring]

/-- On a represented series, `quotientRestrictedPowEquivMvPolynomialQuotient` computes its
polynomial reduction modulo `I ^ m`. -/
@[simp]
theorem quotientRestrictedPowEquivMvPolynomialQuotient_mk (hI : IsAdic I) (hfg : I.FG) (m : ℕ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    quotientRestrictedPowEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ f) =
      restrictedReduction (I ^ m) (hI.isOpen_pow m) f := by
  simp [quotientRestrictedPowEquivMvPolynomialQuotient]


/-- On a represented series the quotient comparison computes its polynomial reduction. -/
@[simp]
theorem quotientRestrictedEquivMvPolynomialQuotient_mk (hI : IsAdic I) (hfg : I.FG)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    quotientRestrictedEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ f) =
      restrictedReduction I (pow_one I ▸ hI.isOpen_pow 1) f := by
  rw [quotientRestrictedEquivMvPolynomialQuotient, quotientOneEquivOfPow_mk,
    quotientPowRestrictedEquivMvPolynomialQuotient_mk, map_restrictedReduction]

/-- `quotientRestrictedEquivMvPolynomialQuotient.symm` lifts a reduced polynomial to `WPoly`. -/
@[simp] theorem quotientRestrictedEquivMvPolynomialQuotient_symm_map_mk (hI : IsAdic I)
    (hfg : I.FG) (p : MvPolynomial (Fin k) A) :
    (quotientRestrictedEquivMvPolynomialQuotient hI hfg).symm
      (MvPolynomial.map (Ideal.Quotient.mk I) p) = Ideal.Quotient.mk _ (WPoly k A p) :=
  quotientOneEquivOfPow_symm_map_mk _ p
    (quotientPowRestrictedEquivMvPolynomialQuotient_symm_map_mk hI hfg 1 p)

/-- `quotientRestrictedEquivMvPolynomialQuotient.symm` sends `X i` to the class of `weightedX i`. -/
@[simp] theorem quotientRestrictedEquivMvPolynomialQuotient_symm_X (hI : IsAdic I) (hfg : I.FG)
    (i : Fin k) : (quotientRestrictedEquivMvPolynomialQuotient hI hfg).symm (MvPolynomial.X i) =
      Ideal.Quotient.mk _ (WX k A i) :=
  quotientOneEquivOfPow_symm_X _ i
    (quotientPowRestrictedEquivMvPolynomialQuotient_symm_X hI hfg 1 i)

/-- `quotientRestrictedEquivMvPolynomialQuotient.symm` sends `C (mk I a)` to `algebraMap A _ a`. -/
@[simp] theorem quotientRestrictedEquivMvPolynomialQuotient_symm_C_mk (hI : IsAdic I) (hfg : I.FG)
    (a : A) : (quotientRestrictedEquivMvPolynomialQuotient (k := k) hI hfg).symm
      (MvPolynomial.C (Ideal.Quotient.mk I a)) = algebraMap A _ a :=
  quotientOneEquivOfPow_symm_C_mk _ a
    (quotientPowRestrictedEquivMvPolynomialQuotient_symm_C_mk hI hfg 1 a)

/-- Completed reduction is compatible with passing to a larger open ideal. -/
@[simp] theorem map_restrictedCompletionReduction {J : Ideal A} (hJ : IsOpen (J : Set A))
    (hI : IsOpen (I : Set A)) (hJI : J ≤ I) (x : WComp k A) :
    MvPolynomial.map (Ideal.Quotient.factor hJI) (restrictedCompletionReduction J hJ x) =
      restrictedCompletionReduction I hI x := by
  have hfac : Ideal.quotientMap I (RingHom.id A) hJI = Ideal.Quotient.factor hJI :=
    RingHom.ext fun q ↦ by obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q; rfl
  simpa [hfac] using (restrictedCompletionReduction_weightedMapCompletion (φ := RingHom.id A)
    continuous_id hJ hI hJI x).symm

section EvalCompatibility

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [NonarchimedeanRing B] [CompleteSpace B] [T3Space B] {φ : A →+* B} {b : Fin k → B}

/-- **Polynomial reduction commutes with topological evaluation** modulo open ideals. -/
theorem mk_weightedEvalHom_eq_eval₂_restrictedReduction
    (hφ : ContinuousAt φ 0) (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b)
    {J : Ideal B} (hI : IsOpen (I : Set A)) (hJ : IsOpen (J : Set B)) (hIJ : I ≤ J.comap φ)
    (f : WSub k A) :
    Ideal.Quotient.mk J (weightedEvalHom isWeightFamily_one_weight hφ hb f) =
      (restrictedReduction I hI f).eval₂ (Ideal.quotientMap J φ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (b i)) := by
  let : DiscreteTopology (B ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  let ev := MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (fun i ↦ Ideal.Quotient.mk J (b i))
  exact congr($(weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    (f := (Ideal.Quotient.mk J).comp (weightedEvalHom isWeightFamily_one_weight hφ hb))
    (g := ev.comp (restrictedReduction I hI))
    ((QuotientRing.isOpenQuotientMap_mk J).continuous.comp (continuous_weightedEvalHom _ hφ hb))
    (((I.isLocallyConstant_restrictedReduction hI).comp ev).continuous) (fun _ ↦ by simp [ev])
    (fun _ ↦ by simp [ev])) f)

/-- **Completed polynomial reduction commutes with completed topological evaluation** modulo open
ideals. -/
theorem mk_weightedEvalHomCompletion_eq_eval₂_restrictedCompletionReduction
    (hφ : ContinuousAt φ 0) (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b)
    {J : Ideal B} (hI : IsOpen (I : Set A)) (hJ : IsOpen (J : Set B)) (hIJ : I ≤ J.comap φ)
    (x : WComp k A) :
    Ideal.Quotient.mk J (weightedEvalHomCompletion isWeightFamily_one_weight hφ hb x) =
      (restrictedCompletionReduction I hI x).eval₂ (Ideal.quotientMap J φ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (b i)) := by
  let : DiscreteTopology (B ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    ((QuotientRing.isOpenQuotientMap_mk J).continuous.comp
      (continuous_weightedEvalHomCompletion _ hφ hb))
    (((I.isLocallyConstant_restrictedCompletionReduction hI).comp
      (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (b i)))).continuous)) fun f ↦ ?_
  rw [weightedEvalHomCompletion_coe, Ideal.restrictedCompletionReduction_coe]
  exact mk_weightedEvalHom_eq_eval₂_restrictedReduction hφ hb hI hJ hIJ f

end EvalCompatibility

/-- Completed reduction modulo a finitely generated ideal of definition has kernel `I · A⟨T⟩`. -/
theorem ker_restrictedCompletionReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedCompletionReduction (k := k) I (pow_one I ▸ hI.isOpen_pow 1)) =
      I.map (algebraMap A (WComp k A)) := by
  let K : Ideal (WComp k A) := I.map (algebraMap A (WComp k A))
  have hIopen : IsOpen (I : Set A) := pow_one I ▸ hI.isOpen_pow 1
  have hKopen : IsOpen (K : Set (WComp k A)) :=
    pow_one K ▸ (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg).isOpen_pow 1
  have hKle : K ≤ RingHom.ker (restrictedCompletionReduction (k := k) I hIopen) :=
    Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
      rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.restrictedCompletionReduction_algebraMap,
        Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  refine le_antisymm (fun x hx ↦ ?_) hKle
  obtain ⟨f, hfx⟩ := UniformSpace.Completion.denseRange_coe.exists_mem_open
    (hKopen.preimage (f := (· - x)) (continuous_id.sub continuous_const)) ⟨x, by simp⟩
  have hfker : f ∈ I.map (WC k A) := by
    rw [← ker_restrictedReduction hI hfg, RingHom.mem_ker]
    have hsub : restrictedCompletionReduction I hIopen ((f : WComp k A) - x) = 0 := hKle hfx
    rwa [map_sub, Ideal.restrictedCompletionReduction_coe, RingHom.mem_ker.mp hx, sub_zero] at hsub
  have hmapK : (I.map (WC k A)).map UniformSpace.Completion.coeRingHom = K := by
    rw [Ideal.map_map]
    exact congrArg (Ideal.map · I) (RingHom.ext fun _ ↦ by simp)
  have hfK : (f : WComp k A) ∈ K := by
    rw [← hmapK]
    exact Ideal.mem_map_of_mem UniformSpace.Completion.coeRingHom hfker
  simpa only [Set.mem_preimage, SetLike.mem_coe, sub_sub_cancel] using K.sub_mem hfK hfx

/-- Completed reduction modulo `I ^ m` for a finitely generated ideal of definition has kernel
`(I · A⟨T⟩) ^ m`. -/
theorem ker_restrictedCompletionReduction_pow (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    RingHom.ker (restrictedCompletionReduction (k := k) (I ^ m) (hI.isOpen_pow m)) =
      I.map (algebraMap A (WComp k A)) ^ m :=
  ker_pow_of_ker (algebraMap A (WComp k A)) (fun J hJ ↦ restrictedCompletionReduction J hJ)
    (fun hJ hJfg ↦ ker_restrictedCompletionReduction hJ hJfg) hI hfg m

/-- Infinitesimal thickening of order `m` on the completed carrier modulo `(I · A⟨T⟩) ^ m`. -/
noncomputable def quotientPowRestrictedCompletionEquivMvPolynomialQuotient (hI : IsAdic I)
    (hfg : I.FG) (m : ℕ) :
    (WComp k A ⧸ I.map (algebraMap A (WComp k A)) ^ m) ≃ₐ[A] MvPolynomial (Fin k) (A ⧸ I ^ m) :=
  quotientEquivOfReduction (restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m))
    (Ideal.restrictedCompletionReduction_algebraMap (I ^ m) (hI.isOpen_pow m))
    (ker_restrictedCompletionReduction_pow hI hfg m)
    (Ideal.restrictedCompletionReduction_surjective (I ^ m) (hI.isOpen_pow m))

/-- The order-`m` comparison computes completed polynomial reduction modulo `I ^ m`. -/
@[simp] theorem quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk (hI : IsAdic I)
    (hfg : I.FG) (m : ℕ) (x : WComp k A) :
    quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ x) =
      restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m) x :=
  quotientEquivOfReduction_mk ..

/-- `quotientPowRestrictedCompletionEquivMvPolynomialQuotient.symm` lifts `map (mk (I ^ m)) p`. -/
@[simp] theorem quotientPowRestrictedCompletionEquivMvPolynomialQuotient_symm_map_mk (hI : IsAdic I)
    (hfg : I.FG) (m : ℕ) (p : MvPolynomial (Fin k) A) :
    (quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg m).symm
      (MvPolynomial.map (Ideal.Quotient.mk (I ^ m)) p) =
      Ideal.Quotient.mk _ ((WPoly k A p : WSub k A) : WComp k A) := by
  rw [AlgEquiv.symm_apply_eq]; simp

/-- `quotientPowRestrictedCompletionEquivMvPolynomialQuotient.symm` sends `X i` to `weightedX i`. -/
@[simp] theorem quotientPowRestrictedCompletionEquivMvPolynomialQuotient_symm_X (hI : IsAdic I)
    (hfg : I.FG) (m : ℕ) (i : Fin k) :
    (quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg m).symm (MvPolynomial.X i) =
      Ideal.Quotient.mk _ ((WX k A i : WSub k A) : WComp k A) := by
  rw [AlgEquiv.symm_apply_eq]; simp

/-- The inverse of the order-`m` completed comparison sends `C (mk (I ^ m) a)` to scalars. -/
@[simp] theorem quotientPowRestrictedCompletionEquivMvPolynomialQuotient_symm_C_mk (hI : IsAdic I)
    (hfg : I.FG) (m : ℕ) (a : A) :
    (quotientPowRestrictedCompletionEquivMvPolynomialQuotient (k := k) hI hfg m).symm
      (MvPolynomial.C (Ideal.Quotient.mk (I ^ m) a)) = algebraMap A _ a := by
  rw [AlgEquiv.symm_apply_eq, ← Ideal.Quotient.mk_algebraMap]; simp [-Ideal.Quotient.mk_algebraMap]

/-- Reduction modulo `(I · A⟨T⟩) ^ m` of the completed restricted-series algebra is
`(A ⧸ I ^ m)[T]`, with no completeness or separation assumption on `A`. -/
noncomputable def quotientRestrictedCompletionPowEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    (restrictedMvPowerSeriesCompletion k A ⧸
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) ^ m) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I ^ m) :=
  AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq
    (ker_restrictedCompletionReduction_pow (k := k) hI hfg m).symm).trans
    ((restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m)).quotientKerEquivOfSurjective
      (Ideal.restrictedCompletionReduction_surjective (I ^ m) (hI.isOpen_pow m)))) fun a ↦ by
    rw [← Ideal.Quotient.mk_algebraMap]; simp

/-- On a represented completion element,
`quotientRestrictedCompletionPowEquivMvPolynomialQuotient` computes its completed reduction. -/
@[simp]
theorem quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) (x : restrictedMvPowerSeriesCompletion k A) :
    quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ x) =
      restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m) x := by
  simp [quotientRestrictedCompletionPowEquivMvPolynomialQuotient]

/-- Reduction modulo a finitely generated ideal of definition of the completed restricted-series
algebra is `(A ⧸ I)[T]`, with no completeness or separation assumption on `A`. -/
noncomputable def quotientRestrictedCompletionEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) :
    (WComp k A ⧸ I.map (algebraMap A (WComp k A))) ≃ₐ[A] MvPolynomial (Fin k) (A ⧸ I) :=
  quotientOneEquivOfPow (quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg 1)

/-- On a completion element, the quotient comparison computes completed reduction modulo `I`. -/
@[simp] theorem quotientRestrictedCompletionEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) (x : WComp k A) :
    quotientRestrictedCompletionEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ x) =
      restrictedCompletionReduction I (pow_one I ▸ hI.isOpen_pow 1) x := by
  rw [quotientRestrictedCompletionEquivMvPolynomialQuotient, quotientOneEquivOfPow_mk,
    quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk, map_restrictedCompletionReduction]

/-- `quotientRestrictedCompletionEquivMvPolynomialQuotient.symm` lifts a reduced polynomial. -/
@[simp] theorem quotientRestrictedCompletionEquivMvPolynomialQuotient_symm_map_mk
    (hI : IsAdic I) (hfg : I.FG) (p : MvPolynomial (Fin k) A) :
    (quotientRestrictedCompletionEquivMvPolynomialQuotient hI hfg).symm
      (MvPolynomial.map (Ideal.Quotient.mk I) p) =
      Ideal.Quotient.mk _ ((WPoly k A p : WSub k A) : WComp k A) :=
  quotientOneEquivOfPow_symm_map_mk _ p
    (quotientPowRestrictedCompletionEquivMvPolynomialQuotient_symm_map_mk hI hfg 1 p)

/-- `quotientRestrictedCompletionEquivMvPolynomialQuotient.symm` sends `X i` to `weightedX i`. -/
@[simp] theorem quotientRestrictedCompletionEquivMvPolynomialQuotient_symm_X (hI : IsAdic I)
    (hfg : I.FG) (i : Fin k) :
    (quotientRestrictedCompletionEquivMvPolynomialQuotient hI hfg).symm (MvPolynomial.X i) =
      Ideal.Quotient.mk _ ((WX k A i : WSub k A) : WComp k A) :=
  quotientOneEquivOfPow_symm_X _ i
    (quotientPowRestrictedCompletionEquivMvPolynomialQuotient_symm_X hI hfg 1 i)

/-- `quotientRestrictedCompletionEquivMvPolynomialQuotient.symm` sends `C (mk I a)` to scalars. -/
@[simp] theorem quotientRestrictedCompletionEquivMvPolynomialQuotient_symm_C_mk (hI : IsAdic I)
    (hfg : I.FG) (a : A) :
    (quotientRestrictedCompletionEquivMvPolynomialQuotient (k := k) hI hfg).symm
      (MvPolynomial.C (Ideal.Quotient.mk I a)) = algebraMap A _ a :=
  quotientOneEquivOfPow_symm_C_mk _ a
    (quotientPowRestrictedCompletionEquivMvPolynomialQuotient_symm_C_mk hI hfg 1 a)

private noncomputable def weightedPolynomialAlgHom : MvPolynomial (Fin k) A →ₐ[A] WSub k A :=
  { WPoly k A with commutes' a := by simp [algebraMap_weightedRestrictedSubring] }

private theorem map_weightedPolynomialAlgHom_le (I : Ideal A) :
    I.map (MvPolynomial.C (σ := Fin k)) ≤
      (I.map (algebraMap A (WSub k A))).comap (weightedPolynomialAlgHom (k := k) (A := A)) :=
  Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
    rw [← MvPolynomial.algebraMap_eq]
    simpa only [Ideal.mem_comap, AlgHom.coe_ofClass, AlgHom.commutes] using
      Ideal.mem_map_of_mem _ ha

private theorem bijective_mapₐ_weightedPolynomialAlgHom (hI : IsAdic I) (hfg : I.FG) :
    Function.Bijective (AdicCompletion.mapₐ (weightedPolynomialAlgHom (k := k) (A := A))
      (map_weightedPolynomialAlgHom_le I)) := by
  refine AdicCompletion.mapₐ_bijective _ _ fun n ↦ ?_
  let e₁ := (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).toRingEquiv.trans
    (Ideal.quotEquivOfEq (Ideal.map_pow (MvPolynomial.C (σ := Fin k)) I n))
  have halg : I.map (algebraMap A (WSub k A)) ^ n = I.map (WC k A) ^ n := by
    rw [algebraMap_weightedRestrictedSubring]
  let e₂ := (Ideal.quotEquivOfEq halg).trans
    (quotientPowRestrictedEquivMvPolynomialQuotient (k := k) hI hfg n).toRingEquiv
  let qmap := Ideal.quotientMap _ (weightedPolynomialAlgHom (k := k) (A := A)).toRingHom
    ((Ideal.pow_right_mono (map_weightedPolynomialAlgHom_le I) n).trans (Ideal.le_comap_pow _ n))
  have hcomp : (e₂ ∘ (qmap ∘ e₁)) = id := funext fun q ↦ by
    obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective q
    simp [Function.comp_apply, e₁, qmap, e₂, weightedPolynomialAlgHom]
  exact (e₁.bijective.of_comp_iff qmap).mp
    ((e₂.bijective.of_comp_iff' (qmap ∘ e₁)).mp (hcomp.symm ▸ Function.bijective_id))

/-- **Inverse-limit description of completed restricted power series** (EGA I, Ch. 0, §7.5.1). -/
noncomputable def restrictedMvPowerSeriesCompletionEquivAdicCompletion
    (hI : IsAdic I) (hfg : I.FG) :
    WComp k A ≃ₐ[A] AdicCompletion (I.map (MvPolynomial.C (σ := Fin k))) (MvPolynomial (Fin k) A) :=
  let hAdic := isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg
  (AlgEquiv.ofRingEquiv (f := hAdic.completionEquivAdicCompletion (hfg.map _)) fun a ↦ by
    rw [algebraMap_completion_weightedRestrictedSubring_apply,
      IsAdic.completionEquivAdicCompletion_coe, ← algebraMap_weightedRestrictedSubring,
      ← IsScalarTower.algebraMap_apply]).trans
    (AlgEquiv.ofBijective (AdicCompletion.mapₐ (weightedPolynomialAlgHom (k := k) (A := A))
      (map_weightedPolynomialAlgHom_le I)) (bijective_mapₐ_weightedPolynomialAlgHom hI hfg)).symm

/-- On embedded polynomials, `restrictedMvPowerSeriesCompletionEquivAdicCompletion` is
`algebraMap`. -/
@[simp] theorem restrictedMvPowerSeriesCompletionEquivAdicCompletion_weightedPolynomialHom
    (hI : IsAdic I) (hfg : I.FG) (p : MvPolynomial (Fin k) A) :
    restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg
      ((WPoly k A p : WSub k A) : WComp k A) = algebraMap (MvPolynomial (Fin k) A) _ p := by
  let ePoly := AlgEquiv.ofBijective
    (AdicCompletion.mapₐ (weightedPolynomialAlgHom (k := k) (A := A))
      (map_weightedPolynomialAlgHom_le I)) (bijective_mapₐ_weightedPolynomialAlgHom hI hfg)
  apply ePoly.injective; dsimp only [restrictedMvPowerSeriesCompletionEquivAdicCompletion]
  rw [AlgEquiv.trans_apply, ePoly.apply_symm_apply, AlgEquiv.ofRingEquiv_apply,
    IsAdic.completionEquivAdicCompletion_coe]
  simp [ePoly, AdicCompletion.algebraMap_apply, weightedPolynomialAlgHom]

/-- `restrictedMvPowerSeriesCompletionEquivAdicCompletion` sends `weightedX i` to `X i`. -/
@[simp] theorem restrictedMvPowerSeriesCompletionEquivAdicCompletion_weightedX
    (hI : IsAdic I) (hfg : I.FG) (i : Fin k) :
    restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg
      ((WX k A i : WSub k A) : WComp k A) =
      algebraMap (MvPolynomial (Fin k) A) _ (MvPolynomial.X i) := by
  simpa using restrictedMvPowerSeriesCompletionEquivAdicCompletion_weightedPolynomialHom hI hfg
    (MvPolynomial.X i)

/-- `restrictedMvPowerSeriesCompletionEquivAdicCompletion.symm` embeds polynomials via `WPoly`. -/
@[simp] theorem restrictedMvPowerSeriesCompletionEquivAdicCompletion_symm_algebraMap
    (hI : IsAdic I) (hfg : I.FG) (p : MvPolynomial (Fin k) A) :
    (restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg).symm
      (algebraMap (MvPolynomial (Fin k) A) _ p) = ((WPoly k A p : WSub k A) : WComp k A) := by
  rw [AlgEquiv.symm_apply_eq,
    restrictedMvPowerSeriesCompletionEquivAdicCompletion_weightedPolynomialHom]

/-- `restrictedMvPowerSeriesCompletionEquivAdicCompletion` is a homeomorphism for the adic topology
on `AdicCompletion`. -/
theorem isHomeomorph_restrictedMvPowerSeriesCompletionEquivAdicCompletion
    (hI : IsAdic I) (hfg : I.FG) :
    @IsHomeomorph _ _ _ ((I.map (MvPolynomial.C (σ := Fin k))).map (algebraMap _ _)).adicTopology
      (restrictedMvPowerSeriesCompletionEquivAdicCompletion (k := k) hI hfg) := by
  let P := MvPolynomial (Fin k) A; let IP : Ideal P := I.map MvPolynomial.C
  let C := AdicCompletion IP P; let : WithIdeal C := ⟨IP.map (algebraMap P C)⟩
  have hAdicB := isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg
  have hIP : IP.map (algebraMap P C) = I.map (algebraMap A C) :=
    calc IP.map (algebraMap P C)
        = (I.map (algebraMap A P)).map (algebraMap P C) :=
          congrArg (Ideal.map (algebraMap P C)) (by simp only [IP, P, MvPolynomial.algebraMap_eq])
      _ = I.map (algebraMap A C) := Ideal.map_algebraMap_map_algebraMap I
  have hAdicC : IsAdic (I.map (algebraMap A C)) := hIP ▸ (rfl : IsAdic (IP.map (algebraMap P C)))
  let e := restrictedMvPowerSeriesCompletionEquivAdicCompletion (k := k) hI hfg
  have he : (I.map (algebraMap A _)).map e.toRingHom = I.map (algebraMap A C) := by
    rw [Ideal.map_map]; exact congrArg (Ideal.map · I) (RingHom.ext e.commutes)
  have hesymm : (I.map (algebraMap A C)).map e.symm.toRingHom = I.map (algebraMap A _) := by
    rw [Ideal.map_map]; exact congrArg (Ideal.map · I) (RingHom.ext e.symm.commutes)
  exact e.toEquiv.isHomeomorph_iff.mpr
    ⟨hAdicB.continuous_of_map_le_radical hAdicC (hfg.map _) (he.le.trans Ideal.le_radical),
     hAdicC.continuous_of_map_le_radical hAdicB (hfg.map _) (hesymm.le.trans Ideal.le_radical)⟩

/-- Under `restrictedMvPowerSeriesCompletionEquivAdicCompletion`, `evalₐ _ m` computes completed
polynomial reduction modulo `I ^ m`. -/
theorem evalₐ_restrictedMvPowerSeriesCompletionEquivAdicCompletion
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) (x : WComp k A) :
    AdicCompletion.evalₐ _ m (restrictedMvPowerSeriesCompletionEquivAdicCompletion hI hfg x) =
      Ideal.quotEquivOfEq (Ideal.map_pow (MvPolynomial.C (σ := Fin k)) I m)
        (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ m)
          (restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m) x)) := by
  let P := MvPolynomial (Fin k) A; let IP : Ideal P := I.map MvPolynomial.C
  let e := restrictedMvPowerSeriesCompletionEquivAdicCompletion (k := k) hI hfg
  -- Approximate `e x` modulo `(I · A[T]) ^ m` by a polynomial `p`, so `evalₐ m (e x) = mk p`.
  -- Pulling back along `e.symm` puts `x - p` in `(I · A⟨T⟩) ^ m = ker (red mod I ^ m)`,
  -- identifying the reduction of `x` modulo `I ^ m` with `p.map (mk (I ^ m))`.
  obtain ⟨p, hp⟩ := AdicCompletion.exists_sub_algebraMap_mem_map_pow (I := IP) (hfg.map _) m (e x)
  have heval : AdicCompletion.evalₐ IP m (e x) = Ideal.Quotient.mk (IP ^ m) p := by
    have hker := (AdicCompletion.ker_evalₐ_eq_map_pow (R := P) (I := IP) (hfg.map _) m).symm ▸ hp
    simpa [sub_eq_zero, AdicCompletion.algebraMap_apply] using RingHom.mem_ker.mp hker
  have hIP : IP.map (algebraMap P (AdicCompletion IP P)) =
      I.map (algebraMap A (AdicCompletion IP P)) :=
    calc IP.map (algebraMap P (AdicCompletion IP P))
        = (I.map (algebraMap A P)).map (algebraMap P (AdicCompletion IP P)) :=
          congrArg (Ideal.map (algebraMap P (AdicCompletion IP P)))
            (by simp only [IP, P, MvPolynomial.algebraMap_eq])
      _ = I.map (algebraMap A (AdicCompletion IP P)) := Ideal.map_algebraMap_map_algebraMap I
  have hmap : ((IP ^ m).map (algebraMap P (AdicCompletion IP P))).map e.symm.toRingHom =
      I.map (algebraMap A (WComp k A)) ^ m := by
    rw [Ideal.map_pow, Ideal.map_pow, hIP, Ideal.map_map]
    exact congrArg (fun f ↦ I.map f ^ m) (RingHom.ext e.symm.commutes)
  have hmem : e.symm (e x - algebraMap P (AdicCompletion IP P) p) ∈
      RingHom.ker (restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m)) := by
    rw [ker_restrictedCompletionReduction_pow hI hfg m, ← hmap]
    exact Ideal.mem_map_of_mem e.symm.toRingHom hp
  have hx0 := RingHom.mem_ker.mp hmem
  dsimp only [P, IP, e] at hx0
  rw [map_sub, AlgEquiv.symm_apply_apply,
    restrictedMvPowerSeriesCompletionEquivAdicCompletion_symm_algebraMap, map_sub,
    Ideal.restrictedCompletionReduction_coe, Ideal.restrictedReduction_weightedPolynomialHom,
    sub_eq_zero] at hx0
  rw [heval, hx0, MvPolynomial.quotientEquivQuotientMvPolynomial_map_mk, Ideal.quotEquivOfEq_mk]

section Completion

variable [CompleteSpace (WSub k A)] [T0Space (WSub k A)] {J : Ideal A}

/-- When `WSub k A` is complete and separated, completed reduction agrees with uncompleted reduction
through `restrictedMvPowerSeriesCompletionEquiv`. -/
theorem restrictedCompletionReduction_eq_restrictedReduction
    (hJ : IsOpen (J : Set A)) (x : WComp k A) :
    restrictedCompletionReduction J hJ x =
      restrictedReduction J hJ (restrictedMvPowerSeriesCompletionEquiv k A x) := by
  conv_lhs => rw [← (restrictedMvPowerSeriesCompletionEquiv k A).symm_apply_apply x]
  rw [restrictedMvPowerSeriesCompletionEquiv_symm_apply, Ideal.restrictedCompletionReduction_coe]

end Completion

/-- Over an `I`-adically separated ring carrying the `I`-adic topology, a restricted power series is
uniquely determined by its polynomial reductions modulo `I ^ (m + 1)`. -/
theorem restrictedReduction_pow_succ_injective (hI : IsAdic I) [IsHausdorff I A] :
    Function.Injective (fun (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight) (m : ℕ) ↦
      restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1)) f) := fun _ _ hfg ↦ by
  apply Subtype.ext; ext ν
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun m ↦
    SModEq.mono (Submodule.pow_smul_top_le I A m.le_succ) ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  exact Ideal.Quotient.eq.mp <| by
    simpa only [Ideal.coeff_restrictedReduction] using
      congrArg (fun p : MvPolynomial (Fin k) _ ↦ p.coeff ν) (congrFun hfg m)

/-- **Inverse-limit characterisation of adic restricted power series** (EGA I, Ch. 0, §7.5.1):
over an `I`-adically complete ring carrying the `I`-adic topology (without `I.FG`), every
compatible sequence in `(A ⧸ I ^ (m + 1))[X₁, …, Xₖ]` is the reduction sequence of a unique
series in `A⟨X₁, …, Xₖ⟩`. -/
theorem existsUnique_restrictedReduction_pow_succ_eq (hI : IsAdic I) [IsAdicComplete I A]
    (p : ∀ m : ℕ, MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hp : ∀ m : ℕ, MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ)) (p (m + 1)) = p m) :
    ∃! f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight,
      ∀ m : ℕ, restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1)) f = p m := by
  let ev (ν : Fin k →₀ ℕ) (m : ℕ) :=
    MvPolynomial.eval₂Hom (Int.castRingHom _) fun _ : Unit ↦ (p m).coeff ν
  have compat (ν : Fin k →₀ ℕ) {m : ℕ} :
      (Ideal.Quotient.factorPow I (StrictMono.monotone (f := (· + 1))
        (strictMono_id.add_const 1) m.le_succ)).comp (ev ν (m + 1)) = ev ν m :=
    MvPolynomial.ringHom_ext (fun z ↦ by simp [ev]) fun _ ↦ by
      simpa [ev, MvPolynomial.coeff_map] using
        congrArg (fun q : MvPolynomial (Fin k) _ ↦ q.coeff ν) (hp m)
  let F : MvPowerSeries (Fin k) A := fun ν ↦
    IsAdicComplete.StrictMono.liftRingHom (a := (· + 1)) I (strictMono_id.add_const 1)
      (ev ν) (fun {m} ↦ compat ν) (MvPolynomial.X ())
  have hc (ν : Fin k →₀ ℕ) (m : ℕ) : Ideal.Quotient.mk (I ^ (m + 1)) (F ν) = (p m).coeff ν := by
    simpa only [F, ev, MvPolynomial.eval₂Hom_X'] using
      IsAdicComplete.StrictMono.mk_liftRingHom (a := (· + 1)) (n := m) I
        (strictMono_id.add_const 1) (ev ν) (fun {m} ↦ compat ν) (MvPolynomial.X ())
  have hF : IsWeightedRestricted (fun _ : Fin k ↦ ({1} : Set A)) F := by
    refine isWeightedRestricted_iff.mpr fun U ↦ ?_
    obtain ⟨n, -, hn⟩ := hI.hasBasis_nhds_zero.mem_iff.mp (U.isOpen.mem_nhds U.zero_mem)
    refine Filter.eventually_cofinite.mpr ((p n).support.finite_toSet.subset fun ν hν ↦ ?_)
    simp only [Set.mem_ofPred_eq, weightMul_one_weight] at hν
    exact Finset.mem_coe.mpr <| MvPolynomial.mem_support_iff.mpr fun hzero ↦ hν <|
      hn <| Ideal.pow_le_pow_right n.le_succ <| Ideal.Quotient.eq_zero_iff_mem.mp <|
        (congrArg _ (MvPowerSeries.coeff_apply F ν)).trans ((hc ν n).trans hzero)
  let f₀ : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
    ⟨F, mem_weightedRestrictedSubring.mpr hF⟩
  have hf₀ (m : ℕ) : restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1)) f₀ = p m := by
    ext ν; exact (Ideal.coeff_restrictedReduction _ _ f₀ ν).trans
      ((congrArg _ (MvPowerSeries.coeff_apply F ν)).trans (hc ν m))
  exact ⟨f₀, hf₀, fun g hg ↦ restrictedReduction_pow_succ_injective hI <|
    funext fun m ↦ (hg m).trans (hf₀ m).symm⟩

/-- **Universal property of adic restricted power series as the inverse limit of polynomial
reductions**, over an `I`-adically complete ring with the `I`-adic topology (without `I.FG`). -/
noncomputable def liftRestrictedReductionPowSucc {S : Type*} [NonAssocSemiring S] (hI : IsAdic I)
    [IsAdicComplete I A] (φ : ∀ m : ℕ, S →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ, (MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp (φ (m + 1)) = φ m) :
    S →+* weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight := by
  let liftElem (s : S) :=
    (existsUnique_restrictedReduction_pow_succ_eq hI (fun m ↦ φ m s)
      fun m ↦ RingHom.congr_fun (hφ m) s).choose
  have hlift (s : S) (m : ℕ) :
      restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1)) (liftElem s) = φ m s :=
    (existsUnique_restrictedReduction_pow_succ_eq hI (fun m ↦ φ m s)
      fun m ↦ RingHom.congr_fun (hφ m) s).choose_spec.1 m
  exact
    { toFun := liftElem
      map_one' := restrictedReduction_pow_succ_injective hI <| funext fun m ↦ by simp [hlift]
      map_mul' := fun _ _ ↦
        restrictedReduction_pow_succ_injective hI <| funext fun m ↦ by simp [hlift]
      map_zero' := restrictedReduction_pow_succ_injective hI <| funext fun m ↦ by simp [hlift]
      map_add' := fun _ _ ↦
        restrictedReduction_pow_succ_injective hI <| funext fun m ↦ by simp [hlift] }

/-- Reducing `liftRestrictedReductionPowSucc hI φ hφ s` modulo `I ^ (m + 1)` recovers `φ m s`. -/
@[simp]
theorem restrictedReduction_pow_succ_liftRestrictedReductionPowSucc {S : Type*}
    [NonAssocSemiring S] (hI : IsAdic I) [IsAdicComplete I A]
    (φ : ∀ m : ℕ, S →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ, (MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp (φ (m + 1)) = φ m)
    (m : ℕ) (s : S) :
    restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1))
        (liftRestrictedReductionPowSucc hI φ hφ s) = φ m s :=
  (existsUnique_restrictedReduction_pow_succ_eq hI (fun n ↦ φ n s)
    fun n ↦ RingHom.congr_fun (hφ n) s).choose_spec.1 m

/-- Uniqueness of `liftRestrictedReductionPowSucc`. -/
theorem eq_liftRestrictedReductionPowSucc {S : Type*} [NonAssocSemiring S] (hI : IsAdic I)
    [IsAdicComplete I A] (φ : ∀ m : ℕ, S →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ, (MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp (φ (m + 1)) = φ m)
    {ψ : S →+* weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight}
    (hψ : ∀ m : ℕ, (restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1))).comp ψ = φ m) :
    ψ = liftRestrictedReductionPowSucc hI φ hφ :=
  RingHom.ext fun s ↦ restrictedReduction_pow_succ_injective hI <| funext fun m ↦
    (RingHom.congr_fun (hψ m) s).trans
      (restrictedReduction_pow_succ_liftRestrictedReductionPowSucc hI φ hφ m s).symm

/-- On the completed restricted-series algebra for a finitely generated ideal of definition `I`
(with `A` not assumed complete or Hausdorff), elements are uniquely determined by their reductions
modulo `I ^ (m + 1)`. -/
theorem restrictedCompletionReduction_pow_succ_injective (hI : IsAdic I) (hfg : I.FG) :
    Function.Injective (fun (x : restrictedMvPowerSeriesCompletion k A) (m : ℕ) ↦
      restrictedCompletionReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1)) x) := fun _ _ hxy ↦ by
  let J := I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))
  have : IsAdicComplete J (restrictedMvPowerSeriesCompletion k A) :=
    (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg).isAdicComplete_iff.mpr
      ⟨inferInstance, inferInstance⟩
  refine (IsHausdorff.eq_iff_smodEq (I := J)).mpr fun m ↦
    SModEq.mono (Submodule.pow_smul_top_le J _ m.le_succ) ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  exact Ideal.Quotient.eq.mp <|
    (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg (m + 1)).injective <|
      by simpa [J] using congrFun hxy m

private theorem factorPow_quotientRestrictedCompletionPowEquiv_symm (hI : IsAdic I) (hfg : I.FG)
    (φ : ∀ m : ℕ, MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ, MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ)) (φ (m + 1)) = φ m)
    (m : ℕ) :
    Ideal.Quotient.factorPow (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
        (StrictMono.monotone (f := (· + 1)) (strictMono_id.add_const 1) m.le_succ)
        ((quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg (m + 2)).symm
          (φ (m + 1))) =
      (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg (m + 1)).symm
        (φ m) := by
  let e₁ := quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg (m + 1)
  let e₂ := quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg (m + 2)
  apply e₁.injective
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e₂.symm (φ (m + 1)))
  rw [← hx]
  simp only [e₁, Ideal.Quotient.factor_mk,
    quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk, AlgEquiv.apply_symm_apply,
    ← hφ m, ← map_restrictedCompletionReduction (hI.isOpen_pow (m + 2)) (hI.isOpen_pow (m + 1))
      (Ideal.pow_le_pow_right m.succ.le_succ) x]
  exact congrArg _ (by simpa [e₂] using congrArg e₂ hx)

/-- **Universal property of `restrictedMvPowerSeriesCompletion` as the inverse limit of polynomial
reductions**, for a finitely generated ideal of definition `I` (with no completeness or
Hausdorffness assumption on `A`). -/
noncomputable def liftRestrictedCompletionReductionPowSucc {S : Type*} [NonAssocSemiring S]
    (hI : IsAdic I) (hfg : I.FG) (φ : ∀ m : ℕ, S →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ, (MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp (φ (m + 1)) = φ m) :
    S →+* restrictedMvPowerSeriesCompletion k A :=
  letI : IsAdicComplete (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
      (restrictedMvPowerSeriesCompletion k A) :=
    (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg).isAdicComplete_iff.mpr
      ⟨inferInstance, inferInstance⟩
  IsAdicComplete.StrictMono.liftRingHom (a := (· + 1)) _ (strictMono_id.add_const 1)
    (fun m ↦ (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := k) hI hfg
      (m + 1)).symm.toRingHom.comp (φ m))
    (fun {m} ↦ RingHom.ext fun s ↦ factorPow_quotientRestrictedCompletionPowEquiv_symm hI hfg
      (fun n ↦ φ n s) (fun n ↦ RingHom.congr_fun (hφ n) s) m)

/-- Reducing `liftRestrictedCompletionReductionPowSucc hI hfg φ hφ s` modulo `I ^ (m + 1)` gives
`φ m s`. -/
@[simp]
theorem restrictedCompletionReduction_pow_succ_liftRestrictedCompletionReductionPowSucc
    {S : Type*} [NonAssocSemiring S] (hI : IsAdic I) (hfg : I.FG)
    (φ : ∀ m : ℕ, S →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ, (MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp (φ (m + 1)) = φ m)
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
    IsAdicComplete.StrictMono.mk_liftRingHom (a := (· + 1)) (n := m)
      (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))) (strictMono_id.add_const 1) _
      (fun {m} ↦ RingHom.ext fun t ↦ factorPow_quotientRestrictedCompletionPowEquiv_symm hI hfg
        (fun n ↦ φ n t) (fun n ↦ RingHom.congr_fun (hφ n) t) m) s
  simpa [e] using congrArg e hmk

/-- Uniqueness of `liftRestrictedCompletionReductionPowSucc`. -/
theorem eq_liftRestrictedCompletionReductionPowSucc {S : Type*} [NonAssocSemiring S]
    (hI : IsAdic I) (hfg : I.FG) (φ : ∀ m : ℕ, S →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hφ : ∀ m : ℕ, (MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp (φ (m + 1)) = φ m)
    {ψ : S →+* restrictedMvPowerSeriesCompletion k A}
    (hψ : ∀ m : ℕ,
      (restrictedCompletionReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1))).comp ψ = φ m) :
    ψ = liftRestrictedCompletionReductionPowSucc hI hfg φ hφ :=
  RingHom.ext fun s ↦ restrictedCompletionReduction_pow_succ_injective hI hfg <| funext fun m ↦
    (RingHom.congr_fun (hψ m) s).trans
      (restrictedCompletionReduction_pow_succ_liftRestrictedCompletionReductionPowSucc hI hfg φ hφ
        m s).symm

/-- **Inverse-limit characterisation of `restrictedMvPowerSeriesCompletion`** (EGA I, Ch. 0,
§7.5.1), for any finitely generated ideal of definition `I` (with `A` not assumed complete or
Hausdorff). -/
theorem existsUnique_restrictedCompletionReduction_pow_succ_eq (hI : IsAdic I) (hfg : I.FG)
    (p : ∀ m : ℕ, MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hp : ∀ m : ℕ, MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ)) (p (m + 1)) = p m) :
    ∃! x : restrictedMvPowerSeriesCompletion k A,
      ∀ m : ℕ, restrictedCompletionReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1)) x = p m := by
  let φ (m : ℕ) := MvPolynomial.eval₂Hom (Int.castRingHom _) fun _ : Unit ↦ p m
  have hφ (m : ℕ) : (MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))).comp (φ (m + 1)) = φ m :=
    MvPolynomial.ringHom_ext (fun z ↦ by simp [φ]) fun _ ↦ by simpa [φ] using hp m
  let x := liftRestrictedCompletionReductionPowSucc hI hfg φ hφ (MvPolynomial.X ())
  have hx (m : ℕ) :
      restrictedCompletionReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1)) x = p m := by
    simp [x, φ]
  exact ⟨x, hx, fun y hy ↦ restrictedCompletionReduction_pow_succ_injective hI hfg <|
    funext fun m ↦ (hy m).trans (hx m).symm⟩


end TauCeti.Huber
