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

Reduction of restricted power series modulo an open ideal is polynomial on both the uncompleted
subring (`Ideal.restrictedReduction`) and its separated completion
(`Ideal.restrictedCompletionReduction`), with no completeness or separation assumption on `A`.

For a finitely generated ideal of definition `I`, reduction modulo `I ^ m` has kernel
`(I · A⟨T⟩) ^ m`, giving `A⟨T⟩ ⧸ (I · A⟨T⟩) ^ m ≃ₐ[A] (A ⧸ I ^ m)[T]` on both carriers. Reduction
is functorial without flatness, commutes with evaluation, and yields the inverse-limit description
from compatible polynomial families modulo `I ^ (m + 1)`: on `weightedRestrictedSubring` under
`IsAdic I` and `[IsAdicComplete I A]` (without `I.FG`), and on `restrictedMvPowerSeriesCompletion`
under `IsAdic I` and `I.FG` (without completeness or Hausdorffness on `A`).

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

/-- Reduction of completed restricted series modulo an open ideal `J`, defined via
`UniformSpace.Completion` into the discrete complete Hausdorff ring over `A ⧸ J` with no
completeness or separation assumption on `A`. -/
noncomputable def restrictedCompletionReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    restrictedMvPowerSeriesCompletion k A →+* MvPolynomial (Fin k) (A ⧸ J) := by
  letI : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  haveI : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  haveI : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := IsRightUniformAddGroup.discreteUniformity
  have hmk := (QuotientRing.isOpenQuotientMap_mk J).continuous
  exact (weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).symm.toRingHom.comp
    (Completion.extensionHom
      (weightedMap hmk isWeightFamily_one_weight isWeightFamily_one_weight (by simp))
      (continuous_weightedMap hmk isWeightFamily_one_weight isWeightFamily_one_weight (by simp)))

/-- On the uncompleted subring, `restrictedCompletionReduction` agrees with
`restrictedReduction`. -/
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

/-- Completed reduction sends a constant series from `A` to the constant polynomial over `A ⧸ J`. -/
theorem restrictedCompletionReduction_algebraMap (J : Ideal A) (hJ : IsOpen (J : Set A)) (a : A) :
    restrictedCompletionReduction (k := k) J hJ
        (algebraMap A (restrictedMvPowerSeriesCompletion k A) a) =
      MvPolynomial.C (Ideal.Quotient.mk J a) := by
  simp [algebraMap_completion_weightedRestrictedSubring_apply]

/-- Completed reduction preserves the coordinate variables. -/
theorem restrictedCompletionReduction_weightedX (J : Ideal A) (hJ : IsOpen (J : Set A))
    (i : Fin k) :
    restrictedCompletionReduction J hJ
        ((weightedX _ isWeightFamily_one_weight i :
          weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion k A) = MvPolynomial.X i := by
  simp

/-- Completed polynomial reduction is surjective. -/
theorem restrictedCompletionReduction_surjective (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    Function.Surjective (restrictedCompletionReduction (k := k) J hJ) := fun p ↦
  let ⟨f, hf⟩ := restrictedReduction_surjective (k := k) J hJ p
  ⟨f, (restrictedCompletionReduction_coe J hJ f).trans hf⟩

/-- Precomposing any map with `restrictedCompletionReduction J hJ` is continuous. -/
theorem continuous_comp_restrictedCompletionReduction {X : Type*} [TopologicalSpace X]
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (g : MvPolynomial (Fin k) (A ⧸ J) → X) :
    Continuous (g ∘ restrictedCompletionReduction (k := k) J hJ) := by
  let : DiscreteTopology (A ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  have : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set (A ⧸ J)))
      isWeightFamily_one_weight) := IsRightUniformAddGroup.discreteUniformity
  exact (continuous_of_discreteTopology (f := fun y ↦
    g ((weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).symm y))).comp
    Completion.continuous_extension

/-- The kernel of `restrictedCompletionReduction` is an open ideal. -/
theorem isOpen_ker_restrictedCompletionReduction (J : Ideal A) (hJ : IsOpen (J : Set A)) :
    IsOpen (RingHom.ker (restrictedCompletionReduction (k := k) J hJ) :
      Set (restrictedMvPowerSeriesCompletion k A)) := by
  let : TopologicalSpace (MvPolynomial (Fin k) (A ⧸ J)) := ⊥
  have : DiscreteTopology (MvPolynomial (Fin k) (A ⧸ J)) := ⟨rfl⟩
  exact (isOpen_discrete ({0} : Set _)).preimage
    (continuous_comp_restrictedCompletionReduction J hJ id)

/-- When the uncompleted restricted-series subring is complete and separated (`T0Space`),
`restrictedCompletionReduction` agrees with `restrictedReduction` across
`restrictedMvPowerSeriesCompletionAlgEquiv`. -/
theorem restrictedCompletionReduction_eq_restrictedReduction
    [CompleteSpace (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight)]
    [T0Space (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)]
    (J : Ideal A) (hJ : IsOpen (J : Set A)) (x : restrictedMvPowerSeriesCompletion k A) :
    restrictedCompletionReduction J hJ x =
      restrictedReduction J hJ (restrictedMvPowerSeriesCompletionAlgEquiv k A x) := by
  rw [coe_restrictedMvPowerSeriesCompletionAlgEquiv]
  let : TopologicalSpace (MvPolynomial (Fin k) (A ⧸ J)) := ⊥
  have : DiscreteTopology (MvPolynomial (Fin k) (A ⧸ J)) := ⟨rfl⟩
  exact RingHom.congr_fun (completion_weightedRestrictedSubring_ringHom_ext_of_continuous
    isWeightFamily_one_weight (g := (restrictedReduction J hJ).comp
      (restrictedMvPowerSeriesCompletionEquiv k A).toRingHom)
    (continuous_comp_restrictedCompletionReduction J hJ id)
    ((continuous_comp_restrictedReduction J hJ id).comp
      uniformContinuous_restrictedMvPowerSeriesCompletionEquiv.continuous)
    (fun a ↦ by simp) (fun i ↦ by simp)) x

end Ideal

namespace TauCeti.Huber

open Ideal (restrictedReduction restrictedReduction_surjective mem_ker_restrictedReduction
  continuous_comp_restrictedReduction restrictedCompletionReduction
  restrictedCompletionReduction_coe restrictedCompletionReduction_algebraMap
  restrictedCompletionReduction_surjective continuous_comp_restrictedCompletionReduction)

/-- **Functoriality of polynomial reduction in the coefficient ring**, with no flatness needed. -/
theorem restrictedReduction_weightedMap {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ) (I : Ideal A)
    (hI : IsOpen (I : Set A)) (J : Ideal B) (hJ : IsOpen (J : Set B)) (hIJ : I ≤ J.comap φ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    restrictedReduction J hJ
        (weightedMap hφ isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (restrictedReduction I hI f) := by
  ext ν; simp [MvPolynomial.coeff_map]

/-- Completed reduction is compatible with passing to a larger open ideal. -/
@[simp]
theorem map_restrictedCompletionReduction {J : Ideal A} (hJ : IsOpen (J : Set A))
    (hI : IsOpen (I : Set A)) (hJI : J ≤ I) (x : restrictedMvPowerSeriesCompletion k A) :
    MvPolynomial.map (Ideal.Quotient.factor hJI) (restrictedCompletionReduction J hJ x) =
      restrictedCompletionReduction I hI x := by
  let : TopologicalSpace (MvPolynomial (Fin k) (A ⧸ I)) := ⊥
  have : DiscreteTopology (MvPolynomial (Fin k) (A ⧸ I)) := ⟨rfl⟩
  exact RingHom.congr_fun (completion_weightedRestrictedSubring_ringHom_ext_of_continuous
    isWeightFamily_one_weight
    (f := (MvPolynomial.map (Ideal.Quotient.factor hJI)).comp (restrictedCompletionReduction J hJ))
    (continuous_comp_restrictedCompletionReduction J hJ
      (MvPolynomial.map (Ideal.Quotient.factor hJI)))
    (continuous_comp_restrictedCompletionReduction I hI id)
    (fun a ↦ by simp) (fun i ↦ by simp)) x

/-- **Functoriality of completed polynomial reduction in the coefficient ring**, with no
completeness, separation, or flatness assumption on either ring. -/
theorem restrictedCompletionReduction_weightedMapCompletion {B : Type*} [CommRing B]
    [TopologicalSpace B] [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ)
    (I : Ideal A) (hI : IsOpen (I : Set A)) (J : Ideal B) (hJ : IsOpen (J : Set B))
    (hIJ : I ≤ J.comap φ) (x : restrictedMvPowerSeriesCompletion k A) :
    restrictedCompletionReduction J hJ
        (weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight (by simp) x) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (restrictedCompletionReduction I hI x) := by
  let : TopologicalSpace (MvPolynomial (Fin k) (B ⧸ J)) := ⊥
  have : DiscreteTopology (MvPolynomial (Fin k) (B ⧸ J)) := ⟨rfl⟩
  exact RingHom.congr_fun (completion_weightedRestrictedSubring_ringHom_ext_of_continuous
    isWeightFamily_one_weight
    (f := (restrictedCompletionReduction J hJ).comp
      (weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight (by simp)))
    (g := (MvPolynomial.map (Ideal.quotientMap J φ hIJ)).comp (restrictedCompletionReduction I hI))
    ((continuous_comp_restrictedCompletionReduction J hJ id).comp
      (continuous_weightedMapCompletion hφ _ _ _))
    (continuous_comp_restrictedCompletionReduction I hI
      (MvPolynomial.map (Ideal.quotientMap J φ hIJ)))
    (fun a ↦ by simp) (fun i ↦ by simp)) x

/-- Reduction modulo a finitely generated ideal of definition has exactly the extended ideal
as its kernel. -/
theorem ker_restrictedReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedReduction (k := k) I (by simpa only [pow_one] using hI.isOpen_pow 1)) =
      I.map (weightedC _ isWeightFamily_one_weight) := by
  ext f
  rw [mem_ker_restrictedReduction, mem_map_weightedC_iff_of_isAdic hI hfg]

/-- Reduction modulo `I ^ m` for a finitely generated ideal of definition has kernel
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

/-- The infinitesimal reduction of restricted power series is a polynomial algebra. -/
noncomputable def quotientRestrictedEquivMvPolynomialQuotient (hI : IsAdic I) (hfg : I.FG) :
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
      I.map (weightedC _ isWeightFamily_one_weight)) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I) :=
  ((Ideal.quotientEquivAlgOfEq A (pow_one _).symm).trans
    (quotientRestrictedPowEquivMvPolynomialQuotient hI hfg 1)).trans
    (MvPolynomial.mapAlgEquiv (Fin k) (Ideal.quotientEquivAlgOfEq A (pow_one I)))

/-- On a represented series the quotient comparison computes its polynomial reduction. -/
@[simp]
theorem quotientRestrictedEquivMvPolynomialQuotient_mk (hI : IsAdic I) (hfg : I.FG)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) :
    quotientRestrictedEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ f) =
      restrictedReduction I (by simpa only [pow_one] using hI.isOpen_pow 1) f := by
  simp only [quotientRestrictedEquivMvPolynomialQuotient, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, quotientRestrictedPowEquivMvPolynomialQuotient_mk,
    MvPolynomial.mapAlgEquiv_apply, Ideal.quotientEquivAlgOfEq_coe_eq_factor]
  exact map_restrictedReduction _ _ _ _

/-! ### Completed reductions modulo powers of an ideal of definition -/

/-- On the completed restricted-series algebra, reduction modulo `I ^ m` has kernel
`(I · A⟨T⟩) ^ m` for every finitely generated ideal of definition `I` and `m : ℕ`, with no
completeness or separation assumption on `A`. -/
theorem ker_restrictedCompletionReduction_pow (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    RingHom.ker (restrictedCompletionReduction (k := k) (I ^ m) (hI.isOpen_pow m)) =
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) ^ m := by
  let S := restrictedMvPowerSeriesCompletion k A
  let JK := I.map (algebraMap A S) ^ m
  have hle : JK ≤
      RingHom.ker (restrictedCompletionReduction (k := k) (I ^ m) (hI.isOpen_pow m)) := by
    dsimp only [JK]
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, restrictedCompletionReduction_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  refine le_antisymm (fun x hx ↦ ?_) hle
  have hopen := (isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg).isOpen_pow m
  have hnhds : {y : S | x - y ∈ JK} ∈ nhds x :=
    (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
      (by simpa using hopen.mem_nhds (zero_mem JK))
  obtain ⟨f, hf⟩ := Completion.denseRange_coe.mem_nhds hnhds
  have hfker : f ∈ I.map (weightedC _ isWeightFamily_one_weight) ^ m := by
    rw [← ker_restrictedReduction_pow hI hfg m, RingHom.mem_ker,
      ← restrictedCompletionReduction_coe, ← RingHom.mem_ker]
    simpa only [sub_sub_cancel] using
      (RingHom.ker (restrictedCompletionReduction (I ^ m) (hI.isOpen_pow m))).sub_mem hx (hle hf)
  have hmap :
      JK = (I.map (weightedC _ isWeightFamily_one_weight) ^ m).map Completion.coeRingHom := by
    dsimp only [JK, S]
    rw [Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map, ← Ideal.map_pow]
    exact congrArg (Ideal.map · (I ^ m)) (RingHom.ext <|
      algebraMap_completion_weightedRestrictedSubring_apply k A isWeightFamily_one_weight)
  exact sub_add_cancel x f ▸ JK.add_mem hf (hmap ▸ Ideal.mem_map_of_mem _ hfker)

/-- Reduction modulo a finitely generated ideal of definition on the completed restricted-series
algebra has kernel `I · A⟨T⟩`. -/
theorem ker_restrictedCompletionReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (restrictedCompletionReduction (k := k) I
        (by simpa only [pow_one] using hI.isOpen_pow 1)) =
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)) := by
  rw [← pow_one (I.map _), ← ker_restrictedCompletionReduction_pow (k := k) hI hfg 1]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker,
    ← map_restrictedCompletionReduction (hI.isOpen_pow 1) _ (le_of_eq (pow_one I)) x,
    ← Ideal.quotientEquivAlgOfEq_coe_eq_factor A (pow_one I), ← MvPolynomial.mapAlgEquiv_apply]
  exact map_eq_zero_iff _ (AlgEquiv.injective _)

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
      (restrictedCompletionReduction_surjective (I ^ m) (hI.isOpen_pow m)))) fun a ↦ by
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
    (restrictedMvPowerSeriesCompletion k A ⧸
      I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I) :=
  ((Ideal.quotientEquivAlgOfEq A (pow_one _).symm).trans
    (quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg 1)).trans
    (MvPolynomial.mapAlgEquiv (Fin k) (Ideal.quotientEquivAlgOfEq A (pow_one I)))

/-- On a represented completion element, `quotientRestrictedCompletionEquivMvPolynomialQuotient`
computes its completed polynomial reduction modulo `I`. -/
@[simp]
theorem quotientRestrictedCompletionEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) (x : restrictedMvPowerSeriesCompletion k A) :
    quotientRestrictedCompletionEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ x) =
      restrictedCompletionReduction I (by simpa only [pow_one] using hI.isOpen_pow 1) x := by
  simp only [quotientRestrictedCompletionEquivMvPolynomialQuotient, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk,
    MvPolynomial.mapAlgEquiv_apply, Ideal.quotientEquivAlgOfEq_coe_eq_factor]
  exact map_restrictedCompletionReduction _ _ _ _

/-! ### Compatibility with evaluation -/

section Evaluation

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T2Space B]

/-- **Evaluation commutes with polynomial reduction modulo open ideals.** -/
theorem mk_weightedEvalHom_eq_eval₂_restrictedReduction {φ : A →+* B} (hφ : ContinuousAt φ 0)
    {b : Fin k → B} (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b)
    (I : Ideal A) (hI : IsOpen (I : Set A)) (J : Ideal B) (hJ : IsOpen (J : Set B))
    (hIJ : I ≤ J.comap φ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    Ideal.Quotient.mk J (weightedEvalHom isWeightFamily_one_weight hφ hb f) =
      (restrictedReduction I hI f).eval₂ (Ideal.quotientMap J φ hIJ) (Ideal.Quotient.mk J ∘ b) := by
  let : DiscreteTopology (B ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  exact RingHom.congr_fun (weightedRestrictedSubring_ringHom_ext_of_continuous
    isWeightFamily_one_weight
    (f := (Ideal.Quotient.mk J).comp (weightedEvalHom isWeightFamily_one_weight hφ hb))
    (g := (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (Ideal.Quotient.mk J ∘ b)).comp
      (restrictedReduction I hI))
    (continuous_quot_mk.comp (continuous_weightedEvalHom isWeightFamily_one_weight hφ hb))
    (continuous_comp_restrictedReduction I hI
      (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (Ideal.Quotient.mk J ∘ b)))
    (fun a ↦ by simp) (fun i ↦ by simp)) f

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
  exact RingHom.congr_fun (completion_weightedRestrictedSubring_ringHom_ext_of_continuous
    isWeightFamily_one_weight
    (f := (Ideal.Quotient.mk J).comp (weightedEvalHomCompletion isWeightFamily_one_weight hφ hb))
    (g := (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (Ideal.Quotient.mk J ∘ b)).comp
      (restrictedCompletionReduction I hI))
    (continuous_quot_mk.comp (continuous_weightedEvalHomCompletion isWeightFamily_one_weight hφ hb))
    (continuous_comp_restrictedCompletionReduction I hI
      (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (Ideal.Quotient.mk J ∘ b)))
    (fun a ↦ by simp) (fun i ↦ by simp)) x

end Evaluation

/-! ### Inverse-limit description from compatible polynomial reductions -/

section InverseLimit

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

end InverseLimit

end TauCeti.Huber
