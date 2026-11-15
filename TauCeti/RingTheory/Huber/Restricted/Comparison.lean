/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.Adic
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.Restricted.Reduction
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty

import TauCeti.Topology.Algebra.Module.Quotient
import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

/-!
# Coefficient maps, reductions, and universal properties under the Gauss comparison

The unit-radius Gauss comparison identifies the Huber and normed restricted-series carriers.
This file proves that their coefficient maps, open-ideal polynomial reductions, adic polynomial
quotients, and evaluations agree, both before and after completion, and records the explicit
hypotheses distinguishing the normed, topological, and linearly topologised universal properties:

1. **Normed evaluation** (`RingHom.restrictedEval₂OfBound`): requires a bounded coefficient map
   `‖φ r‖ ≤ C * ‖r‖` into a complete ultrametric normed ring and coordinate bounds `‖a i‖ ≤ 1`,
   and yields the operator norm bound `‖·‖ ≤ C * ‖·‖` (`norm_weightedEvalHomCompletion_le`).
2. **Topological power-bounded evaluation** (`TauCeti.MvPowerSeries.restrictedLift`): requires a
   continuous coefficient map into a complete Hausdorff nonarchimedean ring and power-bounded
   arguments `IsPowerBounded (b i)` (so in a normed target `‖b i‖` may exceed `1` provided the
   powers stay bounded); it agrees with `weightedEvalHom` and `weightedEvalHomCompletion`.
3. **Linearly topologised evaluation** (`TauCeti.MvPowerSeries.restrictedLiftLinearAlgHom`): when
   the target `S` is a complete Hausdorff linearly topologised `R`-algebra with continuous
   structure map, open-ideal neighbourhoods of zero absorb multiplication by all of `S`, making
   every element of `S` power-bounded (`isBounded_of_isLinearTopology`). Arbitrary variable images
   `b : Fin k → S` therefore determine a unique continuous `R`-algebra homomorphism out of
   `R⟨X₁, …, Xₖ⟩`, agreeing with `weightedEvalLinearAlgHom` and
   `weightedEvalCompletionLinearAlgHom`.

## Main definitions

* `Ideal.isRestrictedReduction`: polynomial reduction `R⟨X⟩ →+* (R ⧸ J)[X]` of unit-radius
  Gauss-normed restricted series modulo an open ideal `J`.
* `TauCeti.MvPowerSeries.quotientIsRestrictedPowEquivMvPolynomialQuotient`: the `R`-algebra
  equivalence `R⟨X₁, …, Xₖ⟩ ⧸ (I · R⟨X⟩) ^ m ≃ₐ[R] (R ⧸ I ^ m)[X₁, …, Xₖ]` for an `I`-adic norm.
* `TauCeti.MvPowerSeries.restrictedLiftLinearAlgHom`: continuous `R`-algebra evaluation of
  `R⟨X₁, …, Xₖ⟩` at arbitrary points of a complete Hausdorff linearly topologised `R`-algebra.

## Main results

* `restrictedMvPowerSeriesGaussEquiv_weightedMap` and
  `restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion`: coefficient-map naturality.
* `isRestrictedReduction_restrictedMvPowerSeriesGaussEquiv` and
  `isRestrictedReduction_restrictedMvPowerSeriesCompletionGaussEquiv`: open-ideal polynomial
  reductions commute with the uncompleted and completed Gauss comparisons, and agree with the
  residue-field reduction on the Gauss unit ball (`restrictedReduction_restrictedIntegerEquiv_eq`).
* `TauCeti.MvPowerSeries.isAdic_map_algebraMap_isRestricted_subring`,
  `TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_of_isAdic`, and
  `TauCeti.MvPowerSeries.existsUnique_isRestrictedReduction_pow_succ_eq`: adic topology,
  noetherianity, and the inverse-limit description on the Gauss carrier.
* `weightedEvalHom_eq_restrictedEval₂OfBound`, `weightedEvalHom_eq_restrictedLift`, and
  `weightedEvalLinearAlgHom_eq_restrictedLiftLinearAlgHom` (and their completed counterparts):
  comparison of the three evaluation regimes across the Gauss equivalence.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.1–7.5.4.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1.
* T. Wedhorn, *Adic Spaces*, §5.6, Proposition 5.50.
-/

public section

namespace Ideal

open Filter Topology

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- Only finitely many coefficients of a unit-radius restricted series lie outside an open ideal. -/
private theorem finite_support_mk_coeff_isRestricted (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    (Function.support fun ν ↦
      Ideal.Quotient.mk J (MvPowerSeries.coeff ν (f : MvPowerSeries σ R))).Finite := by
  obtain ⟨ε, hε, hball⟩ :=
    NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp (hJ.mem_nhds J.zero_mem)
  have hfin : {ν | ε ≤ ‖MvPowerSeries.coeff ν (f : MvPowerSeries σ R)‖}.Finite := by
    simpa [eventually_cofinite, not_lt] using f.2.eventually (gt_mem_nhds hε)
  refine hfin.subset fun ν hν ↦ ?_
  rw [Function.mem_support, Ne, Ideal.Quotient.eq_zero_iff_mem] at hν
  exact not_lt.mp fun hlt ↦ hν (hball (Set.mem_ofPred_eq.mpr hlt))

/-- Coefficientwise reduction of a Gauss-normed restricted series modulo an open ideal `J`. -/
private noncomputable def isRestrictedReductionFun (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) : MvPolynomial σ (R ⧸ J) :=
  .ofCoeff (Finsupp.ofSupportFinite _ (finite_support_mk_coeff_isRestricted J hJ f))

private theorem coe_isRestrictedReductionFun (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    (isRestrictedReductionFun J hJ f : MvPowerSeries σ (R ⧸ J)) =
      MvPowerSeries.map (Ideal.Quotient.mk J) (f : MvPowerSeries σ R) := by
  ext ν
  simp [MvPolynomial.coeff_coe, isRestrictedReductionFun, Finsupp.ofSupportFinite_coe]

/-- **Polynomial reduction of Gauss-normed restricted series modulo an open ideal.** Because the
coefficients of a unit-radius restricted series tend to zero in norm and `J` contains a norm ball
around `0`, only finitely many coefficients survive in `R ⧸ J`. -/
noncomputable def isRestrictedReduction (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1) →+* MvPolynomial σ (R ⧸ J) where
  toFun := isRestrictedReductionFun J hJ
  map_one' := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedReductionFun]
  map_mul' f g := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedReductionFun]
  map_zero' := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedReductionFun]
  map_add' f g := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedReductionFun]

/-- `isRestrictedReduction` reduces each coefficient modulo `J`. -/
@[simp]
theorem coeff_isRestrictedReduction (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) (ν : σ →₀ ℕ) :
    (J.isRestrictedReduction hJ f).coeff ν =
      Ideal.Quotient.mk J (MvPowerSeries.coeff ν (f : MvPowerSeries σ R)) := by
  rw [← MvPolynomial.coeff_coe]
  simp [isRestrictedReduction, coe_isRestrictedReductionFun]

/-- On polynomials, `isRestrictedReduction` is coefficientwise reduction modulo `J`. -/
@[simp]
theorem isRestrictedReduction_polynomialToRestricted (J : Ideal R) (hJ : IsOpen (J : Set R))
    (p : MvPolynomial σ R) :
    J.isRestrictedReduction hJ (TauCeti.MvPowerSeries.polynomialToRestricted (fun _ : σ ↦ 1) p) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  ext ν
  simp [TauCeti.MvPowerSeries.coe_polynomialToRestricted, MvPolynomial.coeff_map,
    MvPolynomial.coeff_coe]

/-- `isRestrictedReduction` sends a constant series to the constant polynomial on its residue. -/
@[simp]
theorem isRestrictedReduction_algebraMap (J : Ideal R) (hJ : IsOpen (J : Set R)) (r : R) :
    J.isRestrictedReduction (σ := σ) hJ (algebraMap R _ r) =
      MvPolynomial.C (Ideal.Quotient.mk J r) := by
  simpa using isRestrictedReduction_polynomialToRestricted (σ := σ) J hJ (MvPolynomial.C r)

/-- `isRestrictedReduction` sends each coordinate variable to the corresponding variable. -/
@[simp]
theorem isRestrictedReduction_X (J : Ideal R) (hJ : IsOpen (J : Set R)) (i : σ) :
    J.isRestrictedReduction hJ ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ =
      MvPolynomial.X i := by
  simpa using isRestrictedReduction_polynomialToRestricted J hJ (MvPolynomial.X i)

/-- Every polynomial over `R ⧸ J` lifts to a Gauss-normed restricted series, already to a
polynomial over `R`. -/
theorem isRestrictedReduction_surjective (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    Function.Surjective (J.isRestrictedReduction (σ := σ) hJ) := fun p ↦ by
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective p
  exact ⟨TauCeti.MvPowerSeries.polynomialToRestricted (fun _ : σ ↦ 1) q, by simp⟩

/-- A Gauss-normed restricted series lies in the kernel of reduction modulo `J` if and only if
every coefficient lies in `J`. -/
theorem mem_ker_isRestrictedReduction (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    f ∈ RingHom.ker (J.isRestrictedReduction hJ) ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries σ R) ∈ J := by
  rw [RingHom.mem_ker, MvPolynomial.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

/-- Precomposing any map with `isRestrictedReduction` gives a continuous map for the Gauss norm,
because `J` contains an open norm ball around `0` on whose translates `isRestrictedReduction` is
constant. -/
theorem continuous_comp_isRestrictedReduction {X : Type*} [TopologicalSpace X]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (g : MvPolynomial σ (R ⧸ J) → X) :
    Continuous (g ∘ J.isRestrictedReduction hJ) := by
  obtain ⟨ε, hε, hball⟩ :=
    NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp (hJ.mem_nhds J.zero_mem)
  refine continuous_iff_continuousAt.mpr fun f₀ ↦ tendsto_const_nhds.congr' ?_
  filter_upwards [Metric.ball_mem_nhds f₀ hε] with f hf
  rw [Metric.mem_ball, dist_eq_norm] at hf
  dsimp only [Function.comp_apply]
  congr 1
  ext ν
  rw [coeff_isRestrictedReduction, coeff_isRestrictedReduction, Ideal.Quotient.eq]
  have hle := MvPowerSeries.norm_coeff_mul_prod_le (f₀ - f) ν
  exact hball <| by
    simpa only [one_pow, Finsupp.prod, Finset.prod_const_one, mul_one, Set.mem_ofPred_eq,
      AddSubgroupClass.coe_sub, map_sub] using hle.trans_lt (by rwa [norm_sub_rev])

/-- `isRestrictedReduction` is compatible with enlarging the open ideal. -/
@[simp]
theorem map_isRestrictedReduction {I J : Ideal R} (hI : IsOpen (I : Set R))
    (hJ : IsOpen (J : Set R)) (hIJ : I ≤ J)
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    MvPolynomial.map (Ideal.Quotient.factor hIJ) (I.isRestrictedReduction hI f) =
      J.isRestrictedReduction hJ f := by
  ext ν
  simp [MvPolynomial.coeff_map]

/-- **Functoriality of `isRestrictedReduction` under bounded coefficient maps.** No flatness
hypothesis is needed. -/
theorem isRestrictedReduction_restrictedMap {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    {φ : R →+* S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (I : Ideal R) (hI : IsOpen (I : Set R))
    (J : Ideal S) (hJ : IsOpen (J : Set S)) (hIJ : I ≤ J.comap φ)
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    J.isRestrictedReduction hJ (TauCeti.MvPowerSeries.restrictedMap φ hφ f) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (I.isRestrictedReduction hI f) := by
  ext ν
  simp [MvPolynomial.coeff_map]

end Ideal

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries IsLocalRing
open scoped NormedField Valued

section UnitBallReduction

variable {σ K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- The maximal ideal of the valuation subring `𝒪[K]` is open for the subspace norm topology, being
the open ball of radius `1` around `0`. -/
theorem isOpen_maximalIdeal_integer :
    IsOpen ((maximalIdeal 𝒪[K] : Ideal 𝒪[K]) : Set 𝒪[K]) := by
  have hball : ((maximalIdeal 𝒪[K] : Ideal 𝒪[K]) : Set 𝒪[K]) = Metric.ball (0 : 𝒪[K]) 1 := by
    ext x
    simp only [SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff,
      Valued.integer.isUnit_iff_norm_eq_one, Metric.mem_ball, dist_zero_right]
    exact ⟨fun h ↦ (Valued.integer.norm_le_one x).lt_of_ne h, ne_of_lt⟩
  rw [hball]
  exact Metric.isOpen_ball

/-- **Compatibility of unit-ball reduction and open-ideal reduction.** Under the coefficient
identification `restrictedIntegerEquiv : 𝒪[K]⟨X⟩ ≃+* K⟨X⟩°`, the residue-field reduction
`TauCeti.MvPowerSeries.restrictedReduction` on the Gauss unit ball agrees with
`(maximalIdeal 𝒪[K]).isRestrictedReduction` on `𝒪[K]⟨X⟩`. -/
@[simp]
theorem restrictedReduction_restrictedIntegerEquiv_eq
    (f : IsRestricted.subring (R := 𝒪[K]) (fun _ : σ ↦ 1)) :
    restrictedReduction (restrictedIntegerEquiv f) =
      (maximalIdeal 𝒪[K]).isRestrictedReduction isOpen_maximalIdeal_integer f := by
  refine MvPolynomial.ext _ _ fun ν ↦ ?_
  rw [coeff_restrictedReduction]
  exact (congrArg (residue 𝒪[K]) (Subtype.ext (coeff_restrictedIntegerEquiv f ν))).trans
    (Ideal.coeff_isRestrictedReduction (maximalIdeal 𝒪[K]) isOpen_maximalIdeal_integer f ν).symm

end UnitBallReduction

end TauCeti.MvPowerSeries

namespace TauCeti.Huber

open _root_.MvPowerSeries TauCeti.MvPowerSeries

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {φ : R →+* S} {C : ℝ}

section Coefficients

variable (hφc : Continuous φ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)

/-- The Gauss comparison commutes with bounded coefficient maps. -/
theorem restrictedMvPowerSeriesGaussEquiv_weightedMap
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R))
      isWeightFamily_one_weight) :
    restrictedMvPowerSeriesGaussEquiv
        (weightedMap hφc isWeightFamily_one_weight isWeightFamily_one_weight (by simp) f) =
      restrictedMap φ hφ (restrictedMvPowerSeriesGaussEquiv f) := by
  apply Subtype.ext
  simp only [coe_restrictedMvPowerSeriesGaussEquiv, coe_weightedMap, coe_restrictedMap]

variable [CompleteSpace R] [CompleteSpace S]

/-- The completed Gauss comparison commutes with the continuous coefficient map on completions.
Thus completing the topological coefficient map does not change the normed coefficient map. -/
theorem restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion
    (f : restrictedMvPowerSeriesCompletion k R) :
    restrictedMvPowerSeriesCompletionGaussEquiv
        (weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) f) =
      restrictedMap φ hφ (restrictedMvPowerSeriesCompletionGaussEquiv f) := by
  refine UniformSpace.Completion.induction_on f (isClosed_eq
    (continuous_restrictedMvPowerSeriesCompletionGaussEquiv.comp
      (continuous_weightedMapCompletion _ _ _ _))
    ((continuous_restrictedMap φ hφ).comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)) ?_
  intro g
  simp only [weightedMapCompletion_coe, restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    restrictedMvPowerSeriesGaussEquiv_weightedMap hφc hφ]

include hφ in
/-- A bounded coefficient map on Huber completions has the same bound in the compared Gauss
norms. No norm on the topological completion is chosen independently of the comparison. -/
theorem norm_restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion_le
    (f : restrictedMvPowerSeriesCompletion k R) :
    ‖restrictedMvPowerSeriesCompletionGaussEquiv
        (weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) f)‖ ≤
      C * ‖restrictedMvPowerSeriesCompletionGaussEquiv f‖ := by
  rw [restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion hφc hφ]
  exact norm_restrictedMap_le φ hφ _

end Coefficients

section Reduction

/-- **The uncompleted Gauss comparison commutes with open-ideal polynomial reduction.** -/
@[simp]
theorem isRestrictedReduction_restrictedMvPowerSeriesGaussEquiv (J : Ideal R)
    (hJ : IsOpen (J : Set R))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    J.isRestrictedReduction hJ (restrictedMvPowerSeriesGaussEquiv f) =
      J.restrictedReduction hJ f := by
  ext ν
  simp

/-- Applying `restrictedReduction` after the inverse Gauss comparison agrees with
`isRestrictedReduction`. -/
@[simp]
theorem restrictedReduction_restrictedMvPowerSeriesGaussEquiv_symm (J : Ideal R)
    (hJ : IsOpen (J : Set R)) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    J.restrictedReduction hJ (restrictedMvPowerSeriesGaussEquiv.symm f) =
      J.isRestrictedReduction hJ f := by
  simpa using (isRestrictedReduction_restrictedMvPowerSeriesGaussEquiv J hJ
    (restrictedMvPowerSeriesGaussEquiv.symm f)).symm

section CompleteReduction

variable [CompleteSpace R]

/-- **The completed Gauss comparison commutes with open-ideal polynomial reduction.** -/
@[simp]
theorem isRestrictedReduction_restrictedMvPowerSeriesCompletionGaussEquiv (J : Ideal R)
    (hJ : IsOpen (J : Set R)) (x : restrictedMvPowerSeriesCompletion k R) :
    J.isRestrictedReduction hJ (restrictedMvPowerSeriesCompletionGaussEquiv x) =
      J.restrictedCompletionReduction hJ x := by
  let : TopologicalSpace (MvPolynomial (Fin k) (R ⧸ J)) := ⊥
  have : DiscreteTopology (MvPolynomial (Fin k) (R ⧸ J)) := ⟨rfl⟩
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    ((J.continuous_comp_isRestrictedReduction hJ id).comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)
    (J.continuous_comp_restrictedCompletionReduction hJ id)) ?_
  intro f
  simp

/-- Applying `restrictedCompletionReduction` after the inverse completed Gauss comparison agrees
with `isRestrictedReduction`. -/
theorem restrictedCompletionReduction_restrictedMvPowerSeriesCompletionGaussEquiv_symm
    (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    J.restrictedCompletionReduction hJ (restrictedMvPowerSeriesCompletionGaussEquiv.symm f) =
      J.isRestrictedReduction hJ f := by
  simp

end CompleteReduction

end Reduction

end TauCeti.Huber

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries TauCeti.Huber

section Adic

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {I : Ideal R}

/-- **Adic topology of Gauss-normed restricted series.** When the norm topology of `R` is defined
by a finitely generated ideal `I`, the Gauss norm topology on `R⟨X₁, …, Xₖ⟩` is the adic topology
of the extended ideal `I · R⟨X₁, …, Xₖ⟩`. -/
theorem isAdic_map_algebraMap_isRestricted_subring (k : ℕ) (hI : IsAdic I) (hfg : I.FG) :
    IsAdic (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) := by
  let er := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  have hind : Topology.IsInducing er.symm :=
    (Homeomorph.mk er.symm.toEquiv continuous_restrictedMvPowerSeriesGaussEquiv_symm
      continuous_restrictedMvPowerSeriesGaussEquiv).isInducing
  have h := (isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg).comap
    er.symm hind
  have hcomap : (I.map (algebraMap R _)).comap er.symm =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) := by
    rw [← Ideal.map_symm, RingEquiv.symm_symm]
    change (I.map (algebraMap R _)).map er.toRingHom = _
    rw [Ideal.map_map]
    refine congrArg (Ideal.map · I) (RingHom.ext fun r ↦ ?_)
    simp [er, algebraMap_weightedRestrictedSubring]
  rwa [hcomap] at h

/-- Reduction modulo `I ^ m` on the Gauss-normed restricted-series ring has kernel
`(I · R⟨X₁, …, Xₖ⟩) ^ m` for every finitely generated ideal of definition `I` and every `m : ℕ`. -/
theorem ker_isRestrictedReduction_pow (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    RingHom.ker ((I ^ m).isRestrictedReduction (σ := Fin k) (hI.isOpen_pow m)) =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ^ m := by
  let er := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  have hker : RingHom.ker ((I ^ m).isRestrictedReduction (σ := Fin k) (hI.isOpen_pow m)) =
      (RingHom.ker ((I ^ m).restrictedReduction (k := k) (hI.isOpen_pow m))).map er.toRingHom := by
    ext f
    rw [Ideal.mem_map_iff_of_surjective er.toRingHom er.surjective]
    refine ⟨fun hf ↦ ⟨er.symm f, ?_, er.apply_symm_apply f⟩, ?_⟩
    · rwa [RingHom.mem_ker, restrictedReduction_restrictedMvPowerSeriesGaussEquiv_symm]
    · rintro ⟨g, hg, rfl⟩
      rwa [RingHom.mem_ker, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        isRestrictedReduction_restrictedMvPowerSeriesGaussEquiv]
  rw [hker, ker_restrictedReduction_pow hI hfg m, Ideal.map_pow, Ideal.map_map]
  refine congrArg (· ^ m) (congrArg (Ideal.map · I) (RingHom.ext fun r ↦ ?_))
  simp [er]

/-- Reduction modulo a finitely generated ideal of definition `I` on the Gauss-normed
restricted-series ring has kernel `I · R⟨X₁, …, Xₖ⟩`. -/
theorem ker_isRestrictedReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (I.isRestrictedReduction (σ := Fin k)
        (by simpa only [pow_one] using hI.isOpen_pow 1)) =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) := by
  let er := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  have hker : RingHom.ker (I.isRestrictedReduction (σ := Fin k)
        (by simpa only [pow_one] using hI.isOpen_pow 1)) =
      (RingHom.ker (I.restrictedReduction (k := k)
        (by simpa only [pow_one] using hI.isOpen_pow 1))).map er.toRingHom := by
    ext f
    rw [Ideal.mem_map_iff_of_surjective er.toRingHom er.surjective]
    refine ⟨fun hf ↦ ⟨er.symm f, ?_, er.apply_symm_apply f⟩, ?_⟩
    · rwa [RingHom.mem_ker, restrictedReduction_restrictedMvPowerSeriesGaussEquiv_symm]
    · rintro ⟨g, hg, rfl⟩
      rwa [RingHom.mem_ker, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        isRestrictedReduction_restrictedMvPowerSeriesGaussEquiv]
  rw [hker, TauCeti.Huber.ker_restrictedReduction hI hfg, Ideal.map_map]
  exact congrArg (Ideal.map · I) (RingHom.ext fun r ↦ by simp [er])

/-- **Polynomial quotient equivalence on Gauss-normed restricted series.** For a finitely generated
ideal of definition `I` of `R` and any `m : ℕ`, reducing `R⟨X₁, …, Xₖ⟩` modulo
`(I · R⟨X₁, …, Xₖ⟩) ^ m` gives the polynomial `R`-algebra `(R ⧸ I ^ m)[X₁, …, Xₖ]`. -/
noncomputable def quotientIsRestrictedPowEquivMvPolynomialQuotient (hI : IsAdic I) (hfg : I.FG)
    (m : ℕ) :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ^ m) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I ^ m) := by
  let e := (Ideal.quotEquivOfEq (ker_isRestrictedReduction_pow (k := k) hI hfg m).symm).trans
    (((I ^ m).isRestrictedReduction (hI.isOpen_pow m)).quotientKerEquivOfSurjective
      ((I ^ m).isRestrictedReduction_surjective (hI.isOpen_pow m)))
  refine AlgEquiv.ofRingEquiv (f := e) fun r ↦ ?_
  have he : e (algebraMap R _ r) =
      (I ^ m).isRestrictedReduction (hI.isOpen_pow m) (algebraMap R _ r) := by
    rw [← Ideal.Quotient.mk_algebraMap]
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [he, Ideal.isRestrictedReduction_algebraMap]
  rfl

/-- On a represented series, `quotientIsRestrictedPowEquivMvPolynomialQuotient` computes its
open-ideal polynomial reduction modulo `I ^ m`. -/
@[simp]
theorem quotientIsRestrictedPowEquivMvPolynomialQuotient_mk (hI : IsAdic I) (hfg : I.FG) (m : ℕ)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientIsRestrictedPowEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ f) =
      (I ^ m).isRestrictedReduction (hI.isOpen_pow m) f := by
  simp [quotientIsRestrictedPowEquivMvPolynomialQuotient]

/-- **Compatibility of adic polynomial quotients with the uncompleted Gauss comparison.** -/
@[simp]
theorem quotientIsRestrictedPowEquivMvPolynomialQuotient_quotientEquivAlg (hI : IsAdic I)
    (hfg : I.FG) (m : ℕ)
    (q : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight ⧸
      I.map (weightedC _ isWeightFamily_one_weight) ^ m) :
    quotientIsRestrictedPowEquivMvPolynomialQuotient hI hfg m
        (Ideal.quotientEquivAlg _ _ restrictedMvPowerSeriesGaussAlgEquiv
          (by
            rw [Ideal.map_pow, Ideal.map_map]
            refine congrArg (· ^ m) (congrArg (Ideal.map · I) ?_)
            rw [← algebraMap_weightedRestrictedSubring]
            exact restrictedMvPowerSeriesGaussAlgEquiv.toAlgHom.comp_algebraMap.symm) q) =
      quotientRestrictedPowEquivMvPolynomialQuotient hI hfg m q := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

/-- **Inverse-limit characterisation on the Gauss-normed carrier** (EGA I, Ch. 0, §7.5.1). Over an
`I`-adically complete ultrametric normed ring whose norm topology is `I`-adic (with no finite
generation assumption on `I`), every compatible sequence in `(R ⧸ I ^ (m + 1))[X₁, …, Xₖ]` is the
reduction sequence of a unique series in `R⟨X₁, …, Xₖ⟩`. -/
theorem existsUnique_isRestrictedReduction_pow_succ_eq (hI : IsAdic I) [IsAdicComplete I R]
    (p : ∀ m : ℕ, MvPolynomial (Fin k) (R ⧸ I ^ (m + 1)))
    (hp : ∀ m : ℕ,
      MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right m.succ.le_succ))
        (p (m + 1)) = p m) :
    ∃! f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1),
      ∀ m : ℕ, (I ^ (m + 1)).isRestrictedReduction (hI.isOpen_pow (m + 1)) f = p m := by
  obtain ⟨g, hg, huniq⟩ := existsUnique_restrictedReduction_pow_succ_eq hI p hp
  refine ⟨restrictedMvPowerSeriesGaussEquiv g, fun m ↦ by simp [hg m], fun f hf ↦ ?_⟩
  have hsymm := huniq (restrictedMvPowerSeriesGaussEquiv.symm f) (fun m ↦ by simp [hf m])
  exact (restrictedMvPowerSeriesGaussEquiv.apply_symm_apply f).symm.trans
    (congrArg restrictedMvPowerSeriesGaussEquiv hsymm)

/-- Over an adic ultrametric normed ring of finite ideal type, the Gauss-normed restricted-series
ring `R⟨X₁, …, Xₖ⟩` is itself an adic ring of finite ideal type. -/
instance isAdicRing_isRestricted_subring (k : ℕ) [IsAdicRing R] :
    IsAdicRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
  obtain ⟨hfg, hI, -⟩ := IsAdicRing.ideal_spec R
  let J := (IsAdicRing.ideal R).map
    (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))
  have hJ : IsAdic J := isAdic_map_algebraMap_isRestricted_subring k hI hfg
  exact ⟨J, hfg.map _, hJ, hJ.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩⟩

section CompleteAdic

variable [CompleteSpace R]

/-- **Compatibility of adic polynomial quotients with the completed Gauss comparison.** -/
@[simp]
theorem quotientIsRestrictedPowEquivMvPolynomialQuotient_completionGaussAlgEquiv (hI : IsAdic I)
    (hfg : I.FG) (m : ℕ)
    (q : restrictedMvPowerSeriesCompletion k R ⧸
      I.map (algebraMap R (restrictedMvPowerSeriesCompletion k R)) ^ m) :
    quotientIsRestrictedPowEquivMvPolynomialQuotient hI hfg m
        (Ideal.quotientEquivAlg _ _ restrictedMvPowerSeriesCompletionGaussAlgEquiv
          (by
            rw [Ideal.map_pow, Ideal.map_map]
            exact congrArg (· ^ m) (congrArg (Ideal.map · I)
              restrictedMvPowerSeriesCompletionGaussAlgEquiv.toAlgHom.comp_algebraMap.symm)) q) =
      quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg m q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

/-- **Noetherianity of Gauss-normed restricted series over a complete noetherian adic ring.**
Transported from `isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic` across the
completed Gauss comparison. -/
theorem isNoetherianRing_isRestricted_subring_of_isAdic (k : ℕ) [IsNoetherianRing R]
    (hI : IsAdic I) :
    IsNoetherianRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
  have := isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic k hI
  exact isNoetherianRing_of_ringEquiv _
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R))

end CompleteAdic

/-- Over a noetherian adic ultrametric normed ring, `R⟨X₁, …, Xₖ⟩` is noetherian (and hence
strongly noetherian via `IsStronglyNoetherian.of_isAdicRing`). -/
instance isNoetherianRing_isRestricted_subring_of_isAdicRing (k : ℕ) [IsAdicRing R]
    [IsNoetherianRing R] :
    IsNoetherianRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  isNoetherianRing_isRestricted_subring_of_isAdic k (IsAdicRing.ideal_spec R).2.1

end Adic

section LinearTopology

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [CompleteSpace S] [T2Space S]

/-- **Evaluation of `restrictedLift` commutes with open-ideal polynomial reduction.** -/
theorem mk_restrictedLift_eq_eval₂_isRestrictedReduction [NonarchimedeanRing S] {φ : R →+* S}
    (hφ : Continuous φ) {b : Fin k → S} (hb : ∀ i, IsPowerBounded (b i))
    (I : Ideal R) (hI : IsOpen (I : Set R)) (J : Ideal S) (hJ : IsOpen (J : Set S))
    (hIJ : I ≤ J.comap φ) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk J (restrictedLift hφ hb f) =
      (I.isRestrictedReduction hI f).eval₂ (Ideal.quotientMap J φ hIJ)
        (Ideal.Quotient.mk J ∘ b) := by
  let : DiscreteTopology (S ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have h := isRestricted_subring_ringHom_ext_of_continuous
    (ψ₁ := (Ideal.Quotient.mk J).comp (restrictedLift hφ hb))
    (ψ₂ := (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ)
      (Ideal.Quotient.mk J ∘ b)).comp (I.isRestrictedReduction (σ := Fin k) hI))
    (continuous_quot_mk.comp (continuous_restrictedLift hφ hb))
    (I.continuous_comp_isRestrictedReduction hI
      (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (Ideal.Quotient.mk J ∘ b)))
    (fun r ↦ by simp)
    (fun i ↦ by simp)
  exact RingHom.congr_fun h f

variable [IsLinearTopology S S] [Algebra R S]

/-- **Continuous `R`-algebra evaluation of Gauss-normed restricted series in a linearly topologised
`R`-algebra** (EGA I, Ch. 0, §7.5.3). Because open ideals form a neighbourhood basis of zero in
`S`, every subset of `S` is bounded (`isBounded_of_isLinearTopology`) and every element is
power-bounded, so arbitrary points `b : Fin k → S` (with neither `‖b i‖ ≤ 1` nor an explicit
`IsPowerBounded (b i)` hypothesis) determine a continuous `R`-algebra homomorphism. -/
noncomputable def restrictedLiftLinearAlgHom (hR : Continuous (algebraMap R S)) (b : Fin k → S) :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R] S := by
  haveI := IsLinearTopology.isTopologicalRing (R := S)
  haveI := IsLinearTopology.nonarchimedeanRing S
  let φ := restrictedLift hR (b := b)
    fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)
  exact
    { __ := φ
      toFun := φ
      commutes' := fun r ↦ restrictedLift_algebraMap hR _ r }

/-- Underlying ring homomorphism of `restrictedLiftLinearAlgHom`. -/
@[simp]
theorem coe_restrictedLiftLinearAlgHom (hR : Continuous (algebraMap R S)) (b : Fin k → S) :
    (restrictedLiftLinearAlgHom hR b :
      IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* S) =
      letI := IsLinearTopology.isTopologicalRing (R := S)
      letI := IsLinearTopology.nonarchimedeanRing S
      restrictedLift hR (b := b) fun _ ↦
        isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _) := by
  ext f
  rfl

/-- `restrictedLiftLinearAlgHom` sends each variable `Xᵢ` to `bᵢ`. -/
@[simp]
theorem restrictedLiftLinearAlgHom_X (hR : Continuous (algebraMap R S)) (b : Fin k → S)
    (i : Fin k) :
    restrictedLiftLinearAlgHom hR b ⟨X i, isRestricted_X _ i⟩ = b i := by
  have := IsLinearTopology.isTopologicalRing (R := S)
  have := IsLinearTopology.nonarchimedeanRing S
  exact restrictedLift_X hR (b := b)
    (fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)) i

/-- `restrictedLiftLinearAlgHom` is continuous for the Gauss norm topology. -/
theorem continuous_restrictedLiftLinearAlgHom (hR : Continuous (algebraMap R S)) (b : Fin k → S) :
    Continuous (restrictedLiftLinearAlgHom hR b) := by
  have := IsLinearTopology.isTopologicalRing (R := S)
  have := IsLinearTopology.nonarchimedeanRing S
  exact continuous_restrictedLift hR (b := b)
    fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)

/-- **Universal property of Gauss-normed restricted series for linearly topologised `R`-algebras.**
Unlike the general topological universal property
(`existsUnique_continuous_ringHom_isRestricted_subring`, which requires `IsPowerBounded (b i)`) and
normed evaluation (`RingHom.restrictedEval₂OfBound`, which requires `‖b i‖ ≤ 1`), open-ideal
neighbourhoods in `S` make every element power-bounded, so arbitrary `b : Fin k → S` extend
uniquely. -/
theorem existsUnique_continuous_algHom_isRestricted_subring_of_isLinearTopology
    (hR : Continuous (algebraMap R S)) (b : Fin k → S) :
    ∃! ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R] S,
      Continuous ψ ∧ ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i := by
  have := IsLinearTopology.isTopologicalRing (R := S)
  have := IsLinearTopology.nonarchimedeanRing S
  refine ⟨restrictedLiftLinearAlgHom hR b,
    ⟨continuous_restrictedLiftLinearAlgHom hR b, restrictedLiftLinearAlgHom_X hR b⟩,
    fun ψ ⟨hψ, hX⟩ ↦ AlgHom.toRingHom_injective ?_⟩
  exact isRestricted_subring_ringHom_ext_of_continuous hψ
    (continuous_restrictedLiftLinearAlgHom hR b)
    (fun r ↦ (ψ.commutes r).trans ((restrictedLiftLinearAlgHom hR b).commutes r).symm)
    (fun i ↦ (hX i).trans (restrictedLiftLinearAlgHom_X hR b i).symm)

end LinearTopology

end TauCeti.MvPowerSeries

namespace TauCeti.Huber

open _root_.MvPowerSeries TauCeti.MvPowerSeries

section Evaluation

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] {φ : R →+* S} {C : ℝ}
  {a : Fin k → S}
  (hφc : ContinuousAt φ 0) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
  (ha : ∀ i, ‖a i‖ ≤ 1)
  (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set R)) a)

/-- Huber evaluation and bounded normed evaluation agree under the Gauss comparison. The
power-boundedness witness may be any witness, not just the one supplied by the norm bounds. -/
theorem weightedEvalHom_eq_restrictedEval₂OfBound
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R))
      isWeightFamily_one_weight) :
    weightedEvalHom isWeightFamily_one_weight hφc hb f =
      φ.restrictedEval₂OfBound a hφ ha (restrictedMvPowerSeriesGaussEquiv f) := by
  rw [coe_weightedEvalHom, RingHom.restrictedEval₂OfBound_apply,
    coe_restrictedMvPowerSeriesGaussEquiv]

include hφ ha in
/-- Huber evaluation obeys the coefficient-map bound, measured in the Gauss norm. -/
theorem norm_weightedEvalHom_le
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R))
      isWeightFamily_one_weight) :
    ‖weightedEvalHom isWeightFamily_one_weight hφc hb f‖ ≤
      C * ‖restrictedMvPowerSeriesGaussEquiv f‖ := by
  rw [weightedEvalHom_eq_restrictedEval₂OfBound hφc hφ ha hb]
  exact φ.norm_restrictedEval₂OfBound_le a hφ ha _

variable [CompleteSpace R]

/-- Evaluation on the completed Huber algebra is normed evaluation through the completed Gauss
comparison. This identifies the extensions on every element, not just on polynomials. -/
theorem weightedEvalHomCompletion_eq_restrictedEval₂OfBound
    (f : restrictedMvPowerSeriesCompletion k R) :
    weightedEvalHomCompletion isWeightFamily_one_weight hφc hb f =
      φ.restrictedEval₂OfBound a hφ ha (restrictedMvPowerSeriesCompletionGaussEquiv f) := by
  refine UniformSpace.Completion.induction_on f (isClosed_eq
    (continuous_weightedEvalHomCompletion _ _ _)
    ((φ.continuous_restrictedEval₂OfBound a hφ ha).comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)) ?_
  intro g
  rw [weightedEvalHomCompletion_coe, restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    weightedEvalHom_eq_restrictedEval₂OfBound hφc hφ ha hb]

include hφ ha in
/-- Completed Huber evaluation has the coefficient homomorphism's bound in the Gauss norm
transported by the completed comparison. -/
theorem norm_weightedEvalHomCompletion_le (f : restrictedMvPowerSeriesCompletion k R) :
    ‖weightedEvalHomCompletion isWeightFamily_one_weight hφc hb f‖ ≤
      C * ‖restrictedMvPowerSeriesCompletionGaussEquiv f‖ := by
  rw [weightedEvalHomCompletion_eq_restrictedEval₂OfBound hφc hφ ha hb]
  exact φ.norm_restrictedEval₂OfBound_le a hφ ha _

end Evaluation

section PowerBoundedEvaluation

variable {k : ℕ} {R T : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [CommRing T] [UniformSpace T] [IsUniformAddGroup T] [CompleteSpace T] [T2Space T]

/-- **Comparison of power-bounded evaluations.** For any continuous `φ : R →+* T` into a complete
Hausdorff nonarchimedean ring and power-bounded `b : Fin k → T` (without requiring `‖b i‖ ≤ 1` or
a norm on `T`), Huber's `weightedEvalHom` agrees with `restrictedLift` across the Gauss
comparison, independently of the witness `hb'`. -/
theorem weightedEvalHom_eq_restrictedLift [NonarchimedeanRing T] {φ : R →+* T}
    (hφ : Continuous φ) {b : Fin k → T} (hb : ∀ i, IsPowerBounded (b i))
    (hb' : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set R)) b)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    weightedEvalHom isWeightFamily_one_weight hφ.continuousAt hb' f =
      restrictedLift hφ hb (restrictedMvPowerSeriesGaussEquiv f) := by
  have h := weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    (f := weightedEvalHom isWeightFamily_one_weight hφ.continuousAt hb')
    (g := (restrictedLift hφ hb).comp
      (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).toRingHom)
    (continuous_weightedEvalHom _ _ _)
    ((continuous_restrictedLift hφ hb).comp continuous_restrictedMvPowerSeriesGaussEquiv)
    (fun r ↦ by simp)
    (fun i ↦ by simp)
  exact RingHom.congr_fun h f

/-- **Comparison of linearly topologised evaluations** before completion:
`weightedEvalLinearAlgHom` agrees with `restrictedLiftLinearAlgHom` across the Gauss comparison. -/
theorem weightedEvalLinearAlgHom_eq_restrictedLiftLinearAlgHom [IsLinearTopology T T]
    [Algebra R T] (hR : Continuous (algebraMap R T)) (b : Fin k → T)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    weightedEvalLinearAlgHom hR.continuousAt b f =
      restrictedLiftLinearAlgHom hR b (restrictedMvPowerSeriesGaussAlgEquiv f) := by
  have := IsLinearTopology.isTopologicalRing (R := T)
  have := IsLinearTopology.nonarchimedeanRing T
  rw [coe_restrictedMvPowerSeriesGaussAlgEquiv,
    ← RingHom.coe_coe (weightedEvalLinearAlgHom hR.continuousAt b), coe_weightedEvalLinearAlgHom]
  exact weightedEvalHom_eq_restrictedLift hR
    (fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _))
    (isWeightBounded_of_isLinearTopology (algebraMap R T) _ b) f

section CompletePowerBoundedEvaluation

variable [CompleteSpace R]

/-- **Completed power-bounded evaluation agrees with `restrictedLift`** across the completed Gauss
comparison. -/
theorem weightedEvalHomCompletion_eq_restrictedLift [NonarchimedeanRing T] {φ : R →+* T}
    (hφ : Continuous φ) {b : Fin k → T} (hb : ∀ i, IsPowerBounded (b i))
    (hb' : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set R)) b)
    (x : restrictedMvPowerSeriesCompletion k R) :
    weightedEvalHomCompletion isWeightFamily_one_weight hφ.continuousAt hb' x =
      restrictedLift hφ hb (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq
    (continuous_weightedEvalHomCompletion _ _ _)
    ((continuous_restrictedLift hφ hb).comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)) ?_
  intro f
  rw [weightedEvalHomCompletion_coe, restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    weightedEvalHom_eq_restrictedLift hφ hb hb' f]

/-- **Completed linearly topologised evaluation agrees with `restrictedLiftLinearAlgHom`** across
the completed Gauss comparison. -/
theorem weightedEvalCompletionLinearAlgHom_eq_restrictedLiftLinearAlgHom [IsLinearTopology T T]
    [Algebra R T] (hR : Continuous (algebraMap R T)) (b : Fin k → T)
    (x : restrictedMvPowerSeriesCompletion k R) :
    weightedEvalCompletionLinearAlgHom hR.continuousAt b x =
      restrictedLiftLinearAlgHom hR b (restrictedMvPowerSeriesCompletionGaussAlgEquiv x) := by
  have := IsLinearTopology.isTopologicalRing (R := T)
  have := IsLinearTopology.nonarchimedeanRing T
  rw [coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv,
    ← RingHom.coe_coe (weightedEvalCompletionLinearAlgHom hR.continuousAt b),
    coe_weightedEvalCompletionLinearAlgHom]
  exact weightedEvalHomCompletion_eq_restrictedLift hR
    (fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _))
    (isWeightBounded_of_isLinearTopology (algebraMap R T) _ b) x

end CompletePowerBoundedEvaluation

end PowerBoundedEvaluation

end TauCeti.Huber
