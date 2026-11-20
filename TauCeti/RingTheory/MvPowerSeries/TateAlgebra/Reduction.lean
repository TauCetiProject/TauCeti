/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval
public import TauCeti.Topology.Algebra.Group.LocallyConstant
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Algebra.Ring.Ideal
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map

/-!
# Polynomial reduction of normed restricted power series modulo open ideals

For an ultrametric normed commutative ring `R` and an open ideal `J` of `R`, only finitely many
coefficients of `f ∈ R⟨X⟩` lie outside `J`. Reducing coefficients modulo `J` defines a surjective
ring homomorphism `Ideal.isRestrictedSubringReduction : R⟨X⟩ →+* MvPolynomial σ (R ⧸ J)` without
completeness, valuation, or field hypotheses on `R`. Its kernel is open, so reduction is locally
constant, natural along continuous coefficient maps, and commutes with bounded and contractive
evaluation modulo any open ideal of a complete ultrametric target ring.

## Main definitions and results

* `Ideal.isRestrictedSubringReduction`: reduction `R⟨X⟩ →+* MvPolynomial σ (R ⧸ J)` modulo open `J`.
* `Ideal.isOpen_ker_isRestrictedSubringReduction`,
  `Ideal.isLocallyConstant_isRestrictedSubringReduction`,
  `Ideal.isRestrictedSubringReduction_surjective`,
  `isRestrictedSubringReduction_restrictedMapOfContinuous`,
  `mk_restrictedEval₂OfBound_eq_eval₂_isRestrictedSubringReduction`, and
  `mk_restrictedEval₂_eq_eval₂_isRestrictedSubringReduction`.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §§5.1.1–5.1.3.
-/

public section

open _root_.MvPowerSeries
local notation:max "Tate" σ':max R':max => IsRestricted.subring (R := R') (fun _ : σ' ↦ 1)

namespace Ideal

open Filter TauCeti.MvPowerSeries
open scoped Topology

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

private theorem finite_support_mk_coeff (J : Ideal R) (hJ : IsOpen (J : Set R)) (f : Tate σ R) :
    (Function.support fun t ↦ Ideal.Quotient.mk J (coeff t (f : MvPowerSeries σ R))).Finite := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hJ 0 J.zero_mem
  have hfin : {t | ε ≤ ‖coeff t (f : MvPowerSeries σ R)‖}.Finite := by
    simpa [eventually_cofinite, not_lt] using f.property.eventually (gt_mem_nhds hε)
  exact hfin.subset fun t ht ↦ not_lt.mp fun hlt ↦
    (Ideal.Quotient.eq_zero_iff_mem.not.mp ht) (hball (by simpa [dist_zero_right] using hlt))

private noncomputable def isRestrictedSubringReductionAux (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : Tate σ R) : MvPolynomial σ (R ⧸ J) :=
  .ofCoeff (Finsupp.ofSupportFinite _ (finite_support_mk_coeff J hJ f))

private theorem coe_isRestrictedSubringReductionAux (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : Tate σ R) :
    (isRestrictedSubringReductionAux J hJ f : MvPowerSeries σ (R ⧸ J)) =
      MvPowerSeries.map (Ideal.Quotient.mk J) (f : MvPowerSeries σ R) := by
  ext t
  simp [MvPolynomial.coeff_coe, isRestrictedSubringReductionAux, Finsupp.ofSupportFinite_coe]

/-- **Polynomial reduction of normed restricted power series modulo an open ideal.** -/
noncomputable def isRestrictedSubringReduction (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    Tate σ R →+* MvPolynomial σ (R ⧸ J) where
  toFun := isRestrictedSubringReductionAux J hJ
  map_one' := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedSubringReductionAux]
  map_mul' _ _ := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedSubringReductionAux]
  map_zero' := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedSubringReductionAux]
  map_add' _ _ := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedSubringReductionAux]

/-- Each coefficient of `J.isRestrictedSubringReduction hJ f` reduces that of `f` modulo `J`. -/
@[simp] theorem coeff_isRestrictedSubringReduction (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : Tate σ R) (t : σ →₀ ℕ) : (J.isRestrictedSubringReduction hJ f).coeff t =
      Ideal.Quotient.mk J (coeff t (f : MvPowerSeries σ R)) := by
  rw [← MvPolynomial.coeff_coe]
  simp [isRestrictedSubringReduction, coe_isRestrictedSubringReductionAux]

/-- A restricted series reduces to `0` modulo `J` iff all of its coefficients belong to `J`. -/
theorem isRestrictedSubringReduction_eq_zero_iff {J : Ideal R} (hJ : IsOpen (J : Set R))
    {f : Tate σ R} : J.isRestrictedSubringReduction hJ f = 0 ↔
      ∀ t, coeff t (f : MvPowerSeries σ R) ∈ J := by
  simp [MvPolynomial.ext_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- The kernel of `J.isRestrictedSubringReduction hJ` is open in `R⟨X⟩`. -/
theorem isOpen_ker_isRestrictedSubringReduction (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    IsOpen (RingHom.ker (J.isRestrictedSubringReduction (σ := σ) hJ) : Set (Tate σ R)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hJ 0 J.zero_mem
  refine AddSubgroup.isOpen_of_mem_nhds
    (RingHom.ker (J.isRestrictedSubringReduction hJ)).toAddSubgroup (g := 0) ?_
  filter_upwards [Metric.ball_mem_nhds 0 hε] with f hf
  rw [SetLike.mem_coe, Submodule.mem_toAddSubgroup, RingHom.mem_ker,
    isRestrictedSubringReduction_eq_zero_iff hJ]
  exact fun t ↦ hball <| by simpa [dist_zero_right] using
    (MvPowerSeries.norm_coeff_le_norm f t).trans_lt (by simpa [dist_zero_right] using hf)

/-- `J.isRestrictedSubringReduction hJ` has open kernel and is therefore locally constant. -/
theorem isLocallyConstant_isRestrictedSubringReduction (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    IsLocallyConstant (J.isRestrictedSubringReduction (σ := σ) hJ) :=
  (J.isRestrictedSubringReduction (σ := σ) hJ).toAddMonoidHom.isLocallyConstant_of_isOpen_ker
    (J.isOpen_ker_isRestrictedSubringReduction hJ)

/-- `J.isRestrictedSubringReduction hJ` is continuous into any topology on
`MvPolynomial σ (R ⧸ J)`. -/
theorem continuous_isRestrictedSubringReduction (J : Ideal R)
    [TopologicalSpace (MvPolynomial σ (R ⧸ J))] (hJ : IsOpen (J : Set R)) :
    Continuous (J.isRestrictedSubringReduction (σ := σ) hJ) :=
  (J.isLocallyConstant_isRestrictedSubringReduction hJ).continuous

/-- On embedded polynomials, `isRestrictedSubringReduction` reduces coefficients modulo `J`. -/
@[simp] theorem isRestrictedSubringReduction_polynomialToRestricted (J : Ideal R)
    (hJ : IsOpen (J : Set R)) (p : MvPolynomial σ R) :
    J.isRestrictedSubringReduction hJ (polynomialToRestricted (fun _ : σ ↦ 1) p) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  ext t; simp [MvPolynomial.coeff_map, polynomialToRestricted_apply, MvPolynomial.coeff_coe]

/-- Constant restricted series reduce to constant polynomials modulo `J`. -/
@[simp] theorem isRestrictedSubringReduction_algebraMap (J : Ideal R) (hJ : IsOpen (J : Set R))
    (r : R) : J.isRestrictedSubringReduction (σ := σ) hJ (algebraMap R _ r) =
      MvPolynomial.C (Ideal.Quotient.mk J r) := by
  simpa [← MvPolynomial.algebraMap_eq] using
    J.isRestrictedSubringReduction_polynomialToRestricted (σ := σ) hJ (MvPolynomial.C r)

/-- Each coordinate variable reduces to the corresponding polynomial variable. -/
@[simp] theorem isRestrictedSubringReduction_X (J : Ideal R) (hJ : IsOpen (J : Set R)) (i : σ) :
    J.isRestrictedSubringReduction hJ ⟨X i, isRestricted_X (fun _ : σ ↦ 1) i⟩ =
      MvPolynomial.X i := by
  simpa using J.isRestrictedSubringReduction_polynomialToRestricted hJ (MvPolynomial.X i)

/-- Every polynomial over `R ⧸ J` lifts to a restricted series, already to a polynomial. -/
theorem isRestrictedSubringReduction_surjective (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    Function.Surjective (J.isRestrictedSubringReduction (σ := σ) hJ) := fun p ↦ by
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective p
  exact ⟨polynomialToRestricted (fun _ : σ ↦ 1) q, by simp⟩

end Ideal

namespace TauCeti.MvPowerSeries

section Functoriality

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- Reduction is compatible with passing to a larger open ideal. -/
@[simp] theorem map_isRestrictedSubringReduction {J I : Ideal R} (hJ : IsOpen (J : Set R))
    (hI : IsOpen (I : Set R)) (hJI : J ≤ I) (f : Tate σ R) :
    MvPolynomial.map (Ideal.Quotient.factor hJI) (J.isRestrictedSubringReduction hJ f) =
      I.isRestrictedSubringReduction hI f := by ext t; simp [MvPolynomial.coeff_map]

/-- Polynomial reduction is natural along continuous coefficient homomorphisms. -/
theorem isRestrictedSubringReduction_restrictedMapOfContinuous {S : Type*} [NormedCommRing S]
    [IsUltrametricDist S] {φ : R →+* S} (hφ : Continuous φ) {I : Ideal R} {J : Ideal S}
    (hI : IsOpen (I : Set R)) (hJ : IsOpen (J : Set S)) (hIJ : I ≤ J.comap φ) (f : Tate σ R) :
    J.isRestrictedSubringReduction hJ (restrictedMapOfContinuous hφ f) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (I.isRestrictedSubringReduction hI f) := by
  ext t; simp [MvPolynomial.coeff_map]

end Functoriality

section EvalCompatibility

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]

/-- **Polynomial reduction commutes with bounded evaluation** modulo open ideals. -/
theorem mk_restrictedEval₂OfBound_eq_eval₂_isRestrictedSubringReduction
    {φ : R →+* S} {a : Fin k → S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (ha : ∀ i, ‖a i‖ ≤ 1)
    {I : Ideal R} {J : Ideal S} (hI : IsOpen (I : Set R)) (hJ : IsOpen (J : Set S))
    (hIJ : I ≤ J.comap φ) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk J (φ.restrictedEval₂OfBound a hφ ha f) =
      (I.isRestrictedSubringReduction hI f).eval₂ (Ideal.quotientMap J φ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (a i)) := by
  let : DiscreteTopology (S ⧸ J) := QuotientAddGroup.discreteTopology (N := J.toAddSubgroup) hJ
  refine congrFun (denseRange_polynomialToRestricted.equalizer
    ((QuotientRing.isOpenQuotientMap_mk J).continuous.comp
      (φ.continuous_restrictedEval₂OfBound a hφ ha))
    (((I.isLocallyConstant_isRestrictedSubringReduction hI).comp
      (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (a i)))).continuous) (funext fun p ↦ ?_)) f
  simp only [Function.comp_apply, RingHom.restrictedEval₂OfBound_polynomial,
    Ideal.isRestrictedSubringReduction_polynomialToRestricted, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_map]
  rw [Ideal.quotientMap_comp_mk hIJ, ← MvPolynomial.hom_eval₂]

/-- **Polynomial reduction commutes with contractive evaluation** modulo open ideals. -/
theorem mk_restrictedEval₂_eq_eval₂_isRestrictedSubringReduction
    {φ : R →+* S} {a : Fin k → S} (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) (ha : ∀ i, ‖a i‖ ≤ 1)
    {I : Ideal R} {J : Ideal S} (hI : IsOpen (I : Set R)) (hJ : IsOpen (J : Set S))
    (hIJ : I ≤ J.comap φ) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk J (restrictedEval₂ φ a hφ ha f) =
      (I.isRestrictedSubringReduction hI f).eval₂ (Ideal.quotientMap J φ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (a i)) := by
  have hφ1 : ∀ r, ‖φ r‖ ≤ 1 * ‖r‖ := fun r ↦ by simpa using hφ r
  rw [← RingHom.restrictedEval₂OfBound_eq_restrictedEval₂ φ a hφ1 ha hφ]
  exact mk_restrictedEval₂OfBound_eq_eval₂_isRestrictedSubringReduction hφ1 ha hI hJ hIJ f

end EvalCompatibility

end TauCeti.MvPowerSeries

/-! ### Further results -/

public section

namespace Ideal

open Filter Topology

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

private theorem finite_support_mk_coeff_isRestricted (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    (Function.support fun ν ↦
      Ideal.Quotient.mk J (MvPowerSeries.coeff ν (f : MvPowerSeries σ R))).Finite := by
  obtain ⟨ε, hε, hball⟩ :=
    NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp (hJ.mem_nhds J.zero_mem)
  have hfin : {ν | ε ≤ ‖MvPowerSeries.coeff ν (f : MvPowerSeries σ R)‖}.Finite := by
    simpa [eventually_cofinite, not_lt] using f.property.eventually (gt_mem_nhds hε)
  refine hfin.subset fun ν hν ↦ ?_
  rw [Function.mem_support, Ne, Ideal.Quotient.eq_zero_iff_mem] at hν
  exact not_lt.mp fun hlt ↦ hν (hball (Set.mem_ofPred_eq.mpr hlt))

private noncomputable def isRestrictedReductionFun (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) : MvPolynomial σ (R ⧸ J) :=
  .ofCoeff (Finsupp.ofSupportFinite _ (finite_support_mk_coeff_isRestricted J hJ f))

private theorem coe_isRestrictedReductionFun (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    (isRestrictedReductionFun J hJ f : MvPowerSeries σ (R ⧸ J)) =
      MvPowerSeries.map (Ideal.Quotient.mk J) (f : MvPowerSeries σ R) := by
  ext ν; simp [MvPolynomial.coeff_coe, isRestrictedReductionFun, Finsupp.ofSupportFinite_coe]

/-- **Polynomial reduction of Gauss-normed restricted series modulo an open ideal.** -/
noncomputable def isRestrictedReduction (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1) →+* MvPolynomial σ (R ⧸ J) where
  toFun := isRestrictedReductionFun J hJ
  map_one' := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedReductionFun]
  map_mul' _ _ := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedReductionFun]
  map_zero' := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedReductionFun]
  map_add' _ _ := MvPolynomial.coe_injective _ _ <| by simp [coe_isRestrictedReductionFun]

/-- `isRestrictedReduction` reduces each coefficient modulo `J`. -/
@[simp]
theorem coeff_isRestrictedReduction (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) (ν : σ →₀ ℕ) :
    (J.isRestrictedReduction hJ f).coeff ν =
      Ideal.Quotient.mk J (MvPowerSeries.coeff ν (f : MvPowerSeries σ R)) := by
  rw [← MvPolynomial.coeff_coe]; simp [isRestrictedReduction, coe_isRestrictedReductionFun]

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

/-- Every polynomial over `R ⧸ J` lifts to a polynomial (hence restricted series) over `R`. -/
theorem isRestrictedReduction_surjective (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    Function.Surjective (J.isRestrictedReduction (σ := σ) hJ) := fun p ↦
  let ⟨q, hq⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective p
  ⟨TauCeti.MvPowerSeries.polynomialToRestricted (fun _ : σ ↦ 1) q, by simp [hq]⟩

/-- A series lies in `ker (J.isRestrictedReduction hJ)` iff every coefficient lies in `J`. -/
theorem mem_ker_isRestrictedReduction (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    f ∈ RingHom.ker (J.isRestrictedReduction hJ) ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries σ R) ∈ J := by
  rw [RingHom.mem_ker, MvPolynomial.ext_iff]; simp [Ideal.Quotient.eq_zero_iff_mem]

/-- Precomposing any map with `isRestrictedReduction` is continuous for the Gauss norm. -/
theorem continuous_comp_isRestrictedReduction {X : Type*} [TopologicalSpace X]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (g : MvPolynomial σ (R ⧸ J) → X) :
    Continuous (g ∘ J.isRestrictedReduction hJ) := by
  obtain ⟨ε, hε, hball⟩ :=
    NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp (hJ.mem_nhds J.zero_mem)
  refine continuous_iff_continuousAt.mpr fun f₀ ↦ tendsto_const_nhds.congr' ?_
  filter_upwards [Metric.ball_mem_nhds f₀ hε] with f hf
  rw [Metric.mem_ball, dist_eq_norm] at hf
  refine congrArg g (MvPolynomial.ext _ _ fun ν ↦ ?_)
  rw [coeff_isRestrictedReduction, coeff_isRestrictedReduction, Ideal.Quotient.eq]
  exact hball <| by
    simpa only [one_pow, Finsupp.prod, Finset.prod_const_one, mul_one, Set.mem_ofPred_eq,
      AddSubgroupClass.coe_sub, map_sub] using
      (MvPowerSeries.norm_coeff_mul_prod_le (f₀ - f) ν).trans_lt (by rwa [norm_sub_rev])

end Ideal

namespace TauCeti.MvPowerSeries

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- `isRestrictedReduction` is compatible with enlarging the open ideal. -/
@[simp]
theorem map_isRestrictedReduction {I J : Ideal R} (hI : IsOpen (I : Set R))
    (hJ : IsOpen (J : Set R)) (hIJ : I ≤ J)
    (f : _root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    MvPolynomial.map (Ideal.Quotient.factor hIJ) (I.isRestrictedReduction hI f) =
      J.isRestrictedReduction hJ f := by
  ext ν; simp [MvPolynomial.coeff_map]

/-- **Functoriality of `isRestrictedReduction` under bounded coefficient maps.** -/
theorem isRestrictedReduction_restrictedMap {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    {φ : R →+* S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (I : Ideal R) (hI : IsOpen (I : Set R))
    (J : Ideal S) (hJ : IsOpen (J : Set S)) (hIJ : I ≤ J.comap φ)
    (f : _root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    J.isRestrictedReduction hJ (restrictedMap φ hφ f) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (I.isRestrictedReduction hI f) := by
  ext ν; simp [MvPolynomial.coeff_map]

end TauCeti.MvPowerSeries
