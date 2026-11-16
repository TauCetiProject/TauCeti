/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Polynomial reduction of normed restricted power series modulo open ideals

For an ultrametric normed commutative ring `R` and an open ideal `J` of `R`, only finitely many
coefficients of a unit-radius restricted power series `f ∈ R⟨X⟩` lie outside `J`: an open ball
around `0` is contained in `J`, and the coefficients of `f` tend to `0` along the cofinite filter.
Reducing each coefficient modulo `J` therefore defines a surjective ring homomorphism
`TauCeti.MvPowerSeries.restrictedIdealReduction : R⟨X⟩ →+* MvPolynomial σ (R ⧸ J)` without any
completeness, valuation-ring, or field hypothesis on `R`.

Reduction has an open kernel, so it is locally constant and continuous into any topology on
`MvPolynomial σ (R ⧸ J)`. It is natural along bounded coefficient homomorphisms carrying an open
ideal of the source into an open ideal of the target, and commutes with bounded evaluation
(`RingHom.restrictedEval₂OfBound`) and contractive evaluation (`MvPowerSeries.restrictedEval₂`)
modulo any open ideal of a complete ultrametric target ring. Over the integer subring `𝒪[K]` of a
nonarchimedean normed field `K`, reducing modulo the maximal ideal `𝓂[K]` recovers the Gauss unit
ball reduction `TauCeti.MvPowerSeries.restrictedReduction` under
`TauCeti.MvPowerSeries.restrictedIntegerEquiv`.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedIdealReduction`: coefficientwise reduction
  `IsRestricted.subring (R := R) (fun _ : σ ↦ 1) →+* MvPolynomial σ (R ⧸ J)` modulo an open ideal
  `J` of `R`.

## Main results

* `TauCeti.MvPowerSeries.restrictedIdealReduction_eq_zero_iff` and
  `TauCeti.MvPowerSeries.isOpen_ker_restrictedIdealReduction`: the kernel consists of the
  restricted series whose coefficients all lie in `J`, and is open in `R⟨X⟩`.
* `TauCeti.MvPowerSeries.continuous_restrictedIdealReduction` and
  `TauCeti.MvPowerSeries.continuous_comp_restrictedIdealReduction`: continuity of
  `restrictedIdealReduction` into any topological space.
* `TauCeti.MvPowerSeries.restrictedIdealReduction_surjective`: every polynomial over `R ⧸ J` lifts
  to a restricted series, already to an embedded polynomial.
* `TauCeti.MvPowerSeries.restrictedIdealReduction_restrictedMap`: naturality along bounded
  coefficient homomorphisms.
* `TauCeti.MvPowerSeries.mk_restrictedEval₂OfBound_eq_eval₂_restrictedIdealReduction` and
  `TauCeti.MvPowerSeries.mk_restrictedEval₂_eq_eval₂_restrictedIdealReduction`: polynomial
  reduction commutes with bounded and contractive evaluation modulo open ideals.
* `TauCeti.MvPowerSeries.restrictedReduction_restrictedIntegerEquiv_eq_restrictedIdealReduction`:
  compatibility with Gauss unit-ball reduction over `𝒪[K]`.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §§5.1.1–5.1.3.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries Filter
open scoped Topology NormedField Valued

section OpenIdeal

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- Only finitely many coefficients of a unit-radius restricted series lie outside an open ideal,
since an open ball around `0` is contained in the ideal. -/
private theorem finite_support_mk_coeff (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    (Function.support fun t ↦ Ideal.Quotient.mk J (coeff t (f : MvPowerSeries σ R))).Finite := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hJ 0 J.zero_mem
  have hfin : {t | ε ≤ ‖coeff t (f : MvPowerSeries σ R)‖}.Finite := by
    simpa [eventually_cofinite, not_lt] using f.2.eventually (gt_mem_nhds hε)
  refine hfin.subset fun t ht ↦ ?_
  rw [Function.mem_support, Ne, Ideal.Quotient.eq_zero_iff_mem] at ht
  exact not_lt.mp fun hlt ↦ ht (hball (by simpa [dist_zero_right] using hlt))

/-- Coefficientwise reduction modulo an open ideal as a polynomial. -/
private noncomputable def restrictedIdealReductionFun (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) : MvPolynomial σ (R ⧸ J) :=
  .ofCoeff (Finsupp.ofSupportFinite _ (finite_support_mk_coeff J hJ f))

private theorem coe_restrictedIdealReductionFun (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    (restrictedIdealReductionFun J hJ f : MvPowerSeries σ (R ⧸ J)) =
      MvPowerSeries.map (Ideal.Quotient.mk J) (f : MvPowerSeries σ R) := by
  ext t; simp [MvPolynomial.coeff_coe, restrictedIdealReductionFun, Finsupp.ofSupportFinite_coe]

/-- **Polynomial reduction of normed restricted power series modulo an open ideal.** Because `J`
is open and the coefficients of `f ∈ R⟨X⟩` tend to zero, only finitely many coefficients survive
modulo `J`. -/
noncomputable def restrictedIdealReduction (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    IsRestricted.subring (R := R) (fun _ : σ ↦ 1) →+* MvPolynomial σ (R ⧸ J) where
  toFun := restrictedIdealReductionFun J hJ
  map_one' := MvPolynomial.coe_injective _ _ <| by simp [coe_restrictedIdealReductionFun]
  map_mul' _ _ := MvPolynomial.coe_injective _ _ <| by simp [coe_restrictedIdealReductionFun]
  map_zero' := MvPolynomial.coe_injective _ _ <| by simp [coe_restrictedIdealReductionFun]
  map_add' _ _ := MvPolynomial.coe_injective _ _ <| by simp [coe_restrictedIdealReductionFun]

/-- Each coefficient of `restrictedIdealReduction J hJ f` is the class modulo `J` of the
corresponding coefficient of `f`. -/
@[simp]
theorem coeff_restrictedIdealReduction (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) (t : σ →₀ ℕ) :
    (restrictedIdealReduction J hJ f).coeff t =
      Ideal.Quotient.mk J (coeff t (f : MvPowerSeries σ R)) := by
  rw [← MvPolynomial.coeff_coe]; simp [restrictedIdealReduction, coe_restrictedIdealReductionFun]

/-- A restricted series reduces to `0` modulo an open ideal `J` if and only if all of its
coefficients belong to `J`. -/
theorem restrictedIdealReduction_eq_zero_iff {J : Ideal R} (hJ : IsOpen (J : Set R))
    {f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)} :
    restrictedIdealReduction J hJ f = 0 ↔ ∀ t, coeff t (f : MvPowerSeries σ R) ∈ J := by
  simp [MvPolynomial.ext_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- The kernel of `restrictedIdealReduction J hJ` is open in `R⟨X⟩`, since an open ball around `0`
in `R` lies inside `J` and the Gauss norm bounds every coefficient norm. -/
theorem isOpen_ker_restrictedIdealReduction (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    IsOpen (RingHom.ker (restrictedIdealReduction (σ := σ) J hJ) :
      Set (IsRestricted.subring (R := R) (fun _ : σ ↦ 1))) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hJ 0 J.zero_mem
  refine AddSubgroup.isOpen_of_mem_nhds (RingHom.ker (restrictedIdealReduction J hJ)).toAddSubgroup
    (g := 0) ?_
  filter_upwards [Metric.ball_mem_nhds 0 hε] with f hf
  rw [SetLike.mem_coe, Submodule.mem_toAddSubgroup, RingHom.mem_ker,
    restrictedIdealReduction_eq_zero_iff hJ]
  exact fun t ↦ hball <| by
    simpa [dist_zero_right] using (MvPowerSeries.norm_coeff_le_norm f t).trans_lt
      (by simpa [dist_zero_right] using hf)

/-- Any post-composition of `restrictedIdealReduction J hJ` into a topological space is continuous,
because `restrictedIdealReduction J hJ` has open kernel and is therefore locally constant. -/
theorem continuous_comp_restrictedIdealReduction {Z : Type*} [TopologicalSpace Z]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (g : MvPolynomial σ (R ⧸ J) → Z) :
    Continuous (fun f ↦ g (restrictedIdealReduction J hJ f)) := by
  refine continuous_iff_continuousAt.mpr fun f₀ ↦ Filter.tendsto_def.mpr fun W hW ↦ ?_
  filter_upwards [((isOpen_ker_restrictedIdealReduction (σ := σ) J hJ).preimage
    (f := (· - f₀)) (continuous_id.sub continuous_const)).mem_nhds (by simp)] with f hf
  have hfeq : restrictedIdealReduction J hJ f = restrictedIdealReduction J hJ f₀ :=
    by simpa [sub_eq_zero] using hf
  simpa only [Set.mem_preimage, hfeq] using mem_of_mem_nhds hW

/-- `restrictedIdealReduction J hJ` is continuous into any topology on `MvPolynomial σ (R ⧸ J)`. -/
theorem continuous_restrictedIdealReduction (J : Ideal R)
    [TopologicalSpace (MvPolynomial σ (R ⧸ J))] (hJ : IsOpen (J : Set R)) :
    Continuous (restrictedIdealReduction (σ := σ) J hJ) :=
  continuous_comp_restrictedIdealReduction J hJ id

/-- On embedded polynomials, `restrictedIdealReduction` reduces coefficients modulo `J`. -/
@[simp]
theorem restrictedIdealReduction_polynomialToRestricted (J : Ideal R) (hJ : IsOpen (J : Set R))
    (p : MvPolynomial σ R) :
    restrictedIdealReduction J hJ (polynomialToRestricted (fun _ : σ ↦ 1) p) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  ext t; simp [MvPolynomial.coeff_map, polynomialToRestricted_apply, MvPolynomial.coeff_coe]

/-- Constant restricted series reduce to constant polynomials modulo `J`. -/
@[simp]
theorem restrictedIdealReduction_algebraMap (J : Ideal R) (hJ : IsOpen (J : Set R)) (r : R) :
    restrictedIdealReduction (σ := σ) J hJ (algebraMap R _ r) =
      MvPolynomial.C (Ideal.Quotient.mk J r) := by
  simpa [← MvPolynomial.algebraMap_eq] using
    restrictedIdealReduction_polynomialToRestricted (σ := σ) J hJ (MvPolynomial.C r)

/-- Each coordinate variable reduces to the corresponding polynomial variable. -/
@[simp]
theorem restrictedIdealReduction_X (J : Ideal R) (hJ : IsOpen (J : Set R)) (i : σ) :
    restrictedIdealReduction J hJ ⟨X i, isRestricted_X (fun _ : σ ↦ 1) i⟩ = MvPolynomial.X i := by
  simpa using restrictedIdealReduction_polynomialToRestricted J hJ (MvPolynomial.X i)

/-- Every polynomial over `R ⧸ J` lifts to a restricted series, already to a polynomial. -/
theorem restrictedIdealReduction_surjective (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    Function.Surjective (restrictedIdealReduction (σ := σ) J hJ) := fun p ↦ by
  obtain ⟨q, rfl⟩ :=
    MvPolynomial.map_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective p
  exact ⟨polynomialToRestricted (fun _ : σ ↦ 1) q, by simp⟩

/-- Reduction is compatible with passing to a larger open ideal. -/
@[simp]
theorem map_restrictedIdealReduction {J I : Ideal R} (hJ : IsOpen (J : Set R))
    (hI : IsOpen (I : Set R)) (hJI : J ≤ I) (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    MvPolynomial.map (Ideal.Quotient.factor hJI) (restrictedIdealReduction J hJ f) =
      restrictedIdealReduction I hI f := by
  ext t; simp [MvPolynomial.coeff_map]

/-- Polynomial reduction is natural along a bounded coefficient homomorphism carrying an open
ideal of the source into an open ideal of the target. -/
theorem restrictedIdealReduction_restrictedMap {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    {φ : R →+* S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) {I : Ideal R} {J : Ideal S}
    (hI : IsOpen (I : Set R)) (hJ : IsOpen (J : Set S)) (hIJ : I ≤ J.comap φ)
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ 1)) :
    restrictedIdealReduction J hJ (restrictedMap φ hφ f) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (restrictedIdealReduction I hI f) := by
  ext t; simp [MvPolynomial.coeff_map]

end OpenIdeal

section EvalCompatibility

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]

/-- **Polynomial reduction commutes with bounded evaluation.** Modulo an open ideal `J` of `S`,
evaluating a restricted series `f ∈ R⟨X₁, …, Xₖ⟩` along a bounded homomorphism `φ : R →+* S` at
unit-bounded arguments `a` agrees with polynomial evaluation of its reduction modulo `I`, whenever
`φ` carries `I` into `J`. -/
theorem mk_restrictedEval₂OfBound_eq_eval₂_restrictedIdealReduction
    (φ : R →+* S) (a : Fin k → S) {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (ha : ∀ i, ‖a i‖ ≤ 1)
    {I : Ideal R} {J : Ideal S} (hI : IsOpen (I : Set R)) (hJ : IsOpen (J : Set S))
    (hIJ : I ≤ J.comap φ) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk J (φ.restrictedEval₂OfBound a hφ ha f) =
      (restrictedIdealReduction I hI f).eval₂ (Ideal.quotientMap J φ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (a i)) := by
  let : DiscreteTopology (S ⧸ J) := QuotientAddGroup.discreteTopology (N := J.toAddSubgroup) hJ
  refine congrFun (denseRange_polynomialToRestricted.equalizer
    ((QuotientRing.isOpenQuotientMap_mk J).continuous.comp
      (φ.continuous_restrictedEval₂OfBound a hφ ha))
    (continuous_comp_restrictedIdealReduction I hI
      (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (fun i ↦ Ideal.Quotient.mk J (a i))))
    (funext fun p ↦ ?_)) f
  simp only [Function.comp_apply, RingHom.restrictedEval₂OfBound_polynomial,
    restrictedIdealReduction_polynomialToRestricted, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_map]
  rw [show (Ideal.quotientMap J φ hIJ).comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp φ
    from RingHom.ext fun _ ↦ by simp, ← MvPolynomial.hom_eval₂]

/-- **Polynomial reduction commutes with contractive evaluation** modulo open ideals. -/
theorem mk_restrictedEval₂_eq_eval₂_restrictedIdealReduction
    (φ : R →+* S) (a : Fin k → S) (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) (ha : ∀ i, ‖a i‖ ≤ 1)
    {I : Ideal R} {J : Ideal S} (hI : IsOpen (I : Set R)) (hJ : IsOpen (J : Set S))
    (hIJ : I ≤ J.comap φ) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk J (restrictedEval₂ φ a hφ ha f) =
      (restrictedIdealReduction I hI f).eval₂ (Ideal.quotientMap J φ hIJ)
        (fun i ↦ Ideal.Quotient.mk J (a i)) := by
  have hφ1 : ∀ r, ‖φ r‖ ≤ 1 * ‖r‖ := fun r ↦ by simpa using hφ r
  rw [← RingHom.restrictedEval₂OfBound_eq_restrictedEval₂ φ a hφ1 ha hφ]
  exact mk_restrictedEval₂OfBound_eq_eval₂_restrictedIdealReduction φ a hφ1 ha hI hJ hIJ f

end EvalCompatibility

section UnitBallComparison

variable {σ K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Over the integer subring `𝒪[K]` of a nonarchimedean normed field, open-ideal reduction modulo
`𝓂[K]` agrees with Gauss unit-ball reduction under `restrictedIntegerEquiv`. -/
theorem restrictedReduction_restrictedIntegerEquiv_eq_restrictedIdealReduction
    (f : IsRestricted.subring (R := 𝒪[K]) (fun _ : σ ↦ 1)) :
    restrictedReduction (restrictedIntegerEquiv f) =
      restrictedIdealReduction 𝓂[K] TauCeti.isOpen_maximalIdeal_integer f :=
  MvPolynomial.ext _ _ fun t ↦ (coeff_restrictedReduction (restrictedIntegerEquiv f) t).trans <|
    (congrArg (IsLocalRing.residue 𝒪[K]) (Subtype.ext (coeff_restrictedIntegerEquiv f t))).trans <|
      (IsLocalRing.residue_def _).trans
        (coeff_restrictedIdealReduction 𝓂[K] TauCeti.isOpen_maximalIdeal_integer f t).symm

end UnitBallComparison

end TauCeti.MvPowerSeries
