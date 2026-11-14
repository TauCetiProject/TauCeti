/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.Adic
public import TauCeti.RingTheory.Huber.Restricted.Comparison
public import TauCeti.RingTheory.Huber.Restricted.Reduction.Limit
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty

import TauCeti.Topology.Algebra.Nonarchimedean.Quotient
import TauCeti.Topology.Algebra.Module.Quotient

/-!
# Polynomial reduction, adic structure, and universal properties under the Gauss norm

For an ultrametric normed commutative ring `R`, the unit-radius Gauss-normed restricted-series
subring `MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)` is topologically
isomorphic to the trivial-weight Huber ring via `TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv`,
and when `R` is complete to the completed Huber algebra `restrictedMvPowerSeriesCompletion k R` via
`TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussEquiv`.

This file transports open-ideal polynomial reduction, adic quotient and inverse-limit
descriptions, adic Noetherianity, and the comparison between topological and normed evaluation
across that equivalence:

* `Ideal.isRestrictedSubringReduction` reduces a unit-radius restricted series modulo any open
  ideal `J` of `R` to a polynomial in `MvPolynomial (Fin k) (R ⧸ J)`, commuting with bounded
  coefficient maps (`Ideal.isRestrictedSubringReduction_restrictedMap`) and, over the valuation
  ring `𝒪[K]` of a nonarchimedean field, agreeing with the Gauss unit-ball reduction
  `TauCeti.MvPowerSeries.restrictedReduction`
  (`Ideal.map_isRestrictedSubringReduction_maximalIdeal_eq_restrictedReduction`).
* When `I` is a finitely generated ideal of definition of `R`, the extended ideal `I · R⟨X⟩`
  defines the Gauss-norm topology
  (`TauCeti.MvPowerSeries.isAdic_map_algebraMap_isRestrictedSubring`) and
  `R⟨X⟩ ⧸ (I · R⟨X⟩) ^ m ≃ₐ[R] (R ⧸ I ^ m)[X]`
  (`TauCeti.MvPowerSeries.quotientPowIsRestrictedSubringEquivMvPolynomialQuotient`). Consequently,
  when `R` is an adic ring of finite ideal type, so is `R⟨X⟩`, and if `R` is also Noetherian then
  `R⟨X⟩` is Noetherian
  (`TauCeti.MvPowerSeries.isNoetherianRing_isRestrictedSubring_of_isAdicRing`).
* When `R` is complete and `IsAdic I` holds (even without `I.FG`), `R⟨X⟩` is the limit in
  `CommRingCat` of `(R ⧸ I ^ (n + 1))[X]`
  (`TauCeti.MvPowerSeries.isLimitIsRestrictedSubringReductionPowSuccCone`,
  `TauCeti.MvPowerSeries.existsUnique_isRestrictedSubringReduction_pow_succ_eq`).
* Both topological power-bounded evaluation (`TauCeti.MvPowerSeries.restrictedLift`) and bounded
  normed evaluation (`RingHom.restrictedEval₂OfBound`) commute with open-ideal reduction. Because
  `‖φ r‖ ≤ C * ‖r‖` implies continuity of `φ` and `‖a i‖ ≤ 1` implies `IsPowerBounded (a i)`
  (`IsPowerBounded.of_norm_le_one`), `RingHom.restrictedEval₂OfBound` is a special case of
  `TauCeti.MvPowerSeries.restrictedLift` and agrees with it whenever the normed hypotheses hold
  (`TauCeti.MvPowerSeries.restrictedLift_eq_restrictedEval₂OfBound`); into a complete separated
  linearly topologised target ring every element is power-bounded (`isBounded_of_isLinearTopology`),
  so neither norm bounds nor separate power-boundedness hypotheses are needed (see
  `TauCeti.MvPowerSeries.existsUnique_continuous_ringHom_isRestricted_subring_of_isLinearTopology`).

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§1.4, 5.1.1–5.1.3.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.5.
* T. Wedhorn, *Adic Spaces*, §5.6, Proposition 5.50.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped NormedField

namespace Ideal

open TauCeti.Huber

section NormedRing

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- **Open-ideal polynomial reduction on unit-radius Gauss-normed restricted series.** For an open
ideal `J` of an ultrametric normed commutative ring `R`, only finitely many coefficients of a
unit-radius restricted series lie outside `J`, yielding a ring homomorphism to `(R ⧸ J)[X₁, …, Xₖ]`
by transporting `Ideal.restrictedReduction` across `restrictedMvPowerSeriesGaussEquiv`. -/
noncomputable def isRestrictedSubringReduction (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+*
      MvPolynomial (Fin k) (R ⧸ J) :=
  (J.restrictedReduction hJ).comp
    (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm.toRingHom

/-- `Ideal.isRestrictedSubringReduction` transports `Ideal.restrictedReduction` across
`restrictedMvPowerSeriesGaussEquiv`. -/
@[simp]
theorem isRestrictedSubringReduction_restrictedMvPowerSeriesGaussEquiv (J : Ideal R)
    (hJ : IsOpen (J : Set R))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    J.isRestrictedSubringReduction hJ (restrictedMvPowerSeriesGaussEquiv f) =
      J.restrictedReduction hJ f := by
  simp [isRestrictedSubringReduction]

/-- The `ν`-th polynomial coefficient of `J.isRestrictedSubringReduction hJ f` is the `J`-residue
of the `ν`-th power-series coefficient of `f`. -/
@[simp]
theorem coeff_isRestrictedSubringReduction (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) (ν : Fin k →₀ ℕ) :
    (J.isRestrictedSubringReduction hJ f).coeff ν =
      Ideal.Quotient.mk J (MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) R)) := by
  simp [isRestrictedSubringReduction]

/-- On embedded polynomials, `Ideal.isRestrictedSubringReduction` reduces coefficients
modulo `J`. -/
@[simp]
theorem isRestrictedSubringReduction_polynomialToRestricted (J : Ideal R) (hJ : IsOpen (J : Set R))
    (p : MvPolynomial (Fin k) R) :
    J.isRestrictedSubringReduction hJ
        (TauCeti.MvPowerSeries.polynomialToRestricted (fun _ : Fin k ↦ (1 : ℝ)) p) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  ext ν
  simp [MvPolynomial.coeff_map]

/-- `Ideal.isRestrictedSubringReduction` sends a constant series to the reduced constant
polynomial. -/
@[simp]
theorem isRestrictedSubringReduction_algebraMap (J : Ideal R) (hJ : IsOpen (J : Set R)) (r : R) :
    J.isRestrictedSubringReduction (k := k) hJ (algebraMap R _ r) =
      MvPolynomial.C (Ideal.Quotient.mk J r) := by
  simpa using J.isRestrictedSubringReduction_polynomialToRestricted (k := k) hJ (MvPolynomial.C r)

/-- `Ideal.isRestrictedSubringReduction` sends each coordinate variable `Xᵢ` to
`MvPolynomial.X i`. -/
@[simp]
theorem isRestrictedSubringReduction_X (J : Ideal R) (hJ : IsOpen (J : Set R)) (i : Fin k) :
    J.isRestrictedSubringReduction hJ ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ =
      MvPolynomial.X i := by
  have hX : (⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ :
      MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) =
      TauCeti.MvPowerSeries.polynomialToRestricted (fun _ : Fin k ↦ (1 : ℝ)) (MvPolynomial.X i) :=
    Subtype.ext (by simp)
  rw [hX, isRestrictedSubringReduction_polynomialToRestricted, MvPolynomial.map_X]

/-- Open-ideal polynomial reduction on `R⟨X₁, …, Xₖ⟩` is surjective. -/
theorem isRestrictedSubringReduction_surjective (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    Function.Surjective (J.isRestrictedSubringReduction (k := k) hJ) :=
  (J.restrictedReduction_surjective hJ).comp restrictedMvPowerSeriesGaussEquiv.symm.surjective

/-- A unit-radius restricted series lies in the kernel of `J.isRestrictedSubringReduction hJ`
if and only if every coefficient lies in `J`. -/
theorem mem_ker_isRestrictedSubringReduction (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    f ∈ RingHom.ker (J.isRestrictedSubringReduction hJ) ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) R) ∈ J := by
  rw [isRestrictedSubringReduction, RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker,
    J.mem_ker_restrictedReduction hJ]
  simp

/-- The kernel of `J.isRestrictedSubringReduction hJ` is open in the Gauss-norm topology. -/
theorem isOpen_ker_isRestrictedSubringReduction (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    IsOpen (RingHom.ker (J.isRestrictedSubringReduction (k := k) hJ) :
      Set (MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) :=
  (J.isOpen_ker_restrictedReduction hJ).preimage continuous_restrictedMvPowerSeriesGaussEquiv_symm

/-- Open-ideal polynomial reduction is locally constant for the Gauss-norm topology. -/
theorem isLocallyConstant_isRestrictedSubringReduction (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    IsLocallyConstant (J.isRestrictedSubringReduction (k := k) hJ) :=
  (J.isRestrictedSubringReduction (k := k) hJ).toAddMonoidHom.isLocallyConstant_of_isOpen_ker
    (J.isOpen_ker_isRestrictedSubringReduction hJ)

/-- Open-ideal polynomial reduction on `R⟨X₁, …, Xₖ⟩` is compatible with enlarging the ideal. -/
@[simp]
theorem map_isRestrictedSubringReduction {J I : Ideal R} (hJ : IsOpen (J : Set R))
    (hI : IsOpen (I : Set R)) (hJI : J ≤ I)
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    MvPolynomial.map (Ideal.Quotient.factor hJI) (J.isRestrictedSubringReduction hJ f) =
      I.isRestrictedSubringReduction hI f := by
  ext ν
  simp [MvPolynomial.coeff_map]

/-- Open-ideal polynomial reduction commutes with bounded coefficient maps
`TauCeti.MvPowerSeries.restrictedMap`; continuity of `φ` is not assumed separately. -/
theorem isRestrictedSubringReduction_restrictedMap {S : Type*} [NormedCommRing S]
    [IsUltrametricDist S] (J : Ideal R) (hJ : IsOpen (J : Set R)) (K : Ideal S)
    (hK : IsOpen (K : Set S)) {φ : R →+* S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    (hJK : J ≤ K.comap φ)
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    K.isRestrictedSubringReduction hK (TauCeti.MvPowerSeries.restrictedMap φ hφ f) =
      MvPolynomial.map (Ideal.quotientMap K φ hJK) (J.isRestrictedSubringReduction hJ f) := by
  ext ν
  simp [MvPolynomial.coeff_map, TauCeti.MvPowerSeries.coeff_restrictedMap]

/-- Over a complete ultrametric normed commutative ring, `Ideal.isRestrictedSubringReduction`
identifies with `Ideal.restrictedCompletionReduction` across
`restrictedMvPowerSeriesCompletionGaussEquiv`. -/
@[simp]
theorem isRestrictedSubringReduction_restrictedMvPowerSeriesCompletionGaussEquiv [CompleteSpace R]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (x : restrictedMvPowerSeriesCompletion k R) :
    J.isRestrictedSubringReduction hJ (restrictedMvPowerSeriesCompletionGaussEquiv x) =
      J.restrictedCompletionReduction hJ x := by
  let : TopologicalSpace (MvPolynomial (Fin k) (R ⧸ J)) := ⊥
  have : DiscreteTopology (MvPolynomial (Fin k) (R ⧸ J)) := ⟨rfl⟩
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq
      ((J.isLocallyConstant_isRestrictedSubringReduction hJ).continuous.comp
        continuous_restrictedMvPowerSeriesCompletionGaussEquiv)
      (J.isLocallyConstant_restrictedCompletionReduction hJ).continuous)
    fun f ↦ ?_
  simp

end NormedRing

section ValuationUnitBall

variable {k : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Over the valuation ring `Valued.integer K` of a nontrivially normed ultrametric field `K`,
open-ideal reduction modulo the maximal ideal agrees with the Gauss unit-ball reduction
`TauCeti.MvPowerSeries.restrictedReduction` under `TauCeti.MvPowerSeries.restrictedIntegerEquiv`. -/
theorem map_isRestrictedSubringReduction_maximalIdeal_eq_restrictedReduction
    (f : MvPowerSeries.IsRestricted.subring (R := Valued.integer K) (fun _ : Fin k ↦ 1)) :
    MvPolynomial.map
        (Ideal.Quotient.lift (IsLocalRing.maximalIdeal (Valued.integer K))
          (IsLocalRing.residue (Valued.integer K))
          fun _ ↦ (IsLocalRing.residue_eq_zero_iff _).mpr)
        ((IsLocalRing.maximalIdeal (Valued.integer K)).isRestrictedSubringReduction
          Valued.isOpen_maximalIdeal f) =
      TauCeti.MvPowerSeries.restrictedReduction
        (TauCeti.MvPowerSeries.restrictedIntegerEquiv f) := by
  ext ν
  rw [MvPolynomial.coeff_map, coeff_isRestrictedSubringReduction, Ideal.Quotient.lift_mk,
    TauCeti.MvPowerSeries.coeff_restrictedReduction]
  exact congrArg (IsLocalRing.residue (Valued.integer K))
    (Subtype.ext (TauCeti.MvPowerSeries.coeff_restrictedIntegerEquiv f ν).symm)

/-- Symmetric form of `map_isRestrictedSubringReduction_maximalIdeal_eq_restrictedReduction` on
elements of the Gauss unit ball of `K⟨X₁, …, Xₖ⟩`. -/
theorem restrictedReduction_eq_map_isRestrictedSubringReduction_maximalIdeal
    (g : Subring.unitClosedBall
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin k ↦ 1))) :
    TauCeti.MvPowerSeries.restrictedReduction g =
      MvPolynomial.map
        (Ideal.Quotient.lift (IsLocalRing.maximalIdeal (Valued.integer K))
          (IsLocalRing.residue (Valued.integer K))
          fun _ ↦ (IsLocalRing.residue_eq_zero_iff _).mpr)
        ((IsLocalRing.maximalIdeal (Valued.integer K)).isRestrictedSubringReduction
          Valued.isOpen_maximalIdeal
          (TauCeti.MvPowerSeries.restrictedIntegerEquiv.symm g)) := by
  rw [map_isRestrictedSubringReduction_maximalIdeal_eq_restrictedReduction,
    RingEquiv.apply_symm_apply]

end ValuationUnitBall

end Ideal

namespace RingHom

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]

/-- Reducing bounded normed evaluation `φ.restrictedEval₂OfBound a hφ ha f` modulo an open ideal `K`
of `S` agrees with polynomial evaluation of `J.isRestrictedSubringReduction hJ f` at the reduced
point. -/
theorem quotientMk_restrictedEval₂OfBound (φ : R →+* S) (a : Fin k → S) {C : ℝ}
    (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (ha : ∀ i, ‖a i‖ ≤ 1)
    {J : Ideal R} (hJ : IsOpen (J : Set R)) {K : Ideal S} (hK : IsOpen (K : Set S))
    (hJK : J ≤ K.comap φ)
    (f : MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk K (φ.restrictedEval₂OfBound a hφ ha f) =
      (J.isRestrictedSubringReduction hJ f).eval₂ (Ideal.quotientMap K φ hJK)
        (Ideal.Quotient.mk K ∘ a) := by
  let : DiscreteTopology (S ⧸ K) := Submodule.Quotient.discreteTopology_of_isOpen K hK
  have : ∀ _ : Fin k, Fact ((0 : ℝ) < 1) := fun _ ↦ ⟨zero_lt_one⟩
  have hcont₁ : Continuous ((Ideal.Quotient.mk K).comp (φ.restrictedEval₂OfBound a hφ ha)) :=
    (QuotientRing.isOpenQuotientMap_mk K).continuous.comp
      (φ.continuous_restrictedEval₂OfBound a hφ ha)
  let rhs := (MvPolynomial.eval₂Hom (Ideal.quotientMap K φ hJK)
    (Ideal.Quotient.mk K ∘ a)).comp (J.isRestrictedSubringReduction hJ)
  have hcont₂ : Continuous rhs :=
    ((J.isLocallyConstant_isRestrictedSubringReduction hJ).comp
      (MvPolynomial.eval₂Hom (Ideal.quotientMap K φ hJK) (Ideal.Quotient.mk K ∘ a))).continuous
  have heq := TauCeti.MvPowerSeries.isRestricted_subring_ringHom_ext_of_continuous hcont₁ hcont₂
    (fun r ↦ by simp [rhs]) (fun i ↦ by simp [rhs])
  exact congr($heq f)

end RingHom

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries TauCeti.Huber

section AdicQuotient

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- When `I` is a finitely generated ideal of definition of an ultrametric normed commutative ring
`R`, the Gauss-norm topology on `R⟨X₁, …, Xₖ⟩` is the adic topology of the extended ideal
`I · R⟨X₁, …, Xₖ⟩`. -/
theorem isAdic_map_algebraMap_isRestrictedSubring {I : Ideal R} (hI : IsAdic I) (hfg : I.FG) :
    IsAdic (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) := by
  let e := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  let h : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight ≃ₜ
      IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) :=
    { toEquiv := e.toEquiv
      continuous_toFun := continuous_restrictedMvPowerSeriesGaussEquiv
      continuous_invFun := continuous_restrictedMvPowerSeriesGaussEquiv_symm }
  have hadic := (isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg).comap
    e.symm h.symm.isInducing
  have heq : (I.map (algebraMap R
      (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight))).comap
        e.symm =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) := by
    have hcomap : (I.map (algebraMap R
        (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R))
          isWeightFamily_one_weight))).comap e.symm =
        Ideal.map e.toRingHom (I.map (algebraMap R
          (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R))
            isWeightFamily_one_weight))) := by
      ext f
      rw [Ideal.mem_comap, Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
      exact ⟨fun hf ↦ ⟨e.symm f, hf, by simp [e]⟩,
        by rintro ⟨g, hg, rfl⟩; simpa [e] using hg⟩
    rw [hcomap, Ideal.map_map]
    refine congrArg (I.map ·) (RingHom.ext fun r ↦ ?_)
    simp [e, algebraMap_weightedRestrictedSubring]
  exact heq ▸ hadic

/-- For a finitely generated ideal of definition `I` of `R`, the kernel of polynomial reduction
modulo `I ^ m` on `R⟨X₁, …, Xₖ⟩` is `(I · R⟨X₁, …, Xₖ⟩) ^ m`. -/
theorem ker_isRestrictedSubringReduction_pow {I : Ideal R} (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    RingHom.ker ((I ^ m).isRestrictedSubringReduction (k := k) (hI.isOpen_pow m)) =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ^ m := by
  let e := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  have hmap : Ideal.map e.toRingHom
      (I.map (weightedC (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) ^ m) =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ^ m := by
    rw [Ideal.map_pow, Ideal.map_map]
    exact congrArg (· ^ m) (congrArg (I.map ·)
      (RingHom.ext fun r ↦ restrictedMvPowerSeriesGaussEquiv_weightedC r))
  ext f
  rw [← hmap, Ideal.isRestrictedSubringReduction, RingHom.mem_ker, RingHom.comp_apply,
    ← RingHom.mem_ker, ker_restrictedReduction_pow hI hfg m]
  exact ⟨fun hf ↦ by simpa [e] using Ideal.mem_map_of_mem e.toRingHom hf, fun hf ↦ by
    simpa [e] using Ideal.mem_map_of_mem e.symm.toRingHom hf⟩

/-- **Adic quotient of Gauss-normed restricted power series.** Modulo `(I · R⟨X⟩) ^ m` for a
finitely generated ideal of definition `I`, unit-radius restricted series reduce to the polynomial
algebra `(R ⧸ I ^ m)[X₁, …, Xₖ]`. -/
noncomputable def quotientPowIsRestrictedSubringEquivMvPolynomialQuotient {I : Ideal R}
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ^ m) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I ^ m) := by
  let e := (Ideal.quotEquivOfEq (ker_isRestrictedSubringReduction_pow (k := k) hI hfg m).symm).trans
    (((I ^ m).isRestrictedSubringReduction (hI.isOpen_pow m)).quotientKerEquivOfSurjective
      ((I ^ m).isRestrictedSubringReduction_surjective (hI.isOpen_pow m)))
  refine AlgEquiv.ofRingEquiv (f := e) fun r ↦ ?_
  have he : e (algebraMap R _ r) =
      (I ^ m).isRestrictedSubringReduction (hI.isOpen_pow m) (algebraMap R _ r) := by
    rw [← Ideal.Quotient.mk_algebraMap]
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [he, Ideal.isRestrictedSubringReduction_algebraMap]
  rfl

/-- `quotientPowIsRestrictedSubringEquivMvPolynomialQuotient` computes
`Ideal.isRestrictedSubringReduction` on representatives. -/
@[simp]
theorem quotientPowIsRestrictedSubringEquivMvPolynomialQuotient_mk {I : Ideal R}
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientPowIsRestrictedSubringEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ f) =
      (I ^ m).isRestrictedSubringReduction (hI.isOpen_pow m) f := by
  simp [quotientPowIsRestrictedSubringEquivMvPolynomialQuotient]

/-- Over an ultrametric normed commutative ring whose topology is adic of finite ideal type and
complete, unit-radius restricted series form an adic ring of finite ideal type. -/
instance isAdicRing_isRestrictedSubring [IsAdicRing R] :
    IsAdicRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
  obtain ⟨hfg, hI, -⟩ := IsAdicRing.ideal_spec R
  let J := (IsAdicRing.ideal R).map
    (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))
  have hJ : IsAdic J := isAdic_map_algebraMap_isRestrictedSubring hI hfg
  exact ⟨J, hfg.map _, hJ, hJ.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩⟩

/-- Unit-radius restricted power series over a Noetherian adic ultrametric normed commutative ring
form a Noetherian ring. -/
instance isNoetherianRing_isRestrictedSubring_of_isAdicRing [IsAdicRing R] [IsNoetherianRing R] :
    IsNoetherianRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
  obtain ⟨-, hI, hcomp⟩ := IsAdicRing.ideal_spec R
  have : CompleteSpace R := (hI.isAdicComplete_iff.mp hcomp).1
  have := isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic k hI
  exact isNoetherianRing_of_ringEquiv _
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R))

end AdicQuotient

section InverseLimit

variable {k : ℕ} {R : Type u} [NormedCommRing R] [IsUltrametricDist R] {I : Ideal R}

/-- Cone in `CommRingCat` with apex `IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)` over
`polynomialQuotientPowSuccDiagram k I` given by `Ideal.isRestrictedSubringReduction`. -/
noncomputable def isRestrictedSubringReductionPowSuccCone (hI : IsAdic I) :
    Cone (polynomialQuotientPowSuccDiagram k I) where
  pt := .of (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))
  π :=
    { app n := CommRingCat.ofHom
        ((I ^ (n.unop + 1)).isRestrictedSubringReduction (hI.isOpen_pow (n.unop + 1)))
      naturality {m n} f := by
        dsimp
        exact CommRingCat.hom_ext <| RingHom.ext fun g ↦
          (Ideal.map_isRestrictedSubringReduction (hI.isOpen_pow (m.unop + 1))
            (hI.isOpen_pow (n.unop + 1))
            (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))) g).symm }

/-- Over a complete ultrametric normed commutative ring `R` with `IsAdic I` (not necessarily
finitely generated), `R⟨X₁, …, Xₖ⟩` is the limit in `CommRingCat` of
`(R ⧸ I ^ (n + 1))[X₁, …, Xₖ]`. -/
noncomputable def isLimitIsRestrictedSubringReductionPowSuccCone [CompleteSpace R] (hI : IsAdic I) :
    IsLimit (isRestrictedSubringReductionPowSuccCone (k := k) hI) :=
  IsLimit.ofIsoLimit (isLimitRestrictedCompletionReductionPowSuccCone (k := k) hI) <|
    Cone.ext (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)).toCommRingCatIso
      fun n ↦ by
        ext x
        exact (Ideal.isRestrictedSubringReduction_restrictedMvPowerSeriesCompletionGaussEquiv
          (I ^ (n.unop + 1)) (hI.isOpen_pow (n.unop + 1)) x).symm

/-- Over a complete ultrametric normed commutative ring `R` with `IsAdic I`, every compatible
sequence of polynomials modulo `I ^ (n + 1)` lifts to a unique unit-radius restricted series. -/
theorem existsUnique_isRestrictedSubringReduction_pow_succ_eq [CompleteSpace R] (hI : IsAdic I)
    (p : ∀ n : ℕ, MvPolynomial (Fin k) (R ⧸ I ^ (n + 1)))
    (hp : ∀ n : ℕ, MvPolynomial.map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) (p (n + 1)) = p n) :
    ∃! f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1),
      ∀ n : ℕ, (I ^ (n + 1)).isRestrictedSubringReduction (hI.isOpen_pow (n + 1)) f = p n := by
  let e := restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)
  obtain ⟨x, hx, huniq⟩ := existsUnique_restrictedCompletionReduction_pow_succ_eq (k := k) hI p hp
  refine ⟨e x, fun n ↦ by simpa [e] using hx n, fun f hf ↦ ?_⟩
  have hfx : e.symm f = x := huniq (e.symm f) fun n ↦ by
    rw [← Ideal.isRestrictedSubringReduction_restrictedMvPowerSeriesCompletionGaussEquiv,
      RingEquiv.apply_symm_apply]
    exact hf n
  exact e.symm.injective (hfx.trans (e.symm_apply_apply x).symm)

end InverseLimit

section EvaluationComparison

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- Reducing topological power-bounded evaluation `restrictedLift` modulo an open ideal `K` of the
target agrees with polynomial evaluation of `Ideal.isRestrictedSubringReduction` at the reduced
point. -/
theorem quotientMk_restrictedLift {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
    [NonarchimedeanRing S] [CompleteSpace S] [T0Space S] {φ : R →+* S} (hφ : Continuous φ)
    {b : Fin k → S} (hb : ∀ i, IsPowerBounded (b i))
    {J : Ideal R} (hJ : IsOpen (J : Set R)) {K : Ideal S} (hK : IsOpen (K : Set S))
    (hJK : J ≤ K.comap φ) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk K (restrictedLift hφ hb f) =
      (J.isRestrictedSubringReduction hJ f).eval₂ (Ideal.quotientMap K φ hJK)
        (Ideal.Quotient.mk K ∘ b) := by
  let : DiscreteTopology (S ⧸ K) := Submodule.Quotient.discreteTopology_of_isOpen K hK
  have hcont₁ : Continuous ((Ideal.Quotient.mk K).comp (restrictedLift hφ hb)) :=
    (QuotientRing.isOpenQuotientMap_mk K).continuous.comp (continuous_restrictedLift hφ hb)
  let rhs := (MvPolynomial.eval₂Hom (Ideal.quotientMap K φ hJK)
    (Ideal.Quotient.mk K ∘ b)).comp (J.isRestrictedSubringReduction hJ)
  have hcont₂ : Continuous rhs :=
    ((J.isLocallyConstant_isRestrictedSubringReduction hJ).comp
      (MvPolynomial.eval₂Hom (Ideal.quotientMap K φ hJK) (Ideal.Quotient.mk K ∘ b))).continuous
  have heq := isRestricted_subring_ringHom_ext_of_continuous hcont₁ hcont₂
    (fun r ↦ by simp [rhs]) (fun i ↦ by simp [rhs])
  exact congr($heq f)

/-- **Topological power-bounded evaluation agrees with bounded normed evaluation whenever the
normed hypotheses hold.** Because `‖φ r‖ ≤ C * ‖r‖` implies continuity of `φ` and `‖a i‖ ≤ 1`
implies `IsPowerBounded (a i)` (`IsPowerBounded.of_norm_le_one`), `RingHom.restrictedEval₂OfBound`
is a special case of `restrictedLift` (whereas `restrictedLift` also applies at power-bounded
elements of norm greater than `1`), and both define the same homomorphism `R⟨X₁, …, Xₖ⟩ →+* S`. -/
theorem restrictedLift_eq_restrictedEval₂OfBound {S : Type*} [NormedCommRing S]
    [IsUltrametricDist S] [CompleteSpace S] {φ : R →+* S} (hφc : Continuous φ) {a : Fin k → S}
    (hb : ∀ i, IsPowerBounded (a i)) {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (ha : ∀ i, ‖a i‖ ≤ 1) :
    restrictedLift hφc hb = φ.restrictedEval₂OfBound a hφ ha := by
  have : ∀ _ : Fin k, Fact ((0 : ℝ) < 1) := fun _ ↦ ⟨zero_lt_one⟩
  exact (restrictedLift_unique hφc hb (φ.continuous_restrictedEval₂OfBound a hφ ha)
    (φ.restrictedEval₂OfBound_algebraMap a hφ ha)
    (φ.restrictedEval₂OfBound_X a hφ ha)).symm

/-- **Universal property of `R⟨X₁, …, Xₖ⟩` into a complete separated linearly topologised ring.**
Because every subset of a linearly topologised ring `B` is bounded, every element `b i` is
power-bounded, so arbitrary points `b : Fin k → B` determine a unique continuous ring homomorphism
`R⟨X₁, …, Xₖ⟩ →+* B` extending a continuous `φ : R →+* B`. -/
theorem existsUnique_continuous_ringHom_isRestricted_subring_of_isLinearTopology {B : Type*}
    [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsLinearTopology B B] [CompleteSpace B]
    [T0Space B] {φ : R →+* B} (hφ : Continuous φ) (b : Fin k → B) :
    ∃! ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* B,
      Continuous ψ ∧ (∀ r, ψ (algebraMap R _ r) = φ r) ∧
        ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  exact existsUnique_continuous_ringHom_isRestricted_subring hφ
    fun i ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)

end EvaluationComparison

end TauCeti.MvPowerSeries
