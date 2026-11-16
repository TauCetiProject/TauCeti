/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.Basic
public import TauCeti.RingTheory.Huber.Restricted.Adic
public import TauCeti.RingTheory.Huber.Restricted.Reduction
public import TauCeti.RingTheory.Huber.StronglyNoetherian
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall

/-!
# Adic reductions, noetherianity, and linear evaluation on Gauss-normed restricted series

For an ultrametric normed commutative ring `R`, `R⟨X₁, …, Xₖ⟩` denotes Mathlib's unit-radius
restricted power-series subring `MvPowerSeries.IsRestricted.subring (fun _ : Fin k ↦ 1)` with its
Gauss norm. Through `TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv`, open-ideal polynomial
reduction, the adic topology of extended ideals of definition, and the quotient isomorphisms
`R⟨X⟩ ⧸ (I · R⟨X⟩)ᵐ ≃ₐ[R] (R ⧸ Iᵐ)[X]` carry onto the Gauss-normed carrier for any ultrametric
normed `R`. When `R` is complete (`[CompleteSpace R]`),
`TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussEquiv` further transports adic completeness,
noetherianity, strong noetherianity, and the inverse-limit presentation of `R⟨X₁, …, Xₖ⟩`.

Over the valuation ring `𝒪[K]` of a nontrivially normed ultrametric field `K`, reduction modulo the
maximal ideal `𝓂[K]` agrees across `TauCeti.MvPowerSeries.restrictedIntegerEquiv` with the Gauss
unit-ball reduction `TauCeti.MvPowerSeries.restrictedReduction`.

Into a complete Hausdorff linearly topologised ring `S`, open ideals absorb multiplication by all of
`S` (`J · S ⊆ J`, so `J · T ⊆ J` for every `T ⊆ S`), making every subset bounded
(`isBounded_of_isLinearTopology`) and every element power-bounded
(`TauCeti.Huber.isPowerBounded_of_isLinearTopology`). The unconditional evaluation maps
`restrictedLiftOfIsLinearTopology` and `restrictedLiftAlgHomOfIsLinearTopology` (in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty`) commute with open-ideal reduction
(`TauCeti.MvPowerSeries.mk_restrictedLiftOfIsLinearTopology`).

## Main definitions

* `Ideal.isRestrictedSubringReduction`: coefficientwise polynomial reduction
  `R⟨X₁, …, Xₖ⟩ →+* (R ⧸ J)[X₁, …, Xₖ]` modulo an open ideal `J ⊆ R`.
* `TauCeti.MvPowerSeries.quotientIsRestrictedSubringEquivMvPolynomialQuotient` and
  `TauCeti.MvPowerSeries.quotientIsRestrictedSubringPowEquivMvPolynomialQuotient`: the `R`-algebra
  isomorphisms `R⟨X⟩ ⧸ (I · R⟨X⟩)ᵐ ≃ₐ[R] (R ⧸ Iᵐ)[X]` for finitely generated `I` and `m : ℕ`.
* `TauCeti.MvPowerSeries.liftCompatibleIsRestrictedSubringReduction`: for complete `R`, the
  inverse-limit lift into `R⟨X₁, …, Xₖ⟩` from compatible homomorphisms into
  `(R ⧸ Iⁿ⁺¹)[X₁, …, Xₖ]`.
* `TauCeti.MvPowerSeries.mk_restrictedLift` and
  `TauCeti.MvPowerSeries.mk_restrictedLiftOfIsLinearTopology`: open-ideal polynomial reduction
  commutes with `restrictedLift` and `restrictedLiftOfIsLinearTopology`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.1–7.5.4.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
* T. Wedhorn, *Adic Spaces*, §5.6, Proposition 5.50.
-/

public section

open Topology UniformSpace

namespace Ideal

open _root_.MvPowerSeries TauCeti.Huber TauCeti.MvPowerSeries

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
  (J : Ideal R) (hJ : IsOpen (J : Set R))

/-- Coefficientwise reduction of unit-radius Gauss-normed restricted power series modulo an open
ideal `J` of `R` lands in the polynomial ring `(R ⧸ J)[X₁, …, Xₖ]`. -/
noncomputable def isRestrictedSubringReduction :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* MvPolynomial (Fin k) (R ⧸ J) :=
  (J.restrictedReduction hJ).comp
    (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm.toRingHom

/-- Composing `isRestrictedSubringReduction` with any map into a topological space is continuous. -/
theorem continuous_comp_isRestrictedSubringReduction {X : Type*} [TopologicalSpace X]
    (g : MvPolynomial (Fin k) (R ⧸ J) → X) :
    Continuous (g ∘ J.isRestrictedSubringReduction (k := k) hJ) :=
  (J.continuous_comp_restrictedReduction hJ g).comp
    continuous_restrictedMvPowerSeriesGaussEquiv_symm

/-- Polynomial reduction on `R⟨X₁, …, Xₖ⟩` reduces each coefficient modulo `J`. -/
@[simp]
theorem coeff_isRestrictedSubringReduction
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) (ν : Fin k →₀ ℕ) :
    (J.isRestrictedSubringReduction hJ f).coeff ν =
      Ideal.Quotient.mk J (coeff ν (f : MvPowerSeries (Fin k) R)) := by
  simp [isRestrictedSubringReduction]

/-- On embedded polynomials, `isRestrictedSubringReduction` is coefficientwise reduction. -/
@[simp]
theorem isRestrictedSubringReduction_polynomialToRestricted (p : MvPolynomial (Fin k) R) :
    J.isRestrictedSubringReduction hJ (polynomialToRestricted (fun _ : Fin k ↦ (1 : ℝ)) p) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  ext ν; simp [MvPolynomial.coeff_map]

/-- Reduction sends a constant series `algebraMap R _ r` to `C (r mod J)`. -/
@[simp]
theorem isRestrictedSubringReduction_algebraMap (r : R) :
    J.isRestrictedSubringReduction (k := k) hJ (algebraMap R _ r) =
      MvPolynomial.C (Ideal.Quotient.mk J r) := by
  simp [isRestrictedSubringReduction, ← restrictedMvPowerSeriesGaussEquiv_weightedC]

/-- Reduction sends each coordinate variable `Xᵢ` to `MvPolynomial.X i`. -/
@[simp]
theorem isRestrictedSubringReduction_X (i : Fin k) :
    J.isRestrictedSubringReduction hJ ⟨X i, isRestricted_X _ i⟩ = MvPolynomial.X i := by
  simp [isRestrictedSubringReduction, ← restrictedMvPowerSeriesGaussEquiv_weightedX]

/-- Every polynomial over `R ⧸ J` lifts to `R⟨X₁, …, Xₖ⟩`. -/
theorem isRestrictedSubringReduction_surjective :
    Function.Surjective (J.isRestrictedSubringReduction (k := k) hJ) :=
  (J.restrictedReduction_surjective hJ).comp
    (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm.surjective

/-- Open-ideal reduction on Gauss-normed restricted series agrees with `restrictedReduction` across
`restrictedMvPowerSeriesGaussEquiv`. -/
@[simp]
theorem isRestrictedSubringReduction_restrictedMvPowerSeriesGaussEquiv
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    J.isRestrictedSubringReduction hJ (restrictedMvPowerSeriesGaussEquiv f) =
      J.restrictedReduction hJ f := by
  ext ν; simp

/-- Over a complete ultrametric normed ring `R`, open-ideal reduction on Gauss-normed restricted
series agrees with `restrictedReductionCompletion` across
`restrictedMvPowerSeriesCompletionGaussEquiv`. -/
@[simp]
theorem isRestrictedSubringReduction_restrictedMvPowerSeriesCompletionGaussEquiv [CompleteSpace R]
    (x : restrictedMvPowerSeriesCompletion k R) :
    J.isRestrictedSubringReduction hJ (restrictedMvPowerSeriesCompletionGaussEquiv x) =
      J.restrictedReductionCompletion hJ x := by
  let e := restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)
  conv_rhs =>
    rw [← e.symm_apply_apply x, restrictedMvPowerSeriesCompletionGaussEquiv_symm_apply,
      Ideal.restrictedReductionCompletion_coe,
      ← isRestrictedSubringReduction_restrictedMvPowerSeriesGaussEquiv J hJ]
  simp [e]

end Ideal

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries TauCeti.Huber
open scoped NormedField Valued

section ReductionFunctoriality

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- Reduction on `R⟨X₁, …, Xₖ⟩` is compatible with passing to a larger open ideal. -/
@[simp]
theorem map_isRestrictedSubringReduction {I J : Ideal R} (hJ : IsOpen (J : Set R))
    (hI : IsOpen (I : Set R)) (hJI : J ≤ I)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    MvPolynomial.map (Ideal.Quotient.factor hJI) (J.isRestrictedSubringReduction hJ f) =
      I.isRestrictedSubringReduction hI f := by
  ext ν; simp [MvPolynomial.coeff_map]

/-- **Base-change functoriality on Gauss-normed restricted series.** Along a bounded ring
homomorphism `φ : R →+* S` carrying an open ideal `I` into an open ideal `J`, polynomial reduction
commutes with `restrictedMap`. -/
theorem isRestrictedSubringReduction_restrictedMap {S : Type*} [NormedCommRing S]
    [IsUltrametricDist S] {φ : R →+* S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    {I : Ideal R} (hI : IsOpen (I : Set R)) (J : Ideal S) (hJ : IsOpen (J : Set S))
    (hIJ : I ≤ J.comap φ) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    J.isRestrictedSubringReduction hJ (restrictedMap φ hφ f) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (I.isRestrictedSubringReduction hI f) := by
  ext ν; simp [MvPolynomial.coeff_map]

/-- **Polynomial reduction commutes with `restrictedLift`.** For a continuous ring homomorphism
`φ : R →+* S` into a complete Hausdorff nonarchimedean ring, power-bounded `b : Fin k → S`, and
open ideals `I ⊆ R`, `J ⊆ S` with `φ(I) ⊆ J`, reducing `restrictedLift hφ hb f` modulo `J`
evaluates the polynomial reduction of `f` at the residue classes of `b`. -/
theorem mk_restrictedLift {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
    [NonarchimedeanRing S] [CompleteSpace S] [T3Space S] {φ : R →+* S} (hφ : Continuous φ)
    {b : Fin k → S} (hb : ∀ i, IsPowerBounded (b i)) {I : Ideal R} (hI : IsOpen (I : Set R))
    (J : Ideal S) (hJ : IsOpen (J : Set S)) (hIJ : I ≤ J.comap φ)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk J (restrictedLift hφ hb f) =
      MvPolynomial.eval₂ (Ideal.quotientMap J φ hIJ) (fun i ↦ Ideal.Quotient.mk J (b i))
        (I.isRestrictedSubringReduction hI f) := by
  simpa [restrictedLift_apply, Ideal.isRestrictedSubringReduction] using
    mk_weightedEvalHom hφ.continuousAt
      ((isWeightBounded_one_weight_iff_forall_isPowerBounded φ b).mpr hb) hI J hJ hIJ
      ((restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm f)

end ReductionFunctoriality

section UnitBallBridge

variable {k : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Over the valuation ring `𝒪[K]`, open-ideal reduction modulo `𝓂[K]` agrees across
`restrictedIntegerEquiv` with the Gauss unit-ball reduction `restrictedReduction`. -/
@[simp]
theorem isRestrictedSubringReduction_maximalIdeal_eq_restrictedReduction
    (hm : IsOpen ((IsLocalRing.maximalIdeal 𝒪[K] : Ideal 𝒪[K]) : Set 𝒪[K]))
    (f : IsRestricted.subring (R := 𝒪[K]) (fun _ : Fin k ↦ 1)) :
    (IsLocalRing.maximalIdeal 𝒪[K]).isRestrictedSubringReduction hm f =
      restrictedReduction (restrictedIntegerEquiv f) := by
  -- `Valued.ResidueField K` (`IsLocalRing.ResidueField 𝒪[K]`) is definitionally
  -- `𝒪[K] ⧸ IsLocalRing.maximalIdeal 𝒪[K]`, so `change` aligns the RHS type for
  -- `coeff_restrictedReduction` and `rfl` closes the identical quotient terms after `simp`.
  ext ν
  change _ = (restrictedReduction (restrictedIntegerEquiv f)).coeff ν
  rw [coeff_restrictedReduction]
  simp [IsLocalRing.residue_def]
  rfl

end UnitBallBridge

section Adic

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {I : Ideal R}

/-- If a finitely generated ideal `I` defines the norm topology of `R`, then `I · R⟨X₁, …, Xₖ⟩`
defines the Gauss-norm topology of `R⟨X₁, …, Xₖ⟩`. -/
theorem isAdic_map_algebraMap_isRestricted_subring (hI : IsAdic I) (hfg : I.FG) :
    IsAdic (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) := by
  let e := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  have h := (isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI
    hfg).map_of_isOpenQuotientMap e.toRingHom
      (Homeomorph.mk e.toEquiv continuous_restrictedMvPowerSeriesGaussEquiv
        continuous_restrictedMvPowerSeriesGaussEquiv_symm).isOpenQuotientMap
  have hcomp : e.toRingHom.comp (algebraMap R _) = algebraMap R _ :=
    RingHom.ext fun r ↦ by simp [e, algebraMap_weightedRestrictedSubring]
  rwa [Ideal.map_map, hcomp] at h

section QuotientEquiv

variable (hI : IsAdic I) (hfg : I.FG)

/-- The quotient of `R⟨X₁, …, Xₖ⟩` by `I · R⟨X₁, …, Xₖ⟩` is `(R ⧸ I)[X₁, …, Xₖ]`. -/
noncomputable def quotientIsRestrictedSubringEquivMvPolynomialQuotient :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I) :=
  (Ideal.quotientEquivAlg _ _ (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)) (by
    rw [Ideal.map_map, ← algebraMap_weightedRestrictedSubring]
    exact congrArg (Ideal.map · I)
      (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)).toAlgHom.comp_algebraMap.symm
  )).symm.trans (quotientRestrictedEquivMvPolynomialQuotient hI hfg)

/-- On a represented series, `quotientIsRestrictedSubringEquivMvPolynomialQuotient` computes
`isRestrictedSubringReduction`. -/
@[simp]
theorem quotientIsRestrictedSubringEquivMvPolynomialQuotient_mk
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientIsRestrictedSubringEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ f) =
      I.isRestrictedSubringReduction hI.isOpen f := by
  simp [quotientIsRestrictedSubringEquivMvPolynomialQuotient, Ideal.isRestrictedSubringReduction]

/-- The inverse of `quotientIsRestrictedSubringEquivMvPolynomialQuotient` maps a reduction back to
its quotient class. -/
@[simp]
theorem quotientIsRestrictedSubringEquivMvPolynomialQuotient_symm_isRestrictedSubringReduction
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    (quotientIsRestrictedSubringEquivMvPolynomialQuotient hI hfg).symm
        (I.isRestrictedSubringReduction hI.isOpen f) =
      Ideal.Quotient.mk _ f := by
  rw [← quotientIsRestrictedSubringEquivMvPolynomialQuotient_mk hI hfg, AlgEquiv.symm_apply_apply]

/-- The inverse of `quotientIsRestrictedSubringEquivMvPolynomialQuotient` sends `Xᵢ` to `X i`. -/
@[simp]
theorem quotientIsRestrictedSubringEquivMvPolynomialQuotient_symm_X (i : Fin k) :
    (quotientIsRestrictedSubringEquivMvPolynomialQuotient hI hfg).symm (MvPolynomial.X i) =
      Ideal.Quotient.mk _ ⟨X i, isRestricted_X _ i⟩ := by
  rw [← Ideal.isRestrictedSubringReduction_X I hI.isOpen i,
    quotientIsRestrictedSubringEquivMvPolynomialQuotient_symm_isRestrictedSubringReduction]

/-- The inverse of `quotientIsRestrictedSubringEquivMvPolynomialQuotient` sends `C (r mod I)` to
`algebraMap R _ r`. -/
@[simp]
theorem quotientIsRestrictedSubringEquivMvPolynomialQuotient_symm_C_mk (r : R) :
    (quotientIsRestrictedSubringEquivMvPolynomialQuotient (k := k) hI hfg).symm
        (MvPolynomial.C (Ideal.Quotient.mk I r)) =
      algebraMap R _ r := by
  simpa [MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq] using
    (quotientIsRestrictedSubringEquivMvPolynomialQuotient (k := k) hI hfg).symm.commutes r

/-- `quotientIsRestrictedSubringEquivMvPolynomialQuotient` is the transport of
`quotientRestrictedEquivMvPolynomialQuotient` across `restrictedMvPowerSeriesGaussAlgEquiv`. -/
theorem quotientIsRestrictedSubringEquivMvPolynomialQuotient_eq_trans :
    quotientIsRestrictedSubringEquivMvPolynomialQuotient (k := k) hI hfg =
      (Ideal.quotientEquivAlg _ _ (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)) (by
        rw [Ideal.map_map, ← algebraMap_weightedRestrictedSubring]
        exact congrArg (Ideal.map · I)
          (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)).toAlgHom.comp_algebraMap.symm
      )).symm.trans (quotientRestrictedEquivMvPolynomialQuotient hI hfg) := by rfl

include hI hfg in
/-- Membership in `I · R⟨X₁, …, Xₖ⟩` for finitely generated `I` is coefficientwise in `I`. -/
theorem mem_map_algebraMap_isRestricted_subring_iff_of_isAdic
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    f ∈ I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ↔
      ∀ ν, coeff ν (f : MvPowerSeries (Fin k) R) ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem,
    ← map_eq_zero_iff _ (quotientIsRestrictedSubringEquivMvPolynomialQuotient hI hfg).injective,
    quotientIsRestrictedSubringEquivMvPolynomialQuotient_mk, MvPolynomial.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

section Pow

variable (m : ℕ)

/-- For every `m : ℕ`, `R⟨X₁, …, Xₖ⟩ ⧸ (I · R⟨X⟩)ᵐ ≃ₐ[R] (R ⧸ Iᵐ)[X₁, …, Xₖ]`. -/
noncomputable def quotientIsRestrictedSubringPowEquivMvPolynomialQuotient :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) ^ m) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I ^ m) :=
  (Ideal.quotientEquivAlg _ _ (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)) (by
    rw [← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map, ← algebraMap_weightedRestrictedSubring]
    exact congrArg (Ideal.map · (I ^ m))
      (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)).toAlgHom.comp_algebraMap.symm
  )).symm.trans (quotientRestrictedPowEquivMvPolynomialQuotient hI hfg m)

/-- On a represented series, `quotientIsRestrictedSubringPowEquivMvPolynomialQuotient` computes
reduction modulo `Iᵐ`. -/
@[simp]
theorem quotientIsRestrictedSubringPowEquivMvPolynomialQuotient_mk
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientIsRestrictedSubringPowEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ f) =
      (I ^ m).isRestrictedSubringReduction (hI.isOpen_pow m) f := by
  simp [quotientIsRestrictedSubringPowEquivMvPolynomialQuotient, Ideal.isRestrictedSubringReduction]

/-- The inverse of `quotientIsRestrictedSubringPowEquivMvPolynomialQuotient` maps a reduction modulo
`Iᵐ` back to its quotient class. -/
@[simp]
theorem quotientIsRestrictedSubringPowEquivMvPolynomialQuotient_symm_isRestrictedSubringReduction
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    (quotientIsRestrictedSubringPowEquivMvPolynomialQuotient hI hfg m).symm
        ((I ^ m).isRestrictedSubringReduction (hI.isOpen_pow m) f) =
      Ideal.Quotient.mk _ f := by
  rw [← quotientIsRestrictedSubringPowEquivMvPolynomialQuotient_mk hI hfg m,
    AlgEquiv.symm_apply_apply]

/-- The inverse of `quotientIsRestrictedSubringPowEquivMvPolynomialQuotient` sends `Xᵢ` to `X i`.
-/
@[simp]
theorem quotientIsRestrictedSubringPowEquivMvPolynomialQuotient_symm_X (i : Fin k) :
    (quotientIsRestrictedSubringPowEquivMvPolynomialQuotient hI hfg m).symm (MvPolynomial.X i) =
      Ideal.Quotient.mk _ ⟨X i, isRestricted_X _ i⟩ := by
  rw [← Ideal.isRestrictedSubringReduction_X (I ^ m) (hI.isOpen_pow m) i,
    quotientIsRestrictedSubringPowEquivMvPolynomialQuotient_symm_isRestrictedSubringReduction]

/-- The inverse of `quotientIsRestrictedSubringPowEquivMvPolynomialQuotient` sends `C (r mod Iᵐ)` to
`algebraMap R _ r`. -/
@[simp]
theorem quotientIsRestrictedSubringPowEquivMvPolynomialQuotient_symm_C_mk (r : R) :
    (quotientIsRestrictedSubringPowEquivMvPolynomialQuotient (k := k) hI hfg m).symm
        (MvPolynomial.C (Ideal.Quotient.mk (I ^ m) r)) =
      algebraMap R _ r := by
  simpa [MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq] using
    (quotientIsRestrictedSubringPowEquivMvPolynomialQuotient (k := k) hI hfg m).symm.commutes r

/-- `quotientIsRestrictedSubringPowEquivMvPolynomialQuotient` is the transport of
`quotientRestrictedPowEquivMvPolynomialQuotient` across `restrictedMvPowerSeriesGaussAlgEquiv`. -/
theorem quotientIsRestrictedSubringPowEquivMvPolynomialQuotient_eq_trans :
    quotientIsRestrictedSubringPowEquivMvPolynomialQuotient (k := k) hI hfg m =
      (Ideal.quotientEquivAlg _ _ (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)) (by
        rw [← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map, ← algebraMap_weightedRestrictedSubring]
        exact congrArg (Ideal.map · (I ^ m))
          (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)).toAlgHom.comp_algebraMap.symm
      )).symm.trans (quotientRestrictedPowEquivMvPolynomialQuotient hI hfg m) := by rfl

end Pow

end QuotientEquiv

/-- Reduction modulo a finitely generated ideal of definition `I` on `R⟨X₁, …, Xₖ⟩` has kernel
`I · R⟨X₁, …, Xₖ⟩`. -/
theorem _root_.Ideal.ker_isRestrictedSubringReduction (I : Ideal R) (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (I.isRestrictedSubringReduction (k := k) hI.isOpen) =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) := by
  ext f
  rw [RingHom.mem_ker, ← quotientIsRestrictedSubringEquivMvPolynomialQuotient_mk hI hfg,
    map_eq_zero_iff _ (quotientIsRestrictedSubringEquivMvPolynomialQuotient hI hfg).injective,
    Ideal.Quotient.eq_zero_iff_mem]

/-- Ring homomorphisms into Gauss-normed `R⟨X₁, …, Xₖ⟩` are determined by their reductions modulo
`Iⁿ⁺¹` for all `n : ℕ`. Neither completeness of `R` nor finite generation of `I` is required, since
`R` is Hausdorff and reduction acts coefficientwise. -/
theorem isRestrictedSubringReduction_pow_succ_ext (hI : IsAdic I)
    {D : Type*} [NonAssocSemiring D]
    {f g : D →+* IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)}
    (h : ∀ n : ℕ, ((I ^ (n + 1)).isRestrictedSubringReduction (hI.isOpen_pow (n + 1))).comp f =
      ((I ^ (n + 1)).isRestrictedSubringReduction (hI.isOpen_pow (n + 1))).comp g) :
    f = g := by
  have : IsHausdorff I R := hI.isHausdorff_iff.mpr inferInstance
  refine RingHom.ext fun d ↦ Subtype.ext <| MvPowerSeries.ext <| congrFun <|
    IsHausdorff.StrictMono.funext' I (fun _ _ hlt ↦ Nat.add_lt_add_right hlt 1)
      (f := fun ν ↦ coeff ν (f d : MvPowerSeries (Fin k) R))
      (g := fun ν ↦ coeff ν (g d : MvPowerSeries (Fin k) R)) fun n ν ↦ by
        simpa only [RingHom.comp_apply, Ideal.coeff_isRestrictedSubringReduction] using
          congrArg (fun p ↦ p.coeff ν) (congr($(h n) d))

section Complete

variable [CompleteSpace R]

/-- Over complete `R`, `quotientIsRestrictedSubringEquivMvPolynomialQuotient` agrees with
transporting `quotientRestrictedCompletionEquivMvPolynomialQuotient` across
`restrictedMvPowerSeriesCompletionGaussAlgEquiv`. -/
theorem quotientIsRestrictedSubringEquivMvPolynomialQuotient_eq_completion_trans
    (hI : IsAdic I) (hfg : I.FG) :
    quotientIsRestrictedSubringEquivMvPolynomialQuotient (k := k) hI hfg =
      (Ideal.quotientEquivAlg _ _
        (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k) (R := R)) (by
          rw [Ideal.map_map]
          exact congrArg (Ideal.map · I)
            (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k)
              (R := R)).toAlgHom.comp_algebraMap.symm)).symm.trans
        (quotientRestrictedCompletionEquivMvPolynomialQuotient hI hfg) := by
  ext x; obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [← Ideal.isRestrictedSubringReduction_restrictedMvPowerSeriesCompletionGaussEquiv]

/-- Over complete `R`, `quotientIsRestrictedSubringPowEquivMvPolynomialQuotient` agrees for every
`m : ℕ` with transporting `quotientRestrictedCompletionPowEquivMvPolynomialQuotient` across
`restrictedMvPowerSeriesCompletionGaussAlgEquiv`. -/
theorem quotientIsRestrictedSubringPowEquivMvPolynomialQuotient_eq_completion_trans
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    quotientIsRestrictedSubringPowEquivMvPolynomialQuotient (k := k) hI hfg m =
      (Ideal.quotientEquivAlg _ _
        (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k) (R := R)) (by
          rw [← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map]
          exact congrArg (Ideal.map · (I ^ m))
            (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k)
              (R := R)).toAlgHom.comp_algebraMap.symm)).symm.trans
        (quotientRestrictedCompletionPowEquivMvPolynomialQuotient hI hfg m) := by
  ext x; obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [← Ideal.isRestrictedSubringReduction_restrictedMvPowerSeriesCompletionGaussEquiv]

/-- Over a complete ultrametric normed ring `R` with `I`-adic topology for finitely generated `I`,
`R⟨X₁, …, Xₖ⟩` is `(I · R⟨X⟩)`-adically complete and Hausdorff. -/
theorem isAdicComplete_map_algebraMap_isRestricted_subring (hI : IsAdic I) (hfg : I.FG) :
    IsAdicComplete (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))))
      (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  (isAdic_map_algebraMap_isRestricted_subring hI hfg).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩

omit [CompleteSpace R] in
/-- Unit-radius Gauss-normed restricted power series over an ultrametric normed adic ring form an
adic ring of finite ideal type. -/
instance isAdicRing_isRestricted_subring [IsAdicRing R] :
    IsAdicRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
  obtain ⟨hfg, hI, -⟩ := IsAdicRing.ideal_spec R
  exact ⟨(IsAdicRing.ideal R).map (algebraMap R _), hfg.map _,
    isAdic_map_algebraMap_isRestricted_subring hI hfg,
    isAdicComplete_map_algebraMap_isRestricted_subring hI hfg⟩

/-- Over a complete noetherian ultrametric normed ring with adic topology, `R⟨X₁, …, Xₖ⟩` is
noetherian. -/
theorem isNoetherianRing_isRestricted_subring_of_isAdic [IsNoetherianRing R] (hI : IsAdic I) :
    IsNoetherianRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
  have := isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic k hI
  exact isNoetherianRing_of_ringEquiv _
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R))

omit [CompleteSpace R] in
/-- Over a noetherian ultrametric normed adic ring `R`, `R⟨X₁, …, Xₖ⟩` is strongly noetherian. -/
instance isStronglyNoetherian_isRestricted_subring_of_isAdicRing [IsAdicRing R]
    [IsNoetherianRing R] :
    IsStronglyNoetherian (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  (isStronglyNoetherian_congr (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R))
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm).mp inferInstance

section InverseLimit

variable (hI : IsAdic I) (hfg : I.FG) {D : Type*} [NonAssocSemiring D]
  (φ : ∀ n : ℕ, D →+* MvPolynomial (Fin k) (R ⧸ I ^ (n + 1)))
  (hφ : ∀ n : ℕ, (MvPolynomial.map (Ideal.Quotient.factorPowSucc I (n + 1))).comp
    (φ (n + 1)) = φ n)

/-- **Inverse-limit lift into Gauss-normed `R⟨X₁, …, Xₖ⟩` over complete `R`.** A compatible family
of ring homomorphisms `φₙ : D →+* (R ⧸ Iⁿ⁺¹)[X₁, …, Xₖ]` lifts to `D →+* R⟨X₁, …, Xₖ⟩`. -/
noncomputable def liftCompatibleIsRestrictedSubringReduction :
    D →+* IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) :=
  (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)).toRingHom.comp
    (liftCompatibleRestrictedReductionCompletion hI hfg φ hφ)

/-- `liftCompatibleIsRestrictedSubringReduction` transports
`liftCompatibleRestrictedReductionCompletion` along `restrictedMvPowerSeriesCompletionGaussEquiv`.
-/
theorem liftCompatibleIsRestrictedSubringReduction_eq_comp :
    liftCompatibleIsRestrictedSubringReduction hI hfg φ hφ =
      (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)).toRingHom.comp
        (liftCompatibleRestrictedReductionCompletion hI hfg φ hφ) := by rfl

/-- Reducing `liftCompatibleIsRestrictedSubringReduction` modulo `Iⁿ⁺¹` recovers `φ n`. -/
@[simp]
theorem isRestrictedSubringReduction_comp_liftCompatibleIsRestrictedSubringReduction (n : ℕ) :
    ((I ^ (n + 1)).isRestrictedSubringReduction (hI.isOpen_pow (n + 1))).comp
        (liftCompatibleIsRestrictedSubringReduction hI hfg φ hφ) = φ n := by
  refine RingHom.ext fun d ↦ ?_
  simpa only [RingHom.comp_apply, liftCompatibleIsRestrictedSubringReduction,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    Ideal.isRestrictedSubringReduction_restrictedMvPowerSeriesCompletionGaussEquiv]
    using restrictedReductionCompletion_liftCompatibleRestrictedReductionCompletion hI hfg φ hφ n d

/-- Elementwise form of
`isRestrictedSubringReduction_comp_liftCompatibleIsRestrictedSubringReduction`. -/
@[simp]
theorem isRestrictedSubringReduction_liftCompatibleIsRestrictedSubringReduction (n : ℕ) (d : D) :
    (I ^ (n + 1)).isRestrictedSubringReduction (hI.isOpen_pow (n + 1))
        (liftCompatibleIsRestrictedSubringReduction hI hfg φ hφ d) = φ n d :=
  congr($(isRestrictedSubringReduction_comp_liftCompatibleIsRestrictedSubringReduction
    hI hfg φ hφ n) d)

include hfg hφ in
/-- **Universal property of Gauss-normed `R⟨X₁, …, Xₖ⟩` over complete `R` as the inverse limit of
`(R ⧸ Iⁿ⁺¹)[X₁, …, Xₖ]`.** -/
theorem existsUnique_ringHom_isRestrictedSubringReduction_pow_succ_comp_eq :
    ∃! ψ : D →+* IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1), ∀ n : ℕ,
      ((I ^ (n + 1)).isRestrictedSubringReduction (hI.isOpen_pow (n + 1))).comp ψ = φ n :=
  ⟨liftCompatibleIsRestrictedSubringReduction hI hfg φ hφ,
    isRestrictedSubringReduction_comp_liftCompatibleIsRestrictedSubringReduction hI hfg φ hφ,
    fun _ hψ ↦ isRestrictedSubringReduction_pow_succ_ext hI fun n ↦
      (hψ n).trans (isRestrictedSubringReduction_comp_liftCompatibleIsRestrictedSubringReduction
        hI hfg φ hφ n).symm⟩

end InverseLimit

/-- **Elementwise inverse-limit description of Gauss-normed `R⟨X₁, …, Xₖ⟩` over complete `R`.**
Every compatible family of polynomials `pₙ ∈ (R ⧸ Iⁿ⁺¹)[X₁, …, Xₖ]` is the sequence of reductions of
a unique restricted power series in `R⟨X₁, …, Xₖ⟩`. -/
theorem existsUnique_isRestrictedSubringReduction_pow_succ_eq (hI : IsAdic I) (hfg : I.FG)
    (p : ∀ n : ℕ, MvPolynomial (Fin k) (R ⧸ I ^ (n + 1)))
    (hp : ∀ n : ℕ,
      MvPolynomial.map (Ideal.Quotient.factorPowSucc I (n + 1)) (p (n + 1)) = p n) :
    ∃! f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1), ∀ n : ℕ,
      (I ^ (n + 1)).isRestrictedSubringReduction (hI.isOpen_pow (n + 1)) f = p n := by
  let e := restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)
  obtain ⟨x, hx, huniq⟩ := existsUnique_restrictedReductionCompletion_pow_succ_eq hI hfg p hp
  refine ⟨e x, fun n ↦
    (Ideal.isRestrictedSubringReduction_restrictedMvPowerSeriesCompletionGaussEquiv _ _ x).trans
      (hx n), fun f hf ↦ ?_⟩
  rw [← e.apply_symm_apply f]
  exact congrArg e (huniq (e.symm f) fun n ↦ by
    simpa [e, ← Ideal.isRestrictedSubringReduction_restrictedMvPowerSeriesCompletionGaussEquiv]
      using hf n)

end Complete

end Adic

section LinearTopology

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
  {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
  [IsLinearTopology S S] [CompleteSpace S] [T2Space S]

/-- Open-ideal polynomial reduction commutes with `restrictedLiftOfIsLinearTopology`. -/
theorem mk_restrictedLiftOfIsLinearTopology {φ : R →+* S} (hφ : Continuous φ)
    (b : Fin k → S) {I : Ideal R} (hI : IsOpen (I : Set R)) (J : Ideal S) (hJ : IsOpen (J : Set S))
    (hIJ : I ≤ J.comap φ) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk J (restrictedLiftOfIsLinearTopology hφ b f) =
      MvPolynomial.eval₂ (Ideal.quotientMap J φ hIJ) (fun i ↦ Ideal.Quotient.mk J (b i))
        (I.isRestrictedSubringReduction hI f) := by
  have := IsLinearTopology.isTopologicalRing (R := S)
  have := IsLinearTopology.nonarchimedeanRing S
  rw [restrictedLiftOfIsLinearTopology_eq_restrictedLift]
  exact mk_restrictedLift (b := b) hφ (fun _ ↦ isPowerBounded_of_isLinearTopology _) hI J hJ hIJ f

end LinearTopology

end TauCeti.MvPowerSeries
