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

Let `R` be an ultrametric normed commutative ring and `R⟨X₁, …, Xₖ⟩` be Mathlib's unit-radius
restricted power-series subring `MvPowerSeries.IsRestricted.subring (fun _ : Fin k ↦ 1)` with its
Gauss norm. Through `TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv`, polynomial reduction modulo
an open ideal, the adic topology of extended ideals of definition, and the polynomial quotient
isomorphisms `R⟨X⟩ ⧸ (I · R⟨X⟩)ᵐ ≃ₐ[R] (R ⧸ Iᵐ)[X]` carry onto the Gauss-normed carrier for any
ultrametric normed `R`. When `R` is complete (`[CompleteSpace R]`),
`TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussEquiv` further transports adic completeness,
noetherianity, strong noetherianity, and the inverse-limit presentation of `R⟨X₁, …, Xₖ⟩`.

Over the valuation ring `𝒪[K]` of a nontrivially normed ultrametric field `K`, reduction modulo the
maximal ideal `𝓂[K]` agrees across `TauCeti.MvPowerSeries.restrictedIntegerEquiv` with the Gauss
unit-ball reduction `TauCeti.MvPowerSeries.restrictedReduction`.

Into a complete Hausdorff linearly topologised ring `S` (for instance any adic ring), zero admits a
neighbourhood basis of open ideals; since an ideal `J` absorbs multiplication by arbitrary elements
of `S` (`J · S ⊆ J`, so `J · T ⊆ J` for every `T ⊆ S`), every subset of `S` is bounded
(`isBounded_of_isLinearTopology`) and every element is power-bounded
(`TauCeti.Huber.isPowerBounded_of_isLinearTopology`). The resulting unconditional evaluation maps
`TauCeti.MvPowerSeries.restrictedLiftOfIsLinearTopology` and
`TauCeti.MvPowerSeries.restrictedLiftAlgHomOfIsLinearTopology` (in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty`) commute with open-ideal
polynomial reduction (`TauCeti.MvPowerSeries.mk_restrictedLiftOfIsLinearTopology`).

## Main definitions

* `Ideal.isRestrictedSubringReduction`: coefficientwise polynomial reduction
  `R⟨X₁, …, Xₖ⟩ →+* (R ⧸ J)[X₁, …, Xₖ]` modulo an open ideal `J ⊆ R`.
* `TauCeti.MvPowerSeries.quotientIsRestrictedSubringEquivMvPolynomialQuotient` and
  `TauCeti.MvPowerSeries.quotientIsRestrictedSubringPowEquivMvPolynomialQuotient`: the `R`-algebra
  isomorphisms `R⟨X⟩ ⧸ (I · R⟨X⟩)ᵐ ≃ₐ[R] (R ⧸ Iᵐ)[X]` for a finitely generated ideal of definition
  `I` and every `m : ℕ`.
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

/-- Coefficientwise reduction of unit-radius Gauss-normed restricted power series modulo an open
ideal `J` of `R` lands in the polynomial ring `(R ⧸ J)[X₁, …, Xₖ]`. -/
noncomputable def isRestrictedSubringReduction (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* MvPolynomial (Fin k) (R ⧸ J) :=
  (J.restrictedReduction hJ).comp
    (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm.toRingHom

/-- Composing `isRestrictedSubringReduction` with any map into a topological space produces a
continuous map. -/
theorem continuous_comp_isRestrictedSubringReduction {X : Type*} [TopologicalSpace X]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (g : MvPolynomial (Fin k) (R ⧸ J) → X) :
    Continuous (g ∘ J.isRestrictedSubringReduction (k := k) hJ) :=
  (J.continuous_comp_restrictedReduction hJ g).comp
    continuous_restrictedMvPowerSeriesGaussEquiv_symm

/-- Polynomial reduction on `R⟨X₁, …, Xₖ⟩` reduces each coefficient modulo `J`. -/
@[simp]
theorem coeff_isRestrictedSubringReduction (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) (ν : Fin k →₀ ℕ) :
    (J.isRestrictedSubringReduction hJ f).coeff ν =
      Ideal.Quotient.mk J (coeff ν (f : MvPowerSeries (Fin k) R)) := by
  simp [isRestrictedSubringReduction]

/-- On embedded polynomials, `isRestrictedSubringReduction` is coefficientwise reduction. -/
@[simp]
theorem isRestrictedSubringReduction_polynomialToRestricted (J : Ideal R)
    (hJ : IsOpen (J : Set R)) (p : MvPolynomial (Fin k) R) :
    J.isRestrictedSubringReduction hJ (polynomialToRestricted (fun _ : Fin k ↦ (1 : ℝ)) p) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  ext ν
  simp [MvPolynomial.coeff_map]

/-- Reduction sends a constant series `algebraMap R _ r` to `C (r mod J)`. -/
@[simp]
theorem isRestrictedSubringReduction_algebraMap (J : Ideal R) (hJ : IsOpen (J : Set R)) (r : R) :
    J.isRestrictedSubringReduction (k := k) hJ (algebraMap R _ r) =
      MvPolynomial.C (Ideal.Quotient.mk J r) := by
  simp [isRestrictedSubringReduction, ← restrictedMvPowerSeriesGaussEquiv_weightedC]

/-- Reduction sends each coordinate variable `Xᵢ` to `MvPolynomial.X i`. -/
@[simp]
theorem isRestrictedSubringReduction_X (J : Ideal R) (hJ : IsOpen (J : Set R)) (i : Fin k) :
    J.isRestrictedSubringReduction hJ ⟨X i, isRestricted_X _ i⟩ = MvPolynomial.X i := by
  simp [isRestrictedSubringReduction, ← restrictedMvPowerSeriesGaussEquiv_weightedX]

/-- Every polynomial over `R ⧸ J` lifts to `R⟨X₁, …, Xₖ⟩`. -/
theorem isRestrictedSubringReduction_surjective (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    Function.Surjective (J.isRestrictedSubringReduction (k := k) hJ) :=
  (J.restrictedReduction_surjective hJ).comp
    (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm.surjective

/-- Open-ideal polynomial reduction on Gauss-normed restricted series agrees with Huber
`restrictedReduction` across `restrictedMvPowerSeriesGaussEquiv`. -/
@[simp]
theorem isRestrictedSubringReduction_restrictedMvPowerSeriesGaussEquiv
    (J : Ideal R) (hJ : IsOpen (J : Set R))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    J.isRestrictedSubringReduction hJ (restrictedMvPowerSeriesGaussEquiv f) =
      J.restrictedReduction hJ f := by
  ext ν
  simp

/-- Over a complete ultrametric normed ring `R`, open-ideal polynomial reduction on Gauss-normed
restricted series agrees with `restrictedReductionCompletion` across
`restrictedMvPowerSeriesCompletionGaussEquiv`. -/
@[simp]
theorem isRestrictedSubringReduction_restrictedMvPowerSeriesCompletionGaussEquiv [CompleteSpace R]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (x : restrictedMvPowerSeriesCompletion k R) :
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
  ext ν
  simp [MvPolynomial.coeff_map]

/-- **Base-change functoriality on Gauss-normed restricted series.** Along a bounded ring
homomorphism `φ : R →+* S` carrying an open ideal `I` into an open ideal `J`, polynomial reduction
commutes with `restrictedMap`. -/
theorem isRestrictedSubringReduction_restrictedMap {S : Type*} [NormedCommRing S]
    [IsUltrametricDist S] {φ : R →+* S} {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    {I : Ideal R} (hI : IsOpen (I : Set R)) (J : Ideal S) (hJ : IsOpen (J : Set S))
    (hIJ : I ≤ J.comap φ) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    J.isRestrictedSubringReduction hJ (restrictedMap φ hφ f) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (I.isRestrictedSubringReduction hI f) := by
  ext ν
  simp [MvPolynomial.coeff_map]

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
      restrictedReduction (restrictedIntegerEquiv f) :=
  MvPolynomial.ext _ _ fun ν ↦
    (Ideal.coeff_isRestrictedSubringReduction _ _ f ν).trans <|
      (IsLocalRing.residue_def _).symm.trans <|
        (congrArg (IsLocalRing.residue 𝒪[K])
          (Subtype.ext (coeff_restrictedIntegerEquiv f ν).symm)).trans
          (coeff_restrictedReduction (restrictedIntegerEquiv f) ν).symm

end UnitBallBridge

section Adic

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {I : Ideal R}

/-- If a finitely generated ideal `I` defines the norm topology of `R`, then the extended ideal
`I · R⟨X₁, …, Xₖ⟩` defines the Gauss-norm topology of `R⟨X₁, …, Xₖ⟩`. -/
theorem isAdic_map_algebraMap_isRestricted_subring (hI : IsAdic I) (hfg : I.FG) :
    IsAdic (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) := by
  let hhomeo : Homeomorph
      (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight)
      (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
    { toEquiv := (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).toEquiv
      continuous_toFun := continuous_restrictedMvPowerSeriesGaussEquiv
      continuous_invFun := continuous_restrictedMvPowerSeriesGaussEquiv_symm }
  have hoqm : IsOpenQuotientMap
      (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)).toRingHom := by
    simpa [hhomeo] using hhomeo.isOpenQuotientMap
  have h :=
    (isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg).map_of_isOpenQuotientMap
      (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)).toRingHom hoqm
  rw [Ideal.map_map] at h
  have hcomp : (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)).toRingHom.comp
      (algebraMap R _) = algebraMap R _ :=
    (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)).toAlgHom.comp_algebraMap
  exact hcomp ▸ h

/-- The quotient of `R⟨X₁, …, Xₖ⟩` by `I · R⟨X₁, …, Xₖ⟩` is the polynomial algebra
`(R ⧸ I)[X₁, …, Xₖ]`. -/
noncomputable def quotientIsRestrictedSubringEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I) :=
  (Ideal.quotientEquivAlg _ _ (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)) (by
    rw [Ideal.map_map, ← algebraMap_weightedRestrictedSubring]
    exact congrArg (Ideal.map · I)
      (restrictedMvPowerSeriesGaussAlgEquiv (n := k)
        (R := R)).toAlgHom.comp_algebraMap.symm)).symm.trans
    (quotientRestrictedEquivMvPolynomialQuotient hI hfg)

/-- On a represented series, `quotientIsRestrictedSubringEquivMvPolynomialQuotient` computes
`isRestrictedSubringReduction`. -/
@[simp]
theorem quotientIsRestrictedSubringEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientIsRestrictedSubringEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ f) =
      I.isRestrictedSubringReduction hI.isOpen f := by
  simp [quotientIsRestrictedSubringEquivMvPolynomialQuotient, Ideal.isRestrictedSubringReduction]

/-- For every `m : ℕ`, the quotient of `R⟨X₁, …, Xₖ⟩` by `(I · R⟨X⟩)ᵐ` is the polynomial algebra
`(R ⧸ Iᵐ)[X₁, …, Xₖ]`. -/
noncomputable def quotientIsRestrictedSubringPowEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) ^ m) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I ^ m) :=
  (Ideal.quotientEquivAlg _ _ (restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)) (by
    rw [← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map,
      ← algebraMap_weightedRestrictedSubring]
    exact congrArg (Ideal.map · (I ^ m))
      (restrictedMvPowerSeriesGaussAlgEquiv (n := k)
        (R := R)).toAlgHom.comp_algebraMap.symm)).symm.trans
    (quotientRestrictedPowEquivMvPolynomialQuotient hI hfg m)

/-- On a represented series, `quotientIsRestrictedSubringPowEquivMvPolynomialQuotient` computes
reduction modulo `Iᵐ`. -/
@[simp]
theorem quotientIsRestrictedSubringPowEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientIsRestrictedSubringPowEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ f) =
      (I ^ m).isRestrictedSubringReduction (hI.isOpen_pow m) f := by
  simp [quotientIsRestrictedSubringPowEquivMvPolynomialQuotient, Ideal.isRestrictedSubringReduction]

section Complete

variable [CompleteSpace R]

/-- Over a complete ultrametric normed ring `R` whose topology is `I`-adic for finitely generated
`I`, `R⟨X₁, …, Xₖ⟩` is `(I · R⟨X⟩)`-adically complete and Hausdorff. -/
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

/-- Over a complete noetherian ultrametric normed ring whose topology is adic, `R⟨X₁, …, Xₖ⟩` is
noetherian. -/
theorem isNoetherianRing_isRestricted_subring_of_isAdic [IsNoetherianRing R] (hI : IsAdic I) :
    IsNoetherianRing (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
  have := isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic k hI
  exact isNoetherianRing_of_ringEquiv _
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R))

omit [CompleteSpace R] in
/-- Over a noetherian ultrametric normed adic ring `R`, the Gauss-normed algebra `R⟨X₁, …, Xₖ⟩` is
strongly noetherian. -/
instance isStronglyNoetherian_isRestricted_subring_of_isAdicRing [IsAdicRing R]
    [IsNoetherianRing R] :
    IsStronglyNoetherian (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  (isStronglyNoetherian_congr (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R))
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm).mp inferInstance

/-- Over a complete ultrametric normed ring `R`, ring homomorphisms into Gauss-normed
`R⟨X₁, …, Xₖ⟩` are determined by their polynomial reductions modulo `Iⁿ⁺¹` for all `n : ℕ`. -/
theorem isRestrictedSubringReduction_pow_succ_ext (hI : IsAdic I) (hfg : I.FG)
    {D : Type*} [NonAssocSemiring D]
    {f g : D →+* IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)}
    (h : ∀ n : ℕ, ((I ^ (n + 1)).isRestrictedSubringReduction (hI.isOpen_pow (n + 1))).comp f =
      ((I ^ (n + 1)).isRestrictedSubringReduction (hI.isOpen_pow (n + 1))).comp g) :
    f = g := by
  let e := restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)
  have hext := restrictedReductionCompletion_pow_succ_ext hI hfg
    (f := e.symm.toRingHom.comp f) (g := e.symm.toRingHom.comp g) fun n ↦ RingHom.ext fun d ↦ by
      simpa only [e, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        ← Ideal.isRestrictedSubringReduction_restrictedMvPowerSeriesCompletionGaussEquiv _
          (hI.isOpen_pow (n + 1)), RingEquiv.apply_symm_apply] using congr($(h n) d)
  exact RingHom.ext fun d ↦ e.symm.injective congr($hext d)

/-- **Inverse-limit lift into Gauss-normed `R⟨X₁, …, Xₖ⟩` over complete `R`.** A compatible family
of ring homomorphisms `φₙ : D →+* (R ⧸ Iⁿ⁺¹)[X₁, …, Xₖ]` lifts to `D →+* R⟨X₁, …, Xₖ⟩`. -/
noncomputable def liftCompatibleIsRestrictedSubringReduction (hI : IsAdic I) (hfg : I.FG)
    {D : Type*} [NonAssocSemiring D]
    (φ : ∀ n : ℕ, D →+* MvPolynomial (Fin k) (R ⧸ I ^ (n + 1)))
    (hφ : ∀ n : ℕ, (MvPolynomial.map (Ideal.Quotient.factorPowSucc I (n + 1))).comp
      (φ (n + 1)) = φ n) :
    D →+* IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) :=
  (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)).toRingHom.comp
    (liftCompatibleRestrictedReductionCompletion hI hfg φ hφ)

/-- Reducing `liftCompatibleIsRestrictedSubringReduction` modulo `Iⁿ⁺¹` recovers `φ n`. -/
@[simp]
theorem isRestrictedSubringReduction_comp_liftCompatibleIsRestrictedSubringReduction
    (hI : IsAdic I) (hfg : I.FG) {D : Type*} [NonAssocSemiring D]
    (φ : ∀ n : ℕ, D →+* MvPolynomial (Fin k) (R ⧸ I ^ (n + 1)))
    (hφ : ∀ n : ℕ, (MvPolynomial.map (Ideal.Quotient.factorPowSucc I (n + 1))).comp
      (φ (n + 1)) = φ n) (n : ℕ) :
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
theorem isRestrictedSubringReduction_liftCompatibleIsRestrictedSubringReduction
    (hI : IsAdic I) (hfg : I.FG) {D : Type*} [NonAssocSemiring D]
    (φ : ∀ n : ℕ, D →+* MvPolynomial (Fin k) (R ⧸ I ^ (n + 1)))
    (hφ : ∀ n : ℕ, (MvPolynomial.map (Ideal.Quotient.factorPowSucc I (n + 1))).comp
      (φ (n + 1)) = φ n) (n : ℕ) (d : D) :
    (I ^ (n + 1)).isRestrictedSubringReduction (hI.isOpen_pow (n + 1))
        (liftCompatibleIsRestrictedSubringReduction hI hfg φ hφ d) = φ n d :=
  congr($(isRestrictedSubringReduction_comp_liftCompatibleIsRestrictedSubringReduction
    hI hfg φ hφ n) d)

/-- **Universal property of Gauss-normed `R⟨X₁, …, Xₖ⟩` over complete `R` as the inverse limit of
`(R ⧸ Iⁿ⁺¹)[X₁, …, Xₖ]`.** -/
theorem existsUnique_ringHom_comp_isRestrictedSubringReduction_pow_succ
    (hI : IsAdic I) (hfg : I.FG) {D : Type*} [NonAssocSemiring D]
    (φ : ∀ n : ℕ, D →+* MvPolynomial (Fin k) (R ⧸ I ^ (n + 1)))
    (hφ : ∀ n : ℕ, (MvPolynomial.map (Ideal.Quotient.factorPowSucc I (n + 1))).comp
      (φ (n + 1)) = φ n) :
    ∃! ψ : D →+* IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1), ∀ n : ℕ,
      ((I ^ (n + 1)).isRestrictedSubringReduction (hI.isOpen_pow (n + 1))).comp ψ = φ n :=
  ⟨liftCompatibleIsRestrictedSubringReduction hI hfg φ hφ,
    isRestrictedSubringReduction_comp_liftCompatibleIsRestrictedSubringReduction hI hfg φ hφ,
    fun _ hψ ↦ isRestrictedSubringReduction_pow_succ_ext hI hfg fun n ↦
      (hψ n).trans (isRestrictedSubringReduction_comp_liftCompatibleIsRestrictedSubringReduction
        hI hfg φ hφ n).symm⟩

/-- **Elementwise inverse-limit description of Gauss-normed `R⟨X₁, …, Xₖ⟩` over complete `R`.**
Every compatible family of polynomials `pₙ ∈ (R ⧸ Iⁿ⁺¹)[X₁, …, Xₖ]` is the sequence of reductions of
a unique restricted power series in `R⟨X₁, …, Xₖ⟩`. -/
theorem existsUnique_isRestrictedSubringReduction_pow_succ (hI : IsAdic I) (hfg : I.FG)
    (p : ∀ n : ℕ, MvPolynomial (Fin k) (R ⧸ I ^ (n + 1)))
    (hp : ∀ n : ℕ,
      MvPolynomial.map (Ideal.Quotient.factorPowSucc I (n + 1)) (p (n + 1)) = p n) :
    ∃! f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1), ∀ n : ℕ,
      (I ^ (n + 1)).isRestrictedSubringReduction (hI.isOpen_pow (n + 1)) f = p n := by
  let e := restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)
  obtain ⟨x, hx, huniq⟩ := existsUnique_restrictedReductionCompletion_pow_succ hI hfg p hp
  refine ⟨e x, fun n ↦
    (Ideal.isRestrictedSubringReduction_restrictedMvPowerSeriesCompletionGaussEquiv _ _ x).trans
      (hx n), fun f hf ↦ ?_⟩
  rw [← e.apply_symm_apply f]
  refine congrArg e (huniq (e.symm f) fun n ↦ ?_)
  rw [← Ideal.isRestrictedSubringReduction_restrictedMvPowerSeriesCompletionGaussEquiv _ _
    (e.symm f)]
  simpa only [e, RingEquiv.apply_symm_apply] using hf n

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
