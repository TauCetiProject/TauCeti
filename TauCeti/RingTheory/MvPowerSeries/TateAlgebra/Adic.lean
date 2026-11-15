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
import TauCeti.Topology.Algebra.Module.Quotient
import Mathlib.RingTheory.AdicCompletion.RingHom

/-!
# Adic reductions, noetherianity, and linear evaluation on Gauss-normed restricted series

Let `R` be an ultrametric normed commutative ring and `R⟨X₁, …, Xₖ⟩` be Mathlib's unit-radius
restricted power-series subring `MvPowerSeries.IsRestricted.subring (fun _ : Fin k ↦ 1)` with its
Gauss norm. Through `TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv`, polynomial reduction modulo
an open ideal, adic topology and completeness, noetherianity, and the inverse-limit presentation
carry directly onto the Gauss-normed carrier.

Over the valuation ring `𝒪[K]` of a nontrivially normed ultrametric field `K`, reduction modulo the
maximal ideal `𝓂[K]` agrees across `TauCeti.MvPowerSeries.restrictedIntegerEquiv` with the Gauss
unit-ball reduction `TauCeti.MvPowerSeries.restrictedReduction`.

Into a complete Hausdorff linearly topologised ring `S` (for instance any adic ring), every element
of `S` is power-bounded because a neighbourhood basis of zero consists of ideals closed under
multiplication (`isBounded_of_isLinearTopology`). Consequently, `restrictedLift` applies to
arbitrary variable images `b : Fin k → S` with no norm or power-boundedness hypothesis on `b`, in
contrast with normed targets such as `ℚ_[p]` where elements of norm greater than one fail to be
power-bounded.

## Main definitions

* `Ideal.isRestrictedSubringReduction`: coefficientwise polynomial reduction
  `R⟨X₁, …, Xₖ⟩ →+* (R ⧸ J)[X₁, …, Xₖ]` modulo an open ideal `J ⊆ R`.
* `TauCeti.MvPowerSeries.quotientIsRestrictedSubringEquivMvPolynomialQuotient` and
  `TauCeti.MvPowerSeries.quotientIsRestrictedSubringPowEquivMvPolynomialQuotient`: the `R`-algebra
  isomorphisms `R⟨X⟩ ⧸ (I · R⟨X⟩)ᵐ ≃ₐ[R] (R ⧸ Iᵐ)[X]` for a finitely generated ideal of definition
  `I` and `0 < m`.
* `TauCeti.MvPowerSeries.liftCompatibleIsRestrictedSubringReduction`: inverse-limit lift into
  `R⟨X₁, …, Xₖ⟩` from compatible homomorphisms into `(R ⧸ Iⁿ⁺¹)[X₁, …, Xₖ]`.
* `TauCeti.MvPowerSeries.restrictedLiftOfIsLinearTopology` and
  `TauCeti.MvPowerSeries.restrictedLiftAlgHomOfIsLinearTopology`: continuous evaluation into a
  complete Hausdorff linearly topologised ring or `R`-algebra at arbitrary points.

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

private theorem continuous_comp_isRestrictedSubringReduction {X : Type*} [TopologicalSpace X]
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
  ext ν
  rcases eq_or_ne ν 0 with rfl | h
  · simp [MvPolynomial.coeff_C]
  · simp [h, ne_comm.mp h, MvPolynomial.coeff_C, MvPowerSeries.coeff_C]

/-- Reduction sends each coordinate variable `Xᵢ` to `MvPolynomial.X i`. -/
@[simp]
theorem isRestrictedSubringReduction_X (J : Ideal R) (hJ : IsOpen (J : Set R)) (i : Fin k) :
    J.isRestrictedSubringReduction hJ ⟨X i, isRestricted_X _ i⟩ = MvPolynomial.X i := by
  ext ν
  rcases eq_or_ne ν (Finsupp.single i 1) with rfl | h
  · simp [MvPolynomial.coeff_X]
  · simp [h, ne_comm.mp h, MvPolynomial.coeff_X, MvPowerSeries.coeff_X]

/-- Every polynomial over `R ⧸ J` lifts to `R⟨X₁, …, Xₖ⟩`. -/
theorem isRestrictedSubringReduction_surjective (J : Ideal R) (hJ : IsOpen (J : Set R)) :
    Function.Surjective (J.isRestrictedSubringReduction (k := k) hJ) :=
  (J.restrictedReduction_surjective hJ).comp
    (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm.surjective

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
  have : DiscreteTopology (S ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  let evalHom := MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ)
    fun i ↦ Ideal.Quotient.mk J (b i)
  have h := isRestricted_subring_ringHom_ext_of_continuous
    (ψ₁ := (Ideal.Quotient.mk J).comp (restrictedLift hφ hb))
    (ψ₂ := evalHom.comp (I.isRestrictedSubringReduction hI))
    ((QuotientRing.isOpenQuotientMap_mk J).continuous.comp (continuous_restrictedLift hφ hb))
    (continuous_comp_isRestrictedSubringReduction I hI evalHom)
    (fun r ↦ by simp [evalHom])
    (fun i ↦ by simp [evalHom])
  exact congr($h f)

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

/-- Membership in `I · R⟨X₁, …, Xₖ⟩` for a finitely generated ideal of definition `I` is
coefficientwise membership in `I`. -/
theorem mem_map_algebraMap_isRestricted_subring_iff_of_isAdic (hI : IsAdic I) (hfg : I.FG)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    f ∈ I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) ↔
      ∀ ν, coeff ν (f : MvPowerSeries (Fin k) R) ∈ I := by
  let e := restrictedMvPowerSeriesGaussAlgEquiv (n := k) (R := R)
  have hmap : I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) =
      (I.map (weightedC _ isWeightFamily_one_weight)).map e.toRingHom := by
    rw [Ideal.map_map, ← algebraMap_weightedRestrictedSubring]
    exact congrArg (Ideal.map · I) e.toAlgHom.comp_algebraMap.symm
  rw [hmap, Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
  refine ⟨fun ⟨g, hg, hge⟩ ↦ ?_, fun hf ↦ ⟨e.symm f, ?_, e.apply_symm_apply f⟩⟩
  · have hgf : g = e.symm f := e.injective (hge.trans (e.apply_symm_apply f).symm)
    subst hgf
    simpa [e] using (mem_map_weightedC_iff_of_isAdic hI hfg _).mp hg
  · exact (mem_map_weightedC_iff_of_isAdic hI hfg _).mpr (by simpa [e] using hf)

/-- Reduction modulo a finitely generated ideal of definition `I` on `R⟨X₁, …, Xₖ⟩` has kernel
`I · R⟨X₁, …, Xₖ⟩`. -/
theorem ker_isRestrictedSubringReduction (hI : IsAdic I) (hfg : I.FG) :
    RingHom.ker (I.isRestrictedSubringReduction (k := k)
        (by simpa only [pow_one] using hI.isOpen_pow 1)) =
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))) := by
  ext f
  rw [RingHom.mem_ker, mem_map_algebraMap_isRestricted_subring_iff_of_isAdic hI hfg,
    MvPolynomial.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

/-- The quotient of `R⟨X₁, …, Xₖ⟩` by `I · R⟨X₁, …, Xₖ⟩` is the polynomial algebra
`(R ⧸ I)[X₁, …, Xₖ]`. -/
noncomputable def quotientIsRestrictedSubringEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I) := by
  have hIopen : IsOpen (I : Set R) := by simpa only [pow_one] using hI.isOpen_pow 1
  let e := (Ideal.quotEquivOfEq (ker_isRestrictedSubringReduction (k := k) hI hfg).symm).trans
    ((I.isRestrictedSubringReduction hIopen).quotientKerEquivOfSurjective
      (I.isRestrictedSubringReduction_surjective hIopen))
  refine AlgEquiv.ofRingEquiv (f := e) fun r ↦ ?_
  have he : e (algebraMap R _ r) = I.isRestrictedSubringReduction hIopen (algebraMap R _ r) := by
    rw [← Ideal.Quotient.mk_algebraMap]
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [he, Ideal.isRestrictedSubringReduction_algebraMap]
  rfl

/-- On a represented series, `quotientIsRestrictedSubringEquivMvPolynomialQuotient` computes
`isRestrictedSubringReduction`. -/
@[simp]
theorem quotientIsRestrictedSubringEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientIsRestrictedSubringEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ f) =
      I.isRestrictedSubringReduction (by simpa only [pow_one] using hI.isOpen_pow 1) f := by
  simp [quotientIsRestrictedSubringEquivMvPolynomialQuotient]

/-- For every positive `m`, the quotient of `R⟨X₁, …, Xₖ⟩` by `(I · R⟨X⟩)ᵐ` is the polynomial
algebra `(R ⧸ Iᵐ)[X₁, …, Xₖ]`. -/
noncomputable def quotientIsRestrictedSubringPowEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : 0 < m) :
    (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) ^ m) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I ^ m) :=
  (Ideal.quotientEquivAlgOfEq R
    (Ideal.map_pow (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))
      I m).symm).trans
        (quotientIsRestrictedSubringEquivMvPolynomialQuotient (is_ideal_adic_pow hI hm) hfg.pow)

/-- On a represented series, `quotientIsRestrictedSubringPowEquivMvPolynomialQuotient` computes
reduction modulo `Iᵐ`. -/
@[simp]
theorem quotientIsRestrictedSubringPowEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) {m : ℕ} (hm : 0 < m)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientIsRestrictedSubringPowEquivMvPolynomialQuotient hI hfg hm (Ideal.Quotient.mk _ f) =
      (I ^ m).isRestrictedSubringReduction (hI.isOpen_pow m) f := by
  simp [quotientIsRestrictedSubringPowEquivMvPolynomialQuotient]

section Complete

variable [CompleteSpace R]

/-- Over a complete ultrametric normed ring `R` whose topology is `I`-adic for finitely generated
`I`, `R⟨X₁, …, Xₖ⟩` is `(I · R⟨X⟩)`-adically complete and Hausdorff. -/
theorem isAdicComplete_map_algebraMap_isRestricted_subring (hI : IsAdic I) (hfg : I.FG) :
    IsAdicComplete (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))))
      (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  (isAdic_map_algebraMap_isRestricted_subring hI hfg).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩

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

/-- Over a noetherian ultrametric normed adic ring `R`, the Gauss-normed algebra `R⟨X₁, …, Xₖ⟩` is
strongly noetherian. -/
instance IsStronglyNoetherian.isRestricted_subring_of_isAdicRing [IsAdicRing R]
    [IsNoetherianRing R] :
    IsStronglyNoetherian (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  (isStronglyNoetherian_congr (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R))
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm).mp inferInstance

/-- Ring homomorphisms into Gauss-normed `R⟨X₁, …, Xₖ⟩` are determined by their polynomial
reductions modulo `Iⁿ⁺¹` for all `n : ℕ`. -/
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

/-- **Inverse-limit lift into Gauss-normed `R⟨X₁, …, Xₖ⟩`.** A compatible family of ring
homomorphisms `φₙ : D →+* (R ⧸ Iⁿ⁺¹)[X₁, …, Xₖ]` lifts to `D →+* R⟨X₁, …, Xₖ⟩`. -/
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

/-- **Universal property of Gauss-normed `R⟨X₁, …, Xₖ⟩` as the inverse limit of
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

/-- **Elementwise inverse-limit description of Gauss-normed `R⟨X₁, …, Xₖ⟩`.** Every compatible
family of polynomials `pₙ ∈ (R ⧸ Iⁿ⁺¹)[X₁, …, Xₖ]` is the sequence of reductions of a unique
restricted power series in `R⟨X₁, …, Xₖ⟩`. -/
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

/-! ### Universal property into linearly topologised rings and algebras

When `S` is linearly topologised (`[IsLinearTopology S S]`), zero admits a neighbourhood basis of
ideals. Since an ideal `J` satisfies `J · J ⊆ J`, every subset of `S` is bounded, so
`IsPowerBounded b` holds unconditionally for all `b : S`. Specialising `restrictedLift` therefore
removes the power-boundedness hypothesis on the evaluation point `b : Fin k → S`. -/

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
  {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
  [IsLinearTopology S S] [CompleteSpace S] [T2Space S]

/-- **Continuous evaluation of `R⟨X₁, …, Xₖ⟩` into a complete Hausdorff linearly topologised
ring**, at an arbitrary tuple `b : Fin k → S` with no norm or power-boundedness condition on `b`. -/
noncomputable def restrictedLiftOfIsLinearTopology {φ : R →+* S} (hφ : Continuous φ)
    (b : Fin k → S) :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* S :=
  letI := IsLinearTopology.isTopologicalRing (R := S)
  letI := IsLinearTopology.nonarchimedeanRing S
  restrictedLift (b := b) hφ fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)

/-- `restrictedLiftOfIsLinearTopology` is continuous. -/
theorem continuous_restrictedLiftOfIsLinearTopology {φ : R →+* S} (hφ : Continuous φ)
    (b : Fin k → S) :
    Continuous (restrictedLiftOfIsLinearTopology hφ b) := by
  have := IsLinearTopology.isTopologicalRing (R := S)
  have := IsLinearTopology.nonarchimedeanRing S
  exact continuous_restrictedLift hφ _

/-- `restrictedLiftOfIsLinearTopology` extends `φ` on constants. -/
@[simp]
theorem restrictedLiftOfIsLinearTopology_algebraMap {φ : R →+* S} (hφ : Continuous φ)
    (b : Fin k → S) (r : R) :
    restrictedLiftOfIsLinearTopology hφ b (algebraMap R _ r) = φ r := by
  have := IsLinearTopology.isTopologicalRing (R := S)
  have := IsLinearTopology.nonarchimedeanRing S
  exact restrictedLift_algebraMap hφ _ r

/-- `restrictedLiftOfIsLinearTopology` sends each coordinate variable `Xᵢ` to `bᵢ`. -/
@[simp]
theorem restrictedLiftOfIsLinearTopology_X {φ : R →+* S} (hφ : Continuous φ)
    (b : Fin k → S) (i : Fin k) :
    restrictedLiftOfIsLinearTopology hφ b ⟨X i, isRestricted_X _ i⟩ = b i := by
  have := IsLinearTopology.isTopologicalRing (R := S)
  have := IsLinearTopology.nonarchimedeanRing S
  exact restrictedLift_X hφ _ i

/-- Polynomial reduction commutes with `restrictedLiftOfIsLinearTopology`. -/
theorem _root_.Ideal.mk_restrictedLiftOfIsLinearTopology {φ : R →+* S} (hφ : Continuous φ)
    (b : Fin k → S) {I : Ideal R} (hI : IsOpen (I : Set R)) (J : Ideal S) (hJ : IsOpen (J : Set S))
    (hIJ : I ≤ J.comap φ) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk J (restrictedLiftOfIsLinearTopology hφ b f) =
      MvPolynomial.eval₂ (Ideal.quotientMap J φ hIJ) (fun i ↦ Ideal.Quotient.mk J (b i))
        (I.isRestrictedSubringReduction hI f) := by
  have := IsLinearTopology.isTopologicalRing (R := S)
  have := IsLinearTopology.nonarchimedeanRing S
  exact I.mk_restrictedLift (b := b) hφ
    (fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)) hI J hJ hIJ f

/-- **Universal property of `R⟨X₁, …, Xₖ⟩` into complete Hausdorff linearly topologised rings.**
A continuous ring homomorphism `φ : R →+* S` extends uniquely to a continuous ring homomorphism
`R⟨X₁, …, Xₖ⟩ →+* S` sending each `Xᵢ` to an arbitrary `bᵢ ∈ S`. -/
theorem existsUnique_continuous_ringHom_isRestricted_subring_of_isLinearTopology
    {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S) :
    ∃! ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* S,
      Continuous ψ ∧ (∀ r, ψ (algebraMap R _ r) = φ r) ∧
        ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i := by
  have := IsLinearTopology.isTopologicalRing (R := S)
  have := IsLinearTopology.nonarchimedeanRing S
  exact existsUnique_continuous_ringHom_isRestricted_subring (b := b) hφ
    fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)

/-- **Continuous `R`-algebra evaluation of `R⟨X₁, …, Xₖ⟩` into a complete Hausdorff linearly
topologised `R`-algebra**, at an arbitrary point `b : Fin k → S`. -/
noncomputable def restrictedLiftAlgHomOfIsLinearTopology [Algebra R S]
    (hφ : Continuous (algebraMap R S)) (b : Fin k → S) :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R] S :=
  { restrictedLiftOfIsLinearTopology hφ b with
    commutes' := restrictedLiftOfIsLinearTopology_algebraMap hφ b }

/-- Underlying ring map of `restrictedLiftAlgHomOfIsLinearTopology`. -/
@[simp]
theorem coe_restrictedLiftAlgHomOfIsLinearTopology [Algebra R S]
    (hφ : Continuous (algebraMap R S)) (b : Fin k → S) :
    ⇑(restrictedLiftAlgHomOfIsLinearTopology hφ b) = ⇑(restrictedLiftOfIsLinearTopology hφ b) :=
  (rfl)

/-- `restrictedLiftAlgHomOfIsLinearTopology` is continuous. -/
theorem continuous_restrictedLiftAlgHomOfIsLinearTopology [Algebra R S]
    (hφ : Continuous (algebraMap R S)) (b : Fin k → S) :
    Continuous (restrictedLiftAlgHomOfIsLinearTopology hφ b) :=
  continuous_restrictedLiftOfIsLinearTopology hφ b

/-- `restrictedLiftAlgHomOfIsLinearTopology` sends each `Xᵢ` to `bᵢ`. -/
@[simp]
theorem restrictedLiftAlgHomOfIsLinearTopology_X [Algebra R S]
    (hφ : Continuous (algebraMap R S)) (b : Fin k → S) (i : Fin k) :
    restrictedLiftAlgHomOfIsLinearTopology hφ b ⟨X i, isRestricted_X _ i⟩ = b i :=
  restrictedLiftOfIsLinearTopology_X hφ b i

/-- **Universal property of `R⟨X₁, …, Xₖ⟩` for continuous `R`-algebra maps into a complete
Hausdorff linearly topologised `R`-algebra.** -/
theorem existsUnique_continuous_algHom_isRestricted_subring_of_isLinearTopology [Algebra R S]
    (hφ : Continuous (algebraMap R S)) (b : Fin k → S) :
    ∃! ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R] S,
      Continuous ψ ∧ ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i := by
  refine ⟨restrictedLiftAlgHomOfIsLinearTopology hφ b,
    ⟨continuous_restrictedLiftAlgHomOfIsLinearTopology hφ b,
      restrictedLiftAlgHomOfIsLinearTopology_X hφ b⟩, fun ψ ⟨hψ, hX⟩ ↦ ?_⟩
  apply AlgHom.toRingHom_injective
  have := IsLinearTopology.isTopologicalRing (R := S)
  have := IsLinearTopology.nonarchimedeanRing S
  exact restrictedLift_unique hφ _ hψ ψ.commutes hX

end LinearTopology

end TauCeti.MvPowerSeries
