/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.Comparison
public import TauCeti.RingTheory.Huber.StronglyNoetherian

/-!
# Quotient specializations, inverse limits, and linear evaluation on Gauss-normed restricted series

This file complements `TauCeti.RingTheory.Huber.Restricted.Comparison` and
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Reduction` for the unit-radius Gauss-normed
restricted power-series ring `R⟨X₁, …, Xₖ⟩`:

* Bounded-map reduction compatibility (`isRestrictedSubringReduction_restrictedMap`) and
  coefficientwise uniqueness modulo powers `Iⁿ⁺¹` (`isRestrictedSubringReduction_pow_succ_ext`).
* The `m = 1` quotient isomorphism `quotientIsRestrictedSubringEquivMvPolynomialQuotient`,
  `symm_isRestrictedSubringReduction` simp lemmas, and transport compatibility with the Huber
  subring and completion quotient isomorphisms.
* Over complete `R`, adic completeness (`isAdicComplete_map_algebraMap_isRestricted_subring`),
  strong noetherianity (`isStronglyNoetherian_isRestricted_subring_of_isAdicRing`), and the direct
  inverse-limit universal property (`liftCompatibleIsRestrictedSubringReduction` and
  `existsUnique_ringHom_isRestrictedSubringReduction_pow_succ_comp_eq`).
* Open-ideal reduction compatibility for unconditional linear-topology evaluation
  (`mk_restrictedLiftOfIsLinearTopology`).

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.1–7.5.4.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
* T. Wedhorn, *Adic Spaces*, §5.6, Proposition 5.50.
-/

public section

open Topology UniformSpace

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries TauCeti.Huber

section ReductionFunctoriality

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

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

end ReductionFunctoriality

section Adic

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {I : Ideal R}

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
  simp [quotientIsRestrictedSubringEquivMvPolynomialQuotient,
    restrictedReduction_eq_isRestrictedSubringReduction]

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

section Pow

variable (m : ℕ)

/-- The inverse of `quotientPowIsRestrictedEquivMvPolynomialQuotient` maps a reduction modulo
`Iᵐ` back to its quotient class. -/
@[simp]
theorem quotientPowIsRestrictedEquivMvPolynomialQuotient_symm_isRestrictedSubringReduction
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    (quotientPowIsRestrictedEquivMvPolynomialQuotient hI hfg m).symm
        ((I ^ m).isRestrictedSubringReduction (hI.isOpen_pow m) f) =
      Ideal.Quotient.mk _ f := by
  rw [← quotientPowIsRestrictedEquivMvPolynomialQuotient_mk hI hfg m,
    AlgEquiv.symm_apply_apply]

end Pow

end QuotientEquiv

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
  simp [restrictedCompletionReduction_eq_isRestrictedSubringReduction]

/-- Over complete `R`, `quotientPowIsRestrictedEquivMvPolynomialQuotient` agrees for every
`m : ℕ` with transporting `quotientPowRestrictedCompletionEquivMvPolynomialQuotient` across
`restrictedMvPowerSeriesCompletionGaussAlgEquiv`. -/
theorem quotientPowIsRestrictedEquivMvPolynomialQuotient_eq_completion_trans
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    quotientPowIsRestrictedEquivMvPolynomialQuotient (k := k) hI hfg m =
      (Ideal.quotientEquivAlg _ _
        (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k) (R := R)) (by
          rw [← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map]
          exact congrArg (Ideal.map · (I ^ m))
            (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k)
              (R := R)).toAlgHom.comp_algebraMap.symm)).symm.trans
        (quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg m) := by
  ext x; obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [restrictedCompletionReduction_eq_isRestrictedSubringReduction]

/-- Over a complete ultrametric normed ring `R` with `I`-adic topology for finitely generated `I`,
`R⟨X₁, …, Xₖ⟩` is `(I · R⟨X⟩)`-adically complete and Hausdorff. -/
theorem isAdicComplete_map_algebraMap_isRestricted_subring (hI : IsAdic I) (hfg : I.FG) :
    IsAdicComplete (I.map (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))))
      (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  (isAdic_map_algebraMap_isRestricted_subring hI hfg).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩

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
    (liftCompatibleRestrictedCompletionReduction hI hfg φ hφ)

/-- `liftCompatibleIsRestrictedSubringReduction` transports
`liftCompatibleRestrictedCompletionReduction` along `restrictedMvPowerSeriesCompletionGaussEquiv`.
-/
theorem liftCompatibleIsRestrictedSubringReduction_eq_comp :
    liftCompatibleIsRestrictedSubringReduction hI hfg φ hφ =
      (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)).toRingHom.comp
        (liftCompatibleRestrictedCompletionReduction hI hfg φ hφ) := by rfl

/-- Reducing `liftCompatibleIsRestrictedSubringReduction` modulo `Iⁿ⁺¹` recovers `φ n`. -/
@[simp]
theorem isRestrictedSubringReduction_comp_liftCompatibleIsRestrictedSubringReduction (n : ℕ) :
    ((I ^ (n + 1)).isRestrictedSubringReduction (hI.isOpen_pow (n + 1))).comp
        (liftCompatibleIsRestrictedSubringReduction hI hfg φ hφ) = φ n := by
  refine RingHom.ext fun d ↦ ?_
  dsimp only [RingHom.comp_apply, liftCompatibleIsRestrictedSubringReduction,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← restrictedCompletionReduction_eq_isRestrictedSubringReduction (hI.isOpen_pow (n + 1))]
  exact restrictedCompletionReduction_liftCompatibleRestrictedCompletionReduction hI hfg φ hφ n d

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
  obtain ⟨x, hx, huniq⟩ := existsUnique_restrictedCompletionReduction_pow_succ_eq hI hfg p hp
  refine ⟨e x, fun n ↦ by
    rw [← restrictedCompletionReduction_eq_isRestrictedSubringReduction (hI.isOpen_pow (n + 1))]
    exact hx n, fun f hf ↦ ?_⟩
  rw [← e.apply_symm_apply f]
  exact congrArg e (huniq (e.symm f) fun n ↦ by
    rw [restrictedCompletionReduction_eq_isRestrictedSubringReduction]
    simpa [e] using hf n)

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
  exact mk_restrictedLift_eq_eval₂_isRestrictedSubringReduction hφ
    (fun _ ↦ isPowerBounded_of_isLinearTopology _) hI hJ hIJ f

end LinearTopology

end TauCeti.MvPowerSeries
