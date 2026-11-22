/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Filtration
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Huber.Padic.Basic
import TauCeti.RingTheory.Huber.Restricted.Comparison.Basic
import TauCeti.RingTheory.PowerSeries.AdicComplete
import TauCeti.RingTheory.PowerSeries.Geometric
import TauCeti.RingTheory.PowerSeries.Restricted

/-!
# Examples of restricted power series over adic, discrete, and `p`-adic rings

Concrete tests of adic quotient presentations, noetherianity, Gauss comparisons, universal
properties into linearly topologized and normed targets, and `k = 0` boundary cases:
discrete coefficients (`A[X₁, …, Xₖ]`), `p`-adic integers `ℤ_[p]` (`(ℤ/pᵐℤ)[X₁, …, Xₖ]` for all
`m : ℕ` and noetherianity), `(p, X)`-adic evaluation `ℤ_[p]⟨T⟩ →+* ℤ_[p]⟦X⟧` (`T ↦ 1 + X`) vs.
non-existence of `T ↦ p⁻¹` over `ℚ_[p]`, and `k = 0` completion counterexamples on `ℤ[X]`.
-/

open Filter Topology TauCeti.Huber TauCeti.MvPowerSeries IsLocalRing Polynomial

namespace TauCeti.Examples

-- Over a discrete base ring `A`, uncompleted restricted series coincide with `A[X₁, …, Xₖ]`.
noncomputable example (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
    [DiscreteTopology A] : MvPolynomial (Fin k) A ≃+*
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight

-- Over a discrete base ring `A`, completed restricted series also coincide with `A[X₁, …, Xₖ]`.
noncomputable example (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
    [DiscreteTopology A] : MvPolynomial (Fin k) A ≃+* restrictedMvPowerSeriesCompletion k A :=
  let _ := discreteTopology_weightedRestrictedSubring
    (T := fun _ : Fin k ↦ ({1} : Set A)) (hT := isWeightFamily_one_weight)
  let _ : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
    isWeightFamily_one_weight) := IsRightUniformAddGroup.discreteUniformity
  (weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).trans
    (restrictedMvPowerSeriesCompletionEquiv k A).symm

-- Over a discretely normed ultrametric commutative ring `R`, `R⟨X₁, …, Xₖ⟩ ≃+* R[X₁, …, Xₖ]`.
noncomputable example (k : ℕ) (R : Type*) [NormedCommRing R] [IsUltrametricDist R]
    [DiscreteTopology R] :
    MvPolynomial (Fin k) R ≃+* MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) :=
  (weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).trans
    restrictedMvPowerSeriesGaussEquiv

section Padic
variable (p : ℕ) [hp : Fact p.Prime]
-- For every `m : ℕ`, reducing `ℤ_[p]⟨X₁, …, Xₖ⟩` modulo `(p)ᵐ` yields `(ℤ/pᵐℤ)[X₁, …, Xₖ]`.
noncomputable example (k m : ℕ) :
    (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1) ⧸
      (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p]
        (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1))) ^ m) ≃+*
      MvPolynomial (Fin k) (ZMod (p ^ m)) :=
  (quotientPowIsRestrictedEquivMvPolynomialQuotient PadicInt.isAdic_maximalIdeal
    (IsNoetherian.noetherian _) m).toRingEquiv.trans <| MvPolynomial.mapEquiv (Fin k) <|
    (Ideal.quotEquivOfEq (by rw [_root_.PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]))
      |>.trans (_root_.PadicInt.quotientSpanPowEquivZMod m)
-- For every `m : ℕ`, completed Huber restricted series over `ℤ_[p]` mod `(p)ᵐ` give `(ℤ/pᵐℤ)[X]`.
noncomputable example (k m : ℕ) :
    (restrictedMvPowerSeriesCompletion k ℤ_[p] ⧸
      (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (restrictedMvPowerSeriesCompletion k ℤ_[p])) ^ m)
      ≃+* MvPolynomial (Fin k) (ZMod (p ^ m)) :=
  (quotientPowRestrictedCompletionEquivMvPolynomialQuotient PadicInt.isAdic_maximalIdeal
    (IsNoetherian.noetherian _) m).toRingEquiv.trans <| MvPolynomial.mapEquiv (Fin k) <|
    (Ideal.quotEquivOfEq (by rw [_root_.PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]))
      |>.trans (_root_.PadicInt.quotientSpanPowEquivZMod m)
-- `ℤ_[p]⟨X₁, …, Xₖ⟩` is noetherian with `(p · ℤ_[p]⟨X⟩)`-adic Gauss-norm topology.
example (k : ℕ) :
    IsNoetherianRing (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1)) ∧
    IsAdic ((maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p]
      (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1)))) :=
  ⟨isNoetherianRing_isRestricted_subring_of_isAdic PadicInt.isAdic_maximalIdeal,
   isAdic_map_algebraMap_isRestricted_subring PadicInt.isAdic_maximalIdeal
     (IsNoetherian.noetherian _)⟩
-- Over `ℤ_[p]`, `∑ Xⁿ` inverts `1 - X` in `ℤ_[p]⟦X⟧` yet is not restricted.
example : (PowerSeries.mk (1 : ℕ → ℤ_[p])) * (1 - PowerSeries.X) = 1 ∧
    ¬ (PowerSeries.mk (1 : ℕ → ℤ_[p])).IsRestricted 1 :=
  ⟨by rw [Pi.one_def]; simpa using powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one (1 : ℤ_[p]),
   PowerSeries.not_isRestricted_mk_one⟩

-- `(p, X)`-adic `ℤ_[p]⟦X⟧` has a unique continuous lift `ℤ_[p]⟨T⟩ →+* ℤ_[p]⟦X⟧` (`T ↦ 1 + X`).
example : letI : WithIdeal (PowerSeries ℤ_[p]) := ⟨maximalIdeal (PowerSeries ℤ_[p])⟩
    ∃! ψ : MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1) →+*
        PowerSeries ℤ_[p],
      Continuous ψ ∧ (∀ r : ℤ_[p], ψ (algebraMap ℤ_[p] _ r) = PowerSeries.C r) ∧
        ∀ i, ψ ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ = 1 + PowerSeries.X := by
  let : WithIdeal (PowerSeries ℤ_[p]) := ⟨maximalIdeal (PowerSeries ℤ_[p])⟩
  have hAdic : IsAdic (maximalIdeal (PowerSeries ℤ_[p])) := rfl
  obtain ⟨_, _⟩ := hAdic.isAdicComplete_iff.mp PowerSeries.isAdicComplete_maximalIdeal
  have : IsLinearTopology (PowerSeries ℤ_[p]) (PowerSeries ℤ_[p]) := hAdic.isLinearTopology
  have hmap : (maximalIdeal ℤ_[p]).map PowerSeries.C ≤ maximalIdeal (PowerSeries ℤ_[p]) :=
    Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      rw [mem_maximalIdeal, mem_nonunits_iff] at ha
      exact fun hu ↦ ha (by simpa using hu.map PowerSeries.constantCoeff)
  exact existsUnique_continuous_ringHom_isRestricted_subring_of_isLinearTopology
    (PadicInt.isAdic_maximalIdeal.continuous_of_map_le_radical hAdic (IsNoetherian.noetherian _)
      (hmap.trans Ideal.le_radical)) fun _ ↦ 1 + PowerSeries.X
-- Over `ℚ_[p]`, no continuous ring map `ℚ_[p]⟨T⟩ →+* ℚ_[p]` extending `id` sends `T ↦ p⁻¹`.
example : ¬ ∃ ψ : MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) (fun _ : Fin 1 ↦ 1) →+* ℚ_[p],
    Continuous ψ ∧ (∀ r : ℚ_[p], ψ (algebraMap ℚ_[p] _ r) = r) ∧
      ∀ i, ψ ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ = (p : ℚ_[p])⁻¹ := by
  rintro ⟨ψ, hψc, hC, hX⟩
  have hle := (exists_continuous_ringHom_isRestricted_subring_iff_forall_norm_le_one
    (φ := RingHom.id ℚ_[p]) continuous_id (fun _ : Fin 1 ↦ (p : ℚ_[p])⁻¹)).mp ⟨ψ, hψc, hC, hX⟩ 0
  rw [norm_inv, Padic.norm_p, inv_inv] at hle; exact not_le_of_gt (mod_cast hp.out.one_lt) hle
end Padic

-- Complete `T0` base `A` has bijective `algebraMap : A →+* restrictedMvPowerSeriesCompletion 0 A`.
example (A : Type*) [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
    [CompleteSpace A] [T0Space A] :
    Function.Bijective (algebraMap A (restrictedMvPowerSeriesCompletion 0 A)) := by
  let e := (restrictedMvPowerSeriesCompletionEquiv 0 A).trans
    (weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set A)))
  have hcomp : ∀ a : A, e (algebraMap A _ a) = a := fun a ↦ by simp [e]
  exact ⟨Function.LeftInverse.injective hcomp, fun x ↦ ⟨e x, e.injective (hcomp (e x))⟩⟩
-- Indiscrete (`⊤`-adic) `ℤ[X]` has non-injective `algebraMap` into `k = 0` completion.
example : letI : WithIdeal ℤ[X] := ⟨⊤⟩
    CompleteSpace ℤ[X] ∧
      ¬ Function.Injective (algebraMap ℤ[X] (restrictedMvPowerSeriesCompletion 0 ℤ[X])) := by
  let : WithIdeal ℤ[X] := ⟨⊤⟩; have hAdic : IsAdic (⊤ : Ideal ℤ[X]) := rfl
  have hpre : IsPrecomplete (⊤ : Ideal ℤ[X]) ℤ[X] :=
    ⟨fun _ _ ↦ ⟨0, fun n ↦ by simp [SModEq.zero, Submodule.eq_top_iff'.mp (Ideal.top_pow _ n)]⟩⟩
  refine ⟨hAdic.isPrecomplete_iff.mp hpre, fun hinj ↦ ?_⟩
  let P := MvPolynomial (Fin 0) ℤ[X]
  let e := restrictedMvPowerSeriesCompletionEquivAdicCompletion (k := 0) hAdic ⟨{1}, by simp⟩
  have : Subsingleton (AdicCompletion ((⊤ : Ideal ℤ[X]).map (MvPolynomial.C : ℤ[X] →+* P)) P) :=
    ⟨fun _ _ ↦ AdicCompletion.ext fun n ↦ @Subsingleton.elim _ (Submodule.Quotient.subsingleton_iff
      |>.mpr (by rw [Ideal.map_top, Ideal.top_pow, smul_eq_mul, Ideal.top_mul])) _ _⟩
  exact one_ne_zero (hinj (e.injective (Subsingleton.elim _ _)))
-- `(X)`-adic `ℤ[X]` has non-surjective `algebraMap` into `k = 0` completion.
example : letI : WithIdeal ℤ[X] := ⟨Ideal.span {Polynomial.X}⟩
    T2Space ℤ[X] ∧
      ¬ Function.Surjective (algebraMap ℤ[X] (restrictedMvPowerSeriesCompletion 0 ℤ[X])) := by
  let I : Ideal ℤ[X] := Ideal.span {Polynomial.X}; let : WithIdeal ℤ[X] := ⟨I⟩
  have hAdic : IsAdic I := rfl; have hfg : I.FG := Submodule.fg_span_singleton Polynomial.X
  have hHaus : IsHausdorff I ℤ[X] := isHausdorff_iff.mpr fun f hf ↦ by
    have hf' : f ∈ ⨅ n : ℕ, I ^ n := (Submodule.mem_iInf _).mpr fun n ↦ by
      simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hf n
    rwa [Ideal.iInf_pow_eq_bot_of_isDomain I
      (Ideal.span_singleton_ne_top Polynomial.not_isUnit_X), Submodule.mem_bot] at hf'
  refine ⟨hAdic.isHausdorff_iff.mp hHaus, fun hsurj ↦ ?_⟩
  let e := restrictedMvPowerSeriesCompletionFinZeroEquiv.trans
    (hAdic.completionEquivAdicCompletion hfg)
  have he (f : ℤ[X]) : e (algebraMap ℤ[X] (restrictedMvPowerSeriesCompletion 0 ℤ[X]) f) =
      AdicCompletion.of I ℤ[X] f := by
    simp [e, hAdic.completionEquivAdicCompletion_coe hfg, AdicCompletion.algebraMap_apply]
  have hsurj_of : Function.Surjective (AdicCompletion.of I ℤ[X]) := fun y ↦ by
    obtain ⟨f, hf⟩ := hsurj (e.symm y); exact ⟨f, by rw [← he f, hf, e.apply_symm_apply]⟩
  have : IsAdicComplete I ℤ[X] := AdicCompletion.of_bijective_iff.mp
    ⟨by have := hHaus; exact AdicCompletion.of_injective I ℤ[X], hsurj_of⟩
  have hunit : IsUnit (1 + (Polynomial.X : ℤ[X])) := by
    rw [add_comm]; simpa using Ring.mem_jacobson_iff.mp
      (IsAdicComplete.le_jacobson I (Ideal.mem_span_singleton_self Polynomial.X)) 1
  have hC := congrArg (fun p : ℤ[X] ↦ p.coeff 1)
    (Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hunit))
  simp at hC
end TauCeti.Examples
