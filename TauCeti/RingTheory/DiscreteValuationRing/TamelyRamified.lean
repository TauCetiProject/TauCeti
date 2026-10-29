/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RamificationInertia.Basic
public import TauCeti.RingTheory.RamificationInertia.Unramified

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Smooth.Fiber

/-!
# Unramified, tamely and totally ramified extensions of a discrete valuation ring

Let `A` be a discrete valuation ring with fraction field `K`, let `L / K` be a finite separable
extension and let `B` be the integral closure of `A` in `L`. The maximal ideals `𝔪₁, …, 𝔪ₙ` of
`B` are the primes over the maximal ideal of `A`; write `eᵢ` for their ramification indices and
`fᵢ` for their residue degrees. Following Stacks, Definition 15.113.7, we say that `L` is

* *unramified with respect to `A`* (`TauCeti.Algebra.IsUnramifiedWRT A L`) if every `eᵢ = 1`
  and every residue extension `κ(𝔪ᵢ) / κ_A` is separable;
* *tamely ramified with respect to `A`* (`TauCeti.Algebra.IsTamelyRamifiedWRT A L`) if every
  residue extension is separable and every `eᵢ` is invertible in `κ_A`;
* *totally ramified with respect to `A`* (`TauCeti.Algebra.IsTotallyRamifiedWRT A L`) if
  `n = 1` and `κ(𝔪₁) = κ_A`.

The definitions take `L` to be a field; for a finite separable `K`-algebra `∏ Lⱼ` Stacks asks
for them of every factor `Lⱼ`. Ramification indices are Mathlib's `Ideal.ramificationIdx`
and residue degrees are Mathlib's `Ideal.inertiaDeg`. The definitions themselves only need `A`
to be local; the results below assume `A` is a discrete valuation ring. For extensions of
nonarchimedean local fields, the valuation-theoretic counterparts are `TauCeti.IsTamelyRamified`
and `TauCeti.IsTotallyRamified`.

## Main results

* `TauCeti.Algebra.IsUnramifiedWRT.isTamelyRamifiedWRT`: unramified extensions are tamely
  ramified.
* `TauCeti.Algebra.isTamelyRamifiedWRT_of_charZero`: if the residue field of `A` has
  characteristic zero, every finite extension of `K` is tamely ramified with respect to `A`.
* `TauCeti.Algebra.isUnramifiedWRT_iff_forall_isUnramifiedAt`: `L` is unramified with respect
  to `A` iff the integral closure of `A` in `L` is unramified over `A` at every prime.
* `TauCeti.Algebra.isUnramifiedWRT_iff_etale`: `L` is unramified with respect to `A` iff the
  integral closure of `A` in `L` is étale over `A`.
* `TauCeti.Algebra.isTotallyRamifiedWRT_iff_exists_ramificationIdx_eq_finrank`: `L` is totally
  ramified with respect to `A` iff some maximal ideal of the integral closure has ramification
  index `[L : K]`.

## References

* [Stacks Project, Remark 15.113.6 and Definition 15.113.7](https://stacks.math.columbia.edu/tag/09E9).
-/

public section

open Algebra IsLocalRing

namespace TauCeti.Algebra

section Definitions

variable (A L : Type*) [CommRing A] [IsLocalRing A] [Field L] [Algebra A L]

/-- `L` is **unramified with respect to the local ring `A`**: every maximal ideal of the integral
closure of `A` in `L` has ramification index one and separable residue field extension over the
residue field of `A`. This is Stacks' notion for `A` a discrete valuation ring and `L` a finite
separable extension of its fraction field. -/
@[stacks 09E9 "(1)"]
def IsUnramifiedWRT : Prop :=
  ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
    P.ramificationIdx A = 1 ∧
      Algebra.IsSeparable (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P)

/-- `L` is **tamely ramified with respect to the local ring `A`**: every maximal ideal of the
integral closure of `A` in `L` has separable residue field extension over the residue field of
`A`, and a ramification index invertible in that residue field. This is Stacks' notion for `A` a
discrete valuation ring and `L` a finite separable extension of its fraction field. -/
@[stacks 09E9 "(2)"]
def IsTamelyRamifiedWRT : Prop :=
  ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
    Algebra.IsSeparable (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P) ∧
      IsUnit ((P.ramificationIdx A : ℕ) : A ⧸ maximalIdeal A)

/-- `L` is **totally ramified with respect to the local ring `A`**: the integral closure of `A`
in `L` has exactly one maximal ideal, and its residue degree over `A` is one. This is Stacks'
notion for `A` a discrete valuation ring and `L` a finite separable extension of its fraction
field. -/
@[stacks 09E9 "(3)"]
def IsTotallyRamifiedWRT : Prop :=
  (∃! P : Ideal (integralClosure A L), P.IsMaximal) ∧
    ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.inertiaDeg A = 1

variable {A L}

/-- Unfolds `IsUnramifiedWRT` to its defining condition on maximal ideals. -/
theorem isUnramifiedWRT_def :
    IsUnramifiedWRT A L ↔
      ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
        P.ramificationIdx A = 1 ∧
          Algebra.IsSeparable (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P) :=
  Iff.rfl

/-- Unfolds `IsTamelyRamifiedWRT` to its defining condition on maximal ideals. -/
theorem isTamelyRamifiedWRT_def :
    IsTamelyRamifiedWRT A L ↔
      ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
        Algebra.IsSeparable (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P) ∧
          IsUnit ((P.ramificationIdx A : ℕ) : A ⧸ maximalIdeal A) :=
  Iff.rfl

omit [IsLocalRing A] in
/-- Unfolds `IsTotallyRamifiedWRT` to its defining condition on maximal ideals. -/
theorem isTotallyRamifiedWRT_def :
    IsTotallyRamifiedWRT A L ↔
      (∃! P : Ideal (integralClosure A L), P.IsMaximal) ∧
        ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.inertiaDeg A = 1 :=
  Iff.rfl

/-- Unramified extensions are tamely ramified. -/
theorem IsUnramifiedWRT.isTamelyRamifiedWRT (h : IsUnramifiedWRT A L) :
    IsTamelyRamifiedWRT A L := fun P _ _ ↦ ⟨(h P).2, by simp [(h P).1]⟩

end Definitions

section DiscreteValuationRing

variable (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L] [FiniteDimensional K L]

include K in
/-- If the residue field of a discrete valuation ring `A` has characteristic zero, every finite
extension `L` of its fraction field `K` is tamely ramified with respect to `A`. -/
theorem isTamelyRamifiedWRT_of_charZero [CharZero (A ⧸ maximalIdeal A)] :
    IsTamelyRamifiedWRT A L := by
  have : CharZero A := (Ideal.Quotient.mk (maximalIdeal A)).charZero
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  have : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : IsNoetherianRing (integralClosure A L) := IsIntegralClosure.isNoetherianRing A K L _
  intro P _ _
  let := Ideal.Quotient.field (maximalIdeal A)
  let := Ideal.Quotient.field P
  refine ⟨Algebra.IsAlgebraic.isSeparable_of_perfectField, ?_⟩
  exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Ideal.ramificationIdx_pos A P).ne')

variable [Algebra.IsSeparable K L]

include K

/-- For a finite separable extension `L` of the fraction field of a discrete valuation ring `A`,
the integral closure of `A` in `L` is unramified over `A` at every prime exactly when `L` is
unramified with respect to `A`. -/
theorem isUnramifiedWRT_iff_forall_isUnramifiedAt :
    IsUnramifiedWRT A L ↔
      ∀ (P : Ideal (integralClosure A L)) [P.IsPrime], Algebra.IsUnramifiedAt A P := by
  have : IsDedekindDomain (integralClosure A L) := integralClosure.isDedekindDomain A K L
  have : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L _
  refine ⟨fun h P _ ↦ ?_, fun h P _ _ ↦
    (Ideal.isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable_quotient _ P).mp (h P)⟩
  rcases eq_or_ne P ⊥ with rfl | hP
  · -- The localization at the generic point is the fraction field `L`, separable over `K`.
    have : IsFractionRing (integralClosure A L) L :=
      IsIntegralClosure.isFractionRing_of_finite_extension A K L _
    have : IsFractionRing (integralClosure A L)
        (Localization.AtPrime (⊥ : Ideal (integralClosure A L))) := by
      simpa [Ideal.primeCompl_bot] using
        Localization.isLocalization (M := (⊥ : Ideal (integralClosure A L)).primeCompl)
    have : FormallyUnramified A K := .of_isLocalization (nonZeroDivisors A)
    have : FormallyUnramified K L := .of_isSeparable K L
    have : FormallyUnramified A L := .comp A K L
    exact .of_equiv
      ((IsLocalization.algEquiv (nonZeroDivisors (integralClosure A L)) L
        (Localization.AtPrime (⊥ : Ideal (integralClosure A L)))).restrictScalars A)
  have : P.IsMaximal := Ideal.IsPrime.isMaximal ‹_› hP
  have : P.LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A P)).symm⟩
  exact (Ideal.isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable_quotient _ P).mpr (h P)

/-- A finite separable extension `L` of the fraction field of a discrete valuation ring `A` is
unramified with respect to `A` iff the integral closure of `A` in `L` is étale over `A`. -/
theorem isUnramifiedWRT_iff_etale :
    IsUnramifiedWRT A L ↔ Algebra.Etale A (integralClosure A L) := by
  have : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L _
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.Free A (integralClosure A L) := IsIntegralClosure.module_free A K L _
  have : Algebra.FinitePresentation A (integralClosure A L) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  rw [isUnramifiedWRT_iff_forall_isUnramifiedAt A K L]
  refine ⟨fun h ↦ ?_, fun _ P _ ↦ inferInstance⟩
  have : FormallyUnramified A (integralClosure A L) :=
    formallyUnramified_iff_forall.mpr fun q ↦ h q.1
  exact .of_formallyUnramified_of_flat

/-- A finite separable extension `L` of the fraction field `K` of a discrete valuation ring `A` is
totally ramified with respect to `A` iff some maximal ideal of the integral closure of `A` in `L`
has ramification index `[L : K]`. -/
theorem isTotallyRamifiedWRT_iff_exists_ramificationIdx_eq_finrank :
    IsTotallyRamifiedWRT A L ↔
      ∃ P : Ideal (integralClosure A L), P.IsMaximal ∧
        P.ramificationIdx A = Module.finrank K L := by
  have : IsDedekindDomain (integralClosure A L) := integralClosure.isDedekindDomain A K L
  have : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L _
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.Free A (integralClosure A L) := IsIntegralClosure.module_free A K L _
  -- The fundamental identity `∑ eᵢ fᵢ = [L : K]` over the primes above the closed point.
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal A) (integralClosure A L)
  rw [IsIntegralClosure.rank A K L (integralClosure A L)] at hsum
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  have hliesOver (P : Ideal (integralClosure A L)) [P.IsMaximal] :
      P ∈ (maximalIdeal A).primesOver (integralClosure A L) :=
    ⟨inferInstance, ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A P)).symm⟩⟩
  have hmax (Q : (maximalIdeal A).primesOver (integralClosure A L)) : Q.1.IsMaximal :=
    have := Q.2.1
    have := Q.2.2
    Ideal.IsMaximal.of_liesOver_isMaximal Q.1 (maximalIdeal A)
  have he (Q : (maximalIdeal A).primesOver (integralClosure A L)) : 0 < Q.1.ramificationIdx A :=
    have := Q.2.1
    Ideal.ramificationIdx_pos A Q.1
  have hf (Q : (maximalIdeal A).primesOver (integralClosure A L)) : 0 < Q.1.inertiaDeg A :=
    have := Q.2.1
    Ideal.inertiaDeg_pos Q.1 A
  constructor
  · rintro ⟨⟨P, hP, huniq⟩, hf1⟩
    refine ⟨P, hP, ?_⟩
    rw [Finset.sum_eq_single_of_mem ⟨P, hliesOver P⟩ (Finset.mem_univ _)
      fun Q _ hQ ↦ (hQ (Subtype.ext (huniq Q.1 (hmax Q)))).elim, hf1 P, mul_one] at hsum
    exact hsum
  · rintro ⟨P, hP, heP⟩
    -- The term of `P` alone already accounts for `[L : K]`, so `f(P) = 1` and no other prime
    -- lies over the closed point.
    have hPf : P.inertiaDeg A = 1 := by
      have h : P.ramificationIdx A * P.inertiaDeg A ≤ Module.finrank K L :=
        hsum ▸ Finset.single_le_sum (f := fun Q : (maximalIdeal A).primesOver _ ↦
          Q.1.ramificationIdx A * Q.1.inertiaDeg A) (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ ⟨P, hliesOver P⟩)
      rw [heP] at h
      have := hf ⟨P, hliesOver P⟩
      nlinarith
    have huniq (Q : Ideal (integralClosure A L)) [Q.IsMaximal] : Q = P := by
      by_contra hQP
      have h : Q.ramificationIdx A * Q.inertiaDeg A + P.ramificationIdx A * P.inertiaDeg A ≤
          Module.finrank K L := by
        rw [← hsum]
        exact (Finset.sum_pair (f := fun Q : (maximalIdeal A).primesOver _ ↦
          Q.1.ramificationIdx A * Q.1.inertiaDeg A) (a := ⟨Q, hliesOver Q⟩)
          (b := ⟨P, hliesOver P⟩) fun h ↦ hQP (congrArg Subtype.val h)).ge.trans
          (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
      rw [heP, hPf] at h
      have := he ⟨Q, hliesOver Q⟩
      have := hf ⟨Q, hliesOver Q⟩
      nlinarith
    exact ⟨⟨P, hP, fun Q _ ↦ huniq Q⟩, fun Q _ ↦ huniq Q ▸ hPf⟩

end DiscreteValuationRing

end TauCeti.Algebra
