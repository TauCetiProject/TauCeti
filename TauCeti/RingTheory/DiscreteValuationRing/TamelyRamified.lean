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

import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Smooth.Fiber
import TauCeti.RingTheory.Ideal.LiesOver
import TauCeti.RingTheory.Localization.Integral
import TauCeti.RingTheory.RamificationInertia.Bijective

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
and residue degrees are Mathlib's `Ideal.inertiaDeg`. The definitions, the comparisons between
them, their transport along integral-closure models and the tower lemmas `trans` only need `A`
to be local (`trans` also asks the integral closure of `A` in the intermediate field to be a
discrete valuation ring); the remaining results assume `A` is a discrete valuation ring. For
extensions of nonarchimedean local fields, the valuation-theoretic counterparts are
`TauCeti.IsTamelyRamified` and `TauCeti.IsTotallyRamified`.

## Main results

* `TauCeti.Algebra.IsUnramifiedWRT.isTamelyRamifiedWRT`: unramified extensions are tamely
  ramified.
* `TauCeti.Algebra.IsTotallyRamifiedWRT.isTamelyRamifiedWRT_iff`: a totally ramified extension
  is tamely ramified iff its ramification index is invertible in the residue field of `A`.
* `TauCeti.Algebra.isTamelyRamifiedWRT_iff_of_isIntegralClosure` and
  `TauCeti.Algebra.isUnramifiedWRT_iff_of_isIntegralClosure`: the conditions may be checked on
  any integral closure of `A` in `L`.
* `TauCeti.Algebra.IsTamelyRamifiedWRT.trans` and `TauCeti.Algebra.IsUnramifiedWRT.trans`: for a
  tower `K ⊆ M ⊆ L` such that the integral closure `A_M` of `A` in `M` is a discrete valuation
  ring, if `M` is tamely ramified (resp. unramified) with respect to `A` and `L` with respect to
  `A_M`, then `L` is tamely ramified (resp. unramified) with respect to `A`.
* `TauCeti.Algebra.IsTamelyRamifiedWRT.tower_bot` and
  `TauCeti.Algebra.IsUnramifiedWRT.tower_bot`: both properties pass from an extension `L` of `M`
  to `M`, for `M` finite and separable over `K`.
* `TauCeti.Algebra.isTamelyRamifiedWRT_of_charZero`: if the residue field of `A` has
  characteristic zero, every finite extension of `K` is tamely ramified with respect to `A`.
* `TauCeti.Algebra.isUnramifiedWRT_iff_forall_isUnramifiedAt`: `L` is unramified with respect
  to `A` iff the integral closure of `A` in `L` is unramified over `A` at every prime.
* `TauCeti.Algebra.isUnramifiedWRT_iff_etale`: `L` is unramified with respect to `A` iff the
  integral closure of `A` in `L` is étale over `A`.
* `TauCeti.Algebra.isUnramifiedWRT_of_isFractionRing`: the fraction field of `A` is unramified
  with respect to `A`.
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

/-- A totally ramified extension has trivial residue field extensions, so it is tamely ramified
exactly when its ramification index is invertible in the residue field of `A`. -/
theorem IsTotallyRamifiedWRT.isTamelyRamifiedWRT_iff (h : IsTotallyRamifiedWRT A L) :
    IsTamelyRamifiedWRT A L ↔
      ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
        IsUnit ((P.ramificationIdx A : ℕ) : A ⧸ maximalIdeal A) := by
  refine ⟨fun h' P _ _ ↦ (h' P).2, fun he P _ _ ↦ ⟨⟨fun x ↦ ?_⟩, he P⟩⟩
  let := Ideal.Quotient.field (maximalIdeal A)
  let := Ideal.Quotient.field P
  have : Module.Free (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P) := .of_divisionRing _ _
  have htop : (⊥ : Subalgebra (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P)) = ⊤ :=
    Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr
      ((Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) P).symm.trans (h.2 P))
  obtain ⟨a, rfl⟩ := Algebra.mem_bot.mp (htop ▸ Algebra.mem_top : x ∈ (⊥ : Subalgebra _ _))
  exact isSeparable_algebraMap a

end Definitions

section IntegralClosure

variable {A L : Type*} [CommRing A] [IsLocalRing A] [Field L] [Algebra A L]

/-- Tameness at the maximal ideals over the closed point transfers along an isomorphism of
`A`-algebras. -/
private theorem forall_tame_of_algEquiv {B C : Type*} [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C] (e : B ≃ₐ[A] C)
    (h : ∀ (Q : Ideal C) [Q.IsMaximal] [Q.LiesOver (maximalIdeal A)],
      Algebra.IsSeparable (A ⧸ maximalIdeal A) (C ⧸ Q) ∧
        IsUnit ((Q.ramificationIdx A : ℕ) : A ⧸ maximalIdeal A))
    (P : Ideal B) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
    Algebra.IsSeparable (A ⧸ maximalIdeal A) (B ⧸ P) ∧
      IsUnit ((P.ramificationIdx A : ℕ) : A ⧸ maximalIdeal A) := by
  let σ := Ideal.Quotient.algEquivOfEqMap (maximalIdeal A) e (Q := P.map e) rfl
  let := Ideal.Quotient.field (maximalIdeal A)
  let := Ideal.Quotient.field P
  let := Ideal.Quotient.field (P.map e)
  have := (h (P.map e)).1
  exact ⟨.of_algHom _ _ σ.toAlgHom, Ideal.ramificationIdx_map_algEquiv e P ▸ (h (P.map e)).2⟩

/-- Unramifiedness at the maximal ideals over the closed point transfers along an isomorphism of
`A`-algebras. -/
private theorem forall_unramified_of_algEquiv {B C : Type*} [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (e : B ≃ₐ[A] C)
    (h : ∀ (Q : Ideal C) [Q.IsMaximal] [Q.LiesOver (maximalIdeal A)],
      Q.ramificationIdx A = 1 ∧ Algebra.IsSeparable (A ⧸ maximalIdeal A) (C ⧸ Q))
    (P : Ideal B) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
    P.ramificationIdx A = 1 ∧ Algebra.IsSeparable (A ⧸ maximalIdeal A) (B ⧸ P) := by
  let σ := Ideal.Quotient.algEquivOfEqMap (maximalIdeal A) e (Q := P.map e) rfl
  let := Ideal.Quotient.field (maximalIdeal A)
  let := Ideal.Quotient.field P
  let := Ideal.Quotient.field (P.map e)
  have := (h (P.map e)).2
  exact ⟨Ideal.ramificationIdx_map_algEquiv e P ▸ (h (P.map e)).1, .of_algHom _ _ σ.toAlgHom⟩

variable (B : Type*) [CommRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
  [IsIntegralClosure B A L]

/-- `IsTamelyRamifiedWRT A L` can be checked on any integral closure `B` of `A` in `L`, not only
on the subalgebra `integralClosure A L`. -/
theorem isTamelyRamifiedWRT_iff_of_isIntegralClosure :
    IsTamelyRamifiedWRT A L ↔
      ∀ (P : Ideal B) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
        Algebra.IsSeparable (A ⧸ maximalIdeal A) (B ⧸ P) ∧
          IsUnit ((P.ramificationIdx A : ℕ) : A ⧸ maximalIdeal A) :=
  ⟨fun h ↦ forall_tame_of_algEquiv (IsIntegralClosure.equiv A B L (integralClosure A L)) h,
    fun h ↦ forall_tame_of_algEquiv (IsIntegralClosure.equiv A (integralClosure A L) L B) h⟩

/-- `IsUnramifiedWRT A L` can be checked on any integral closure `B` of `A` in `L`, not only on
the subalgebra `integralClosure A L`. -/
theorem isUnramifiedWRT_iff_of_isIntegralClosure :
    IsUnramifiedWRT A L ↔
      ∀ (P : Ideal B) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
        P.ramificationIdx A = 1 ∧ Algebra.IsSeparable (A ⧸ maximalIdeal A) (B ⧸ P) :=
  ⟨fun h ↦ forall_unramified_of_algEquiv (IsIntegralClosure.equiv A B L (integralClosure A L)) h,
    fun h ↦ forall_unramified_of_algEquiv (IsIntegralClosure.equiv A (integralClosure A L) L B) h⟩

end IntegralClosure

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

section Tower

variable {A M L : Type*} [CommRing A] [Field M] [Field L] [Algebra A M]
  [Algebra A L] [Algebra M L] [IsScalarTower A M L]

attribute [local instance] integralClosureMapAlgebra isScalarTower_integralClosureMapAlgebra_left
  isScalarTower_integralClosureMapAlgebra_right

/-- **Tame ramification in towers.** Let `M ⊆ L` be fields over the local ring `A` such that the
integral closure `A_M` of `A` in `M` is a discrete valuation ring. If `M` is tamely ramified with
respect to `A` and `L` is tamely ramified with respect to `A_M`, then `L` is tamely ramified with
respect to `A`. -/
theorem IsTamelyRamifiedWRT.trans [IsLocalRing A] [IsDiscreteValuationRing (integralClosure A M)]
    (hM : IsTamelyRamifiedWRT A M) (hL : IsTamelyRamifiedWRT (integralClosure A M) L) :
    IsTamelyRamifiedWRT A L := by
  have : Algebra.IsIntegral (integralClosure A M) (integralClosure A L) := .tower_top A
  have : FaithfulSMul (integralClosure A M) (integralClosure A L) := .tower_bot _ _ L
  have : Module.IsTorsionFree (integralClosure A M) (integralClosure A L) :=
    FaithfulSMul.to_isTorsionFree ..
  have : IsIntegralClosure (integralClosure A L) (integralClosure A M) L :=
    IsIntegralClosure.tower_top (R := A)
  rw [isTamelyRamifiedWRT_iff_of_isIntegralClosure (integralClosure A L)] at hL
  intro P _ _
  have hQ : P.under (integralClosure A M) = maximalIdeal (integralClosure A M) :=
    eq_maximalIdeal (Ideal.IsMaximal.under _ P)
  have : P.LiesOver (maximalIdeal (integralClosure A M)) := ⟨hQ.symm⟩
  have : (maximalIdeal (integralClosure A M)).LiesOver (maximalIdeal A) :=
    ⟨(eq_maximalIdeal (Ideal.IsMaximal.under A _)).symm⟩
  obtain ⟨hsepM, heM⟩ := hM (maximalIdeal (integralClosure A M))
  obtain ⟨hsepL, heL⟩ := hL P
  let := Ideal.Quotient.field (maximalIdeal A)
  let := Ideal.Quotient.field (maximalIdeal (integralClosure A M))
  let := Ideal.Quotient.field P
  have := Ideal.Quotient.isScalarTower_quotient_of_liesOver (maximalIdeal A)
    (maximalIdeal (integralClosure A M)) P
  refine ⟨.trans _ (integralClosure A M ⧸ maximalIdeal (integralClosure A M)) _, ?_⟩
  rw [Ideal.ramificationIdx_tower (q := maximalIdeal (integralClosure A M)), Nat.cast_mul]
  refine heM.mul (isUnit_iff_ne_zero.mpr fun h ↦ isUnit_iff_ne_zero.mp heL ?_)
  rw [← map_natCast (algebraMap (A ⧸ maximalIdeal A)
    (integralClosure A M ⧸ maximalIdeal (integralClosure A M))), h, map_zero]

/-- **Unramified extensions in towers.** Let `M ⊆ L` be fields over the local ring `A` such that
the integral closure `A_M` of `A` in `M` is a discrete valuation ring. If `M` is unramified with
respect to `A` and `L` is unramified with respect to `A_M`, then `L` is unramified with respect
to `A`. -/
theorem IsUnramifiedWRT.trans [IsLocalRing A] [IsDiscreteValuationRing (integralClosure A M)]
    (hM : IsUnramifiedWRT A M) (hL : IsUnramifiedWRT (integralClosure A M) L) :
    IsUnramifiedWRT A L := by
  have : Algebra.IsIntegral (integralClosure A M) (integralClosure A L) := .tower_top A
  have : FaithfulSMul (integralClosure A M) (integralClosure A L) := .tower_bot _ _ L
  have : Module.IsTorsionFree (integralClosure A M) (integralClosure A L) :=
    FaithfulSMul.to_isTorsionFree ..
  have : IsIntegralClosure (integralClosure A L) (integralClosure A M) L :=
    IsIntegralClosure.tower_top (R := A)
  rw [isUnramifiedWRT_iff_of_isIntegralClosure (integralClosure A L)] at hL
  intro P _ _
  have : P.LiesOver (maximalIdeal (integralClosure A M)) :=
    ⟨(eq_maximalIdeal (Ideal.IsMaximal.under _ P)).symm⟩
  have : (maximalIdeal (integralClosure A M)).LiesOver (maximalIdeal A) :=
    ⟨(eq_maximalIdeal (Ideal.IsMaximal.under A _)).symm⟩
  obtain ⟨heM, hsepM⟩ := hM (maximalIdeal (integralClosure A M))
  obtain ⟨heL, hsepL⟩ := hL P
  let := Ideal.Quotient.field (maximalIdeal A)
  let := Ideal.Quotient.field (maximalIdeal (integralClosure A M))
  let := Ideal.Quotient.field P
  have := Ideal.Quotient.isScalarTower_quotient_of_liesOver (maximalIdeal A)
    (maximalIdeal (integralClosure A M)) P
  rw [Ideal.ramificationIdx_tower (q := maximalIdeal (integralClosure A M)), heM, heL]
  exact ⟨rfl, .trans _ (integralClosure A M ⧸ maximalIdeal (integralClosure A M)) _⟩

section TowerBot

variable (K : Type*) [Field K] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A K]
  [IsFractionRing A K] [Algebra K M] [IsScalarTower A K M] [FiniteDimensional K M]
  [Algebra.IsSeparable K M]

include K in
/-- Let `M` be a finite separable extension of the fraction field `K` of a discrete valuation ring
`A`, and `L` any extension of `M`. If `L` is tamely ramified with respect to `A`, then so is `M`. -/
theorem IsTamelyRamifiedWRT.tower_bot (h : IsTamelyRamifiedWRT A L) : IsTamelyRamifiedWRT A M := by
  intro Q _ _
  have : IsDedekindDomain (integralClosure A M) := integralClosure.isDedekindDomain A K M
  have : Algebra.IsIntegral (integralClosure A M) (integralClosure A L) := .tower_top A
  have : FaithfulSMul (integralClosure A M) (integralClosure A L) := .tower_bot _ _ L
  have : Module.IsTorsionFree (integralClosure A M) (integralClosure A L) :=
    FaithfulSMul.to_isTorsionFree ..
  obtain ⟨P, _, _, hdvd⟩ :=
    Ideal.exists_isMaximal_liesOver_ramificationIdx_dvd A (T := integralClosure A L) Q
  have : P.LiesOver (maximalIdeal A) := .trans P Q (maximalIdeal A)
  obtain ⟨hsep, he⟩ := h P
  let := Ideal.Quotient.field (maximalIdeal A)
  let := Ideal.Quotient.field Q
  let := Ideal.Quotient.field P
  have := Ideal.Quotient.isScalarTower_quotient_of_liesOver (maximalIdeal A) Q P
  exact ⟨Algebra.isSeparable_tower_bot_of_isSeparable _ _ (integralClosure A L ⧸ P),
    isUnit_of_dvd_unit (Nat.cast_dvd_cast hdvd) he⟩

include K in
/-- Let `M` be a finite separable extension of the fraction field `K` of a discrete valuation ring
`A`, and `L` any extension of `M`. If `L` is unramified with respect to `A`, then so is `M`. -/
theorem IsUnramifiedWRT.tower_bot (h : IsUnramifiedWRT A L) : IsUnramifiedWRT A M := by
  intro Q _ _
  have : IsDedekindDomain (integralClosure A M) := integralClosure.isDedekindDomain A K M
  have : Algebra.IsIntegral (integralClosure A M) (integralClosure A L) := .tower_top A
  have : FaithfulSMul (integralClosure A M) (integralClosure A L) := .tower_bot _ _ L
  have : Module.IsTorsionFree (integralClosure A M) (integralClosure A L) :=
    FaithfulSMul.to_isTorsionFree ..
  obtain ⟨P, _, _, hdvd⟩ :=
    Ideal.exists_isMaximal_liesOver_ramificationIdx_dvd A (T := integralClosure A L) Q
  have : P.LiesOver (maximalIdeal A) := .trans P Q (maximalIdeal A)
  obtain ⟨he, hsep⟩ := h P
  let := Ideal.Quotient.field (maximalIdeal A)
  let := Ideal.Quotient.field Q
  let := Ideal.Quotient.field P
  have := Ideal.Quotient.isScalarTower_quotient_of_liesOver (maximalIdeal A) Q P
  exact ⟨Nat.dvd_one.mp (he ▸ hdvd),
    Algebra.isSeparable_tower_bot_of_isSeparable _ _ (integralClosure A L ⧸ P)⟩

end TowerBot

end Tower

/-- The fraction field of a discrete valuation ring `A` is unramified with respect to `A`: the
integral closure of `A` in it is `A` itself. -/
theorem isUnramifiedWRT_of_isFractionRing (A L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field L] [Algebra A L] [IsFractionRing A L] :
    IsUnramifiedWRT A L := by
  rw [isUnramifiedWRT_iff_etale A L L]
  exact .of_equiv ((Algebra.botEquivOfInjective (IsFractionRing.injective A L)).symm.trans
    (Subalgebra.equivOfEq _ _ (IsIntegrallyClosed.integralClosure_eq_bot A L).symm))

end TauCeti.Algebra
