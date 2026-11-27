/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Data.Fintype.Pigeonhole
import TauCeti.NumberTheory.NumberField.SplitsCompletely.Basic
import TauCeti.NumberTheory.NumberField.TotallyPositive

/-!
# Products of split primes as norms in quadratic fields

A finite set of split primes larger than the class number of an imaginary quadratic field
contains two distinct primes whose product is the norm of an algebraic integer. The two primes
can thus be chosen from a prescribed progression or interval without asking that either prime
split into principal ideals individually.

The prime-pair target and its ideal-class argument are from `New.Parameters.exists_prime_pair_norm`
in `New/Reduction/Data/Existence.lean` of lsernau/grh-lean, commit `72fead1`.
-/

public section

open Ideal Module
open scoped NumberField nonZeroDivisors

namespace NumberField

/-- In a quadratic number field, among more positive ideal norms than the class number,
two distinct norms have a product equal to the absolute norm of an algebraic integer.
The norms need not be prime: the ideal complementary to `I` in `(N(I))` has norm `N(I)`
and inverse ideal class. -/
theorem exists_natAbs_norm_eq_mul_of_classNumber_lt_card {K : Type*} [Field K] [NumberField K]
    (hK : finrank ℚ K = 2) {S : Finset ℕ} (hcard : classNumber K < S.card)
    (hS : ∀ p ∈ S, ∃ I : (Ideal (𝓞 K))⁰, absNorm (I : Ideal (𝓞 K)) = p) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ ∃ x : 𝓞 K, (Algebra.norm ℤ x).natAbs = p * q := by
  classical
  choose P hP using fun p : S ↦ hS p p.property
  obtain ⟨p, q, hpq, hclass⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun p ↦ ClassGroup.mk0 (P p)) (by simpa [classNumber] using hcard)
  have hq : (q : ℕ) ≠ 0 := (hP q) ▸ absNorm_ne_zero_of_nonZeroDivisors (P q)
  have hle : span {((q : ℕ) : 𝓞 K)} ≤ P q := by
    simpa only [hP q] using span_singleton_absNorm_le (P q : Ideal (𝓞 K))
  obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le.mpr hle)
  have hspan : absNorm (span {((q : ℕ) : 𝓞 K)}) = (q : ℕ) ^ 2 := by
    rw [absNorm_span_natCast, RingOfIntegers.rank, hK]
  have hNJ : absNorm J = q := by
    have hn := congrArg absNorm hJ
    rw [hspan, map_mul, hP q, pow_two] at hn
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) hn.symm
  let Q : (Ideal (𝓞 K))⁰ := ⟨J, absNorm_ne_zero_iff_mem_nonZeroDivisors.mp (hNJ ▸ hq)⟩
  have hprincipal : Submodule.IsPrincipal ((P p * Q : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) := by
    apply (ClassGroup.mk0_eq_one_iff (P p * Q).property).mp
    rw [map_mul, hclass, ← map_mul]
    apply (ClassGroup.mk0_eq_one_iff (P q * Q).property).mpr
    have hmul : ((P q * Q : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = span {((q : ℕ) : 𝓞 K)} :=
      hJ.symm
    rw [hmul]
    infer_instance
  obtain ⟨x, hx⟩ := hprincipal
  have hx' : ((P p * Q : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = span {x} :=
    hx.trans Ideal.submodule_span_eq
  refine ⟨p, p.property, q, q.property, fun h ↦ hpq (Subtype.ext h), x, ?_⟩
  rw [← absNorm_span_singleton, ← hx', Submonoid.coe_mul, map_mul, hP p]
  exact congrArg ((p : ℕ) * ·) hNJ

/-- **Norm of a pair of split primes.** A set of completely split rational primes in an
imaginary quadratic field, of size greater than its class number, contains two distinct primes
whose product is the integral norm of an algebraic integer. Complete splitting is expressed by
the number of primes above each rational prime. -/
theorem exists_norm_eq_mul_of_classNumber_lt_card_of_ncard_primesOver_eq_finrank {K : Type*}
    [Field K] [NumberField K] [IsTotallyComplex K] (hK : finrank ℚ K = 2) {S : Finset ℕ}
    (hcard : classNumber K < S.card)
    (hsplit : ∀ p ∈ S, ((span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)).ncard = finrank ℚ K) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ ∃ x : 𝓞 K, Algebra.norm ℤ x = (p : ℤ) * (q : ℤ) := by
  have hideal (p : ℕ) (hp : p ∈ S) : ∃ I : (Ideal (𝓞 K))⁰, absNorm (I : Ideal (𝓞 K)) = p := by
    have hsplit' := hsplit p hp
    have hp₀ : p ≠ 0 := by
      rintro rfl
      simp [primesOver_bot, hK] at hsplit'
    obtain ⟨P, hPprime, hPover⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hsplit', hK]; decide)
    have := hPprime
    have := hPover
    have hN := P.absNorm_eq_of_ncard_primesOver_eq_finrank hsplit'
    exact ⟨⟨P, absNorm_ne_zero_iff_mem_nonZeroDivisors.mp (hN ▸ hp₀)⟩, hN⟩
  obtain ⟨p, hp, q, hq, hne, x, hx⟩ :=
    exists_natAbs_norm_eq_mul_of_classNumber_lt_card hK hcard hideal
  have hpos : 0 ≤ Algebra.norm ℤ x := by
    have hr := norm_nonneg_of_isTotallyPositive (x := (x : K)) (by simp [isTotallyPositive_iff])
    exact_mod_cast (Algebra.coe_norm_int x ▸ hr)
  refine ⟨p, hp, q, hq, hne, x, ?_⟩
  calc
    Algebra.norm ℤ x = ((Algebra.norm ℤ x).natAbs : ℤ) := (Int.natAbs_of_nonneg hpos).symm
    _ = (p : ℤ) * (q : ℤ) := by exact_mod_cast hx

end NumberField
