/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Lifting units between ideal quotients of a Dedekind domain

Reduction between quotients by nonzero ideals is surjective on units. This is stronger than
surjectivity on ring elements: a representative must also avoid the extra prime divisors of the
larger modulus. The Chinese remainder theorem lets us impose residue one at these extra primes
without changing the prescribed residue at the smaller modulus.

The proof uses Mathlib's `Ideal.quotientInfEquivQuotientProd` and
`IsDedekindDomain.quotientEquivPiFactors`, together with its unit criterion modulo a prime power.
This lifting statement supplies the residue-unit transition maps for ray class groups.
-/

public section

open Ideal.Quotient

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Every prime factor of an ideal in a Dedekind domain is a maximal ideal. -/
theorem Ideal.isMaximal_of_mem_factors {J P : Ideal R}
    (hP : P ∈ UniqueFactorizationMonoid.factors J) : P.IsMaximal :=
  Ideal.IsPrime.isMaximal
    (Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_factor P hP))
    (UniqueFactorizationMonoid.prime_of_factor P hP).ne_zero

namespace TauCeti

/-- Reduction between ideal quotients of a Dedekind domain is surjective on units when the source
ideal is nonzero. No finiteness assumption on the residue fields is needed. -/
theorem units_map_quotient_factor_surjective {I J : Ideal R} (h : J ≤ I) (hJ : J ≠ ⊥) :
    Function.Surjective (Units.map (factor h).toMonoidHom) := by
  classical
  intro u
  -- Use CRT to avoid exactly the prime factors of J which do not contain I.
  let s := (UniqueFactorizationMonoid.factors J).toFinset.filter fun P => ¬I ≤ P
  let B : Ideal R := ∏ P ∈ s, P
  have hmax (P : Ideal R) (hP : P ∈ UniqueFactorizationMonoid.factors J) : P.IsMaximal :=
    Ideal.isMaximal_of_mem_factors hP
  have hIB : I ⊔ B = ⊤ := by
    apply Ideal.sup_prod_eq_top
    intro P hP
    obtain ⟨hPJ, hIP⟩ := Finset.mem_filter.mp hP
    have hPm := hmax P (Multiset.mem_toFinset.mp hPJ)
    by_contra hne
    exact hIP (le_sup_left.trans_eq (hPm.eq_of_le hne le_sup_right).symm)
  let e := Ideal.quotientInfEquivQuotientProd I B (Ideal.isCoprime_iff_sup_eq.mpr hIB)
  obtain ⟨q, hq⟩ := e.surjective ((u : R ⧸ I), 1)
  obtain ⟨a, rfl⟩ := mk_surjective q
  have haI : mk I a = u := by
    simpa [e] using congrArg Prod.fst hq
  have haB : mk B a = 1 := by
    simpa [e] using congrArg Prod.snd hq
  have ha (P : Ideal R) (hP : P ∈ UniqueFactorizationMonoid.factors J) : a ∉ P := by
    have := hmax P hP
    -- Modulo `P`, the residue of `a` is a unit: it is `u` if `I ≤ P` and `1` otherwise.
    have hu : IsUnit (mk P a) := by
      by_cases hIP : I ≤ P
      · rw [← factor_mk hIP, haI]
        exact u.isUnit.map (factor hIP)
      · have hBP : B ≤ P := Ideal.le_of_dvd <| Finset.dvd_prod_of_mem (f := id) <|
          Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hP, hIP⟩
        rw [← factor_mk hBP, haB, map_one]
        exact isUnit_one
    exact fun haP => hu.ne_zero (eq_zero_iff_mem.mpr haP)
  -- The prime-power factors of J detect whether a residue class is a unit.
  have haUnit : IsUnit (mk J a) := by
    apply (MulEquiv.isUnit_map (IsDedekindDomain.quotientEquivPiFactors hJ)).mp
    rw [IsDedekindDomain.quotientEquivPiFactors_mk, Pi.isUnit_iff]
    intro P
    have := hmax P (Multiset.mem_toFinset.mp P.2)
    exact isUnit_mk_pow_of_notMem _ (ha P (Multiset.mem_toFinset.mp P.2))
  refine ⟨haUnit.unit, Units.ext ?_⟩
  simpa using haI

end TauCeti
