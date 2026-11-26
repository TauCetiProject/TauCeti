/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LocalFactor

/-!
# Quadratic Dirichlet characters at powers of a fixed modulus

A character whose square is principal at level `m ^ k`, `k ≥ 2`, descends to `m ^ 2`
provided the latter level retains a factor of `8` whenever the former has one. This
holds in particular if `4 ∣ m` or `m` is odd. Consequently the quadratic characters
in such a tower can be studied using the characters at a single fixed level.

The fixed-level reduction is the statement of `New.factorsThrough_sq_of_sq_eq_one` in
`grh/src/Lib/Analytic/Primes.lean` of https://github.com/lsernau/grh-lean (rev. `72fead1`).
Here it is deduced from the bounds on the prime exponents of a quadratic conductor.
-/

public section

namespace DirichletCharacter

/-- A character of order dividing two modulo `m ^ k` descends to `m ^ 2` if `2 ≤ k`
and the reduction does not lose a factor of `8`. The condition at `2` is necessary:
a primitive character of order two modulo `8` need not descend modulo `4`. -/
theorem factorsThrough_sq_of_sq_eq_one {R : Type*} [CommMonoidWithZero R] {m k : ℕ}
    (χ : DirichletCharacter R (m ^ k)) (hχ : χ ^ 2 = 1) (hk : 2 ≤ k)
    (h₈ : 8 ∣ m ^ k → 8 ∣ m ^ 2) : χ.FactorsThrough (m ^ 2) := by
  have hk₀ : k ≠ 0 := by omega
  by_cases hm : m = 0
  · subst m
    simpa only [zero_pow hk₀, zero_pow two_ne_zero] using
      (FactorsThrough.same_level χ)
  let : NeZero (m ^ k) := ⟨pow_ne_zero _ hm⟩
  refine FactorsThrough.mono χ χ.factorsThrough_conductor ?_ (pow_dvd_pow m hk)
  rw [← Nat.factorization_le_iff_dvd χ.conductor_ne_zero (pow_ne_zero _ hm)]
  intro p
  by_cases h : χ.conductor.factorization p = 0
  · simp [h]
  have hp : p ∈ χ.conductor.primeFactors := by
    simpa only [← Nat.support_factorization, Finsupp.mem_support_iff] using h
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpm : p ∣ m := hprime.dvd_of_dvd_pow
    ((Nat.dvd_of_mem_primeFactors hp).trans χ.conductor_dvd_level)
  have hsq : 2 ≤ (m ^ 2).factorization p := by
    have hpos := hprime.factorization_pos_of_dvd hm hpm
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    omega
  rcases eq_or_ne p 2 with rfl | hp₂
  · rcases factorization_two_conductor_eq_zero_or_two_or_three_of_sq_eq_one hχ with
      h₀ | h₂ | h₃
    · exact (h h₀).elim
    · exact h₂.le.trans hsq
    · have hd : 8 ∣ χ.conductor :=
        (Nat.prime_two.pow_dvd_iff_le_factorization χ.conductor_ne_zero).mpr h₃.ge
      rw [h₃]
      exact (Nat.prime_two.pow_dvd_iff_le_factorization (pow_ne_zero 2 hm)).mp
        (h₈ (hd.trans χ.conductor_dvd_level))
  · exact (factorization_conductor_le_one_of_sq_eq_one hχ hprime hp₂).trans (by omega)

end DirichletCharacter
