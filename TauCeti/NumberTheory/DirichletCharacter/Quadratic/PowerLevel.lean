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

A character whose square is principal at level `m ^ k` descends to `m ^ j` for
`2 ≤ j ≤ k` provided the latter level retains a factor of `8` whenever the former has one.
In particular one can always descend to `m ^ min k 3`.

The fixed-level reduction is the statement of `New.factorsThrough_sq_of_sq_eq_one` in
`grh/src/Lib/Analytic/Primes.lean` of https://github.com/lsernau/grh-lean (rev. `72fead1`).
Here it is deduced from the bounds on the prime exponents of a quadratic conductor.
-/

public section

namespace DirichletCharacter

/-- A character of order dividing two modulo `m ^ k` descends to `m ^ j` if `2 ≤ j ≤ k`
and the reduction does not lose a factor of `8`. The condition at `2` is necessary:
a primitive character of order two modulo `8` need not descend modulo `4`. -/
theorem factorsThrough_pow_of_sq_eq_one {R : Type*} [CommMonoidWithZero R] {m j k : ℕ}
    (χ : DirichletCharacter R (m ^ k)) (hχ : χ ^ 2 = 1) (hj : 2 ≤ j) (hjk : j ≤ k)
    (h₈ : 8 ∣ m ^ k → 8 ∣ m ^ j) : χ.FactorsThrough (m ^ j) := by
  have hk₀ : k ≠ 0 := by omega
  by_cases hm : m = 0
  · subst m
    simpa only [zero_pow hk₀, zero_pow (by omega : j ≠ 0)] using
      (FactorsThrough.same_level χ)
  let : NeZero (m ^ k) := ⟨pow_ne_zero _ hm⟩
  refine FactorsThrough.mono χ χ.factorsThrough_conductor ?_ (pow_dvd_pow m hjk)
  rw [← Nat.factorization_le_iff_dvd χ.conductor_ne_zero (pow_ne_zero _ hm)]
  intro p
  by_cases h : χ.conductor.factorization p = 0
  · simp [h]
  have hp : p ∈ χ.conductor.primeFactors := by
    simpa only [← Nat.support_factorization, Finsupp.mem_support_iff] using h
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpm : p ∣ m := hprime.dvd_of_dvd_pow
    ((Nat.dvd_of_mem_primeFactors hp).trans χ.conductor_dvd_level)
  have hsq : 2 ≤ (m ^ j).factorization p := by
    have hpos := hprime.factorization_pos_of_dvd hm hpm
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact hj.trans (Nat.le_mul_of_pos_right _ hpos)
  rcases eq_or_ne p 2 with rfl | hp₂
  · rcases factorization_two_conductor_eq_zero_or_two_or_three_of_sq_eq_one hχ with
      h₀ | h₂ | h₃
    · exact (h h₀).elim
    · exact h₂.le.trans hsq
    · have hd : 8 ∣ χ.conductor :=
        (Nat.prime_two.pow_dvd_iff_le_factorization χ.conductor_ne_zero).mpr h₃.ge
      rw [h₃]
      exact (Nat.prime_two.pow_dvd_iff_le_factorization (pow_ne_zero j hm)).mp
        (h₈ (hd.trans χ.conductor_dvd_level))
  · exact (factorization_conductor_le_one_of_sq_eq_one hχ hprime hp₂).trans (by omega)

/-- In a tower of powers of any modulus `m`, the exponent can be capped at three for
characters of order dividing two. -/
theorem factorsThrough_pow_min_three_of_sq_eq_one {R : Type*} [CommMonoidWithZero R] {m k : ℕ}
    (χ : DirichletCharacter R (m ^ k)) (hχ : χ ^ 2 = 1) : χ.FactorsThrough (m ^ min k 3) := by
  rcases le_or_gt k 3 with hk | hk
  · simpa only [min_eq_left hk] using FactorsThrough.same_level χ
  rw [min_eq_right hk.le]
  refine χ.factorsThrough_pow_of_sq_eq_one hχ (by decide) hk.le fun hd ↦ ?_
  exact pow_dvd_pow_of_dvd (Nat.prime_two.dvd_of_dvd_pow ((by decide : 2 ∣ 8).trans hd)) 3

end DirichletCharacter
