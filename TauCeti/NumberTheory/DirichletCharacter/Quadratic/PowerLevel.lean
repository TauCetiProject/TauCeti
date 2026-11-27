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

A character whose square is principal descends to a smaller positive power of the same
base provided the smaller level retains the factors of `4` and `8` of the larger one.
For descent to `m ^ 2`, the factor of `4` is retained automatically. The cube retains both
factors, so a single fixed level suffices without any restriction on the base modulus.

Descent to the square is the statement of `New.factorsThrough_sq_of_sq_eq_one` in
`grh/src/Lib/Analytic/Primes.lean` of https://github.com/lsernau/grh-lean (rev. `72fead1`).
Here it is deduced from the bounds on the prime exponents of a quadratic conductor.
-/

public section

namespace DirichletCharacter

/-- A character of order dividing two modulo `m ^ k` descends to `m ^ j` if `0 < j ≤ k`
and the smaller level retains the factors of `4` and `8` of the larger level. -/
theorem factorsThrough_pow_of_sq_eq_one {R : Type*} [CommMonoidWithZero R] {m j k : ℕ}
    (χ : DirichletCharacter R (m ^ k)) (hχ : χ ^ 2 = 1) (hj : 0 < j) (hjk : j ≤ k)
    (h₄ : 4 ∣ m ^ k → 4 ∣ m ^ j) (h₈ : 8 ∣ m ^ k → 8 ∣ m ^ j) : χ.FactorsThrough (m ^ j) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simpa only [Nat.zero_pow hj, Nat.zero_pow (hj.trans_le hjk)] using FactorsThrough.same_level χ
  let : NeZero (m ^ k) := ⟨pow_ne_zero _ hm⟩
  refine FactorsThrough.mono χ χ.factorsThrough_conductor ?_ (pow_dvd_pow m hjk)
  refine (Nat.factorization_prime_le_iff_dvd χ.conductor_ne_zero (pow_ne_zero _ hm)).mp ?_
  intro p hp
  by_cases hd : p ∣ χ.conductor
  · have hpm := hp.dvd_of_dvd_pow (hd.trans χ.conductor_dvd_level)
    rcases eq_or_ne p 2 with rfl | hp₂
    · have hsource (e : ℕ) := Nat.prime_two.pow_dvd_iff_le_factorization (k := e)
        χ.conductor_ne_zero
      have htarget (e : ℕ) := Nat.prime_two.pow_dvd_iff_le_factorization (k := e) (pow_ne_zero j hm)
      rcases χ.factorization_two_conductor_eq_zero_or_two_or_three_of_sq_eq_one hχ with h | h | h
      · simp [h]
      · exact h.le.trans ((htarget 2).mp (h₄ (((hsource 2).mpr h.ge).trans χ.conductor_dvd_level)))
      · exact h.le.trans ((htarget 3).mp (h₈ (((hsource 3).mpr h.ge).trans χ.conductor_dvd_level)))
    · exact (χ.factorization_conductor_le_one_of_sq_eq_one hχ hp hp₂).trans
        (hp.factorization_pos_of_dvd (pow_ne_zero _ hm) (hpm.trans (dvd_pow_self _ hj.ne')))
  · simp [Nat.factorization_eq_zero_of_not_dvd hd]

/-- A character of order dividing two modulo `m ^ k` descends to `m ^ 2` if `2 ≤ k`
and the reduction does not lose a factor of `8`. The condition at `2` is necessary:
a primitive character of order two modulo `8` need not descend modulo `4`. -/
theorem factorsThrough_sq_of_sq_eq_one {R : Type*} [CommMonoidWithZero R] {m k : ℕ}
    (χ : DirichletCharacter R (m ^ k)) (hχ : χ ^ 2 = 1) (hk : 2 ≤ k)
    (h₈ : 8 ∣ m ^ k → 8 ∣ m ^ 2) : χ.FactorsThrough (m ^ 2) := by
  apply χ.factorsThrough_pow_of_sq_eq_one hχ (by decide) hk ?_ h₈
  intro h₄
  exact pow_dvd_pow_of_dvd_of_le (Nat.prime_two.dvd_of_dvd_pow (dvd_trans (by decide : 2 ∣ 4) h₄))
    le_rfl

end DirichletCharacter
