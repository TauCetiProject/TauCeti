/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LocalFactor

/-!
# Descent of quadratic Dirichlet characters on powers of a fixed modulus

When descending a character of order dividing two between positive powers of a fixed modulus,
only the dyadic conductor requires a restriction on the smaller power: it must be divisible by
`8` if the base is even. In particular, the cube always suffices. This generalizes the descent
to the square in `New.factorsThrough_sq_of_sq_eq_one` from `Lib/Analytic/Primes.lean` in
lsernau/grh-lean (commit `72fead1`), using the bounds on the prime exponents in quadratic
conductors.
-/

public section

namespace DirichletCharacter

/-- A character of order dividing two modulo `m ^ k` descends to `m ^ j` if `0 < j ≤ k`
and `m ^ j` is divisible by `8` whenever `m` is even. -/
theorem factorsThrough_pow_of_sq_eq_one {R : Type*} [CommMonoidWithZero R] {m j k : ℕ}
    (χ : DirichletCharacter R (m ^ k)) (hχ : χ ^ 2 = 1) (hj : 0 < j) (hjk : j ≤ k)
    (hm : 2 ∣ m → 8 ∣ m ^ j) : χ.FactorsThrough (m ^ j) := by
  rcases eq_or_ne m 0 with rfl | hm₀
  · simpa [Nat.zero_pow hj, Nat.zero_pow (hj.trans_le hjk)] using FactorsThrough.same_level χ
  let : NeZero (m ^ k) := ⟨pow_ne_zero _ hm₀⟩
  refine FactorsThrough.mono χ χ.factorsThrough_conductor ?_
    (pow_dvd_pow_of_dvd_of_le (dvd_refl m) hjk)
  refine (Nat.factorization_prime_le_iff_dvd χ.conductor_ne_zero (pow_ne_zero _ hm₀)).mp ?_
  intro p hp
  by_cases hd : p ∣ χ.conductor
  · have hpm := hp.dvd_of_dvd_pow (hd.trans χ.conductor_dvd_level)
    by_cases hp₂ : p = 2
    · subst p
      have hm₂ : 3 ≤ (m ^ j).factorization 2 :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (pow_ne_zero _ hm₀)).mp (hm hpm)
      have h := χ.factorization_two_conductor_eq_zero_or_two_or_three_of_sq_eq_one hχ
      omega
    · exact (χ.factorization_conductor_le_one_of_sq_eq_one hχ hp hp₂).trans
        (hp.factorization_pos_of_dvd (pow_ne_zero _ hm₀) (hpm.trans (dvd_pow_self _ hj.ne')))
  · simp [Nat.factorization_eq_zero_of_not_dvd hd]

end DirichletCharacter
