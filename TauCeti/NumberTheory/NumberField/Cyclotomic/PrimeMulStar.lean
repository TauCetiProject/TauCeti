/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Norm-star factorization of primes `p % 4 ≠ 3` from fourth roots of unity

In any commutative star-ring `R` containing an element `i` with `i * i = -1` and `star i = -i`,
every prime `p` with `p % 4 ≠ 3` factors as `y * star y = p` via Fermat's two-square theorem
(`y = a + b * i`). In a domain `R`, any primitive `n`-th root of unity `ζ` with `4 ∣ n` and
`ζ * star ζ = 1` produces such an element `i = ζ ^ (n / 4)`.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026
Anthropic, PBC), commit `72fead102f663d5c7a407964a13dc0cf9d977207`, specifically
`New.Parameters.exists_mul_star_eq_prime` in `grh/src/New/Reduction/Data/Existence.lean`,
generalized from `𝓞 (P.E s)` to arbitrary commutative star-rings.
-/

public section

namespace TauCeti

/-- In a commutative star-ring `R` containing `i` with `i * i = -1` and `star i = -i`, every
prime `p` with `p % 4 ≠ 3` factors as `y * star y = p`. -/
theorem exists_mul_star_eq_prime_of_sq_eq_neg_one {R : Type*} [CommRing R] [StarRing R]
    {i : R} (hi_sq : i * i = -1) (hi_star : star i = -i) {p : ℕ} (hp : p.Prime)
    (hp4 : p % 4 ≠ 3) : ∃ y : R, y * star y = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hp4
  refine ⟨a + b * i, ?_⟩
  simp only [← hab, star_add, star_mul, hi_star, star_natCast, Nat.cast_add, Nat.cast_pow]
  linear_combination -(b : R) ^ 2 * hi_sq

/-- In a commutative star-domain `R`, a primitive `n`-th root of unity `ζ` with `4 ∣ n` and
`ζ * star ζ = 1` yields an element `i = ζ ^ (n / 4)` with `i * i = -1` and `star i = -i`. -/
theorem exists_sq_eq_neg_one_and_star_eq_neg_of_primitiveRoot {R : Type*} [CommRing R]
    [IsDomain R] [StarRing R] {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0)
    (h4 : 4 ∣ n) (hstar : ζ * star ζ = 1) : ∃ i : R, i * i = -1 ∧ star i = -i := by
  obtain ⟨k, rfl⟩ := h4
  have hk : k ≠ 0 := right_ne_zero_of_mul hn
  let i : R := ζ ^ k
  have h2k : i * i = -1 := by
    have hsq : (i * i) ^ 2 = 1 := by
      calc (i * i) ^ 2 = ζ ^ (4 * k) := by dsimp [i]; ring
        _ = 1 := hζ.pow_eq_one
    have hne : i * i ≠ 1 := by
      intro h1
      have hpow : ζ ^ (2 * k) = 1 := by
        calc ζ ^ (2 * k) = i * i := by dsimp [i]; ring
          _ = 1 := h1
      have hdvd : 4 * k ∣ 2 * k := hζ.dvd_of_pow_eq_one (2 * k) hpow
      have hle : 4 * k ≤ 2 * k := Nat.le_of_dvd (by omega) hdvd
      omega
    exact (sq_eq_one_iff.mp hsq).resolve_left hne
  have histar : i * star i = 1 := by
    dsimp [i]
    rw [star_pow, ← mul_pow, hstar, one_pow]
  refine ⟨i, h2k, ?_⟩
  linear_combination -i * histar + star i * h2k

/-- In a commutative star-domain `R` containing a primitive `n`-th root of unity `ζ` with
`4 ∣ n` and `ζ * star ζ = 1`, every prime `p` with `p % 4 ≠ 3` factors as `y * star y = p`. -/
theorem exists_mul_star_eq_prime_of_primitiveRoot {R : Type*} [CommRing R] [IsDomain R]
    [StarRing R] {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0) (h4 : 4 ∣ n)
    (hstar : ζ * star ζ = 1) {p : ℕ} (hp : p.Prime) (hp4 : p % 4 ≠ 3) :
    ∃ y : R, y * star y = p := by
  obtain ⟨i, hi_sq, hi_star⟩ :=
    exists_sq_eq_neg_one_and_star_eq_neg_of_primitiveRoot hζ hn h4 hstar
  exact exists_mul_star_eq_prime_of_sq_eq_neg_one hi_sq hi_star hp hp4

end TauCeti
