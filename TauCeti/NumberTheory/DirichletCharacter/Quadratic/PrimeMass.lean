/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.PrimeFactors.Bounds
public import TauCeti.NumberTheory.Chebyshev.Mertens

/-!
# Splitting the logarithmic prime mass of a quadratic character

For a quadratic Dirichlet character, every prime has character value `0`, `1`, or `-1`.
The zero values occur precisely at primes dividing the level. Their logarithmic mass is
at most half the logarithm of the level, independently of the prime cutoff. Consequently,
Mertens' first theorem gives a lower bound for the combined mass of the `1` and `-1` primes.
This allows separate upper bounds for these two classes to be compared against the full
prime sum without discarding the primes dividing the level.

All cutoffs are inclusive and use `Nat.primesLE`. Neither primitivity nor nonprincipality
is required; the level, not the primitive conductor, controls the omitted primes.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 3.4(a).
-/

public section

open Finset

namespace DirichletCharacter

section ZeroValues

variable {R : Type*} [CommMonoidWithZero R] [Nontrivial R] {q : ℕ}

open Classical in
/-- The primes at which a character vanishes are precisely the prime divisors of its level,
with the same inclusive cutoff. -/
@[simp]
theorem filter_primesLE_eq_zero (χ : DirichletCharacter R q) [NeZero q] (n : ℕ) :
    (Nat.primesLE n).filter (fun p : ℕ ↦ χ p = 0) = q.primeFactors.filter (· ≤ n) := by
  classical
  ext p
  by_cases hp : p.Prime
  · simp [Nat.mem_primesLE, Nat.mem_primeFactors, hp, NeZero.ne q,
      MulChar.apply_eq_zero_iff, ZMod.isUnit_prime_iff_not_dvd hp, and_comm]
  · simp [Nat.mem_primesLE, Nat.mem_primeFactors, hp]

open Classical in
/-- The logarithmic prime mass lost at primes dividing the level is at most `log q / 2`,
uniformly in the real cutoff. -/
theorem sum_primesLE_filter_eq_zero_log_div_le (χ : DirichletCharacter R q) [NeZero q]
    (x : ℝ) :
    ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ χ p = 0), Real.log p / p ≤
      Real.log q / 2 := by
  classical
  rw [χ.filter_primesLE_eq_zero]
  refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p hp _ ↦ ?_).trans
    (Nat.sum_primeFactors_log_div_le q)
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast
    (Nat.prime_of_mem_primeFactors hp).one_lt.le)) (Nat.cast_nonneg p)

end ZeroValues

section Quadratic

variable {R : Type*} [CommRing R] [NeZero (2 : R)] {q : ℕ}

open Classical in
/-- The logarithmic prime sum is the sum of its three character-value classes. This identity
also holds at level zero; only the estimate for the zero-value class needs a positive level. -/
theorem sum_primesLE_log_div_eq_add_filter (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (x : ℝ) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p =
      (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ χ p = 1), Real.log p / p) +
      (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ χ p = -1), Real.log p / p) +
      ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ χ p = 0), Real.log p / p := by
  classical
  have : Nontrivial R := nontrivial_of_ne (2 : R) 0 (NeZero.ne _)
  have hne : (1 : R) ≠ -1 := by
    intro h
    have : (2 : R) = 0 := by linear_combination h
    exact NeZero.ne (2 : R) this
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rcases hχ p with h | h | h <;> simp [h, hne, hne.symm]

end Quadratic

section MassBound

variable {R : Type*} [CommRing R] {q : ℕ}

open Classical in
/-- Mertens' lower bound after removing the zero-value primes of a quadratic character.
The error constant is absolute and the level penalty is only `log q / 2`.
This inequality even permits characteristic two, where the two nonzero classes coincide. -/
theorem log_sub_le_sum_primesLE_filter_one_add_neg_one (χ : DirichletCharacter R q)
    [NeZero q] (hχ : χ.IsQuadratic) {x : ℝ} (hx : 0 ≤ x) :
    Real.log x - (2 * Real.log 4 + 3 / 2) - Real.log q / 2 ≤
      (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ χ p = 1), Real.log p / p) +
      ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ χ p = -1), Real.log p / p := by
  classical
  have hM := Chebyshev.log_sub_le_sum_primesLE_log_div hx
  rcases subsingleton_or_nontrivial R with hR | hR
  · simp only [sum_filter]
    simp only [ite_eq_left (Subsingleton.elim (χ (_ : ZMod q)) (1 : R)),
      ite_eq_left (Subsingleton.elim (χ (_ : ZMod q)) (-1 : R))]
    have hlog : 0 ≤ Real.log q :=
      Real.log_nonneg (by exact_mod_cast (NeZero.one_le : 1 ≤ q))
    have hnonneg : 0 ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p :=
      sum_nonneg fun p _ ↦ div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    linarith
  · have hsum : (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p) ≤
        (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ χ p = 1), Real.log p / p) +
        (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ χ p = -1), Real.log p / p) +
        ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ χ p = 0), Real.log p / p := by
      simp only [sum_filter, ← sum_add_distrib]
      refine sum_le_sum fun p _ ↦ ?_
      have hp : 0 ≤ Real.log p / p :=
        div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
      rcases hχ p with h | h | h <;> simp only [h, ite_true] <;>
        split_ifs <;> linarith
    linarith [χ.sum_primesLE_filter_eq_zero_log_div_le x]

end MassBound

end DirichletCharacter
