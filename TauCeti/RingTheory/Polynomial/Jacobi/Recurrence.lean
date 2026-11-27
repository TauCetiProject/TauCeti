/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Jacobi.Basic
public import Mathlib.Algebra.Polynomial.Derivative

import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.Data.Nat.Factorial.Field

/-!
# Derivative and recurrences of the Jacobi polynomials

This file proves the derivative formula, three contiguous relations and the three-term recurrence
of the Jacobi polynomials `Pₙ^{(α,β)}` over a commutative `ℚ`-algebra, for arbitrary parameters
`α β`.

The derivative formula is a termwise computation in the basis `(X - 1)^{n-k} (X + 1)^k` of the
defining sum. Everything else follows from it by induction on the degree: two polynomials over a
`ℚ`-algebra agree as soon as their derivatives agree and their values at `1` agree, the
derivative formula turns the derivative of a relation in degree `n + 1` into the same relation in
degree `n` with both parameters raised by one, and the values at `1` are
`Polynomial.eval_one_jacobi`. The three-term recurrence is then a linear combination of the
contiguous relations.

## Main results

* `Polynomial.derivative_jacobi`: `(Pₙ₊₁^{(α,β)})' = ((n + α + β + 2) / 2) Pₙ^{(α+1,β+1)}`
  (DLMF 18.9.15).
* `Polynomial.jacobi_succ_contiguous_right`, `Polynomial.jacobi_succ_contiguous_left`: the
  contiguous relations expressing `(2n + α + β + 3) Pₙ₊₁^{(α,β)}` through the polynomials with
  `β`, respectively `α`, raised by one (DLMF 18.9.5 and its reflection).
* `Polynomial.X_add_one_mul_jacobi_add_one`: the contiguous relation expressing
  `(2n + α + β + 2) (X + 1) Pₙ^{(α,β+1)}` through `Pₙ₊₁^{(α,β)}` and `Pₙ^{(α,β)}` (DLMF 18.9.6).
* `Polynomial.jacobi_succ_succ`: the three-term recurrence (DLMF 18.9.1, 18.9.2).

## References

* DLMF, *NIST Digital Library of Mathematical Functions*, <https://dlmf.nist.gov/18>: 18.9.1,
  18.9.2, 18.9.5, 18.9.6, 18.9.15.
* G. Szegő, *Orthogonal Polynomials*, AMS Colloquium Publications 23, Chapter IV.
-/

public section

open Finset

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-! ### The derivative -/

omit [Algebra ℚ R] in
/-- The derivative of a combination of the basis polynomials `(X - 1)^{n+1-k} (X + 1)^k`,
expanded in the basis `(X - 1)^{n-k} (X + 1)^k`. -/
private lemma derivative_sum_smul_X_sub_one_pow_mul_X_add_one_pow (f : ℕ → R) (n : ℕ) :
    derivative (∑ k ∈ range (n + 2), f k • ((X - 1 : R[X]) ^ (n + 1 - k) * (X + 1) ^ k)) =
      ∑ k ∈ range (n + 1), ((((n - k : ℕ) : R) + 1) * f k + ((k : R) + 1) * f (k + 1)) •
        ((X - 1 : R[X]) ^ (n - k) * (X + 1) ^ k) := by
  have h (m k : ℕ) : derivative ((X - 1 : R[X]) ^ m * (X + 1) ^ k) =
      C (m : R) * ((X - 1) ^ (m - 1) * (X + 1) ^ k) +
        C (k : R) * ((X - 1) ^ m * (X + 1) ^ (k - 1)) := by
    simp only [derivative_mul, derivative_pow, derivative_sub, derivative_add, derivative_X,
      derivative_one, sub_zero, add_zero, mul_one]
    ring
  simp only [derivative_sum, derivative_smul, h, smul_add, sum_add_distrib]
  rw [sum_range_succ, sum_range_succ' (fun k =>
    f k • (C (k : R) * ((X - 1 : R[X]) ^ (n + 1 - k) * (X + 1) ^ (k - 1))))]
  simp only [Nat.sub_self, Nat.cast_zero, C_0, zero_mul, smul_zero, add_zero]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
  rw [Nat.add_sub_add_right, Nat.add_sub_cancel, show n + 1 - k = n - k + 1 by omega,
    Nat.add_sub_cancel]
  simp only [smul_eq_C_mul, C_add, C_mul, Nat.cast_add, Nat.cast_one, C_1]
  ring

omit [Algebra ℚ R] in
/-- Peeling the first factor off a rising factorial: `(x)_{r+1} = x (x + 1)_r`. -/
private lemma ascPochhammer_succ_smeval_left (r : ℕ) (x : R) :
    (ascPochhammer R (r + 1)).smeval x = x * (ascPochhammer R r).smeval (x + 1) := by
  simp [← eval_eq_smeval, ascPochhammer_succ_left]

omit [Algebra ℚ R] in
/-- Peeling the last factor off a rising factorial: `(x)_{r+1} = (x)_r (x + r)`. -/
private lemma ascPochhammer_succ_smeval_right (r : ℕ) (x : R) :
    (ascPochhammer R (r + 1)).smeval x = (ascPochhammer R r).smeval x * (x + r) := by
  simp [← eval_eq_smeval, ascPochhammer_succ_right]

/-- The coefficient identity behind `Polynomial.derivative_jacobi`. -/
private lemma derivative_jacobi_coeff (α β : R) (m k : ℕ) :
    ((m : R) + 1) * (((1 : ℚ) / ((m + 1).factorial * k.factorial)) •
        ((ascPochhammer R (m + 1)).smeval (β + k + 1) *
          (ascPochhammer R k).smeval (α + (m + 1 : ℕ) + 1))) +
      ((k : R) + 1) * (((1 : ℚ) / (m.factorial * (k + 1).factorial)) •
        ((ascPochhammer R m).smeval (β + (k + 1 : ℕ) + 1) *
          (ascPochhammer R (k + 1)).smeval (α + m + 1))) =
      ((m + k : ℕ) + α + β + 2) * (((1 : ℚ) / (m.factorial * k.factorial)) •
        ((ascPochhammer R m).smeval (β + 1 + k + 1) *
          (ascPochhammer R k).smeval (α + 1 + m + 1))) := by
  have h₁ := congrArg (algebraMap ℚ R) (Nat.one_div_factorial_mul_factorial_succ_left (K := ℚ) m k)
  have h₂ := congrArg (algebraMap ℚ R) (Nat.one_div_factorial_mul_factorial_succ_right (K := ℚ) m k)
  simp only [map_mul, map_add, map_natCast, map_one] at h₁ h₂
  rw [ascPochhammer_succ_smeval_left, ascPochhammer_succ_smeval_left,
    show α + ((m + 1 : ℕ) : R) + 1 = α + m + 1 + 1 by push_cast; ring,
    show β + ((k + 1 : ℕ) : R) + 1 = β + k + 1 + 1 by push_cast; ring,
    show β + 1 + (k : R) + 1 = β + k + 1 + 1 by ring,
    show α + 1 + (m : R) + 1 = α + m + 1 + 1 by ring]
  simp only [Algebra.smul_def, Nat.cast_add]
  linear_combination
    -((β + k + 1) * (ascPochhammer R m).smeval (β + k + 1 + 1) *
        (ascPochhammer R k).smeval (α + m + 1 + 1)) * h₁ -
      (α + m + 1) * (ascPochhammer R m).smeval (β + k + 1 + 1) *
        (ascPochhammer R k).smeval (α + m + 1 + 1) * h₂

/-- The derivative of a Jacobi polynomial is a Jacobi polynomial with both parameters raised by
one: `(Pₙ₊₁^{(α,β)})' = ((n + α + β + 2) / 2) Pₙ^{(α+1,β+1)}` (DLMF 18.9.15). -/
theorem derivative_jacobi (α β : R) (n : ℕ) :
    derivative (jacobi α β (n + 1)) =
      ((1 : ℚ) / 2) • (C (n + α + β + 2) * jacobi (α + 1) (β + 1) n) := by
  rw [jacobi_def, jacobi_def, derivative_smul,
    derivative_sum_smul_X_sub_one_pow_mul_X_add_one_pow, mul_smul_comm, smul_smul,
    ← smul_eq_C_mul, show (1 : ℚ) / 2 ^ (n + 1) = 1 / 2 * (1 / 2 ^ n) by ring]
  congr 1
  rw [smul_sum]
  refine sum_congr rfl fun k hk => ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.lt_succ_iff.1 (mem_range.1 hk))
  rw [smul_smul, Nat.add_sub_add_right, Nat.add_sub_cancel,
    show m + k + 1 - k = m + 1 by omega, ← derivative_jacobi_coeff]

/-! ### Contiguous relations -/

/-- Over a `ℚ`-algebra, two polynomials with equal derivatives and equal values at `1` agree. -/
private lemma eq_of_derivative_eq_of_eval_one_eq {p q : R[X]}
    (hd : derivative p = derivative q) (he : p.eval 1 = q.eval 1) : p = q := by
  have : HasUniqueDiv R := .of_module_rat R
  have h := eq_C_of_derivative_eq_zero (p := p - q) (by rw [derivative_sub, hd, sub_self])
  have h0 : (p - q).coeff 0 = 0 := by
    have h1 := congrArg (eval 1) h
    rwa [eval_sub, he, sub_self, eval_C, eq_comm] at h1
  rwa [h0, C_0, sub_eq_zero] at h

/-- Raising the factorial in the reciprocal `1 / n!`, transported to a `ℚ`-algebra. -/
private lemma algebraMap_one_div_factorial (n : ℕ) :
    algebraMap ℚ R (1 / (n.factorial : ℚ)) =
      algebraMap ℚ R (1 / ((n + 1).factorial : ℚ)) * (n + 1) := by
  have h := congrArg (algebraMap ℚ R) (Nat.one_div_factorial_mul_factorial_succ_left (K := ℚ) n 0)
  simpa only [Nat.factorial_zero, Nat.cast_one, mul_one, map_mul, map_add, map_natCast,
    map_one] using h

/-- The two sides of `Polynomial.jacobi_succ_contiguous_right` have the same value at `1`. -/
private lemma eval_one_jacobi_succ_contiguous_right (α β : R) (n : ℕ) :
    eval 1 (C (2 * n + α + β + 3) * jacobi α β (n + 1)) =
      eval 1 (C (n + α + β + 2) * jacobi α (β + 1) (n + 1) +
        C (n + 1 + α) * jacobi α (β + 1) n) := by
  simp only [eval_mul, eval_add, eval_C, eval_one_jacobi, Algebra.smul_def,
    ascPochhammer_succ_smeval_right, algebraMap_one_div_factorial n]
  ring

/-- A contiguous relation of the Jacobi polynomials, raising `β` (DLMF 18.9.5):
`(2n + α + β + 3) Pₙ₊₁^{(α,β)} = (n + α + β + 2) Pₙ₊₁^{(α,β+1)} + (n + 1 + α) Pₙ^{(α,β+1)}`. -/
theorem jacobi_succ_contiguous_right (α β : R) (n : ℕ) :
    C (2 * n + α + β + 3) * jacobi α β (n + 1) =
      C (n + α + β + 2) * jacobi α (β + 1) (n + 1) + C (n + 1 + α) * jacobi α (β + 1) n := by
  induction n generalizing α β with
  | zero =>
    refine eq_of_derivative_eq_of_eval_one_eq ?_ (eval_one_jacobi_succ_contiguous_right α β 0)
    simp only [derivative_mul, derivative_add, derivative_C, derivative_one, derivative_jacobi,
      jacobi_zero, Algebra.smul_def]
    simp only [map_add, map_mul, map_ofNat, map_one, map_zero, Nat.cast_zero]
    ring
  | succ n ih =>
    refine eq_of_derivative_eq_of_eval_one_eq ?_
      (eval_one_jacobi_succ_contiguous_right α β (n + 1))
    have ih' := ih (α + 1) (β + 1)
    simp only [derivative_mul, derivative_add, derivative_C, derivative_jacobi,
      Algebra.smul_def]
    simp only [map_add, map_mul, map_natCast, map_ofNat, map_one, Nat.cast_add,
      Nat.cast_one] at ih' ⊢
    linear_combination (algebraMap ℚ R[X] (1 / 2) * (C α + C β + n + 3)) * ih'

/-- The two sides of `Polynomial.jacobi_succ_contiguous_left` have the same value at `1`. -/
private lemma eval_one_jacobi_succ_contiguous_left (α β : R) (n : ℕ) :
    eval 1 (C (2 * n + α + β + 3) * jacobi α β (n + 1)) =
      eval 1 (C (n + α + β + 2) * jacobi (α + 1) β (n + 1) -
        C (n + 1 + β) * jacobi (α + 1) β n) := by
  simp only [eval_mul, eval_sub, eval_C, eval_one_jacobi, Algebra.smul_def,
    algebraMap_one_div_factorial n]
  rw [ascPochhammer_succ_smeval_left n (α + 1), ascPochhammer_succ_smeval_right n (α + 1 + 1)]
  ring

/-- A contiguous relation of the Jacobi polynomials, raising `α` (the reflection of
DLMF 18.9.5):
`(2n + α + β + 3) Pₙ₊₁^{(α,β)} = (n + α + β + 2) Pₙ₊₁^{(α+1,β)} - (n + 1 + β) Pₙ^{(α+1,β)}`. -/
theorem jacobi_succ_contiguous_left (α β : R) (n : ℕ) :
    C (2 * n + α + β + 3) * jacobi α β (n + 1) =
      C (n + α + β + 2) * jacobi (α + 1) β (n + 1) - C (n + 1 + β) * jacobi (α + 1) β n := by
  induction n generalizing α β with
  | zero =>
    refine eq_of_derivative_eq_of_eval_one_eq ?_ (eval_one_jacobi_succ_contiguous_left α β 0)
    simp only [derivative_mul, derivative_sub, derivative_C, derivative_one, derivative_jacobi,
      jacobi_zero, Algebra.smul_def]
    simp only [map_add, map_mul, map_ofNat, map_one, map_zero, Nat.cast_zero]
    ring
  | succ n ih =>
    refine eq_of_derivative_eq_of_eval_one_eq ?_
      (eval_one_jacobi_succ_contiguous_left α β (n + 1))
    have ih' := ih (α + 1) (β + 1)
    simp only [derivative_mul, derivative_sub, derivative_C, derivative_jacobi,
      Algebra.smul_def]
    simp only [map_add, map_mul, map_natCast, map_ofNat, map_one, Nat.cast_add,
      Nat.cast_one] at ih' ⊢
    linear_combination (algebraMap ℚ R[X] (1 / 2) * (C α + C β + n + 3)) * ih'

/-- The two sides of `Polynomial.X_add_one_mul_jacobi_add_one` have the same value at `1`. -/
private lemma eval_one_X_add_one_mul_jacobi_add_one (α β : R) (n : ℕ) :
    eval 1 (C (2 * n + α + β + 2) * (X + 1) * jacobi α (β + 1) n) =
      eval 1 (C (2 * ((n : R) + 1)) * jacobi α β (n + 1) + C (2 * (n + β + 1)) * jacobi α β n) := by
  simp only [eval_mul, eval_add, eval_C, eval_X, eval_one, eval_one_jacobi, Algebra.smul_def,
    ascPochhammer_succ_smeval_right, algebraMap_one_div_factorial n]
  ring

/-- A contiguous relation of the Jacobi polynomials, lowering `β` (DLMF 18.9.6):
`(2n + α + β + 2) (X + 1) Pₙ^{(α,β+1)} = 2 (n + 1) Pₙ₊₁^{(α,β)} + 2 (n + β + 1) Pₙ^{(α,β)}`. -/
theorem X_add_one_mul_jacobi_add_one (α β : R) (n : ℕ) :
    C (2 * n + α + β + 2) * (X + 1) * jacobi α (β + 1) n =
      C (2 * ((n : R) + 1)) * jacobi α β (n + 1) + C (2 * (n + β + 1)) * jacobi α β n := by
  have hH : (2 : R[X]) * algebraMap ℚ R[X] (1 / 2) = 1 := by
    rw [one_div]
    exact TauCeti.ofNat_mul_algebraMap_inv two_ne_zero
  induction n generalizing α β with
  | zero =>
    refine eq_of_derivative_eq_of_eval_one_eq ?_ (eval_one_X_add_one_mul_jacobi_add_one α β 0)
    simp only [derivative_mul, derivative_add, derivative_C, derivative_X, derivative_one,
      derivative_jacobi, jacobi_zero, Algebra.smul_def]
    simp only [map_add, map_mul, map_ofNat, map_one, map_zero, Nat.cast_zero]
    linear_combination (-(C α + C β + 2)) * hH
  | succ n ih =>
    refine eq_of_derivative_eq_of_eval_one_eq ?_
      (eval_one_X_add_one_mul_jacobi_add_one α β (n + 1))
    have ih' := ih (α + 1) (β + 1)
    have hA := jacobi_succ_contiguous_left α (β + 1) n
    simp only [derivative_mul, derivative_add, derivative_C, derivative_X, derivative_one,
      derivative_jacobi, Algebra.smul_def]
    simp only [map_add, map_mul, map_natCast, map_ofNat, map_one, Nat.cast_add,
      Nat.cast_one] at ih' hA ⊢
    linear_combination hA + (algebraMap ℚ R[X] (1 / 2) * (C α + C β + n + 3)) * ih' +
      (-(C α + C β + n + 3) * jacobi (α + 1) (β + 1) (n + 1) +
        ((n : R[X]) + C β + 2) * jacobi (α + 1) (β + 1) n) * hH

/-! ### The three-term recurrence -/

/-- The three-term recurrence of the Jacobi polynomials (DLMF 18.9.1, 18.9.2):
`2 (n + 2) (n + α + β + 2) (2n + α + β + 2) Pₙ₊₂^{(α,β)} =
(2n + α + β + 3) ((2n + α + β + 4) (2n + α + β + 2) X + α² - β²) Pₙ₊₁^{(α,β)} -
2 (n + 1 + α) (n + 1 + β) (2n + α + β + 4) Pₙ^{(α,β)}`. -/
theorem jacobi_succ_succ (α β : R) (n : ℕ) :
    C (2 * (n + 2) * (n + α + β + 2) * (2 * n + α + β + 2)) * jacobi α β (n + 2) =
      C (2 * n + α + β + 3) *
          (C ((2 * n + α + β + 4) * (2 * n + α + β + 2)) * X + C (α ^ 2 - β ^ 2)) *
          jacobi α β (n + 1) -
        C (2 * (n + 1 + α) * (n + 1 + β) * (2 * n + α + β + 4)) * jacobi α β n := by
  have hA := jacobi_succ_contiguous_right α β n
  have hB₁ := X_add_one_mul_jacobi_add_one α β (n + 1)
  have hB₀ := X_add_one_mul_jacobi_add_one α β n
  simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_ofNat, map_one, Nat.cast_add,
    Nat.cast_one] at hA hB₁ hB₀ ⊢
  linear_combination
    (-(X + 1) * (2 * n + C α + C β + 4) * (2 * n + C α + C β + 2)) * hA -
      (n + C α + C β + 2) * (2 * n + C α + C β + 2) * hB₁ -
      (n + 1 + C α) * (2 * n + C α + C β + 4) * hB₀

end Polynomial
