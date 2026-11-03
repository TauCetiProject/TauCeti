/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# Derivatives, recurrence, and parity of the probabilists' Hermite polynomials

Mathlib's `Mathlib/RingTheory/Polynomial/Hermite/Basic.lean` defines `Polynomial.hermite` by the
one-step recursion `hermite (n + 1) = X * hermite n - derivative (hermite n)` and develops its
coefficient API, but it records nothing about the *derivative* of a Hermite polynomial in closed
form. This file fills that gap with the classical lowering identity

  `derivative (hermite (n + 1)) = (n + 1) • hermite n`,

its `n`-indexed restatement `derivative (hermite n) = n • hermite (n - 1)`, the iterated form
`derivative^[k] (hermite n) = n.descFactorial k • hermite (n - k)`, and the three-term recurrence

  `hermite (n + 2) = X * hermite (n + 1) - (n + 1) • hermite n`

obtained by eliminating the derivative from Mathlib's defining recursion. The lowering identity
is the algebraic content behind the weighted-pairing integration-by-parts recursion
`∫ p · H_{n+1} · w = ∫ p' · Hₙ · w` and behind the Hermite generating function, and the three-term
recurrence is the standard form `Hₙ₊₁ = X·Hₙ - n·Hₙ₋₁` that orthogonal-polynomial arguments
consume. The parity theorem records `Hₙ(-x) = (-1)ⁿ Hₙ(x)` in any ring.

## References

* [Mathlib PR #42724](https://github.com/leanprover-community/mathlib4/pull/42724)
  (Kim Morrison), an adaptation of this file and of `GeneratingFunction.lean` for Mathlib;
  `Polynomial.derivative_hermite_succ` is not `@[simp]` here following the simp-normal-form
  analysis made there.
-/

public section

namespace TauCeti

open Polynomial

/-- **Lowering (derivative) identity for the Hermite polynomials.** Differentiating the
`(n + 1)`-st probabilists' Hermite polynomial lowers the index:
`H'_{n+1} = (n + 1) · Hₙ`.

This is not a `simp` lemma because its left-hand side is already reduced by the `n`-indexed
form `Polynomial.derivative_hermite`. -/
theorem _root_.Polynomial.derivative_hermite_succ (n : ℕ) :
    derivative (hermite (n + 1)) = (n + 1) • hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermite_succ (n + 1), derivative_sub, derivative_mul, ih, hermite_succ n]
    simp only [derivative_smul, derivative_X]
    ring

/-- The Hermite derivative identity restated at index `n`: `H'ₙ = n · Hₙ₋₁`. For `n = 0` both sides
vanish (`H₀ = 1`). -/
@[simp]
theorem _root_.Polynomial.derivative_hermite (n : ℕ) :
    derivative (hermite n) = n • hermite (n - 1) := by
  cases n with
  | zero => simp
  | succ n => simpa using derivative_hermite_succ n

/-- Iterating the lowering identity: the `k`-th derivative of `Hₙ` is the descending factorial
`n (n-1) ⋯ (n-k+1)` times `H_{n-k}`. For `k > n` the descending factorial is `0` and both sides
vanish. -/
@[simp]
theorem _root_.Polynomial.iterate_derivative_hermite (n k : ℕ) :
    derivative^[k] (hermite n) = n.descFactorial k • hermite (n - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, derivative_smul, derivative_hermite, smul_smul,
      Nat.descFactorial_succ, Nat.sub_sub, mul_comm]

/-- **Three-term recurrence for the Hermite polynomials.** Eliminating the derivative from Mathlib's
defining recursion `hermite_succ` gives the classical relation `H_{n+2} = X·H_{n+1} - (n+1)·Hₙ`,
i.e. `H_{m+1} = X·H_m - m·H_{m-1}`. -/
theorem _root_.Polynomial.hermite_add_two (n : ℕ) :
    hermite (n + 2) = X * hermite (n + 1) - (n + 1) • hermite n := by
  rw [hermite_succ (n + 1), derivative_hermite_succ]

/-! ## Parity -/

/-- **Parity of the Hermite polynomials.** `Hₙ(-x) = (-1)ⁿ Hₙ(x)` in any ring. -/
@[simp]
theorem _root_.Polynomial.hermite_aeval_neg {R : Type*} [Ring R] (n : ℕ) (x : R) :
    aeval (-x) (hermite n) = (-1) ^ n * aeval x (hermite n) := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  -- only monomials with `n + k` even survive, and on those `(-1) ^ k = (-1) ^ n`
  rcases Nat.even_or_odd (n + k) with h | h
  · rw [neg_pow, mul_smul_comm, neg_one_pow_congr (Nat.even_add.mp h).symm]
  · simp [coeff_hermite_of_odd_add h]

end TauCeti
