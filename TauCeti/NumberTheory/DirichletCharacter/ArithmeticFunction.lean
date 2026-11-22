/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.ArithmeticFunction.CompletelyMultiplicative
public import TauCeti.NumberTheory.DirichletCharacter.Basic

/-!
# Arithmetic functions of products of Dirichlet characters

The product of characters of different levels is taken at their least common multiple. On
natural numbers it is the pointwise product, including at primes dividing either level.
These comparisons allow products of Dirichlet L-functions to be handled on their actual
coefficient functions. A character's arithmetic function is completely multiplicative.
-/

public section

namespace DirichletCharacter

open ArithmeticFunction

section CommMonoidWithZero

variable {R : Type*} [CommMonoidWithZero R] {M N : ℕ}

/-- At a power of a nonzero natural number, a character's arithmetic function is the
corresponding power of its character value. -/
@[simp] theorem toArithmeticFunction_apply_pow (χ : DirichletCharacter R M)
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) : toArithmeticFunction (χ ·) (n ^ k) = χ n ^ k := by
  rw [← χ.apply_eq_toArithmeticFunction_apply (pow_ne_zero _ hn), Nat.cast_pow, map_pow]

/-- Passing from characters to arithmetic functions sends the product at the least common
multiple of their levels to pointwise multiplication. -/
theorem toArithmeticFunction_mul (χ : DirichletCharacter R M) (ψ : DirichletCharacter R N) :
    toArithmeticFunction (χ.mul ψ ·) =
      (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)) := by
  ext n
  rw [ArithmeticFunction.pmul_apply]
  by_cases hn : n = 0
  · simp [hn]
  · rw [← (χ.mul ψ).apply_eq_toArithmeticFunction_apply hn,
      ← χ.apply_eq_toArithmeticFunction_apply hn,
      ← ψ.apply_eq_toArithmeticFunction_apply hn, mul_natCast]

/-- The arithmetic function of a Dirichlet character is completely multiplicative. -/
theorem isCompletelyMultiplicative_toArithmeticFunction (χ : DirichletCharacter R N) :
    (toArithmeticFunction (χ ·)).IsCompletelyMultiplicative := by
  refine .of_ne_zero (isMultiplicative_toArithmeticFunction χ).map_one fun hm hn ↦ ?_
  simp only [← χ.apply_eq_toArithmeticFunction_apply (mul_ne_zero hm hn),
    ← χ.apply_eq_toArithmeticFunction_apply hm, ← χ.apply_eq_toArithmeticFunction_apply hn,
    Nat.cast_mul, map_mul]

end CommMonoidWithZero

/-- On `Re s > 1`, a character's arithmetic function has an absolutely convergent
Dirichlet series with sum equal to its continued L-function. -/
theorem LSeriesHasSum_toArithmeticFunction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (toArithmeticFunction (χ ·)) s (χ.LFunction s) := by
  rw [χ.LFunction_eq_LSeries hs]
  exact (LSeriesHasSum_congr s _ χ.apply_eq_toArithmeticFunction_apply).mp
    (ZMod.LSeriesSummable_of_one_lt_re χ hs).LSeriesHasSum

end DirichletCharacter
