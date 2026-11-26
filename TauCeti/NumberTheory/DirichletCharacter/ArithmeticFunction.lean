/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.ArithmeticFunction.CompletelyMultiplicative
public import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.ArithmeticFunction.Misc

/-!
# Arithmetic functions of Dirichlet characters

The product of characters of different levels is taken at their least common multiple. On
natural numbers it is the pointwise product, including at primes dividing either level.
These comparisons allow products of Dirichlet L-functions to be handled on their actual
coefficient functions. A character's arithmetic function is completely multiplicative.
The finite harmonic form of the twisted von Mangoldt convolution expresses the sum of
`χ(n) log(n) / n` in terms of sums of `χ(n) / n`.
-/

public section

namespace DirichletCharacter

open ArithmeticFunction Finset
open scoped LSeries.notation

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

/-- The finite harmonic form of the twisted von Mangoldt convolution identity. -/
theorem sum_mul_log_div_eq_sum_mul_vonMangoldt_div_mul_sum_div {N : ℕ}
    (χ : DirichletCharacter ℂ N) (m : ℕ) :
    ∑ n ∈ Ioc 0 m, χ n * (Real.log n : ℂ) / (n : ℂ) =
      ∑ d ∈ Ioc 0 m, (χ d * (Λ d : ℂ) / (d : ℂ)) *
        ∑ n ∈ Ioc 0 (m / d), χ n / (n : ℂ) := by
  have h := ArithmeticFunction.sum_Ioc_mul_smul_eq_sum_sum
    (toArithmeticFunction (↗χ * ↗Λ)) (toArithmeticFunction (↗χ))
    (fun n : ℕ ↦ (n : ℂ)⁻¹) m
  rw [← LSeries.convolution, χ.convolution_twist_vonMangoldt] at h
  refine Eq.trans ?_ (h.trans ?_)
  · refine sum_congr rfl fun n _ ↦ ?_
    simp [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm]
  · refine sum_congr rfl fun d hd ↦ ?_
    have hd₀ : d ≠ 0 := (mem_Ioc.mp hd).1.ne'
    simp only [smul_eq_mul, toArithmeticFunction, ArithmeticFunction.coe_mk,
      hd₀, ite_false, Pi.mul_apply, Finset.mul_sum]
    refine sum_congr rfl fun n hn ↦ ?_
    have hn₀ : n ≠ 0 := (mem_Ioc.mp hn).1.ne'
    simp [hn₀, Nat.cast_mul, div_eq_mul_inv]
    ring

end DirichletCharacter
