/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.CompletelyAdditive
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Simproc.Factors

/-!
# Examples of completely additive functions and powers of additive functions

* The real cast of `Ω`, the arithmetic logarithm, and the exponent of a fixed `p` in the
  factorization are completely additive.
* The real cast of `ω` is additive but not completely additive, since `ω 4 = 1` while
  `ω 2 + ω 2 = 2`.
* `powOfAdditive 1 f` and `powOfAdditive k 0` are both the cast of `ζ`.
* `2 ^ ω` is multiplicative but not multiplicative on all pairs, while `2 ^ Ω` is.
-/

public section

open ArithmeticFunction
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega ArithmeticFunction.zeta

-- The real cast of `Ω` is completely additive.
example : IsCompletelyAdditive (Ω : ArithmeticFunction ℝ) :=
  isCompletelyAdditive_cardFactors.natCast

-- The arithmetic logarithm is completely additive.
example : IsCompletelyAdditive log where
  map_one := by simp [log_apply]
  map_mul hm hn := by
    simp only [log_apply, Nat.cast_mul]
    exact Real.log_mul (Nat.cast_ne_zero.2 hm) (Nat.cast_ne_zero.2 hn)

-- The exponent of `p` in the factorization is completely additive.
example (p : ℕ) :
    IsCompletelyAdditive (⟨fun n => n.factorization p, by simp⟩ : ArithmeticFunction ℕ) where
  map_one := by simp
  map_mul hm hn := by simp [Nat.factorization_mul hm hn]

-- The real cast of `ω` is additive but not completely additive: `ω 4 = 1` but `ω 2 = 1`.
example :
    IsAdditive (ω : ArithmeticFunction ℝ) ∧ ¬ IsCompletelyAdditive (ω : ArithmeticFunction ℝ) := by
  refine ⟨{ map_one := by simp, map_mul := fun _ _ h => by simp [cardDistinctFactors_mul h] },
    fun h => ?_⟩
  have h4 := h.map_mul (m := 2) (n := 2) two_ne_zero two_ne_zero
  norm_num [cardDistinctFactors_eq_length_dedup_primeFactorsList, Nat.primeFactorsList_ofNat] at h4

-- Powers of one, and powers along the zero function, give the cast of `ζ`.
example {R : Type*} [Semiring R] (f : ArithmeticFunction ℕ) :
    powOfAdditive (1 : R) f = (ζ : ArithmeticFunction R) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn <;> simp [*]

example {R : Type*} [Semiring R] (k : R) :
    powOfAdditive k 0 = (ζ : ArithmeticFunction R) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn <;> simp [*]

-- `2 ^ ω` is multiplicative: `2 ^ ω 12 = 4 = 2 ^ ω 4 * 2 ^ ω 3`.
example : (powOfAdditive (2 : ℕ) ω).IsMultiplicative :=
  isMultiplicative_powOfAdditive_cardDistinctFactors 2

example : powOfAdditive (2 : ℕ) ω 12 = 4 ∧
    powOfAdditive (2 : ℕ) ω 12 = powOfAdditive 2 ω 4 * powOfAdditive 2 ω 3 := by
  simp [cardDistinctFactors_eq_length_dedup_primeFactorsList, Nat.primeFactorsList_ofNat]

-- `2 ^ ω` is not multiplicative on all pairs: `2 ^ ω 4 = 2` but `2 ^ ω 2 * 2 ^ ω 2 = 4`.
example : powOfAdditive (2 : ℕ) ω 4 = 2 ∧ powOfAdditive (2 : ℕ) ω 2 * powOfAdditive 2 ω 2 = 4 := by
  simp [cardDistinctFactors_eq_length_dedup_primeFactorsList, Nat.primeFactorsList_ofNat]

-- `2 ^ Ω` is multiplicative on all pairs, for instance `2 ^ Ω 4 = 4 = 2 ^ Ω 2 * 2 ^ Ω 2`.
example (m n : ℕ) :
    powOfAdditive (2 : ℕ) Ω (m * n) = powOfAdditive 2 Ω m * powOfAdditive 2 Ω n :=
  isCompletelyAdditive_cardFactors.powOfAdditive_mul 2 m n

example : powOfAdditive (2 : ℕ) Ω 4 = 4 ∧ powOfAdditive (2 : ℕ) Ω 2 * powOfAdditive 2 Ω 2 = 4 := by
  simp [cardFactors_apply, Nat.primeFactorsList_ofNat]
