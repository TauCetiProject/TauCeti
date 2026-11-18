/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.Additive
public import Mathlib.Basic.Real.Basic

/-!
# Examples of additive and strongly additive arithmetic functions

* The zero function, and the real casts of `ω` and `Ω`, are additive; zero and the real cast of `ω`
  are strongly additive.
* `Ω` is not strongly additive, since `Ω 4 = 2` while `Ω 2 = 1`.
* The Dirichlet convolution unit is not additive, since it takes the value `1` at `1`.
* Over `ℕ∞`, the function equal to `⊤` at every positive input satisfies the coprime-product law
  but is not normalized, so the coprime law alone does not imply additivity.
* The distinct-prime and prime-power representations at `12 = 2 ^ 2 * 3`.
-/

public section

open ArithmeticFunction
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

-- Zero and the real casts of `ω` and `Ω` are additive.
example : IsAdditive (0 : ArithmeticFunction ℝ) := isAdditive_zero

example : IsAdditive (ω : ArithmeticFunction ℝ) :=
  isStronglyAdditive_cardDistinctFactors.natCast.toIsAdditive

example : IsAdditive (Ω : ArithmeticFunction ℝ) := isAdditive_cardFactors.natCast

-- Zero and the real cast of `ω` are strongly additive.
example : IsStronglyAdditive (0 : ArithmeticFunction ℝ) := isStronglyAdditive_zero

example : IsStronglyAdditive (ω : ArithmeticFunction ℝ) :=
  isStronglyAdditive_cardDistinctFactors.natCast

-- `Ω` is not strongly additive: `Ω 4 = 2` but `Ω 2 = 1`.
example : ¬ IsStronglyAdditive Ω := by
  intro h
  have h4 := h.map_prime_pow Nat.prime_two (k := 2) two_ne_zero
  rw [cardFactors_apply_prime_pow Nat.prime_two, cardFactors_apply_prime Nat.prime_two] at h4
  omega

-- The convolution unit takes the value `1` at `1`, so it is not additive.
example : (1 : ArithmeticFunction ℝ) 1 = 1 ∧ ¬ IsAdditive (1 : ArithmeticFunction ℝ) := by
  refine ⟨one_one, fun h => ?_⟩
  have := h.map_one
  rw [one_one] at this
  exact one_ne_zero this

-- The `ℕ∞`-valued function equal to `⊤` at every positive input satisfies the coprime-product
-- law, since `⊤ = ⊤ + ⊤`, but is not normalized at one.
example (f : ArithmeticFunction ℕ∞) (hf : ∀ n, n ≠ 0 → f n = ⊤) :
    IsAdditiveOnCoprime f ∧ ¬ IsAdditive f := by
  refine ⟨⟨fun hm hn _ => ?_⟩, fun h => ?_⟩
  · simp [hf _ hm, hf _ hn, hf _ (mul_ne_zero hm hn)]
  · simpa [hf 1 one_ne_zero] using h.map_one

-- Such a function exists.
example : ∃ f : ArithmeticFunction ℕ∞, ∀ n, n ≠ 0 → f n = ⊤ :=
  ⟨⟨fun n => if n = 0 then 0 else ⊤, rfl⟩, fun _ hn => by simp [hn]⟩

-- The distinct-prime representation of `ω` at `12`.
example : ω 12 = ∑ p ∈ Nat.primeFactors 12, ω p :=
  isStronglyAdditive_cardDistinctFactors.apply_eq_sum_primeFactors 12

-- The prime-power representation of `Ω` at `12`.
example : Ω 12 = ∑ p ∈ Nat.primeFactors 12, Ω (p ^ Nat.factorization 12 p) :=
  isAdditive_cardFactors.apply_eq_sum_primeFactors 12
