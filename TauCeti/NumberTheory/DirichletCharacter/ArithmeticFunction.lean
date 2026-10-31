/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import TauCeti.NumberTheory.DirichletCharacter.Basic

/-!
# Arithmetic functions of products of Dirichlet characters

The product of characters of different levels is taken at their least common multiple. On
natural numbers it is the pointwise product, including at primes dividing either level.
Twisting arithmetic functions by a character preserves Dirichlet convolution. These comparisons
allow products of Dirichlet L-functions to be handled on their actual coefficient functions.
-/

public section

namespace DirichletCharacter

open ArithmeticFunction

section CommMonoidWithZero

variable {R : Type*} [CommMonoidWithZero R] {M N : ℕ}

/-- The product character at the least common multiple of the levels is the pointwise product
on natural numbers, including the nonunits. -/
@[simp] theorem mul_natCast (χ : DirichletCharacter R M) (ψ : DirichletCharacter R N) (n : ℕ) :
    χ.mul ψ n = χ n * ψ n := by
  by_cases hn : n.Coprime (Nat.lcm M N)
  · rw [DirichletCharacter.mul, MulChar.mul_apply,
      changeLevel_natCast_of_coprime _ _ hn, changeLevel_natCast_of_coprime _ _ hn]
  · have hzero : χ.mul ψ n = 0 :=
      (χ.mul ψ).map_nonunit (by rwa [ZMod.isUnit_iff_coprime])
    rw [hzero]
    have hbad : ¬ n.Coprime M ∨ ¬ n.Coprime N := by
      by_contra! h
      exact hn ((h.1.mul_right h.2).of_dvd_right (Nat.lcm_dvd_mul M N))
    rcases hbad with h | h
    · rw [χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]
    · rw [ψ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]), mul_zero]

/-- Passing from characters to arithmetic functions sends the product at the least common
multiple of their levels to pointwise multiplication. -/
theorem toArithmeticFunction_mul (χ : DirichletCharacter R M) (ψ : DirichletCharacter R N) :
    toArithmeticFunction (χ.mul ψ ·) =
      (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)) := by
  ext n
  rw [ArithmeticFunction.pmul_apply]
  by_cases hn : n = 0 <;> simp [toArithmeticFunction, hn]

end CommMonoidWithZero

variable {R : Type*} [CommSemiring R] {M : ℕ}

/-- Twisting by a Dirichlet character preserves Dirichlet convolution. -/
theorem toArithmeticFunction_pmul_mul (χ : DirichletCharacter R M)
    (f g : ArithmeticFunction R) :
    (toArithmeticFunction (χ ·)).pmul (f * g) =
      ((toArithmeticFunction (χ ·)).pmul f) * ((toArithmeticFunction (χ ·)).pmul g) := by
  ext n
  by_cases hn : n = 0
  · simp [hn]
  rw [pmul_apply, mul_apply, Finset.mul_sum, mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have hdn := (Nat.mem_divisorsAntidiagonal.mp hd).1
  have hd0 : d.1 ≠ 0 ∧ d.2 ≠ 0 := by
    exact ⟨fun h ↦ hn (by simpa [h] using hdn.symm),
      fun h ↦ hn (by simpa [h] using hdn.symm)⟩
  simp only [pmul_apply, ← χ.apply_eq_toArithmeticFunction_apply hn,
    ← χ.apply_eq_toArithmeticFunction_apply hd0.1,
    ← χ.apply_eq_toArithmeticFunction_apply hd0.2]
  rw [← hdn, Nat.cast_mul, map_mul]
  ring

end DirichletCharacter
