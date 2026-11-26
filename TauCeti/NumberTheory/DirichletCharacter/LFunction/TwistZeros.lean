/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.GCD
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.Product

/-!
# Zeros of twists after lowering the level

Replacing the character being twisted by its primitive character preserves the zeros of the
resulting L-function off the imaginary axis and away from a principal pole. Thus one can test
for zeros of a quadratic twist at the smaller level, where the twisted character is primitive
if the quadratic character is primitive and its level is coprime to the original conductor.

This is the level reduction used in `New.zero_density_quadTwist` in `grh-lean`,
`Lib/Analytic/QuadraticTwist` (revision `72fead1`).
-/

public section

namespace DirichletCharacter

/-- Off the imaginary axis, replacing `χ` by its primitive character before twisting by `ψ`
preserves the zeros of the continued L-function. At `s = 1` this compares values only when the
product is nonprincipal. -/
theorem LFunction_mul_primitiveCharacter_eq_zero_iff {m n : ℕ} [NeZero m] [NeZero n]
    (χ : DirichletCharacter ℂ m) (ψ : DirichletCharacter ℂ n) {s : ℂ} (hs : s.re ≠ 0)
    (h : χ.primitiveCharacter.mul ψ ≠ 1 ∨ s ≠ 1) :
    (χ.mul ψ).LFunction s = 0 ↔ (χ.primitiveCharacter.mul ψ).LFunction s = 0 := by
  have hd : χ.conductor.lcm n ∣ m.lcm n :=
    Nat.lcm_dvd (χ.conductor_dvd_level.trans (Nat.dvd_lcm_left m n)) (Nat.dvd_lcm_right m n)
  have he : (χ.primitiveCharacter.mul ψ).changeLevel hd = χ.mul ψ := by
    simpa only [changeLevel_primitiveCharacter, changeLevel_self] using
      changeLevel_mul χ.primitiveCharacter ψ χ.conductor_dvd_level (dvd_refl n)
  rw [← he, LFunction_changeLevel hd _ h, mul_eq_zero]
  simp only [prod_one_sub_mul_prime_cpow_ne_zero (N := m.lcm n) (χ.primitiveCharacter.mul ψ) hs,
    or_false]

end DirichletCharacter
