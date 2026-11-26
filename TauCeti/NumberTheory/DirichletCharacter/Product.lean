/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.DirichletCharacter.Conductor

/-!
# Products of Dirichlet characters of different levels

`DirichletCharacter.mul` forms the pointwise product after raising both characters to the least
common multiple of their levels. Raising the two levels before forming the product raises that
product, without changing its conductor. For coprime conductors the conductor of the product is
their product, so the product of primitive characters of coprime levels is primitive.

The latter fact is used in quadratic twisting; see Davenport, *Multiplicative Number Theory*,
3rd ed., Chapter 9, and `New.isPrimitive_quadTwist` in `grh-lean`, `Lib/Analytic/QuadraticTwist`
(revision `72fead1`).
-/

public section

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R]

/-- Forming the product at raised levels agrees with raising the original common-level product. -/
theorem changeLevel_mul {m n m' n' : ℕ} (χ : DirichletCharacter R m)
    (ψ : DirichletCharacter R n) (hm : m ∣ m') (hn : n ∣ n') :
    (χ.mul ψ).changeLevel (Nat.lcm_dvd (hm.trans (Nat.dvd_lcm_left m' n'))
      (hn.trans (Nat.dvd_lcm_right m' n'))) = (χ.changeLevel hm).mul (ψ.changeLevel hn) := by
  simp only [DirichletCharacter.mul, MonoidHom.map_mul, ← changeLevel_trans]

/-- The common-level product takes the product of the two values at `−1`, the unit testing
parity. -/
@[simp] theorem mul_apply_neg_one {m n : ℕ} (χ : DirichletCharacter R m)
    (ψ : DirichletCharacter R n) : (χ.mul ψ) (-1) = χ (-1) * ψ (-1) := by
  simp only [DirichletCharacter.mul, MulChar.mul_apply, changeLevel_apply_neg_one]

/-- The conductor of the common-level product is the product of the conductors when the latter
are coprime. The ambient levels themselves need not be coprime. -/
theorem conductor_mul_eq_mul_of_coprime {m n : ℕ}
    (χ : DirichletCharacter R m) (ψ : DirichletCharacter R n)
    (h : χ.conductor.Coprime ψ.conductor) : (χ.mul ψ).conductor = χ.conductor * ψ.conductor := by
  obtain rfl | hm := eq_zero_or_neZero m
  · simp [conductor_eq_zero_iff_level_eq_zero.mpr]
  obtain rfl | hn := eq_zero_or_neZero n
  · simp [conductor_eq_zero_iff_level_eq_zero.mpr]
  have : NeZero (m.lcm n) := ⟨Nat.lcm_ne_zero hm.ne hn.ne⟩
  have hc : (χ.changeLevel (Nat.dvd_lcm_left m n)).conductor.Coprime
      (ψ.changeLevel (Nat.dvd_lcm_right m n)).conductor := by
    simpa only [conductor_changeLevel] using h
  simpa only [DirichletCharacter.mul, conductor_changeLevel] using conductor_mul_of_coprime hc

/-- Primitive characters of coprime levels have primitive common-level product. -/
theorem IsPrimitive.mul_of_coprime {m n : ℕ}
    {χ : DirichletCharacter R m} {ψ : DirichletCharacter R n}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (h : m.Coprime n) : (χ.mul ψ).IsPrimitive := by
  rw [isPrimitive_def] at hχ hψ ⊢
  have hc : χ.conductor.Coprime ψ.conductor := by simpa only [hχ, hψ] using h
  rw [conductor_mul_eq_mul_of_coprime χ ψ hc, hχ, hψ, h.lcm_eq_mul]

end DirichletCharacter
