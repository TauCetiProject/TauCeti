/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Order.Units

/-!
# Equality and squares of signs

The group `ℤˣ = {±1}` has exponent two, so two signs are equal exactly when their product is `1`.
This is the form in which an equality of two products of Hilbert symbols is checked, by expanding
both sides into one common product of symbols. For the same reason, the image of a sign in any
ring squares to `1`.

## Main results

* `Int.units_eq_iff_mul_eq_one`: `u = v ↔ u * v = 1` for signs `u v : ℤˣ`.
* `Int.units_eq_iff_eq_of_mul_eq_mul`: if `u * v = u' * v'` then `u = v ↔ u' = v'`.
* `Int.cast_units_sq`: the square of a sign, cast to any ring, is `1`.
* `Int.exists_apply_eq_and_apply_eq`: two `ℤ`-valued functions that take all four pairs of signs at
  four points take every pair of signs.
-/

public section

namespace Int

/-- Two signs are equal exactly when their product is `1`. -/
theorem units_eq_iff_mul_eq_one (u v : ℤˣ) : u = v ↔ u * v = 1 := by
  rw [mul_eq_one_iff_eq_inv, Int.units_inv_eq_self]

/-- Two pairs of signs with the same product agree in the same cases: if `u * v = u' * v'` then
`u = v` exactly when `u' = v'`. -/
theorem units_eq_iff_eq_of_mul_eq_mul {u v u' v' : ℤˣ} (h : u * v = u' * v') :
    u = v ↔ u' = v' := by
  rw [Int.units_eq_iff_mul_eq_one u v, Int.units_eq_iff_mul_eq_one u' v', h]

/-- The square of a sign `u : ℤˣ`, cast to any ring, is `1`. -/
@[simp]
theorem cast_units_sq {R : Type*} [Ring R] (u : ℤˣ) : ((u : ℤ) : R) ^ 2 = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

/-- Two `ℤ`-valued functions that take the four sign pairs at four points take every pair of
signs. -/
theorem exists_apply_eq_and_apply_eq {α : Type*} {f g : α → ℤ} {a₁ a₂ a₃ a₄ : α}
    (h₁ : f a₁ = 1 ∧ g a₁ = 1) (h₂ : f a₂ = 1 ∧ g a₂ = -1)
    (h₃ : f a₃ = -1 ∧ g a₃ = 1) (h₄ : f a₄ = -1 ∧ g a₄ = -1) (ε ε' : ℤˣ) :
    ∃ a, f a = ε ∧ g a = ε' := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl
  · exact ⟨a₁, by simpa using h₁.1, by simpa using h₁.2⟩
  · exact ⟨a₂, by simpa using h₂.1, by simpa using h₂.2⟩
  · exact ⟨a₃, by simpa using h₃.1, by simpa using h₃.2⟩
  · exact ⟨a₄, by simpa using h₄.1, by simpa using h₄.2⟩

end Int
