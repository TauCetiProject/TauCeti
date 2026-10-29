/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Sign.Basic

/-!
# Basic facts about the sign

In a linearly ordered division ring, the sign of `x` is `x / |x|`. This is the division form of
Mathlib's `sign_mul_abs`, and it holds at `0` too, since both sides vanish there. Inverses keep
the sign, so the sign of a quotient is the product of the signs, as for Mathlib's `sign_mul`.

In a linearly ordered ring, prescribing the signs of finitely many elements amounts to a single
equation, the vanishing of a sum of squares, together with finitely many strict inequalities.

## Main results

* `TauCeti.sign_eq_div_abs`: `sign x = x / |x|`.
* `TauCeti.sign_inv`, `TauCeti.sign_div`: inverses keep the sign, and the sign of a quotient is
  the product of the signs.
* `TauCeti.forall_sign_eq_iff_sum_sq_eq_zero_and_pos`: prescribed signs of the entries of a finite
  family as one sum-of-squares equation and positivity conditions.
-/

public section

namespace TauCeti

/-- In a linearly ordered division ring, the sign of `x` is `x / |x|`. -/
theorem sign_eq_div_abs {α : Type*} [DivisionRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (x : α) : (SignType.sign x : α) = x / |x| := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [eq_div_iff (abs_ne_zero.2 hx), sign_mul_abs]

/-- In a linearly ordered division ring, inverting does not change the sign. -/
@[simp]
theorem sign_inv {α : Type*} [DivisionRing α] [LinearOrder α] [IsStrictOrderedRing α] (x : α) :
    SignType.sign x⁻¹ = SignType.sign x :=
  map_inv₀ signHom x

/-- In a linearly ordered division ring, the sign of a quotient is the product of the signs. -/
@[simp]
theorem sign_div {α : Type*} [DivisionRing α] [LinearOrder α] [IsStrictOrderedRing α] (x y : α) :
    SignType.sign (x / y) = SignType.sign x * SignType.sign y :=
  map_div₀ signHom x y

/-- Prescribed signs `ε` of the entries of `a` amount to a single equation, the vanishing of the sum
of the squares of the `a i` with `ε i = 0`, together with the positivity of `ε i * a i` for the
other `i`. -/
theorem forall_sign_eq_iff_sum_sq_eq_zero_and_pos {ι R : Type*} [Fintype ι] [Ring R]
    [LinearOrder R] [IsStrictOrderedRing R] (a : ι → R) (ε : ι → SignType) :
    (∀ i, SignType.sign (a i) = ε i) ↔
      ∑ i with ε i = 0, a i ^ 2 = 0 ∧ ∀ i, 0 < if ε i = 0 then 1 else (ε i : R) * a i := by
  have (b : R) (δ : SignType) :
      SignType.sign b = δ ↔ (δ = 0 → b = 0) ∧ 0 < if δ = 0 then 1 else (δ : R) * b := by
    rcases δ with _ | _ | _ <;> simp [sign_eq_zero_iff, sign_eq_neg_one_iff, sign_eq_one_iff]
  simp only [Finset.sum_sq_eq_zero_iff, Finset.mem_filter, Finset.mem_univ, true_and, this,
    forall_and]

end TauCeti
