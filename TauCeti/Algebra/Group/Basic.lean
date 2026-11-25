/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Basic

/-!
# Basic identities in groups

## Main results

* `TauCeti.inv_mul_eq_inv_mul_iff_mul_inv_eq_mul_inv`: in a group, `b⁻¹ * a = d⁻¹ * c` if and only
  if `a * c⁻¹ = b * d⁻¹`. In a commutative group, Mathlib's
  `inv_mul_eq_inv_mul_iff_mul_eq_mul` gives the equivalent `a * d = c * b`.
* `TauCeti.apply_iterate_eq_pow_mul`: a monoid-valued function that scales by `a` along a self-map
  `φ` scales by `a ^ n` along `φ^[n]`.
* `TauCeti.ite_inv_of_mul_self` and `TauCeti.ite_neg_of_add_self`: inverting `if p then t else 1`
  leaves it unchanged when `t * t = 1`.
* `TauCeti.ite_mul_ite_of_mul_self` and `TauCeti.ite_add_ite_of_add_self`: multiplying two
  `{1, t}` indicators produces `if Xor p q then t else 1`.
* `TauCeti.ite_mul_ite_mul_ite_of_mul_self` and `TauCeti.ite_add_ite_add_ite_of_add_self`:
  multiplying three `{1, t}` indicators produces `if Xor p (Xor q r) then t else 1`.
-/

public section

namespace TauCeti

section

variable {G : Type*} [Group G] {a b c d : G}

/-- Two left quotients `b⁻¹ * a` and `d⁻¹ * c` are equal exactly when the right quotients
`a * c⁻¹` and `b * d⁻¹` are. -/
@[to_additive /-- Two left differences `-b + a` and `-d + c` are equal exactly when the right
differences `a + -c` and `b + -d` are. -/]
theorem inv_mul_eq_inv_mul_iff_mul_inv_eq_mul_inv : b⁻¹ * a = d⁻¹ * c ↔ a * c⁻¹ = b * d⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul, mul_assoc]

end

/-- A function that scales by `a` along `φ` scales by `a ^ n` along `φ^[n]`. -/
@[to_additive /-- A function that shifts by `a` along `φ` shifts by `n • a` along `φ^[n]`. -/]
theorem apply_iterate_eq_pow_mul {S M : Type*} [Monoid M] {φ : S → S} {a : M} {h : S → M}
    (hh : ∀ s, h (φ s) = a * h s) (n : ℕ) (s : S) : h (φ^[n] s) = a ^ n * h s :=
  (Function.Semiconj.iterate_right (gb := (a * ·)) hh n s).trans (mul_left_iterate_apply a _)

/-- When `t * t = 1` in a group, inverting `if p then t else 1` returns `if p then t else 1`. -/
@[to_additive (attr := simp) /-- When `t + t = 0` in an additive group, negating
`if p then t else 0` returns `if p then t else 0`. -/]
theorem ite_inv_of_mul_self {G : Type*} [Group G] {t : G} (ht : t * t = 1) (p : Prop)
    [Decidable p] : (if p then t else 1)⁻¹ = if p then t else 1 := by
  split_ifs
  · exact inv_eq_of_mul_eq_one_right ht
  · exact inv_one

/-- When `t * t = 1`, the product of `if p then t else 1` and `if q then t else 1` is
`if Xor p q then t else 1`. -/
@[to_additive /-- When `t + t = 0`, the sum of `if p then t else 0` and `if q then t else 0` is
`if Xor p q then t else 0`. -/]
theorem ite_mul_ite_of_mul_self {M : Type*} [MulOneClass M] {t : M} (ht : t * t = 1) (p q : Prop)
    [Decidable p] [Decidable q] :
    (if p then t else 1) * (if q then t else 1) = if Xor p q then t else 1 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, Xor, ht]

/-- When `t * t = 1`, the product of three `{1, t}` indicators is `t` when an odd number of the
conditions hold (`Xor p (Xor q r)`), and `1` otherwise. -/
@[to_additive /-- When `t + t = 0`, the sum of three `{0, t}` indicators is `t` when an odd number
of the conditions hold (`Xor p (Xor q r)`), and `0` otherwise. -/]
theorem ite_mul_ite_mul_ite_of_mul_self {M : Type*} [MulOneClass M] {t : M} (ht : t * t = 1)
    (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] :
    (if p then t else 1) * (if q then t else 1) * (if r then t else 1) =
      if Xor p (Xor q r) then t else 1 := by
  rw [ite_mul_ite_of_mul_self ht, ite_mul_ite_of_mul_self ht]
  congr 1
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> simp [hp, hq, hr, Xor]

end TauCeti
