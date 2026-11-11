/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic

/-!
# Periodicity under integer combinations of two periods

A function periodic under `c₁` and `c₂` is periodic under every integer combination
`m c₁ + n c₂` (`Function.Periodic.int_mul_add_int_mul`). For the periods `1` and `i` of a
function on `ℂ` these are the vectors of the lattice `ℤ + ℤ i`; for the periods `τ` and `1` of a
function on `ℂ` they are the vectors of the lattice `ℤ τ + ℤ`.

More generally, a function twisted by a nonzero factor `a` under translation by `c`,
`f (x + c) = a * f x`, is twisted by `a ^ k` under translation by every integer multiple `k c`
(`Function.apply_add_int_mul_eq_zpow_mul`).
-/

public section

namespace Function

variable {α β : Type*} [NonAssocRing α] {f : α → β} {c₁ c₂ : α}

/-- A function periodic under `c₁` and `c₂` is periodic under every integer combination
`m c₁ + n c₂`. -/
theorem Periodic.int_mul_add_int_mul (h₁ : Periodic f c₁) (h₂ : Periodic f c₂) (m n : ℤ) :
    Periodic f (m * c₁ + n * c₂) :=
  (h₁.int_mul m).add_period (h₂.int_mul n)

/-- A function twisted by a nonzero factor `a` under translation by `c` is twisted by `a ^ k` under
translation by `k c`, for every integer `k`. -/
theorem apply_add_int_mul_eq_zpow_mul {G₀ : Type*} [CommGroupWithZero G₀] {f : α → G₀} {c : α}
    {a : G₀} (ha : a ≠ 0) (h : ∀ x, f (x + c) = a * f x) (k : ℤ) (x : α) :
    f (x + k * c) = a ^ k * f x := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [Int.cast_add, Int.cast_one, add_one_mul, ← add_assoc, h, ih, zpow_add_one₀ ha,
      mul_comm (a ^ (k : ℤ)) a, mul_assoc]
  | pred k ih =>
    have h' := h (x + ((-k - 1 : ℤ) : α) * c)
    rw [add_assoc, ← add_one_mul, Int.cast_sub, Int.cast_one, sub_add_cancel, ih] at h'
    rw [zpow_sub_one₀ ha, mul_right_comm, h', Int.cast_sub, Int.cast_one, mul_comm a,
      mul_inv_cancel_right₀ ha]

end Function
