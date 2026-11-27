/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# `1 + a * b` is a unit exactly when `1 + b * a` is

In a ring, possibly noncommutative, the two products `a * b` and `b * a` are generally unrelated,
but `1 + a * b` and `1 + b * a` are invertible together. This is the elementwise shadow of the
fact that `a * b` and `b * a` have the same spectrum away from `0`, and it is the mechanism behind
the left-right symmetry of the Jacobson radical.

Mathlib records the spectral statement as `spectrum.unit_mem_mul_comm`. The elementwise form is
that statement for the base ring `ℤ`, read at the unit `1`, and that is how it is obtained here.

The file also records that, in a ring without zero divisors, a unit `u` other than `±1` is not
its own inverse in the form `u - u⁻¹ ≠ 0`, as used for quantum integers at `δ = u + u⁻¹`.
It finally records that a pair of units `r + s = 1` gives the pair `r⁻¹ + (-(s r⁻¹)) = 1`, the
step reducing the Steinberg relation for the tame symbol from negative to positive order.
In a semiring, if `q` is a two-sided inverse of `p` and `n₁ q n₂ = 0`, then
`(p + n₁) q (p + n₂) = p + n₁ + n₂`: this splits an invertible matrix over a unitization of a
product into its two factors.

## Main results

* `TauCeti.isUnit_one_sub_mul_comm`: `IsUnit (1 - a * b) ↔ IsUnit (1 - b * a)`.
* `TauCeti.isUnit_one_add_mul_comm`: `IsUnit (1 + a * b) ↔ IsUnit (1 + b * a)`.
* `Units.val_sub_val_inv_ne_zero`: in a ring without zero divisors, a unit `u ≠ ±1` satisfies
  `u - u⁻¹ ≠ 0`.
* `Units.one_add_sq_eq_mul_add_inv`: for a unit `q`, `1 + q ^ 2 = q * (q + q⁻¹)`.
* `Units.mul_sub_val_inv_mul_one_sub`: for a unit `q`,
  `q * (q * η - q⁻¹ * (1 - η)) = (1 + q ^ 2) * η - 1`.
* `Units.val_inv_add_val_neg_mul_inv_eq_one`: if `r + s = 1` for units, then
  `r⁻¹ + (-(s r⁻¹)) = 1`.
* `TauCeti.add_mul_mul_add_of_mul_eq_one`: if `p q = q p = 1` and `n₁ q n₂ = 0`, then
  `(p + n₁) q (p + n₂) = p + n₁ + n₂`.
-/

public section

namespace TauCeti

/-- If `q` is a two-sided inverse of `p` and `n₁ q n₂ = 0`, then
`(p + n₁) q (p + n₂) = p + n₁ + n₂`. -/
theorem add_mul_mul_add_of_mul_eq_one {α : Type*} [Semiring α] {p q n₁ n₂ : α}
    (hpq : p * q = 1) (hqp : q * p = 1) (hn : n₁ * q * n₂ = 0) :
    (p + n₁) * q * (p + n₂) = p + n₁ + n₂ := by
  rw [add_mul, hpq, add_mul, one_mul, mul_add, hn, mul_assoc, hqp, mul_one, add_zero]
  abel

variable {R : Type*} [Ring R]

/-- `1 - a * b` is a unit exactly when `1 - b * a` is.

This is `spectrum.unit_mem_mul_comm` over the base ring `ℤ`, at the unit `1`. -/
theorem isUnit_one_sub_mul_comm {a b : R} : IsUnit (1 - a * b) ↔ IsUnit (1 - b * a) := by
  have h := spectrum.unit_mem_mul_comm (R := ℤ) (a := a) (b := b) (r := 1)
  simpa only [spectrum.mem_iff, Units.val_one, map_one, not_iff_not] using h

/-- `1 + a * b` is a unit exactly when `1 + b * a` is. -/
theorem isUnit_one_add_mul_comm {a b : R} : IsUnit (1 + a * b) ↔ IsUnit (1 + b * a) := by
  simpa only [neg_mul, mul_neg, sub_neg_eq_add] using isUnit_one_sub_mul_comm (a := -a) (b := b)

end TauCeti

namespace Units

variable {R : Type*} [Ring R]

/-- For a unit `q` in a ring, `1 + q ^ 2 = q * (q + q⁻¹)`. -/
theorem one_add_sq_eq_mul_add_inv (q : Rˣ) :
    1 + (q : R) ^ 2 = q * ((q : R) + ↑q⁻¹) := by
  rw [mul_add, ← sq, Units.mul_inv, add_comm]

/-- Converting a projection parameter `η` to the scaled Markov parameter `q * z`:
`q * (q * η - q⁻¹ * (1 - η)) = (1 + q ^ 2) * η - 1`. -/
theorem mul_sub_val_inv_mul_one_sub (q : Rˣ) (η : R) :
    (q : R) * ((q : R) * η - ↑q⁻¹ * (1 - η)) = (1 + (q : R) ^ 2) * η - 1 := by
  rw [mul_sub, ← mul_assoc, ← sq, ← mul_assoc, Units.mul_inv, one_mul, add_mul, one_mul]
  abel

/-- If `r + s = 1` for units `r` and `s`, then `r⁻¹ + (-(s r⁻¹)) = 1`. This trades a pair adding
up to one for another such pair whose first entry is `r⁻¹`, as in the Steinberg relation. -/
theorem val_inv_add_val_neg_mul_inv_eq_one {r s : Rˣ} (h : (r : R) + s = 1) :
    ((r⁻¹ : Rˣ) : R) + ((-(s * r⁻¹) : Rˣ) : R) = 1 := by
  rw [Units.val_neg, Units.val_mul, ← sub_eq_add_neg, ← one_sub_mul, ← eq_sub_of_add_eq h,
    Units.mul_inv]

variable [NoZeroDivisors R]

/-- In a ring without zero divisors, a unit `u ≠ ±1` satisfies `u - u⁻¹ ≠ 0`. -/
theorem val_sub_val_inv_ne_zero {u : Rˣ} (hu₁ : u ≠ 1) (hu₂ : u ≠ -1) :
    (u : R) - ↑u⁻¹ ≠ 0 := fun h ↦
  ((inv_eq_self_iff u).1 (Units.ext (sub_eq_zero.1 h).symm)).elim hu₁ hu₂

end Units
