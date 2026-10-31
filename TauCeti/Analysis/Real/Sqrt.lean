/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Rescaling by a square root

For `0 ≤ a`, multiplying by `(√a)⁻¹` and squaring divides the square by `a`:
`((√a)⁻¹ * x) ^ 2 = x ^ 2 / a`. This is the change of variables `x ↦ (√a)⁻¹ * x` that turns the
kernel `1 + x ^ 2 / a` into `1 + y ^ 2`. A square factor comes out of a square root as its
absolute value: `√(x ^ 2 * y) = |x| * √y`. Powers of `(√a)⁻¹` absorb integer powers of `a`:
`(√a)⁻¹ ^ n * a ^ p = (√a)⁻¹ ^ (n - 2p)` for `a > 0` and `2p ≤ n`, the normalisation that leaves
a factor `(√N)⁻¹ ^ (n - 2p)` in a central limit theorem.

## Main results

* `Real.inv_sqrt_mul_sq`: `((√a)⁻¹ * x) ^ 2 = x ^ 2 / a` for `0 ≤ a`.
* `Real.sqrt_sq_mul`: `√(x ^ 2 * y) = |x| * √y`.
* `Real.inv_sqrt_pow_mul_pow`: `(√a)⁻¹ ^ n * a ^ p = (√a)⁻¹ ^ (n - 2p)` for `0 < a` and `2p ≤ n`.
-/

public section

namespace Real

/-- Multiplying by `(√a)⁻¹` and squaring divides the square by `a`. -/
@[simp]
theorem inv_sqrt_mul_sq {a : ℝ} (ha : 0 ≤ a) (x : ℝ) : ((√a)⁻¹ * x) ^ 2 = x ^ 2 / a := by
  rw [mul_pow, inv_pow, Real.sq_sqrt ha, inv_mul_eq_div]

/-- A square factor comes out of a square root as its absolute value. -/
theorem sqrt_sq_mul (x y : ℝ) : √(x ^ 2 * y) = |x| * √y := by
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- Powers of `(√a)⁻¹` absorb powers of `a`: `(√a)⁻¹ ^ n * a ^ p = (√a)⁻¹ ^ (n - 2p)` for
`0 < a` and `2p ≤ n`. -/
theorem inv_sqrt_pow_mul_pow {a : ℝ} (ha : 0 < a) {n p : ℕ} (h : 2 * p ≤ n) :
    (√a)⁻¹ ^ n * a ^ p = (√a)⁻¹ ^ (n - 2 * p) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have ha' : a ^ p = √a ^ (2 * p) := by rw [pow_mul, Real.sq_sqrt ha.le]
  rw [Nat.add_sub_cancel_left, ha', pow_add, mul_right_comm, ← mul_pow,
    inv_mul_cancel₀ (Real.sqrt_pos.2 ha).ne', one_pow, one_mul]

end Real
