/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Cast.Basic

/-!
# Powers of `1 + x` for a square-zero element `x`

In any semiring, an element `x` with `x ^ 2 = 0` satisfies `(1 + x) ^ n = 1 + n • x`. Hence, in a
ring, `1 + x` has order dividing `n` only when `n • x = 0`, so `x = 0` whenever `n` is invertible.
For an endomorphism `1 + N` with `N ∘ N = 0`, this says that a unipotent element of order
invertible in the base field is the identity.

## Main results

* `TauCeti.one_add_pow_of_sq_eq_zero`: `(1 + x) ^ n = 1 + n • x` when `x ^ 2 = 0`.
* `TauCeti.eq_zero_of_one_add_pow_eq_one_of_sq_eq_zero`: if `x ^ 2 = 0`, `(1 + x) ^ n = 1` and
  `n` is a unit, then `x = 0`.
-/

public section

namespace TauCeti

variable {A : Type*}

/-- If `x ^ 2 = 0`, then `(1 + x) ^ n = 1 + n • x`. -/
theorem one_add_pow_of_sq_eq_zero [Semiring A] {x : A} (hx : x ^ 2 = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + n • x := by
  have hxx : x * x = 0 := by rw [← sq, hx]
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, add_mul, mul_add, mul_assoc, hxx, add_assoc]

/-- If `x ^ 2 = 0` and `(1 + x) ^ n = 1` for some `n` invertible in `A`, then `x = 0`. -/
theorem eq_zero_of_one_add_pow_eq_one_of_sq_eq_zero [Ring A] {x : A} (hx : x ^ 2 = 0) {n : ℕ}
    (hn : IsUnit (n : A)) (h : (1 + x) ^ n = 1) : x = 0 := by
  rw [one_add_pow_of_sq_eq_zero hx, add_eq_left, nsmul_eq_mul] at h
  exact hn.mul_right_eq_zero.1 h

end TauCeti
