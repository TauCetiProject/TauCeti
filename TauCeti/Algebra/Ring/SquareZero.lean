/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.Module.NatInt

/-!
# Powers of `x + y` for a square-zero element `x`

In any semiring, if `x * x = 0` and `x` commutes with `y`, then only the terms of degree at most
one in `x` survive in the binomial expansion:
`(x + y) ^ (n + 1) = y ^ (n + 1) + (n + 1) • (x * y ^ n)`. In particular an element `x` with
`x ^ 2 = 0` satisfies `(1 + x) ^ n = 1 + n • x`. Hence, in a ring, `1 + x` has order dividing `n`
only when `n • x = 0`, so `x = 0` whenever `n` is invertible. For an endomorphism `1 + N` with
`N ∘ N = 0`, this says that a unipotent element of order invertible in the base field is the
identity.

## Main results

* `Commute.add_pow_succ_of_mul_self_eq_zero`: if `x` commutes with `y` and `x * x = 0`, then
  `(x + y) ^ (n + 1) = y ^ (n + 1) + (n + 1) • (x * y ^ n)`.
* `TauCeti.one_add_pow_of_sq_eq_zero`: `(1 + x) ^ n = 1 + n • x` when `x ^ 2 = 0`.
* `TauCeti.eq_zero_of_one_add_pow_eq_one_of_sq_eq_zero`: if `x ^ 2 = 0`, `(1 + x) ^ n = 1` and
  `n` is a unit, then `x = 0`.
-/

public section

variable {A : Type*}

namespace Commute

variable [Semiring A] {x y : A}

/-- If `x` commutes with `y` and `x * x = 0`, then only the terms of degree at most one in `x`
survive in the binomial expansion of `(x + y) ^ (n + 1)`. -/
theorem add_pow_succ_of_mul_self_eq_zero (h : Commute x y) (hx : x * x = 0) (n : ℕ) :
    (x + y) ^ (n + 1) = y ^ (n + 1) + (n + 1) • (x * y ^ n) := by
  induction n with
  | zero => simp [add_comm]
  | succ n ih =>
    have hxy : y * (x * y ^ n) = x * y ^ (n + 1) := by
      rw [← mul_assoc, ← h.eq, mul_assoc, pow_succ']
    have hxx : x * (x * y ^ n) = 0 := by rw [← mul_assoc, hx, zero_mul]
    rw [pow_succ', ih]
    simp only [add_mul, mul_add, mul_smul_comm, hxx, hxy, zero_add, ← pow_succ']
    rw [succ_nsmul _ (n + 1)]
    ac_rfl

end Commute

namespace TauCeti

/-- If `x ^ 2 = 0`, then `(1 + x) ^ n = 1 + n • x`. -/
theorem one_add_pow_of_sq_eq_zero [Semiring A] {x : A} (hx : x ^ 2 = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + n • x := by
  cases n with
  | zero => simp
  | succ n =>
    rw [add_comm, (Commute.one_right x).add_pow_succ_of_mul_self_eq_zero (by rw [← sq, hx])]
    simp

/-- If `x ^ 2 = 0` and `(1 + x) ^ n = 1` for some `n` invertible in `A`, then `x = 0`. -/
theorem eq_zero_of_one_add_pow_eq_one_of_sq_eq_zero [Ring A] {x : A} (hx : x ^ 2 = 0) {n : ℕ}
    (hn : IsUnit (n : A)) (h : (1 + x) ^ n = 1) : x = 0 := by
  rw [one_add_pow_of_sq_eq_zero hx, add_eq_left, nsmul_eq_mul] at h
  exact hn.mul_right_eq_zero.1 h

end TauCeti
