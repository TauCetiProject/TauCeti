/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Reciprocals of products of factorials in a semifield

In a semifield of characteristic zero, the reciprocal `1 / (a! b!)` of a product of two factorials
can be rewritten with either factorial raised by one, at the cost of the matching factor:
`1 / (a! b!) = 1 / ((a + 1)! b!) * (a + 1)`, and symmetrically in `b`. These are the
factorial-ratio steps of coefficient comparisons for hypergeometric polynomial families, whose
coefficients carry such reciprocals.

The single-factorial step `1 / n! = 1 / (n + 1)! * (n + 1)`, the case `b = 0`, is stated after
transport along `algebraMap K A` to a `K`-algebra `A`, which need not be a semifield: this is the
form in which the reciprocals occur in polynomial families over a `ℚ`-algebra.

## Main results

* `Nat.one_div_factorial_mul_factorial_succ_left`: `1 / (a! b!) = 1 / ((a + 1)! b!) * (a + 1)`.
* `Nat.one_div_factorial_mul_factorial_succ_right`: `1 / (a! b!) = 1 / (a! (b + 1)!) * (b + 1)`.
* `Nat.algebraMap_one_div_factorial_eq_mul`: in a `K`-algebra,
  `algebraMap K A (1 / n!) = algebraMap K A (1 / (n + 1)!) * (n + 1)`.
-/

public section

namespace Nat

variable {K : Type*} [Semifield K] [CharZero K]

/-- Raising the left factorial in the reciprocal of a product of factorials:
`1 / (a! b!) = 1 / ((a + 1)! b!) * (a + 1)`. -/
theorem one_div_factorial_mul_factorial_succ_left (a b : ℕ) :
    (1 : K) / (a.factorial * b.factorial) = 1 / ((a + 1).factorial * b.factorial) * (a + 1) := by
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- Raising the right factorial in the reciprocal of a product of factorials:
`1 / (a! b!) = 1 / (a! (b + 1)!) * (b + 1)`. -/
theorem one_div_factorial_mul_factorial_succ_right (a b : ℕ) :
    (1 : K) / (a.factorial * b.factorial) = 1 / (a.factorial * (b + 1).factorial) * (b + 1) := by
  rw [mul_comm (a.factorial : K), mul_comm (a.factorial : K),
    one_div_factorial_mul_factorial_succ_left]

/-- Raising the factorial in the reciprocal `1 / n!`, transported to a `K`-algebra `A`:
`algebraMap K A (1 / n!) = algebraMap K A (1 / (n + 1)!) * (n + 1)`. The algebra `A` need not be a
semifield. Characteristic zero is needed: for `K = A = ZMod 2` and `n = 1` the left side is `1`
and the right side is `1 / 0 * 0 = 0`. -/
theorem algebraMap_one_div_factorial_eq_mul {A : Type*} [Semiring A] [Algebra K A] (n : ℕ) :
    algebraMap K A (1 / n.factorial) = algebraMap K A (1 / (n + 1).factorial) * (n + 1) := by
  have h := congrArg (algebraMap K A) (one_div_factorial_mul_factorial_succ_left (K := K) n 0)
  simpa only [Nat.factorial_zero, Nat.cast_one, mul_one, map_mul, map_add, map_natCast, map_one]
    using h

end Nat
