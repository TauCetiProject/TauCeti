/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Reciprocals of products of factorials in a field

In a field of characteristic zero, the reciprocal `1 / (a! b!)` of a product of two factorials
can be rewritten with either factorial raised by one, at the cost of the matching factor:
`1 / (a! b!) = 1 / ((a + 1)! b!) * (a + 1)`, and symmetrically in `b`. These are the
factorial-ratio steps of coefficient comparisons for hypergeometric polynomial families, whose
coefficients carry such reciprocals.

## Main results

* `Nat.one_div_factorial_mul_factorial_succ_left`: `1 / (a! b!) = 1 / ((a + 1)! b!) * (a + 1)`.
* `Nat.one_div_factorial_mul_factorial_succ_right`: `1 / (a! b!) = 1 / (a! (b + 1)!) * (b + 1)`.
-/

public section

namespace Nat

variable {K : Type*} [Field K] [CharZero K]

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

end Nat
