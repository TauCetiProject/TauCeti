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
# Reciprocals of products of factorials in a field

In a field of characteristic zero, the reciprocal `1 / (a! b!)` of a product of two factorials
can be rewritten with either factorial raised by one, at the cost of the matching factor:
`1 / (a! b!) = 1 / ((a + 1)! b!) * (a + 1)`, and symmetrically in `b`. These are the
factorial-ratio steps of coefficient comparisons for hypergeometric polynomial families, whose
coefficients carry such reciprocals.

The single-factorial step `1 / n! = 1 / (n + 1)! * (n + 1)` holds in every division semiring of
characteristic zero. For a semifield `K` of characteristic zero it is also stated after transport
along `algebraMap K A` to a `K`-algebra `A`, which need not be a field: this is the form in which
the reciprocals occur in polynomial families over a `ℚ`-algebra.

## Main results

* `Nat.one_div_factorial_mul_factorial_succ_left`: `1 / (a! b!) = 1 / ((a + 1)! b!) * (a + 1)`.
* `Nat.one_div_factorial_mul_factorial_succ_right`: `1 / (a! b!) = 1 / (a! (b + 1)!) * (b + 1)`.
* `Nat.one_div_factorial_succ`: `1 / n! = 1 / (n + 1)! * (n + 1)`.
* `Nat.algebraMap_one_div_factorial_succ`: the same identity in a `K`-algebra, between the images
  of the two reciprocals under `algebraMap K A`.
-/

public section

namespace Nat

section Field

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

end Field

/-- Raising the factorial in the reciprocal of a factorial: `1 / n! = 1 / (n + 1)! * (n + 1)`.
It holds in every division semiring of characteristic zero; commutativity is not used.
Characteristic zero is needed: in `ZMod 2` at `n = 1` the left side is `1` and the right side is
`1 / 0 * 0 = 0`. -/
theorem one_div_factorial_succ {K : Type*} [DivisionSemiring K] [CharZero K] (n : ℕ) :
    (1 : K) / n.factorial = 1 / (n + 1).factorial * (n + 1) := by
  rw [Nat.factorial_succ, Nat.cast_mul, one_div, one_div, mul_inv_rev, Nat.cast_succ,
    inv_mul_cancel_right₀ (Nat.cast_add_one_ne_zero n)]

/-- Raising the factorial in the reciprocal `1 / n!`, transported to a `K`-algebra `A`:
`algebraMap K A (1 / n!) = algebraMap K A (1 / (n + 1)!) * (n + 1)`. The algebra `A` need not be a
field. -/
theorem algebraMap_one_div_factorial_succ {K A : Type*} [Semifield K] [CharZero K] [Semiring A]
    [Algebra K A] (n : ℕ) :
    algebraMap K A (1 / n.factorial) = algebraMap K A (1 / (n + 1).factorial) * (n + 1) := by
  rw [one_div_factorial_succ n, map_mul, map_add, map_natCast, map_one]

end Nat
