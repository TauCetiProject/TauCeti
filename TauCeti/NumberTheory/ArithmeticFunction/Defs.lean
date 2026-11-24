/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Casts of arithmetic functions

Mathlib's `ArithmeticFunction.natCoe_one` and `ArithmeticFunction.natCoe_mul` say that the cast
`ArithmeticFunction ℕ → ArithmeticFunction R` into a semiring preserves the Dirichlet unit and
Dirichlet convolution. This file adds the consequence for convolution powers.

## Main results

* `ArithmeticFunction.natCoe_pow`: the cast `ArithmeticFunction ℕ → ArithmeticFunction R`
  commutes with convolution powers.
-/

public section

namespace ArithmeticFunction

/-- The cast of an `ℕ`-valued arithmetic function commutes with Dirichlet-convolution powers. -/
@[simp, norm_cast]
theorem natCoe_pow {R : Type*} [Semiring R] (f : ArithmeticFunction ℕ) (k : ℕ) :
    (↑(f ^ k) : ArithmeticFunction R) = (f : ArithmeticFunction R) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, natCoe_one]
  | succ k ih => rw [pow_succ, pow_succ, natCoe_mul, ih]

end ArithmeticFunction
