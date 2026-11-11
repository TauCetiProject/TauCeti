/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Matrix.Mul

/-!
# Matrices intertwined by a rectangular matrix

Let `E : Matrix m n R` intertwine square matrices `A` and `B`, that is `E * A = B * E`. When `E` is
square this is `SemiconjBy E A B`, and `SemiconjBy.pow_right` carries it to all powers. Here `E`
may be rectangular, as for the embedding of the root lattice of type `Aₙ` into `ℤⁿ⁺¹`.

* `Matrix.mul_pow_eq_pow_mul_of_mul_eq_mul`: `E * A ^ k = B ^ k * E`.
* `Matrix.orderOf_eq_orderOf_of_mul_eq_mul`: if moreover `E * A ^ k = E` forces `A ^ k = 1` and
  `B ^ k * E = E` forces `B ^ k = 1`, then `A` and `B` have the same order.
-/

public section

namespace Matrix

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Semiring R]
  {E : Matrix m n R} {A : Matrix n n R} {B : Matrix m m R}

/-- An intertwining `E * A = B * E` passes to powers. -/
theorem mul_pow_eq_pow_mul_of_mul_eq_mul (h : E * A = B * E) (k : ℕ) : E * A ^ k = B ^ k * E := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, Matrix.one_mul]
  | succ k ih => rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc,
      ← pow_succ]

/-- **Intertwined matrices have the same order**, as long as the intertwiner detects the powers
of each of them that are the identity. -/
theorem orderOf_eq_orderOf_of_mul_eq_mul (h : E * A = B * E)
    (hA : ∀ k : ℕ, E * A ^ k = E → A ^ k = 1) (hB : ∀ k : ℕ, B ^ k * E = E → B ^ k = 1) :
    orderOf A = orderOf B :=
  orderOf_eq_orderOf_iff.2 fun k =>
    ⟨fun hk => hB k (by rw [← mul_pow_eq_pow_mul_of_mul_eq_mul h, hk, Matrix.mul_one]),
      fun hk => hA k (by rw [mul_pow_eq_pow_mul_of_mul_eq_mul h, hk, Matrix.one_mul])⟩

end Matrix

end
