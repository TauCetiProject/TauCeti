/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Intertwining matrices and multiplicative order

A rectangular matrix `V` intertwining two square matrices (`A * V = V * B`) intertwines every
natural power of them (`Matrix.pow_mul_eq_mul_pow`). Over an integral domain, intertwining
`A * P = P * B` by a square matrix `P` of nonzero determinant preserves multiplicative order
(`Matrix.orderOf_eq_of_mul_eq_mul`), because `P` is regular
(`Matrix.isRegular_of_isLeftRegular_det`).

## Main results

* `Matrix.pow_mul_eq_mul_pow`: powers preserve intertwiners.
* `Matrix.orderOf_eq_of_mul_eq_mul`: matrices intertwined by a matrix of nonzero determinant over an
  integral domain have the same multiplicative order.
-/

public section

namespace Matrix

/-- **Powers preserve intertwiners.** If a rectangular matrix `V` intertwines the square matrices
`A` and `B`, that is `A * V = V * B`, then it intertwines every natural power of them. -/
theorem pow_mul_eq_mul_pow {n m R : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [Semiring R] {A : Matrix n n R} {B : Matrix m m R} {V : Matrix n m R} (h : A * V = V * B)
    (k : ℕ) : A ^ k * V = V * B ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

/-- **Intertwining by a matrix of nonzero determinant preserves multiplicative order.** If `P`
has nonzero determinant over an integral domain and `A * P = P * B`, then
`orderOf A = orderOf B`. -/
theorem orderOf_eq_of_mul_eq_mul {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] [IsDomain R] {A B P : Matrix n n R} (hP : P.det ≠ 0) (h : A * P = P * B) :
    orderOf A = orderOf B := by
  have hreg : IsRegular P :=
    Matrix.isRegular_of_isLeftRegular_det (isRegular_iff_ne_zero.mpr hP).left
  refine orderOf_eq_orderOf_iff.mpr fun m ↦ ?_
  have hm := pow_mul_eq_mul_pow h m
  refine ⟨fun hA ↦ hreg.left ?_, fun hB ↦ hreg.right ?_⟩
  · dsimp only; rw [← hm, hA, Matrix.one_mul, Matrix.mul_one]
  · dsimp only; rw [hm, hB, Matrix.mul_one, Matrix.one_mul]

end Matrix
