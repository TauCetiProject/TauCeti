/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Module

/-!
# Row vectors in a right module times matrices

For a right `A`-module `M`, written as a module over `Aᵐᵒᵖ`, a matrix `F : Matrix m n A` acts on
row vectors `φ : m → M` by `(φ ⬝ F) y = ∑ x, φ x * F x y` (`Matrix.rightVecMul`). For `M = A` this
is `Matrix.vecMul` (`Matrix.rightVecMul_eq_vecMul`), and acting by two matrices in turn is acting
by their product (`Matrix.rightVecMul_rightVecMul`). For square matrices it is the action of
`Matrix.Module.matrixModule`, of matrices over `Aᵐᵒᵖ` on column vectors, applied to the
transpose (`Matrix.rightVecMul_eq_smul`); the rectangular form is needed for maps between free
modules on different bases, such as morphisms of type `D` structures.
-/

public section

namespace Matrix

variable {R A M : Type*} [Semiring A] [AddCommMonoid M] [Module Aᵐᵒᵖ M] {m n o : Type*}

/-- The product `φ ⬝ F` of a row vector `φ` with entries in a right `A`-module and a matrix `F`
over `A`: `(φ ⬝ F) y = ∑ x, φ x * F x y`, the right action being written
`MulOpposite.op (F x y) • φ x`. For `M = A` this is `Matrix.vecMul`. -/
def rightVecMul [Fintype m] (φ : m → M) (F : Matrix m n A) : n → M :=
  fun y => ∑ x, MulOpposite.op (F x y) • φ x

variable [Fintype m]

theorem rightVecMul_apply (φ : m → M) (F : Matrix m n A) (y : n) :
    rightVecMul φ F y = ∑ x, MulOpposite.op (F x y) • φ x :=
  (rfl)

@[simp]
theorem rightVecMul_zero (φ : m → M) : rightVecMul φ (0 : Matrix m n A) = 0 := by
  ext y
  simp [rightVecMul_apply]

@[simp]
theorem zero_rightVecMul (F : Matrix m n A) : rightVecMul (0 : m → M) F = 0 := by
  ext y
  simp [rightVecMul_apply]

theorem rightVecMul_add (φ : m → M) (F G : Matrix m n A) :
    rightVecMul φ (F + G) = rightVecMul φ F + rightVecMul φ G := by
  ext y
  simp [rightVecMul_apply, add_smul, Finset.sum_add_distrib]

theorem add_rightVecMul (φ ψ : m → M) (F : Matrix m n A) :
    rightVecMul (φ + ψ) F = rightVecMul φ F + rightVecMul ψ F := by
  ext y
  simp [rightVecMul_apply, smul_add, Finset.sum_add_distrib]

theorem smul_rightVecMul [CommSemiring R] [Module R M] [SMulCommClass R Aᵐᵒᵖ M] (r : R)
    (φ : m → M) (F : Matrix m n A) : rightVecMul (r • φ) F = r • rightVecMul φ F := by
  ext y
  simp only [rightVecMul_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun x _ => (smul_comm r _ _).symm

/-- Acting by two matrices in turn is acting by their product: `(φ ⬝ F) ⬝ G = φ ⬝ (F * G)`. -/
@[simp]
theorem rightVecMul_rightVecMul [Fintype n] (φ : m → M) (F : Matrix m n A) (G : Matrix n o A) :
    rightVecMul (rightVecMul φ F) G = rightVecMul φ (F * G) := by
  ext z
  simp only [rightVecMul_apply, Matrix.mul_apply, Finset.op_sum, Finset.smul_sum, Finset.sum_smul,
    ← mul_smul, ← MulOpposite.op_mul]
  exact Finset.sum_comm

/-- A diagonal matrix acts on a row vector entrywise. -/
theorem rightVecMul_diagonal [DecidableEq m] (φ : m → M) (a : m → A) (y : m) :
    rightVecMul φ (diagonal a) y = MulOpposite.op (a y) • φ y := by
  simp [rightVecMul_apply, diagonal_apply, apply_ite MulOpposite.op, ite_smul]

/-- On the regular right module, `Matrix.rightVecMul` is `Matrix.vecMul`. -/
theorem rightVecMul_eq_vecMul (φ : m → A) (F : Matrix m n A) : rightVecMul φ F = φ ᵥ* F := by
  ext y
  simp [rightVecMul_apply, vecMul, dotProduct]

section Ring

variable {A M : Type*} [Ring A] [AddCommGroup M] [Module Aᵐᵒᵖ M] {m : Type*} [Fintype m]
  [DecidableEq m]

open Matrix.Module in
/-- For a square matrix `F`, `φ ⬝ F` is the action of `Matrix.Module.matrixModule` of the
transpose of `F`, read as a matrix over `Aᵐᵒᵖ`, on the column vector `φ`. -/
theorem rightVecMul_eq_smul (φ : m → M) (F : Matrix m m A) :
    rightVecMul φ F = (F.transpose.map MulOpposite.op) • φ :=
  (rfl)

end Ring

end Matrix
