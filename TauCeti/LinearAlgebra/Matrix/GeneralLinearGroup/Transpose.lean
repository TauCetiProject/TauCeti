/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Transposition on the general linear group

Mathlib's transpose equivalence identifies a general linear group with its opposite group.
This file records that applying the equivalence twice recovers the original invertible matrix, and
that transposition preserves the positive-determinant subgroup `Matrix.GLPos`.

It also records how an invertible matrix `g` acts by congruence `X ↦ g X gᵀ` on square matrices:
congruence by `g⁻¹` undoes it, so it is injective, and it intertwines conjugation by `g`, in that
`(g N g⁻¹) (g C gᵀ) (g N g⁻¹)ᵀ = g (N C Nᵀ) gᵀ`.

## Main results

* `Matrix.GeneralLinearGroup.inv_congruence_congruence`: congruence by `g⁻¹` undoes congruence
  by `g`.
* `Matrix.GeneralLinearGroup.congruence_injective`: congruence by `g` is injective.
* `Matrix.GeneralLinearGroup.conj_congruence_congruence`: congruence by a conjugate `g N g⁻¹` of
  a congruate `g C gᵀ` is the congruate of `N C Nᵀ`.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Transposing an invertible matrix twice is the identity. -/
@[simp] theorem transposeMulEquiv_transposeMulEquiv (g : GL n R) :
    (transposeMulEquiv n (transposeMulEquiv n g).unop).unop = g := by
  have h := (transposeMulEquiv (R := R) n).apply_symm_apply (MulOpposite.op g)
  rw [transposeMulEquiv_symm_apply_op] at h
  exact congrArg MulOpposite.unop h

/-- Transposition preserves `Matrix.GLPos`. -/
theorem transposeMulEquiv_mem_glpos [LinearOrder R] [IsStrictOrderedRing R]
    {g : GL n R} (hg : g ∈ GLPos n R) :
    (transposeMulEquiv n g).unop ∈ GLPos n R := by
  rw [mem_glpos, val_det_apply] at hg ⊢
  rwa [coe_unop_transposeMulEquiv, Matrix.det_transpose]

/-- The transpose of `g⁻¹` is a right inverse of the transpose of `g`. -/
theorem coe_transpose_mul_coe_inv_transpose (g : GL n R) :
    (g : Matrix n n R)ᵀ * ((g⁻¹ : GL n R) : Matrix n n R)ᵀ = 1 := by
  rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]

/-- **Congruence by `g⁻¹` undoes congruence by `g`:** `g⁻¹ (g X gᵀ) (g⁻¹)ᵀ = X`. -/
theorem inv_congruence_congruence (g : GL n R) (X : Matrix n n R) :
    ((g⁻¹ : GL n R) : Matrix n n R) * ((g : Matrix n n R) * X * (g : Matrix n n R)ᵀ) *
        ((g⁻¹ : GL n R) : Matrix n n R)ᵀ = X := by
  simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, coe_transpose_mul_coe_inv_transpose,
    Matrix.mul_one]

/-- Congruence `X ↦ g X gᵀ` by an invertible matrix `g` is injective. -/
theorem congruence_injective (g : GL n R) :
    Function.Injective fun X : Matrix n n R => (g : Matrix n n R) * X * (g : Matrix n n R)ᵀ :=
  Function.LeftInverse.injective (g := fun Y => ((g⁻¹ : GL n R) : Matrix n n R) * Y *
    ((g⁻¹ : GL n R) : Matrix n n R)ᵀ) (inv_congruence_congruence g)

/-- **Congruence intertwines conjugation.** Congruence by the conjugate `g N g⁻¹` of the congruate
`g C gᵀ` is the congruate of `N C Nᵀ`: `(g N g⁻¹) (g C gᵀ) (g N g⁻¹)ᵀ = g (N C Nᵀ) gᵀ`. -/
theorem conj_congruence_congruence (g N : GL n R) (C : Matrix n n R) :
    ((g * N * g⁻¹ : GL n R) : Matrix n n R) * ((g : Matrix n n R) * C * (g : Matrix n n R)ᵀ) *
        ((g * N * g⁻¹ : GL n R) : Matrix n n R)ᵀ =
      (g : Matrix n n R) * ((N : Matrix n n R) * C * (N : Matrix n n R)ᵀ) *
        (g : Matrix n n R)ᵀ := by
  simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc, Units.inv_mul_cancel_left]
  rw [← Matrix.mul_assoc (g : Matrix n n R)ᵀ, coe_transpose_mul_coe_inv_transpose,
    Matrix.one_mul]

end Matrix.GeneralLinearGroup
