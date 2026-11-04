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

end Matrix.GeneralLinearGroup
