/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.LDL
import TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho
import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# The diagonals of the LDL decomposition

Mathlib's LDL decomposition writes a positive-definite matrix `S` as `L * D * Lᴴ` with `L` lower
triangular and `D` diagonal, but records nothing about the individual diagonal entries. This file
supplies them: the diagonal of `D` is positive, and both `LDL.lowerInv` and `LDL.lower` carry `1`
on the diagonal, so the lower factor of the decomposition is unitriangular.

## Main results

* `LDL.diagEntries_pos` — the diagonal entries of `D` are positive.
* `LDL.lowerInv_apply_diag` and `LDL.lower_apply_diag` — the lower factor of the LDL
  decomposition and its inverse are unitriangular.
-/

public section

open scoped ComplexOrder Matrix

namespace TauCeti

variable {𝕜 n : Type*} [RCLike 𝕜] [LinearOrder n] [WellFoundedLT n]
  [LocallyFiniteOrderBot n] [Fintype n] {S : Matrix n n 𝕜} (hS : S.PosDef)

/-- The diagonal entries in Mathlib's LDL decomposition of a positive-definite matrix are
positive. -/
theorem _root_.LDL.diagEntries_pos (i : n) : 0 < LDL.diagEntries hS i := by
  have hdiag : (LDL.diag hS).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact hS.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_invertible (LDL.lowerInv hS))
  simpa [LDL.diag] using hdiag.diag_pos (i := i)

/-- The lower factor in Mathlib's LDL decomposition is unitriangular: its inverse is the
Gram-Schmidt matrix, which carries `1` on the diagonal. -/
@[simp]
theorem _root_.LDL.lowerInv_apply_diag (i : n) : LDL.lowerInv hS i i = 1 := by
  let := Sᵀ.toNormedAddCommGroup hS.transpose
  let := Sᵀ.toInnerProductSpace hS.transpose.posSemidef
  rw [LDL.lowerInv]
  simpa only [Pi.basisFun_repr] using
    (Pi.basisFun 𝕜 n).repr_gramSchmidt_self_eq_one i

/-- The lower factor in Mathlib's LDL decomposition carries `1` on the diagonal, being the
inverse of a matrix that does. -/
@[simp]
theorem _root_.LDL.lower_apply_diag (i : n) : LDL.lower hS i i = 1 := by
  have htri : (LDL.lowerInv hS)ᵀ.IsUpperTriangular :=
    (LDL.isLowerTriangular_lowerInv hS).transpose
  have hinv := Matrix.inv_apply_diag_of_isUpperTriangular htri
    (LDL.lowerInv_apply_diag hS i)
  simpa [LDL.lower, ← Matrix.transpose_nonsing_inv] using hinv

end TauCeti
