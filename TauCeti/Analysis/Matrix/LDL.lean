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

Together these give the Cholesky factorization over `ℝ` or `ℂ`: writing `S = L D Lᴴ`, the matrix
`B = √D Lᴴ` is upper triangular with positive diagonal and `Bᴴ B = S`.

## Main results

* `LDL.diagEntries_pos` — the diagonal entries of `D` are positive.
* `LDL.lowerInv_apply_diag` and `LDL.lower_apply_diag` — the lower factor of the LDL
  decomposition and its inverse are unitriangular.
* `Matrix.PosDef.exists_isUpperTriangular_conjTranspose_mul_self_eq` — a positive-definite matrix
  is `Bᴴ B` for an upper triangular `B` with positive diagonal (Cholesky factorization).
-/

public section

open scoped ComplexOrder Matrix

namespace TauCeti

variable {𝕜 n : Type*} [RCLike 𝕜] [LinearOrder n]
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

include hS in
open Matrix in
/-- **Cholesky factorization**: a positive-definite matrix over `ℝ` or `ℂ` is `Bᴴ B` for an upper
triangular `B` with positive diagonal. Writing the LDL decomposition as `S = L D Lᴴ`, with `L`
lower unitriangular and `D` diagonal with positive real entries, take `B = √D Lᴴ`. -/
theorem _root_.Matrix.PosDef.exists_isUpperTriangular_conjTranspose_mul_self_eq :
    ∃ B : Matrix n n 𝕜, B.IsUpperTriangular ∧ (∀ i, 0 < B i i) ∧ Bᴴ * B = S := by
  have hd := LDL.diagEntries_pos hS
  -- the diagonal entries of `D` are the positive reals `re (d i)`
  have hre (i : n) : ((RCLike.re (LDL.diagEntries hS i) : ℝ) : 𝕜) = LDL.diagEntries hS i := by
    obtain ⟨x, -, hx⟩ := RCLike.pos_iff_exists_ofReal.1 (hd i)
    rw [← hx, RCLike.ofReal_re]
  set t : n → 𝕜 := fun i => ((√(RCLike.re (LDL.diagEntries hS i)) : ℝ) : 𝕜) with ht_def
  have ht (i : n) : 0 < t i :=
    RCLike.ofReal_pos.2 (Real.sqrt_pos.2 (RCLike.pos_iff.1 (hd i)).1)
  have htt : (diagonal t)ᴴ * diagonal t = LDL.diag hS := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, LDL.diag]
    congr 1
    funext i
    rw [Pi.star_apply, ht_def, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul,
      Real.mul_self_sqrt (RCLike.pos_iff.1 (hd i)).1.le, hre]
  have hLH : (LDL.lower hS)ᴴ.IsUpperTriangular := fun i j hji => by
    rw [conjTranspose_apply, LDL.isLowerTriangular_lower hS hji, star_zero]
  refine ⟨diagonal t * (LDL.lower hS)ᴴ, (blockTriangular_diagonal _).mul hLH, fun i => ?_, ?_⟩
  · rw [mul_apply_diag_of_isUpperTriangular (blockTriangular_diagonal _) hLH, diagonal_apply_eq,
      conjTranspose_apply, LDL.lower_apply_diag, star_one, mul_one]
    exact ht i
  · calc (diagonal t * (LDL.lower hS)ᴴ)ᴴ * (diagonal t * (LDL.lower hS)ᴴ)
        = LDL.lower hS * ((diagonal t)ᴴ * diagonal t) * (LDL.lower hS)ᴴ := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = S := by rw [htt, LDL.lower_conj_diag]

end TauCeti
