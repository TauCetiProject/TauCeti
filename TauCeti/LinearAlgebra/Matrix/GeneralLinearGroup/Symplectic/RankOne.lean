/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

import TauCeti.LinearAlgebra.Matrix.SymplecticMultiplier

/-!
# The rank-one symplectic group `Sp(2, R) = SL(2, R)`

In rank one the transported alternating form is `JFin 1 R = [[0, -1], [1, 0]]`, and a `2 × 2`
matrix `M` satisfies `M J Mᵀ = det(M) J`. So every matrix of determinant one is symplectic;
together with `TauCeti.GLSymplecticFin.det_eq_one`, this identifies `Sp(2, R)` with `SL(2, R)`
inside `GL(2, R)`.

## Main declarations

* `TauCeti.JFin_one_eq`: the alternating form `JFin 1` written out.
* `TauCeti.submatrix_mul_JFin_mul_transpose`: reindexing `M J Mᵀ` along `finSumFinEquiv` gives the
  same product with Mathlib's `Matrix.J`.
* `TauCeti.mul_JFin_one_mul_transpose_eq_det_smul`: a `2 × 2` matrix `M` satisfies
  `M J Mᵀ = det(M) J`.
* `Matrix.SpecialLinearGroup.toGL_mem_GLSymplecticFin`: `SL(2, R)` lies in `Sp(2, R)`.
-/

public section

open Matrix

namespace TauCeti

universe u

variable (R : Type u) [CommRing R]

/-- The transported alternating form of `Sp₂`, written out. -/
theorem JFin_one_eq : JFin 1 R = !![0, -1; 1, 0] := by
  rw [JFin_eq_submatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.J, finSumFinEquiv, Fin.addCases, Matrix.fromBlocks]

section JFin

variable {R}

/-- Reindexing `M J Mᵀ` along `finSumFinEquiv` gives the same product for the reindexed `M` and
Mathlib's `Matrix.J`. -/
theorem submatrix_mul_JFin_mul_transpose {m : ℕ} (M : Matrix (Fin (m + m)) (Fin (m + m)) R) :
    (M * JFin m R * Mᵀ).submatrix finSumFinEquiv finSumFinEquiv =
      M.submatrix finSumFinEquiv finSumFinEquiv * J (Fin m) R *
        Mᵀ.submatrix finSumFinEquiv finSumFinEquiv := by
  rw [← JFin_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]

/-- A `2 × 2` matrix scales the transported alternating form by its determinant:
`M J Mᵀ = det(M) J`. This is `Matrix.transpose_mul_J_mul_eq_det_smul` read through the
reindexing. -/
theorem mul_JFin_one_mul_transpose_eq_det_smul (M : Matrix (Fin (1 + 1)) (Fin (1 + 1)) R) :
    M * JFin 1 R * Mᵀ = M.det • JFin 1 R := by
  -- Apply the `Fin 1 ⊕ Fin 1` statement to `Mᵀ` read in those coordinates, then compare both
  -- sides after reindexing along `finSumFinEquiv`.
  apply (reindex finSumFinEquiv.symm finSumFinEquiv.symm).injective
  have h := transpose_mul_J_mul_eq_det_smul (Mᵀ.submatrix finSumFinEquiv finSumFinEquiv)
  rw [transpose_submatrix, transpose_transpose, det_submatrix_equiv_self, det_transpose] at h
  rw [reindex_apply, reindex_apply, Equiv.symm_symm, submatrix_mul_JFin_mul_transpose, h,
    ← JFin_submatrix]
  exact (congrFun₂ (submatrix_smul M.det (JFin 1 R)) _ _).symm

end JFin

variable {R} in
/-- **`SL(2, R)` lies in `Sp(2, R)`**: a `2 × 2` matrix of determinant one preserves the
alternating form, since `M J Mᵀ = det M • J` in rank two. This is the converse of
`TauCeti.GLSymplecticFin.det_eq_one` for `m = 1`. -/
theorem _root_.Matrix.SpecialLinearGroup.toGL_mem_GLSymplecticFin
    (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    Matrix.SpecialLinearGroup.toGL g ∈ GLSymplecticFin 1 R := by
  rw [GLSymplecticFin.mem_iff, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    mul_JFin_one_mul_transpose_eq_det_smul, g.det_coe, one_smul]

end TauCeti
