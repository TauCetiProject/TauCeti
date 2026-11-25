/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# The rank-one symplectic group `Sp(2, R) = SL(2, R)`

In rank one the transported alternating form is `JFin 1 R = [[0, -1], [1, 0]]`, and a `2 × 2`
matrix `A` satisfies `Aᵀ J A = det(A) J`. So every matrix of determinant one is symplectic;
together with `TauCeti.GLSymplecticFin.det_eq_one`, this identifies `Sp(2, R)` with `SL(2, R)`
inside `GL(2, R)`.

## Main declarations

* `TauCeti.JFin_one_eq`: the alternating form `JFin 1` written out.
* `Matrix.SpecialLinearGroup.toGL_mem_GLSymplecticFin`: `SL(2, R)` lies in `Sp(2, R)`.
-/

public section

namespace TauCeti

universe u

variable (R : Type u) [CommRing R]

/-- The transported alternating form of `Sp₂`, written out. -/
theorem JFin_one_eq : JFin 1 R = !![0, -1; 1, 0] := by
  rw [JFin_eq_submatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.J, finSumFinEquiv, Fin.addCases, Matrix.fromBlocks]

variable {R} in
/-- **`SL(2, R)` is `Sp(2, R)`**: a `2 × 2` matrix of determinant one preserves the alternating
form, since `Aᵀ J A = det A • J` in rank two; we check this entrywise. This is the converse of
`TauCeti.GLSymplecticFin.det_eq_one` for `m = 1`. -/
theorem _root_.Matrix.SpecialLinearGroup.toGL_mem_GLSymplecticFin
    (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    Matrix.SpecialLinearGroup.toGL g ∈ GLSymplecticFin 1 R := by
  have h := g.prop
  rw [Matrix.det_fin_two] at h
  rw [GLSymplecticFin.mem_iff', JFin_one_eq, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one, zero_add,
      mul_neg, add_zero, neg_mul] <;>
    first | linear_combination h | linear_combination -h | ring

end TauCeti
