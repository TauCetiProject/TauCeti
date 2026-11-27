/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.Diffeomorph

/-!
# The polar decomposition of `[[0, -2], [1/2, 0]]`

This file computes both polar decompositions of the real matrix of determinant one

`A = [[0, -2], [1/2, 0]]`

and its polar deformation, as a test of the conventions of the polar package
(`TauCeti.Analysis.Matrix.Polar`, `TauCeti.Analysis.Matrix.Polar.Deformation` and
`TauCeti.Analysis.Matrix.Polar.Diffeomorph`).

* **The left decomposition.** `A Aᵀ = diag(4, 1/4)`, so the positive factor is
  `P = √(A Aᵀ) = diag(2, 1/2)`, and the orthogonal factor is the rotation by a quarter turn,
  `U = P⁻¹ A = [[0, -1], [1, 0]]`. Thus `A = P U`.
* **The right decomposition.** The right positive factor is
  `Uᵀ P U = diag(1/2, 2) = √(Aᵀ A)`, and `A = U · diag(1/2, 2)` with the same rotation `U`.
* **The order of the factors matters.** Pairing the right positive factor `√(Aᵀ A)` with a left
  factorization fails: `√(Aᵀ A)⁻¹ A = diag(2, 1/2) A = [[0, -4], [1/4, 0]]` is not orthogonal.
  Equivalently, no orthogonal `V` gives `A = √(Aᵀ A) V`: the positive factor of a left
  decomposition must be `√(A Aᵀ)`.
* **Determinant one.** `det A = 1`, and both factors of each decomposition have determinant one,
  so the polar coordinates of `A` lie in the product of the positive-definite matrices of
  determinant one with `SO(2)`, as the polar coordinates on `SL(2, ℝ)` require.
* **The polar deformation** `A ↦ P ^ (1 - t) U` is `diag(√2, 1/√2) · U` at `t = 1/2` and the
  rotation `U` at `t = 1`.

## Main results

* `TauCeti.PolarFinTwoExample.sqrt_matrix_mul_star`,
  `TauCeti.PolarFinTwoExample.coe_polarUnitary_toGL_matrix`: the two factors of the left polar
  decomposition of `A`.
* `TauCeti.PolarFinTwoExample.sqrt_star_matrix_mul_matrix`,
  `TauCeti.PolarFinTwoExample.star_rotation_mul_diagonal_mul_rotation`: the right positive factor,
  and its expression as the conjugate `Uᵀ P U`.
* `TauCeti.PolarFinTwoExample.inv_sqrt_star_matrix_mul_matrix_mul_matrix_notMem_unitaryGroup`,
  `TauCeti.PolarFinTwoExample.sqrt_star_matrix_mul_matrix_mul_ne`: the right positive factor is
  not a left positive factor.
* `TauCeti.PolarFinTwoExample.coe_polarDiffeomorph_matrix_fst`,
  `TauCeti.PolarFinTwoExample.polarDiffeomorph_matrix_snd`,
  `TauCeti.PolarFinTwoExample.rightPolarDiffeomorph_matrix_fst`,
  `TauCeti.PolarFinTwoExample.coe_rightPolarDiffeomorph_matrix_snd`: the left and right polar
  coordinates of `A` on `SL(2, ℝ)`.
* `TauCeti.PolarFinTwoExample.coe_polarDeformation_toGL_matrix_one_half`,
  `TauCeti.PolarFinTwoExample.coe_polarDeformation_toGL_matrix_one`: the polar deformation of `A`
  at times `1/2` and `1`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
-/

public section

noncomputable section

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace TauCeti.PolarFinTwoExample

attribute [local instance] Matrix.l2OpNormedAlgebraReal

/-- The real matrix `A = [[0, -2], [1/2, 0]]`, of determinant one. -/
def matrix : SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![0, -2; 1 / 2, 0], by norm_num [det_fin_two_of]⟩

/-- The entries of `A`. -/
@[simp]
theorem coe_matrix : (matrix : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -2; 1 / 2, 0] := (rfl)

/-- The rotation `[[0, -1], [1, 0]]` by a quarter turn, as an element of `SO(2)`. -/
def rotation : specialUnitaryGroup (Fin 2) ℝ :=
  ⟨!![0, -1; 1, 0], by
    refine mem_specialUnitaryGroup_iff.2 ⟨mem_unitaryGroup_iff.2 ?_, by simp [det_fin_two_of]⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, star_apply]⟩

/-- The entries of the rotation. -/
@[simp]
theorem coe_rotation : (rotation : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 0] := (rfl)

/-- `A Aᵀ = diag(4, 1/4)`. -/
theorem matrix_mul_star :
    (matrix : Matrix (Fin 2) (Fin 2) ℝ) * star (matrix : Matrix (Fin 2) (Fin 2) ℝ) =
      diagonal ![4, 1 / 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, star_apply]

/-- `Aᵀ A = diag(1/4, 4)`. -/
theorem star_matrix_mul_matrix :
    star (matrix : Matrix (Fin 2) (Fin 2) ℝ) * (matrix : Matrix (Fin 2) (Fin 2) ℝ) =
      diagonal ![1 / 4, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, star_apply]

/-- The square root of a diagonal matrix with nonnegative entries is computed entry by entry. -/
private theorem sqrt_diagonal {n : Type*} [Fintype n] [DecidableEq n] {d : n → ℝ} (hd : 0 ≤ d) :
    CFC.sqrt (diagonal d) = diagonal fun i ↦ √(d i) := by
  refine CFC.sqrt_unique ?_ (PosSemidef.diagonal fun i ↦ Real.sqrt_nonneg (d i)).nonneg
  rw [diagonal_mul_diagonal]
  congr 1
  ext i
  exact Real.mul_self_sqrt (hd i)

/-- The left positive factor is `P = √(A Aᵀ) = diag(2, 1/2)`. -/
theorem sqrt_matrix_mul_star :
    CFC.sqrt ((matrix : Matrix (Fin 2) (Fin 2) ℝ) * star (matrix : Matrix (Fin 2) (Fin 2) ℝ)) =
      diagonal ![2, 1 / 2] := by
  rw [matrix_mul_star, sqrt_diagonal fun i ↦ by fin_cases i <;> norm_num]
  congr 1
  ext i
  fin_cases i <;> norm_num [Real.sqrt_eq_iff_mul_self_eq_of_pos, inv_eq_iff_eq_inv]

/-- The right positive factor is `√(Aᵀ A) = diag(1/2, 2)`. -/
theorem sqrt_star_matrix_mul_matrix :
    CFC.sqrt (star (matrix : Matrix (Fin 2) (Fin 2) ℝ) * (matrix : Matrix (Fin 2) (Fin 2) ℝ)) =
      diagonal ![1 / 2, 2] := by
  rw [star_matrix_mul_matrix, sqrt_diagonal fun i ↦ by fin_cases i <;> norm_num]
  congr 1
  ext i
  fin_cases i <;> norm_num [Real.sqrt_eq_iff_mul_self_eq_of_pos, inv_eq_iff_eq_inv]

/-- The left polar decomposition `A = P U`, with `P = diag(2, 1/2)` and `U` the rotation. -/
theorem diagonal_mul_rotation :
    diagonal ![(2 : ℝ), 1 / 2] * (rotation : Matrix (Fin 2) (Fin 2) ℝ) =
      (matrix : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, star_apply]

/-- The right polar decomposition `A = U · diag(1/2, 2)`, with the same rotation `U`. -/
theorem rotation_mul_diagonal :
    (rotation : Matrix (Fin 2) (Fin 2) ℝ) * diagonal ![1 / 2, 2] =
      (matrix : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, star_apply]

/-- The right positive factor is the left one conjugated by the rotation:
`Uᵀ P U = diag(1/2, 2)`. -/
theorem star_rotation_mul_diagonal_mul_rotation :
    star (rotation : Matrix (Fin 2) (Fin 2) ℝ) * diagonal ![2, 1 / 2] *
        (rotation : Matrix (Fin 2) (Fin 2) ℝ) =
      diagonal ![1 / 2, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, star_apply]

/-- The orthogonal polar factor of `A` is the rotation `U = [[0, -1], [1, 0]]`. -/
theorem coe_polarUnitary_toGL_matrix :
    ((SpecialLinearGroup.toGL matrix).polarUnitary : Matrix (Fin 2) (Fin 2) ℝ) =
      (rotation : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h := Units.polarUnitary_eq_of_mul_eq (SpecialLinearGroup.toGL matrix)
    (PosSemidef.diagonal (d := ![(2 : ℝ), 1 / 2]) (fun i ↦ by fin_cases i <;> norm_num)).nonneg
    (v := ⟨rotation, specialUnitaryGroup_le_unitaryGroup rotation.property⟩)
    diagonal_mul_rotation
  exact congrArg Subtype.val h

/-- Taking the right positive factor as a left factor: `√(Aᵀ A)⁻¹ A = [[0, -4], [1/4, 0]]`. -/
theorem inv_sqrt_star_matrix_mul_matrix_mul_matrix :
    (CFC.sqrt (star (matrix : Matrix (Fin 2) (Fin 2) ℝ) * (matrix : Matrix (Fin 2) (Fin 2) ℝ)))⁻¹ *
      (matrix : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -4; 1 / 4, 0] := by
  have hinv : (diagonal ![(1 : ℝ) / 2, 2])⁻¹ = diagonal ![2, 1 / 2] := by
    refine inv_eq_left_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> norm_num
  rw [sqrt_star_matrix_mul_matrix, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix `√(Aᵀ A)⁻¹ A = [[0, -4], [1/4, 0]]` is not orthogonal, so the right positive
factor `√(Aᵀ A)` is not the positive factor of a decomposition `A = P V` with `V` orthogonal. -/
theorem inv_sqrt_star_matrix_mul_matrix_mul_matrix_notMem_unitaryGroup :
    (CFC.sqrt (star (matrix : Matrix (Fin 2) (Fin 2) ℝ) * (matrix : Matrix (Fin 2) (Fin 2) ℝ)))⁻¹ *
      (matrix : Matrix (Fin 2) (Fin 2) ℝ) ∉ unitaryGroup (Fin 2) ℝ := by
  rw [inv_sqrt_star_matrix_mul_matrix_mul_matrix, mem_unitaryGroup_iff]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, star_apply] at h00

/-- No orthogonal matrix `V` satisfies `√(Aᵀ A) V = A`: the positive factor of a left polar
decomposition is `√(A Aᵀ) = diag(2, 1/2)`, not `√(Aᵀ A) = diag(1/2, 2)`. -/
theorem sqrt_star_matrix_mul_matrix_mul_ne (V : unitaryGroup (Fin 2) ℝ) :
    CFC.sqrt (star (matrix : Matrix (Fin 2) (Fin 2) ℝ) * (matrix : Matrix (Fin 2) (Fin 2) ℝ)) *
      (V : Matrix (Fin 2) (Fin 2) ℝ) ≠ matrix := by
  intro h
  have h' := Units.sqrt_mul_star_eq_of_mul_eq (SpecialLinearGroup.toGL matrix)
    (CFC.sqrt_nonneg _) h
  rw [SpecialLinearGroup.coe_GL_coe_matrix, sqrt_matrix_mul_star, sqrt_star_matrix_mul_matrix]
    at h'
  have h00 := congrFun (congrFun h' 0) 0
  norm_num at h00

/-- The polar coordinates of `A` on `SL(2, ℝ)`: its positive-definite coordinate of determinant
one is `diag(2, 1/2)`. -/
theorem coe_polarDiffeomorph_matrix_fst :
    ((((SpecialLinearGroup.polarDiffeomorph (Fin 2) ℝ matrix).1 : posDefOpens (Fin 2) ℝ) :
      selfAdjoint (Matrix (Fin 2) (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        diagonal ![2, 1 / 2] := by
  rw [SpecialLinearGroup.coe_polarDiffeomorph_apply_fst, sqrt_matrix_mul_star]

/-- The polar coordinates of `A` on `SL(2, ℝ)`: its coordinate in `SO(2)` is the rotation. -/
theorem polarDiffeomorph_matrix_snd :
    (SpecialLinearGroup.polarDiffeomorph (Fin 2) ℝ matrix).2 = rotation :=
  Subtype.ext <| by
    rw [SpecialLinearGroup.coe_polarDiffeomorph_apply_snd, coe_polarUnitary_toGL_matrix]

/-- The right polar coordinates of `A` on `SL(2, ℝ)`: its coordinate in `SO(2)` is the
rotation. -/
theorem rightPolarDiffeomorph_matrix_fst :
    (SpecialLinearGroup.rightPolarDiffeomorph (Fin 2) ℝ matrix).1 = rotation :=
  Subtype.ext <| by
    rw [SpecialLinearGroup.coe_rightPolarDiffeomorph_apply_fst, coe_polarUnitary_toGL_matrix]

/-- The right polar coordinates of `A` on `SL(2, ℝ)`: its positive-definite coordinate of
determinant one is `diag(1/2, 2)`. -/
theorem coe_rightPolarDiffeomorph_matrix_snd :
    ((((SpecialLinearGroup.rightPolarDiffeomorph (Fin 2) ℝ matrix).2 : posDefOpens (Fin 2) ℝ) :
      selfAdjoint (Matrix (Fin 2) (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        diagonal ![1 / 2, 2] := by
  rw [SpecialLinearGroup.coe_rightPolarDiffeomorph_apply_snd, sqrt_star_matrix_mul_matrix]

/-- At time `1/2` the polar deformation of `A` is `diag(√2, 1/√2) · U`. -/
theorem coe_polarDeformation_toGL_matrix_one_half :
    (GeneralLinearGroup.polarDeformation (SpecialLinearGroup.toGL matrix) (1 / 2) :
      Matrix (Fin 2) (Fin 2) ℝ) =
        diagonal ![√2, 1 / √2] * (rotation : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [GeneralLinearGroup.coe_polarDeformation, coe_polarUnitary_toGL_matrix,
    SpecialLinearGroup.coe_GL_coe_matrix, sqrt_matrix_mul_star,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← CFC.sqrt_eq_rpow,
    sqrt_diagonal fun i ↦ by fin_cases i <;> norm_num]
  congr 2
  ext i
  fin_cases i <;> norm_num

/-- At time `1` the polar deformation of `A` is the rotation `U`. -/
theorem coe_polarDeformation_toGL_matrix_one :
    (GeneralLinearGroup.polarDeformation (SpecialLinearGroup.toGL matrix) 1 :
      Matrix (Fin 2) (Fin 2) ℝ) = (rotation : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [GeneralLinearGroup.polarDeformation_one, Unitary.val_toUnits_apply,
    coe_polarUnitary_toGL_matrix]

end TauCeti.PolarFinTwoExample
