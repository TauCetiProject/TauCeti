/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.LinearAlgebra.Matrix.Determinant.IdealDivisibility
public import TauCeti.LinearAlgebra.Matrix.MaximalMinor
import Mathlib.Tactic.NormNum

/-!
# Arithmetic minors under reduction and row changes

These examples distinguish the direction in which a nonzero minor lifts from reduction modulo
`2`, the role of its selected columns, and the row hypotheses in determinant divisibility.
For the integer matrix with rows `(2, 4, 6)` and `(3, 6, 12)`, the three increasing-column minors
are `0`, `6` and `12`, and the general row-divisibility theorem puts every minor in `6ℤ`.

Lower and upper shears preserve full-row minors. Scaling both rows by `2` instead multiplies
minors by `4`, while swapping the rows changes their sign. A product of an upper and a lower
shear can have determinant `1` without being triangular, so determinant preservation applies
more generally than the unitriangular specializations.
-/

public section

open Matrix

namespace TauCeti.ArithmeticMinorExamples

/-! ### Reduction and the chosen columns -/

/-- The minor of `[[1]]` lifts from `ZMod 2` by the general reduction theorem. -/
theorem reduction_one_lifts : (!![(1 : ℤ)].submatrix id id).det ≠ 0 := by
  exact det_submatrix_ne_zero_of_map (Int.castRingHom (ZMod 2))
    (by norm_num [det_unique])

/-- The nonzero integer determinant `2` vanishes after reduction, so nonvanishing does not
descend along this noninjective ring homomorphism. -/
theorem reduction_two_loses_nonvanishing :
    (!![(2 : ℤ)]).det ≠ 0 ∧
      ((!![(2 : ℤ)]).map (Int.castRingHom (ZMod 2))).det = 0 := by
  norm_num [det_unique]; rfl

/-- The row `[2]` is independent over `ℤ`, as its determinant is nonzero. -/
theorem two_row_independent : LinearIndependent ℤ (!![(2 : ℤ)]).row :=
  linearIndependent_rows_of_det_ne_zero reduction_two_loses_nonvanishing.1

/-- After reduction modulo `2` the same row is zero and is not independent. -/
theorem reduced_two_row_not_independent :
    ¬ LinearIndependent (ZMod 2) ((!![(2 : ℤ)]).map (Int.castRingHom (ZMod 2))).row := by
  rw [linearIndependent_unique_iff]
  norm_num [Matrix.row, funext_iff, Fin.forall_fin_one]; rfl

/-- For the same rectangular matrix, columns `(0, 1)` give a nonzero minor and columns `(0, 2)`
give zero, both before and after reduction. -/
theorem reduction_depends_on_chosen_columns :
    ((!![(1 : ℤ), 0, 0; 0, 1, 0]).submatrix id ![0, 1]).det = 1 ∧
      ((!![(1 : ℤ), 0, 0; 0, 1, 0]).submatrix id ![0, 2]).det = 0 ∧
      (((!![(1 : ℤ), 0, 0; 0, 1, 0]).map (Int.castRingHom (ZMod 2))).submatrix id
        ![0, 1]).det = 1 ∧
      (((!![(1 : ℤ), 0, 0; 0, 1, 0]).map (Int.castRingHom (ZMod 2))).submatrix id
        ![0, 2]).det = 0 := by
  norm_num [det_fin_two, submatrix_apply]

/-- Proportional rows give a zero determinant before and after reduction; a vanishing reduced
minor cannot certify independence. -/
theorem proportional_rows_minor_vanishes :
    (!![(1 : ℤ), 1; 2, 2]).det = 0 ∧
      ((!![(1 : ℤ), 1; 2, 2]).map (Int.castRingHom (ZMod 2))).det = 0 := by
  norm_num [det_fin_two]

/-! ### Row divisibility -/

/-- The three increasing-column minors are `0`, `6` and `12`. -/
theorem row_divisible_minors :
    ((!![(2 : ℤ), 4, 6; 3, 6, 12]).submatrix id ![0, 1]).det = 0 ∧
      ((!![(2 : ℤ), 4, 6; 3, 6, 12]).submatrix id ![0, 2]).det = 6 ∧
      ((!![(2 : ℤ), 4, 6; 3, 6, 12]).submatrix id ![1, 2]).det = 12 := by
  norm_num [det_fin_two, submatrix_apply]

/-- The row-divisibility theorem puts every full-row minor, including choices with repeated
columns, in `6ℤ`. -/
theorem six_dvd_every_row_divisible_minor (c : Fin 2 → Fin 3) :
    (6 : ℤ) ∣ ((!![(2 : ℤ), 4, 6; 3, 6, 12]).submatrix id c).det := by
  simpa using prod_dvd_det_submatrix_of_dvd_row !![(2 : ℤ), 4, 6; 3, 6, 12]
    ![2, 3] (by norm_num [Fin.forall_fin_two, Fin.forall_fin_succ]) c

/-- Row factors `2` and `3` give determinant `6`; proportional rows give zero. Without either
row or column divisibility hypotheses, a determinant need not be divisible by `6`. -/
theorem row_divisibility_controls :
    (!![(2 : ℤ), 4; 3, 9]).det = 6 ∧
      (!![(2 : ℤ), 2; 1, 1]).det = 0 ∧
      (!![(2 : ℤ), 3; 4, 9]).det = 6 ∧
      ¬ (6 : ℤ) ∣ (!![(2 : ℤ), 3; 1, 1]).det := by
  norm_num [det_fin_two]

/-- With no rows, the determinant is `1` and the product of row ideals is `⊤`. -/
theorem empty_determinant_and_row_ideal_product :
    (0 : Matrix (Fin 0) (Fin 0) ℤ).det = 1 ∧
      (1 : ℤ) ∈ ∏ _ : Fin 0, (⊥ : Ideal ℤ) := by
  simp

/-! ### Changes of rows -/

/-- The two shears produce the expected row combinations, and the minor on columns `(0, 1)`
of the original matrix is `1`. -/
theorem shear_products_and_selected_minor :
    !![(1 : ℤ), 0; 1, 1] * !![(1 : ℤ), 2, 0; 0, 1, 5] = !![(1 : ℤ), 2, 0; 1, 3, 5] ∧
      !![(1 : ℤ), 2; 0, 1] * !![(1 : ℤ), 2, 0; 0, 1, 5] = !![(1 : ℤ), 4, 10; 0, 1, 5] ∧
      ((!![(1 : ℤ), 2, 0; 0, 1, 5]).submatrix id ![0, 1]).det = 1 := by
  norm_num [Matrix.ext_iff, Fin.forall_fin_two, Fin.forall_fin_succ, Matrix.mul_apply,
    Fin.sum_univ_two, det_fin_two, submatrix_apply]

/-- The lower shear preserves every selected full-row minor of the rectangular matrix. -/
theorem lower_shear_preserves_minors (c : Fin 2 → Fin 3) :
    ((!![(1 : ℤ), 0; 1, 1] * !![(1 : ℤ), 2, 0; 0, 1, 5]).submatrix id c).det =
      ((!![(1 : ℤ), 2, 0; 0, 1, 5]).submatrix id c).det := by
  exact det_submatrix_mul_left_of_isUpperUnitriangular_transpose
    (by norm_num [isUpperUnitriangular_def, IsUpperTriangular, BlockTriangular,
      Fin.forall_fin_two]) _ c

/-- The upper shear also preserves every selected full-row minor. -/
theorem upper_shear_preserves_minors (c : Fin 2 → Fin 3) :
    ((!![(1 : ℤ), 2; 0, 1] * !![(1 : ℤ), 2, 0; 0, 1, 5]).submatrix id c).det =
      ((!![(1 : ℤ), 2, 0; 0, 1, 5]).submatrix id c).det := by
  exact IsUpperUnitriangular.det_submatrix_mul_left
    (by norm_num [isUpperUnitriangular_def, IsUpperTriangular, BlockTriangular,
      Fin.forall_fin_two]) _ c

/-- Scaling both rows by `2` changes the selected minor from `1` to `4`, while a row swap
changes it to `-1`. -/
theorem scaling_and_swap_change_minor :
    ((!![(2 : ℤ), 0; 0, 2] * !![(1 : ℤ), 2, 0; 0, 1, 5]).submatrix id ![0, 1]).det = 4 ∧
      ((!![(0 : ℤ), 1; 1, 0] * !![(1 : ℤ), 2, 0; 0, 1, 5]).submatrix id ![0, 1]).det = -1 := by
  norm_num [det_submatrix_mul_left, det_fin_two, submatrix_apply]

/-- Lower shears compose by adding their off-diagonal entries, and the resulting transpose
remains upper unitriangular. -/
theorem lower_shear_composite :
    !![(1 : ℤ), 0; 1, 1] * !![(1 : ℤ), 0; 2, 1] = !![(1 : ℤ), 0; 3, 1] ∧
      (!![(1 : ℤ), 0; 3, 1]ᵀ).IsUpperUnitriangular := by
  norm_num [Matrix.ext_iff, Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    isUpperUnitriangular_def, IsUpperTriangular, BlockTriangular]

/-- Mixing upper and lower shears gives determinant `1` but need not give either triangular
shape. -/
theorem mixed_shear_is_not_triangular :
    (!![(1 : ℤ), 2; 0, 1] * !![(1 : ℤ), 0; 1, 1]).det = 1 ∧
      ¬ (!![(1 : ℤ), 2; 0, 1] * !![(1 : ℤ), 0; 1, 1]).IsUpperTriangular ∧
      ¬ (!![(1 : ℤ), 2; 0, 1] * !![(1 : ℤ), 0; 1, 1]).IsLowerTriangular := by
  norm_num [det_mul, det_fin_two, IsUpperTriangular, IsLowerTriangular, BlockTriangular,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.forall_fin_two]

/-- Determinant one still preserves every selected minor for this nontriangular product. -/
theorem mixed_shear_preserves_minors (c : Fin 2 → Fin 3) :
    (((!![(1 : ℤ), 2; 0, 1] * !![(1 : ℤ), 0; 1, 1]) *
      !![(1 : ℤ), 2, 0; 0, 1, 5]).submatrix id c).det =
      ((!![(1 : ℤ), 2, 0; 0, 1, 5]).submatrix id c).det := by
  exact det_submatrix_mul_left_of_det_eq_one mixed_shear_is_not_triangular.1 _ c

end TauCeti.ArithmeticMinorExamples
