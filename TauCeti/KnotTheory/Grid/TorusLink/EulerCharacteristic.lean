/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.EulerCharacteristic
public import TauCeti.KnotTheory.Grid.TorusLink.Basic

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Euler characteristic of the trefoil grid

The size-five grid `GridDiagram.torusLink 1 2` has diagonal `O` markings and `X` rows
`[3, 4, 0, 1, 2]`. Its alternating Alexander state sum and its fully blocked homology Euler
characteristic are both
`(1 - T (-2)) ^ 4 * (T 2 - 1 + T (-2))`, with integer coefficients.

Here `T` records twice the Alexander grading, so the usual variable is `t = T 2`. The factor
`T 2 - 1 + T (-2)` is the symmetric trefoil polynomial `t - 1 + t⁻¹`. The four factors
`1 - T (-2)` record the four copies of the stabilization space `W`, whose bigradings are
`(0, 0)` and `(-1, -1)`, in fully blocked homology on a size-five knot grid. Thus the result
computes the Euler characteristic of `GH-tilde`, including its grid-size dependence.

The calculation uses `GridDiagram.stateSum_eq_smul_T_mul_det_weightMatrix`, with local finite
marking counts and a determinant factorization. The homology statement then follows from
`OddComponentGridDiagram.gradedHomologyEulerChar_eq_gradedEulerChar` and
`OddComponentGridDiagram.gradedEulerChar_eq_stateSum`; no homology ranks are computed here.
The polynomial factor has the normalization computed independently by
`TauCeti.KnotTheory.alexander_trefoilSeifertMatrix`. This calculation does not identify the grid
and Seifert-matrix presentations as knots.

## Main results

* `TauCeti.GridDiagram.stateSum_torusLink_one_two`: the factored state sum of the trefoil grid.
* `TauCeti.OddComponentGridDiagram.gradedHomologyEulerChar_torusLink_one_two`: the same formula
  for the graded Euler characteristic of its fully blocked homology over `ZMod 2`.

## References

P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
and Monographs 208, 2015: Chapter 3 (gradings and the determinant formula, especially §3.3)
and §§4.3--4.4 (fully blocked homology and its stabilization factors). The formal determinant
and Euler--Poincaré comparisons credited above supply the conventions used in this computation.
-/

public section

open LaurentPolynomial

namespace TauCeti

namespace GridDiagram

-- Rows of this table are columns c of the grid; its columns are grid rows r.
-- Each entry counts X markings weakly northeast and strictly southwest of (c, r),
-- then subtracts the corresponding O count. Only 25 grid points are checked.
private theorem alexanderTwoWeight_torusLink_one_two (c r : Fin 5) :
    (torusLink 1 2).alexanderTwoWeight c r =
      (!![0, 0, 0, 0, 0;
          0, -2, -2, -2, 0;
          0, -2, -4, -4, -2;
          0, 0, -2, -4, -2;
          0, 0, 0, -2, -2] : Matrix (Fin 5) (Fin 5) ℤ) c r := by
  simp only [alexanderTwoWeight_def, GridState.JNumCenterAt_eq_card,
    torusLink_O_apply, torusLink_X_apply]
  fin_cases c <;> fin_cases r <;> decide

-- The O self-count is 10 and the X self-count is 4, giving 10 - 4 - (5 - 1) = 2.
private theorem alexanderTwoShift_torusLink_one_two :
    (torusLink 1 2).alexanderTwoShift = 2 := by
  simp only [alexanderTwoShift_def, OSet, XSet, GridState.I_self_pointSet_eq_card,
    torusLink_O_apply, torusLink_X_apply]
  decide

-- Exponentiating the integer table gives the matrix with entries 1, z, z²,
-- where z = T (-2). Keeping powers here makes the determinant factorization legible.
private theorem weightMatrix_torusLink_one_two :
    (torusLink 1 2).weightMatrix =
      !![1, 1, 1, 1, 1;
         1, T (-2), T (-2), T (-2), 1;
         1, T (-2), T (-2) ^ 2, T (-2) ^ 2, T (-2);
         1, 1, T (-2), T (-2) ^ 2, T (-2);
         1, 1, 1, T (-2), T (-2)] := by
  ext c r
  rw [weightMatrix_apply, alexanderTwoWeight_torusLink_one_two]
  fin_cases c <;> fin_cases r <;> norm_num [T_pow]

/-- The alternating state sum of the size-five trefoil grid, including the four fully blocked
stabilization factors. The variable `T` records twice the Alexander grading. -/
theorem stateSum_torusLink_one_two :
    (torusLink 1 2).stateSum =
      (1 - T (-2)) ^ 4 * (T 2 - 1 + T (-2)) := by
  -- The determinant formula separates the diagram's sign, grading shift, and weight matrix.
  -- Normalize the sign independently so arithmetic simplification cannot alter Laurent powers.
  have hsign : Equiv.Perm.sign (torusLink 1 2).O.toPerm *
      (((1 + 1 + (2 + 1) : ℕ) : ℤ) + 1).negOnePow = 1 := by
    rw [torusLink_O_toPerm, Equiv.Perm.sign_one, one_mul]
    decide
  rw [stateSum_eq_smul_T_mul_det_weightMatrix, hsign, one_smul,
    alexanderTwoShift_torusLink_one_two, weightMatrix_torusLink_one_two]
  -- This is a local calculation for this grid's matrix, not a new determinant API.
  -- First replace the concrete monomial by an indeterminate: expanding with Laurent
  -- simplification active would obscure the polynomial calculation and use excessive recursion.
  have hdet :
      (!![1, 1, 1, 1, 1;
          1, T (-2), T (-2), T (-2), 1;
          1, T (-2), T (-2) ^ 2, T (-2) ^ 2, T (-2);
          1, 1, T (-2), T (-2) ^ 2, T (-2);
          1, 1, 1, T (-2), T (-2)] : Matrix (Fin 5) (Fin 5) ℤ[T;T⁻¹]).det =
        (1 - T (-2)) ^ 4 * (1 - T (-2) + T (-2) ^ 2) := by
    generalize (T (-2) : ℤ[T;T⁻¹]) = z
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix_apply,
      Fin.succAbove]
    ring
  rw [hdet]
  -- The grading shift multiplies by t = T 2. It turns 1 - z + z² into t - 1 + t⁻¹.
  -- The factor (1 - z)^4 survives: each W contributes 1 - t⁻¹ in the fully blocked theory.
  have hcancel : (T 2 * T (-2) : ℤ[T;T⁻¹]) = 1 := by
    rw [← T_add]
    norm_num
  have hcancel_sq : (T 2 * T (-2) ^ 2 : ℤ[T;T⁻¹]) = T (-2) := by
    rw [T_pow, ← T_add]
    norm_num
  calc
    (T 2 : ℤ[T;T⁻¹]) * ((1 - T (-2)) ^ 4 * (1 - T (-2) + T (-2) ^ 2)) =
        (1 - T (-2)) ^ 4 * (T 2 * (1 - T (-2) + T (-2) ^ 2)) := by rw [mul_left_comm]
    _ = (1 - T (-2)) ^ 4 * (T 2 - 1 + T (-2)) := by
      rw [mul_add, mul_sub, mul_one, hcancel, hcancel_sq]

end GridDiagram

namespace OddComponentGridDiagram

/-- The graded Euler characteristic of fully blocked homology over `ZMod 2` on the size-five
trefoil grid is `(1 - t⁻¹)^4 (t - 1 + t⁻¹)`, where `t = T 2`. -/
theorem gradedHomologyEulerChar_torusLink_one_two :
    (GridDiagram.isKnot_torusLink_one_two.toOddComponentGridDiagram).gradedHomologyEulerChar =
        (1 - T (-2)) ^ 4 * (T 2 - 1 + T (-2)) := by
  rw [gradedHomologyEulerChar_eq_gradedEulerChar, gradedEulerChar_eq_stateSum]
  exact GridDiagram.stateSum_torusLink_one_two

end OddComponentGridDiagram

end TauCeti
