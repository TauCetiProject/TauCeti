/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.EulerCharacteristic

import Mathlib.GroupTheory.Perm.Cycle.Concrete

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A figure-eight grid and its Euler characteristic

This file introduces a `6 × 6` grid diagram `GridDiagram.figureEight` and computes the graded
Euler characteristic of its fully blocked grid homology. Its markings, listed column by column
as rows, are

* `O`: `[0, 1, 3, 2, 5, 4]`, the involution `(2 3) (4 5)`;
* `X`: `[2, 5, 0, 4, 3, 1]`, the involution `(0 2) (1 5) (3 4)`.

The diagram represents a knot (`GridDiagram.isKnot_figureEight`). Its alternating Alexander state
sum, and hence the graded Euler characteristic of its fully blocked homology over `ZMod 2`, is
`(1 - T (-2)) ^ 5 * (-T 2 + 3 - T (-2))`, with integer coefficients.

Here `T` records twice the Alexander grading, so the usual Alexander variable is `t = T 2`. The
factor `-T 2 + 3 - T (-2)` is the symmetric figure-eight polynomial `-t + 3 - t⁻¹`, with the
normalization computed independently from a Seifert matrix by
`TauCeti.KnotTheory.alexander_figureEightSeifertMatrix`. The five factors `1 - T (-2)` are the
contributions of the five copies of the stabilization space `W`, with bigradings `(0, 0)` and
`(-1, -1)`, carried by fully blocked homology on a size-six knot grid. After the size-five
trefoil grid of `TauCeti.KnotTheory.Grid.TorusLink.EulerCharacteristic`, this is a second worked
example of the grid determinant formula, on a grid whose `O`-markings are not on the diagonal.

The name records the intended knot type; as for the torus link grids, that this diagram presents
the figure-eight knot is not proved, since the comparison of grid diagrams with other
presentations of knots is not formalized. The calculation does not compute homology ranks.

## Main definitions

* `TauCeti.GridDiagram.figureEight`: the `6 × 6` figure-eight grid diagram.

## Main results

* `TauCeti.GridDiagram.isKnot_figureEight`: the diagram represents a knot.
* `TauCeti.GridDiagram.stateSum_figureEight`: its factored alternating Alexander state sum.
* `TauCeti.OddComponentGridDiagram.gradedHomologyEulerChar_figureEight`: the same formula for the
  graded Euler characteristic of its fully blocked homology over `ZMod 2`.

## References

P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
and Monographs 208, 2015: Chapter 3 (gradings and the determinant formula, especially §3.3) and
§§4.3--4.4 (fully blocked homology and its stabilization factors). The figure-eight knot has arc
index six (KnotInfo, https://knotinfo.math.indiana.edu), so it needs a grid of size six.
-/

public section

open LaurentPolynomial

namespace TauCeti

namespace GridDiagram

/-- A `6 × 6` grid diagram of the figure-eight knot. Its `O`-markings occupy the rows
`[0, 1, 3, 2, 5, 4]` and its `X`-markings the rows `[2, 5, 0, 4, 3, 1]`, column by column. -/
def figureEight : GridDiagram 6 where
  O := ⟨Equiv.swap 2 3 * Equiv.swap 4 5⟩
  X := ⟨Equiv.swap 0 2 * Equiv.swap 1 5 * Equiv.swap 3 4⟩
  disjoint := by decide

/-- The `O`-markings of the figure-eight grid, as a permutation of the rows. -/
@[simp]
theorem figureEight_O_toPerm : figureEight.O.toPerm = Equiv.swap 2 3 * Equiv.swap 4 5 :=
  (rfl)

/-- The `X`-markings of the figure-eight grid, as a permutation of the rows. -/
@[simp]
theorem figureEight_X_toPerm :
    figureEight.X.toPerm = Equiv.swap 0 2 * Equiv.swap 1 5 * Equiv.swap 3 4 :=
  (rfl)

-- Following the markings visits the `O`-columns in the order 0, 2, 4, 1, 5, 3.
private theorem componentPerm_figureEight :
    figureEight.componentPerm = [0, 2, 4, 1, 5, 3].formPerm := by
  rw [componentPerm_def, figureEight_O_toPerm, figureEight_X_toPerm]
  decide

/-- The figure-eight grid represents a knot: its component permutation is a single `6`-cycle. -/
theorem isKnot_figureEight : figureEight.IsKnot := by
  rw [isKnot_iff_componentPerm_isCycle, componentPerm_figureEight]
  exact List.isCycle_formPerm (by decide) (by decide)

-- Rows of this table are columns c of the grid; its columns are grid rows r.
-- Each entry counts X markings weakly northeast and strictly southwest of (c, r),
-- then subtracts the corresponding O count. Only 36 grid points are checked.
private theorem alexanderTwoWeight_figureEight (c r : Fin 6) :
    figureEight.alexanderTwoWeight c r =
      (!![0, 0, 0, 0, 0, 0;
          0, -2, -2, 0, 0, 0;
          0, -2, -4, -2, -2, -2;
          0, 0, -2, 0, -2, -2;
          0, 0, -2, -2, -4, -2;
          0, 0, -2, -2, -2, 0] : Matrix (Fin 6) (Fin 6) ℤ) c r := by
  rw [alexanderTwoWeight_def, GridState.JNumCenterAt_eq_card, GridState.JNumCenterAt_eq_card]
  fin_cases c <;> fin_cases r <;> decide

-- The O markings have 13 non-inversions and the X markings 6, giving 13 - 6 - (6 - 1) = 2.
private theorem alexanderTwoShift_figureEight : figureEight.alexanderTwoShift = 2 := by
  rw [alexanderTwoShift_def, OSet, XSet, GridState.I_self_pointSet_eq_card,
    GridState.I_self_pointSet_eq_card]
  decide

-- Exponentiating the integer table gives the matrix with entries 1, z, z²,
-- where z = T (-2). Keeping powers here makes the determinant factorization legible.
private theorem weightMatrix_figureEight :
    figureEight.weightMatrix =
      !![1, 1, 1, 1, 1, 1;
         1, T (-2), T (-2), 1, 1, 1;
         1, T (-2), T (-2) ^ 2, T (-2), T (-2), T (-2);
         1, 1, T (-2), 1, T (-2), T (-2);
         1, 1, T (-2), T (-2), T (-2) ^ 2, T (-2);
         1, 1, T (-2), T (-2), T (-2), 1] := by
  ext c r
  rw [weightMatrix_apply, alexanderTwoWeight_figureEight]
  fin_cases c <;> fin_cases r <;> norm_num [T_pow]

/-- The alternating state sum of the size-six figure-eight grid, including the five fully blocked
stabilization factors. The variable `T` records twice the Alexander grading. -/
theorem stateSum_figureEight :
    figureEight.stateSum = (1 - T (-2)) ^ 5 * (-T 2 + 3 - T (-2)) := by
  -- The determinant formula separates the diagram's sign, grading shift, and weight matrix.
  -- The `O`-permutation is even and the grid size is even, so the sign is `-1`.
  have hsign : Equiv.Perm.sign figureEight.O.toPerm * (((6 : ℕ) : ℤ) + 1).negOnePow = -1 := by
    rw [figureEight_O_toPerm]
    decide
  rw [stateSum_eq_smul_T_mul_det_weightMatrix, hsign, Units.neg_smul, one_smul,
    alexanderTwoShift_figureEight, weightMatrix_figureEight]
  -- This is a local calculation for this grid's matrix, not a new determinant API.
  -- First replace the concrete monomial by an indeterminate: expanding with Laurent
  -- simplification active would obscure the polynomial calculation.
  have hdet :
      (!![1, 1, 1, 1, 1, 1;
          1, T (-2), T (-2), 1, 1, 1;
          1, T (-2), T (-2) ^ 2, T (-2), T (-2), T (-2);
          1, 1, T (-2), 1, T (-2), T (-2);
          1, 1, T (-2), T (-2), T (-2) ^ 2, T (-2);
          1, 1, T (-2), T (-2), T (-2), 1] : Matrix (Fin 6) (Fin 6) ℤ[T;T⁻¹]).det =
        (1 - T (-2)) ^ 5 * (1 - 3 * T (-2) + T (-2) ^ 2) := by
    generalize (T (-2) : ℤ[T;T⁻¹]) = z
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove]
    ring
  rw [hdet]
  -- The grading shift multiplies by t = T 2. It turns 1 - 3 z + z² into -(-t + 3 - t⁻¹).
  -- The factor (1 - z)^5 survives: each W contributes 1 - t⁻¹ in the fully blocked theory.
  have hcancel : (T 2 * T (-2) : ℤ[T;T⁻¹]) = 1 := by
    rw [← T_add]
    norm_num
  have hcancel_sq : (T 2 * T (-2) ^ 2 : ℤ[T;T⁻¹]) = T (-2) := by
    rw [T_pow, ← T_add]
    norm_num
  linear_combination (3 * (1 - T (-2)) ^ 5 : ℤ[T;T⁻¹]) * hcancel -
    ((1 - T (-2)) ^ 5 : ℤ[T;T⁻¹]) * hcancel_sq

end GridDiagram

namespace OddComponentGridDiagram

/-- The graded Euler characteristic of fully blocked homology over `ZMod 2` on the size-six
figure-eight grid is `(1 - t⁻¹)^5 (-t + 3 - t⁻¹)`, where `t = T 2`. -/
theorem gradedHomologyEulerChar_figureEight :
    (GridDiagram.isKnot_figureEight.toOddComponentGridDiagram).gradedHomologyEulerChar =
        (1 - T (-2)) ^ 5 * (-T 2 + 3 - T (-2)) := by
  rw [gradedHomologyEulerChar_eq_gradedEulerChar, gradedEulerChar_eq_stateSum]
  exact GridDiagram.stateSum_figureEight

end OddComponentGridDiagram

end TauCeti
