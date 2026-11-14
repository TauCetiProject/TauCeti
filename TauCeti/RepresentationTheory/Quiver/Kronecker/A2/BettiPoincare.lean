/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.A2.Graded
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.BettiPoincare

/-!
# The Betti Poincaré matrix of the one-arrow quiver `1 ⟶ 2`

Give the path algebra of `1 ⟶ 2` (`TauCeti.Quiver.Kronecker A` with `[Unique A]`) its path-length
grading and order the vertices source first (`![src, tgt]`), matching
`TauCeti.Quiver.Kronecker.gradedCartanMatrixA2`.

* The source simple `S₁` has minimal linear resolution `0 ⟶ P₂{1} ⟶ P₁ ⟶ S₁ ⟶ 0`, contributing
  column `[1, q t]ᵀ`.
* The target simple `S₂` is already projective (`0 ⟶ P₂ ⟶ S₂ ⟶ 0`), contributing column `[0, 1]ᵀ`.

Hence the Betti Poincaré matrix is `!![1, 0; C (T 1) * X, 1]`, with projectives indexing rows and
simples indexing columns. Setting `t = -1` produces `!![1, 0; -T 1, 1]`, the exact two-sided
inverse of `gradedCartanMatrixA2 = !![1, 0; T 1, 1]`.

## Main definitions

* `TauCeti.Quiver.Kronecker.bettiPoincareMatrixA2`: the `2 × 2` matrix
  `!![1, 0; C (T 1) * X, 1]` over `PowerSeries (LaurentPolynomial ℤ)`.

## Main results

* `TauCeti.Quiver.Kronecker.submatrix_bettiPoincareMatrix_eq_bettiPoincareMatrixA2`: identifies
  `bettiPoincareMatrix` on `1 ⟶ 2` in source-first order with `bettiPoincareMatrixA2`.
* `TauCeti.Quiver.Kronecker.gradedCartanMatrixA2_mul_evalNegOne_eq_one`: multiplying
  `gradedCartanMatrixA2` by `!![1, 0; -T 1, 1]` gives the identity matrix.
-/

public section

noncomputable section

namespace TauCeti.Quiver.Kronecker

open CategoryTheory LaurentPolynomial
open scoped Matrix

universe u v

/-- The Betti Poincaré matrix of `1 ⟶ 2` in source-first order (`![src, tgt]`), with projectives in
the rows and simples in the columns: `!![1, 0; q t, 1]`. -/
def bettiPoincareMatrixA2 : Matrix (Fin 2) (Fin 2) (PowerSeries (LaurentPolynomial ℤ)) :=
  !![1, 0; PowerSeries.C (T 1) * PowerSeries.X, 1]

@[simp]
theorem bettiPoincareMatrixA2_apply (i j : Fin 2) :
    bettiPoincareMatrixA2 i j = !![1, 0; PowerSeries.C (T 1) * PowerSeries.X, 1] i j :=
  (rfl)

/-- Evaluating `bettiPoincareMatrixA2` at `t = -1` yields `!![1, 0; -q, 1]`, which is the right
inverse of `gradedCartanMatrixA2 = !![1, 0; q, 1]`. -/
@[simp]
theorem gradedCartanMatrixA2_mul_evalNegOne_eq_one :
    gradedCartanMatrixA2 * !![(1 : LaurentPolynomial ℤ), 0; -T 1, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

variable {A : Type v} [Unique A] (k : Type u) [Field k]

/-- **Worked check (`Q = 1 ⟶ 2`)**: in source-first order `![src, tgt]`, the Betti Poincaré matrix
of the first-arrow minimal linear resolutions of `S_src` and `S_tgt` is
`!![1, 0; C (T 1) * X, 1]`. -/
theorem submatrix_bettiPoincareMatrix_eq_bettiPoincareMatrixA2 :
    (bettiPoincareMatrix
      (PathAlgebra.gradedVertexProjectiveClassBasis k (Kronecker A))
      (PathAlgebra.gradedVertexSimpleProjectiveResolution k (Kronecker A))).submatrix
        ![src, tgt] ![src, tgt] = bettiPoincareMatrixA2 := by
  let _ : Fintype A := Unique.fintype
  rw [PathAlgebra.bettiPoincareMatrix_gradedVertexSimpleProjectiveResolution]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bettiPoincareMatrixA2, Nat.card_eq_fintype_card]

end TauCeti.Quiver.Kronecker
