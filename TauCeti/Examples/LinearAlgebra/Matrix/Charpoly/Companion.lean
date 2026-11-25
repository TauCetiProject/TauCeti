/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Rat
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Companion
public import TauCeti.LinearAlgebra.Matrix.RationalCanonicalFormFinTwo
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases

/-!
# Companion matrices in small degree

The companion matrix of the monic quadratic `X² - t X + d`, reindexed along its natural degree
`2`, is `TauCeti.companionFinTwo t d = !![0, -d; 1, t]`; for `X² - X - 1` over `ℤ` it is
`!![0, 1; 1, 1]`, and for `X² + 1` it is `!![0, -1; 1, 0]`, which is not its own transpose, so the
orientation of the convention (ones below the diagonal, coefficients in the last column) is
visible. The companion matrix of `1` is the empty matrix, with characteristic polynomial `1`.
The characteristic polynomial of the companion matrix of `X² - X - 1` is `X² - X - 1`, and the
companion matrix of `X² + 1` has determinant `1` and no eigenvalue over `ℚ`.
-/

public section

open Polynomial Matrix

namespace TauCeti.Examples.Companion

/-- The monic quadratic `X² - t X + d` has natural degree `2` over a nontrivial ring. -/
theorem natDegree_X_sq_sub_C_mul_X_add_C {R : Type*} [CommRing R] [Nontrivial R] (t d : R) :
    (X ^ 2 - C t * X + C d).natDegree = 2 := by
  compute_degree!

/-- The companion matrix of `X² - t X + d`, reindexed along its natural degree `2`, is
`TauCeti.companionFinTwo t d = !![0, -d; 1, t]`. -/
theorem reindex_companion_X_sq_sub_C_mul_X_add_C {R : Type*} [CommRing R] [Nontrivial R]
    (t d : R) :
    reindex (finCongr (natDegree_X_sq_sub_C_mul_X_add_C t d))
        (finCongr (natDegree_X_sq_sub_C_mul_X_add_C t d)) (X ^ 2 - C t * X + C d).companion =
      companionFinTwo t d := by
  rw [companionFinTwo_def]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [reindex_apply, submatrix_apply, companion_apply,
      natDegree_X_sq_sub_C_mul_X_add_C] <;>
    simp [coeff_X, coeff_C]

/-- `X² - X - 1` over `ℤ` has natural degree `2`. -/
theorem natDegree_fib : (X ^ 2 - X - 1 : ℤ[X]).natDegree = 2 := by
  compute_degree!

/-- The companion matrix of `X² - X - 1` over `ℤ`, reindexed along its natural degree `2`, is
`!![0, 1; 1, 1]`. -/
theorem reindex_companion_fib :
    reindex (finCongr natDegree_fib) (finCongr natDegree_fib) (X ^ 2 - X - 1 : ℤ[X]).companion =
      !![0, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [reindex_apply, submatrix_apply, companion_apply, natDegree_fib] <;>
    simp [coeff_X, coeff_one]

/-- The characteristic polynomial of the companion matrix of `X² - X - 1` is `X² - X - 1`. -/
theorem charpoly_companion_fib :
    (X ^ 2 - X - 1 : ℤ[X]).companion.charpoly = X ^ 2 - X - 1 :=
  charpoly_companion (by monicity!)

/-- `X² + 1` over `ℤ` has natural degree `2`. -/
theorem natDegree_X_sq_add_one : (X ^ 2 + 1 : ℤ[X]).natDegree = 2 := by
  compute_degree!

/-- The companion matrix of `X² + 1`, reindexed along its natural degree `2`, is
`!![0, -1; 1, 0]`: the entry in row `0` and column `1` is `-1`, from the last column, and not
the `1` that wrapping the subdiagonal index around `Fin 2` would give. -/
theorem reindex_companion_X_sq_add_one :
    reindex (finCongr natDegree_X_sq_add_one) (finCongr natDegree_X_sq_add_one)
        (X ^ 2 + 1 : ℤ[X]).companion = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [reindex_apply, submatrix_apply, companion_apply, natDegree_X_sq_add_one] <;>
    simp [coeff_one]

/-- The companion matrix of `X² + 1` is not its own transpose. -/
theorem transpose_companion_X_sq_add_one_ne :
    (X ^ 2 + 1 : ℤ[X]).companionᵀ ≠ (X ^ 2 + 1 : ℤ[X]).companion := by
  intro h
  have := congr(reindex (finCongr natDegree_X_sq_add_one)
    (finCongr natDegree_X_sq_add_one) $h)
  rw [← transpose_reindex, reindex_companion_X_sq_add_one] at this
  simpa using congr($this 0 1)

/-- The determinant of the companion matrix of `X² + 1` is its constant coefficient `1`. -/
theorem det_companion_X_sq_add_one : (X ^ 2 + 1 : ℤ[X]).companion.det = 1 := by
  rw [det_companion (by monicity!), natDegree_X_sq_add_one]
  simp

/-- The companion matrix of `X² + 1` has no eigenvalue over `ℚ`, since `X² + 1` has no rational
root. -/
theorem not_hasEigenvalue_companion_X_sq_add_one (μ : ℚ) :
    ¬Module.End.HasEigenvalue (toLin' (X ^ 2 + 1 : ℚ[X]).companion) μ := by
  rw [hasEigenvalue_toLin'_companion_iff (by monicity!)]
  simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_one]
  positivity

/-- The companion matrix of `1` is the empty matrix, and its characteristic polynomial is `1`. -/
theorem charpoly_companion_one : (1 : ℚ[X]).companion.charpoly = 1 :=
  charpoly_companion monic_one

end TauCeti.Examples.Companion
