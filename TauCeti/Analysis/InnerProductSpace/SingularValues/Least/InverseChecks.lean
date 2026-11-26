/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularValues.Least
public import TauCeti.Analysis.InnerProductSpace.SingularValues.Planar

/-!
# Checks for the minimal stretch: inverses and coordinate swaps

Worked examples for `LinearMap.minimalStretch` on a real inner product plane with an orthonormal
basis `e`, writing `toLin e e M` for the operator with matrix `M` in that basis:

* `diag(3, 1/2)` has inverse `diag(1/3, 2)` of operator norm `2`, and `ℓ(A) ‖A⁻¹‖ = 1`;
* composing `diag(3, 1/2)` on either side with the coordinate swap `e₀ ↔ e₁`, an isometry of
  determinant `-1`, keeps the minimal stretch `1/2`.
-/

public section

open Module Matrix LinearMap

namespace TauCeti.Examples.MinimalStretchInverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (e : OrthonormalBasis (Fin 2) ℝ E)

/-- The matrix `diag(1/3, 2)` is a right inverse of `diag(3, 1/2)`. -/
private theorem diagonal_three_half_mul_inverse :
    diagonal ![(3 : ℝ), 1 / 2] * diagonal ![1 / 3, 2] = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  fin_cases i <;> norm_num

/-- The minimal stretch of `diag(3, 1/2)` is `1/2`. -/
theorem minimalStretch_toLin_diagonal_three_half :
    (toLin e.toBasis e.toBasis (diagonal ![3, 1 / 2])).minimalStretch = 1 / 2 := by
  rw [minimalStretch_def, finrank_eq_card_basis e.toBasis,
    singularValues_toLin_diagonal_fin_two e (by norm_num)]
  norm_num

/-- The inverse `diag(1/3, 2)` of `diag(3, 1/2)` has operator norm `2 = 1 / ℓ(diag(3, 1/2))`. -/
example : ‖toContinuousLinearMap (toLin e.toBasis e.toBasis (diagonal ![(1 : ℝ) / 3, 2]))‖ = 2 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ
    (by rw [finrank_eq_card_basis e.toBasis, Fintype.card_fin])
  set A := toLinearEquiv e.toBasis _ (isUnit_det_of_right_inverse diagonal_three_half_mul_inverse)
  have hA : (A : E →ₗ[ℝ] E) = toLin e.toBasis e.toBasis (diagonal ![3, 1 / 2]) :=
    LinearMap.ext (toLinearEquiv_apply _ _ _)
  have hA_symm : (A.symm : E →ₗ[ℝ] E) = toLin e.toBasis e.toBasis (diagonal ![1 / 3, 2]) :=
    LinearMap.ext fun x => A.symm_apply_eq.2 <| by
      rw [toLinearEquiv_apply, ← LinearMap.comp_apply, ← toLin_mul,
        diagonal_three_half_mul_inverse, toLin_one, LinearMap.id_apply]
  have h := minimalStretch_mul_norm_symm A
  rw [hA, hA_symm, minimalStretch_toLin_diagonal_three_half] at h
  linarith

/-- Postcomposing `diag(3, 1/2)` with the coordinate swap keeps its minimal stretch `1/2`. -/
example : ((e.equiv e (Equiv.swap 0 1) : E →ₗ[ℝ] E) ∘ₗ
      toLin e.toBasis e.toBasis (diagonal ![3, 1 / 2])).minimalStretch = 1 / 2 := by
  rw [minimalStretch_linearIsometryEquiv_comp, minimalStretch_toLin_diagonal_three_half]

/-- Precomposing `diag(3, 1/2)` with the coordinate swap keeps its minimal stretch `1/2`. -/
example : (toLin e.toBasis e.toBasis (diagonal ![3, 1 / 2]) ∘ₗ
      (e.equiv e (Equiv.swap 0 1) : E →ₗ[ℝ] E)).minimalStretch = 1 / 2 := by
  rw [minimalStretch_comp_linearIsometryEquiv, minimalStretch_toLin_diagonal_three_half]

end TauCeti.Examples.MinimalStretchInverse
