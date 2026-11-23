/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Matrix
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
public import Mathlib.Analysis.Real.Sqrt

/-!
# Orthogonal matrices and the Spin projection: worked examples

The matrix orthogonal group `Aᵀ A = 1` describes the isometries of the standard sum-of-squares
form only. For `Q(a, b) = a² + 2 b²`, whose Gram matrix is `diag(1, 2)`, the coordinate swap
`!![0, 1; 1, 0]` is an orthogonal matrix, but the coordinate swap does not preserve `Q`: it sends
`Q(1, 0) = 1` to `Q(0, 1) = 2`. So a comparison with `Matrix.orthogonalGroup` that ignores the
Gram matrix would be wrong.

Over `ℝ` the isometry `(a, b) ↦ (a, √2 b)` carries `Q` to the sum of squares, and through it the
same swap matrix corresponds to the genuine isometry `(a, b) ↦ (√2 b, a / √2)` of `Q`, the map
`e₁ ↦ e₂ / √2`, `e₂ ↦ √2 e₁`.

Finally the scalar `-1` of the Spin group acts trivially on vectors, so its matrix is the identity
in every coordinate comparison, although it acts by `-1` on spinors.
-/

public section

open scoped Matrix

namespace TauCeti.Examples

/-- The matrix swapping the two coordinates of the plane. -/
abbrev swapMatrix (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

/-- The coordinate swap is an orthogonal matrix. -/
theorem swapMatrix_mem_orthogonalGroup (R : Type*) [CommRing R] :
    swapMatrix R ∈ Matrix.orthogonalGroup (Fin 2) R := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecHead, Matrix.vecTail]

/-- The coordinate swap, as an isometry of the standard sum-of-squares form on the plane. -/
noncomputable def swapOrthogonal {R : Type*} [CommRing R] (h2 : IsSMulRegular R (2 : R)) :
    QuadraticMap.orthogonalGroup (Matrix.toQuadraticForm' (1 : Matrix (Fin 2) (Fin 2) R)) :=
  (standardOrthogonalGroupEquiv h2).symm ⟨swapMatrix R, swapMatrix_mem_orthogonalGroup R⟩

/-- The coordinate swap, although an orthogonal matrix, does not preserve `a² + 2 b²`. -/
theorem swapOrthogonal_not_mem_orthogonalGroup_weightedSumSquares {R : Type*} [CommRing R]
    [Nontrivial R] (h2 : IsSMulRegular R (2 : R)) :
    (swapOrthogonal h2 : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R)) ∉
      QuadraticMap.orthogonalGroup (QuadraticMap.weightedSumSquares R ![(1 : R), 2]) := by
  intro h
  -- The swap sends `Q(1, 0) = 1` to `Q(0, 1) = 2`.
  have h' : (2 : R) = 1 := by
    simpa [swapOrthogonal, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two] using
      (QuadraticMap.mem_orthogonalGroup_iff.mp h) (Pi.single 0 1)
  exact one_ne_zero (by linear_combination h' : (1 : R) = 0)

/-- The isometry `(a, b) ↦ (a, √2 b)` from `a² + 2 b²` to the sum of squares on the real plane. -/
noncomputable def weightedSumSquaresOneTwoIsometryEquiv :
    (QuadraticMap.weightedSumSquares ℝ ![(1 : ℝ), 2]).IsometryEquiv
      (Matrix.toQuadraticForm' (1 : Matrix (Fin 2) (Fin 2) ℝ)) where
  toLinearEquiv := LinearEquiv.piCongrRight fun i ↦
    LinearEquiv.smulOfNeZero ℝ ℝ (![1, √2] i) (by fin_cases i <;> simp)
  map_app' x := by
    simp [toQuadraticForm'_one_apply, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two,
      dotProduct]
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring

/-- The isometry `(a, b) ↦ (a, √2 b)` scales the second coordinate by `√2`. -/
theorem weightedSumSquaresOneTwoIsometryEquiv_apply (x : Fin 2 → ℝ) :
    weightedSumSquaresOneTwoIsometryEquiv x = ![x 0, √2 * x 1] := by
  rw [← QuadraticMap.IsometryEquiv.coe_toLinearEquiv]
  ext i
  fin_cases i <;> simp [weightedSumSquaresOneTwoIsometryEquiv]

/-- The inverse isometry `(a, b) ↦ (a, b / √2)` divides the second coordinate by `√2`. -/
theorem weightedSumSquaresOneTwoIsometryEquiv_symm_apply (y : Fin 2 → ℝ) :
    weightedSumSquaresOneTwoIsometryEquiv.symm y = ![y 0, y 1 / √2] := by
  rw [QuadraticMap.IsometryEquiv.symm_apply_eq, weightedSumSquaresOneTwoIsometryEquiv_apply]
  ext i
  fin_cases i <;> simp [mul_div_cancel₀]

/-- Along `(a, b) ↦ (a, √2 b)`, the swap matrix corresponds to the isometry
`(a, b) ↦ (√2 b, a / √2)` of `a² + 2 b²`. -/
theorem orthogonalGroupEquivMatrix_symm_swapMatrix_apply (x : Fin 2 → ℝ) :
    ((orthogonalGroupEquivMatrix ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ)
        weightedSumSquaresOneTwoIsometryEquiv).symm
        ⟨swapMatrix ℝ, swapMatrix_mem_orthogonalGroup ℝ⟩ :
        (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)) x = ![√2 * x 1, x 0 / √2] := by
  rw [orthogonalGroupEquivMatrix_symm_apply, weightedSumSquaresOneTwoIsometryEquiv_apply,
    weightedSumSquaresOneTwoIsometryEquiv_symm_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The scalar `-1` of the Spin group has the identity matrix in every coordinate comparison. -/
theorem specialOrthogonalGroupEquivMatrix_spinToSpecialOrthogonal_negOne {K V n : Type*}
    [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V] [Fintype n] [DecidableEq n]
    {Q : QuadraticForm K V} (hQ : Q ≠ 0) (h2 : IsSMulRegular K (2 : K))
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n K))) :
    specialOrthogonalGroupEquivMatrix h2 e
        (CliffordAlgebra.spinToSpecialOrthogonal Q (CliffordAlgebra.spinGroup.negOne Q hQ)) =
      1 := by
  simp

end TauCeti.Examples
