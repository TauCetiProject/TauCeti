/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Model
public import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# Determinants at the boundary hyperplane

A linear map preserving the boundary hyperplane has determinant equal to its normal factor
times the determinant of its restriction. This is the algebra behind outward-first orientation.
-/

public section

noncomputable section

namespace TauCeti

/-- The determinant splits into the normal factor and the boundary restriction determinant. -/
theorem det_eq_normal_mul_boundary {n : ℕ}
    (A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {a : ℝ} (hA : ∀ v, A v 0 = a * v 0) :
    A.det = a * ((euclideanHalfSpaceBoundaryProj n).comp
      (A.comp (euclideanHalfSpaceBoundaryParam n))).det := by
  let b := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  let c := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let T := LinearMap.toMatrix b b A.toLinearMap
  have ht (i j : Fin (n + 1)) : T i j = A (b j) i := by
    simp [T, b, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
  have hp (j : Fin n) : euclideanHalfSpaceBoundaryParam n (c j) = b j.succ := by
    ext i
    refine Fin.cases ?_ (fun k ↦ ?_) i <;>
      simp [b, c, EuclideanSpace.basisFun_apply]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b]
  change T.det = _
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hzero : ∀ j : Fin n, T 0 j.succ = 0 := by
    intro j
    rw [ht, hA]
    simp [b, EuclideanSpace.basisFun_apply]
  simp only [hzero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero,
    pow_zero, one_mul, Fin.succAbove_zero]
  have h00 : T 0 0 = a := by
    rw [ht, hA]
    simp [b, EuclideanSpace.basisFun_apply]
  rw [h00]
  congr 1
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix c]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, ht, LinearMap.toMatrix_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  rw [hp]
  simp [c, OrthonormalBasis.coe_toBasis_repr_apply]

/-- Expansion in the normal row computes the determinant of an outward-first family. -/
theorem det_cons_boundary {n : ℕ} (v : EuclideanSpace ℝ (Fin (n + 1)))
    (w : Fin n → EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det
      (Fin.cons v (fun i ↦ euclideanHalfSpaceBoundaryParam n (w i))) =
        v 0 * (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det w := by
  rw [Module.Basis.det_apply, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, Fin.cons_succ, euclideanHalfSpaceBoundaryParam_apply_zero,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul,
    Fin.cons_zero, Fin.succAbove_zero]
  rw [Module.Basis.det_apply]
  congr 1
  congr 1
  ext i j
  simp [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]

end TauCeti
