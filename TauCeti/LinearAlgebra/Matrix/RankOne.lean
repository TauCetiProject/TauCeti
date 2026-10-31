/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Inverses under rank-one perturbations

For an invertible matrix `A`, the Sherman–Morrison formula expresses the inverse of
`A + vecMulVec u v` in terms of `A⁻¹`. The scalar `1 + v ⬝ᵥ (A⁻¹ *ᵥ u)` is a unit exactly
when the perturbed matrix is invertible. This criterion lets applications establish the
validity of the update from invertibility of the two matrices, rather than assuming a
nonvanishing denominator separately.

The construction specializes Mathlib's matrix determinant lemma
`Matrix.det_add_replicateCol_mul_replicateRow` and Woodbury identity
`Matrix.add_mul_mul_inv_eq_sub` to a single column and row. It works over any commutative ring;
the inverse of the scalar is `Ring.inverse`, agreeing with the usual inverse over a field.

## References

* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press, 2013,
  §0.7.4 (the Sherman–Morrison–Woodbury formula).
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- A rank-one perturbation of an invertible matrix is invertible exactly when its
Sherman–Morrison denominator is a unit. -/
theorem isUnit_add_vecMulVec_iff (A : Matrix n n R) (hA : IsUnit A) (u v : n → R) :
    IsUnit (A + vecMulVec u v) ↔ IsUnit (1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) := by
  rw [isUnit_iff_isUnit_det, vecMulVec_eq Unit,
    det_add_replicateCol_mul_replicateRow ((isUnit_iff_isUnit_det A).1 hA)]
  have hd := (isUnit_iff_isUnit_det A).1 hA
  simp only [IsUnit.mul_iff, hd, true_and]
  rw [Matrix.mul_assoc, ← replicateCol_mulVec, det_unique]
  simp

/-- **Sherman–Morrison formula** over a commutative ring. The rank-one correction is the
outer product of the updated column and row, divided by the scalar denominator. -/
theorem inv_add_vecMulVec (A : Matrix n n R) (hA : IsUnit A) (u v : n → R)
    (hd : IsUnit (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))) :
    (A + vecMulVec u v)⁻¹ = A⁻¹ -
      Ring.inverse (1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) • vecMulVec (A⁻¹ *ᵥ u) (v ᵥ* A⁻¹) := by
  let U := replicateCol Unit u
  let V := replicateRow Unit v
  have hUV : U * V = vecMulVec u v := (vecMulVec_eq Unit u v).symm
  have hinner : 1 + V * A⁻¹ * U =
      diagonal (fun _ : Unit => 1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) := by
    dsimp only [U, V]
    rw [Matrix.mul_assoc, ← replicateCol_mulVec]
    ext i j
    simp
  have hu : IsUnit (1 + V * A⁻¹ * U) := by
    rw [hinner, isUnit_iff_isUnit_det, det_unique]
    simpa using hd
  have h := add_mul_mul_inv_eq_sub A U 1 V hA isUnit_one (by simpa using hu)
  simp only [Matrix.mul_one, inv_one] at h
  have hinv : (1 + V * A⁻¹ * U)⁻¹ =
      Ring.inverse (1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) • (1 : Matrix Unit Unit R) := by
    rw [hinner, inv_subsingleton, smul_one_eq_diagonal]
    simp
  rw [hUV, hinv] at h
  rw [h]
  congr 1
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_assoc A⁻¹ U V, hUV, mul_vecMulVec, vecMulVec_mul]

end Matrix
