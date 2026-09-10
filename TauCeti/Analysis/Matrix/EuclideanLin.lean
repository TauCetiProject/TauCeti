/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The map of a matrix on Euclidean space

Two ingredients of a linear change of variables on `EuclideanSpace 𝕜 ι`.

Pulling the quadratic form `x ↦ ⟪x, B x⟫` of a square matrix `B` back along the linear map of a
rectangular matrix `A` gives the quadratic form of the congruent matrix `Aᴴ * B * A`. This is
the change-of-variables identity behind every computation of a quadratic statistic after a linear
transformation of the underlying vector.

An invertible square matrix induces not just a map but a continuous linear equivalence, whose
inverse is the map of the inverse matrix. That is the form a substitution needs: it supplies the
inverse substitution and, through `LinearMap.det_toLpLin`, the Jacobian.

## Main results

* `Matrix.inner_toEuclideanLin_toEuclideanLin` — the quadratic form of `B` at `A x` is the
  quadratic form of `Aᴴ * B * A` at `x`;
* `Matrix.toEuclideanCLE` — the continuous linear equivalence of an invertible matrix, with its
  `apply`, `symm_apply`, coercion and determinant lemmas.
-/

public section

open scoped InnerProductSpace

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- Pulling the quadratic form of `B` back along the linear map of `A` gives the quadratic form
of the congruent matrix `Aᴴ * B * A`. -/
theorem inner_toEuclideanLin_toEuclideanLin (A : Matrix κ ι 𝕜) (B : Matrix κ κ 𝕜)
    (x : EuclideanSpace 𝕜 ι) :
    ⟪A.toEuclideanLin x, B.toEuclideanLin (A.toEuclideanLin x)⟫_𝕜 =
      ⟪x, (Aᴴ * B * A).toEuclideanLin x⟫_𝕜 := by
  rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [toEuclideanLin, toLpLin_mul_same, LinearMap.comp_apply]

section Invertible

/-- **The continuous linear equivalence of an invertible matrix** on Euclidean space, defined
when `A.det` is a unit. It acts as `A` does, and its inverse is the map of `A⁻¹`, so a change of
variables along it substitutes `A⁻¹`. -/
noncomputable def toEuclideanCLE (A : Matrix ι ι 𝕜) (hA : IsUnit A.det) :
    EuclideanSpace 𝕜 ι ≃L[𝕜] EuclideanSpace 𝕜 ι :=
  (toEuclideanCLM (𝕜 := 𝕜) A).toContinuousLinearEquivOfDetNeZero <| by
    rw [ContinuousLinearMap.det, coe_toEuclideanCLM_eq_toEuclideanLin, LinearMap.det_toLpLin]
    exact hA.ne_zero

/-- The equivalence acts as the matrix does. -/
@[simp]
theorem toEuclideanCLE_apply (A : Matrix ι ι 𝕜) (hA : IsUnit A.det) (x : EuclideanSpace 𝕜 ι) :
    A.toEuclideanCLE hA x = A.toEuclideanLin x := by
  rw [toEuclideanCLE, ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply,
    ← coe_toEuclideanCLM_eq_toEuclideanLin, ContinuousLinearMap.coe_coe]

/-- The inverse of the equivalence is the map of the inverse matrix. -/
@[simp]
theorem toEuclideanCLE_symm_apply (A : Matrix ι ι 𝕜) (hA : IsUnit A.det)
    (y : EuclideanSpace 𝕜 ι) : (A.toEuclideanCLE hA).symm y = A⁻¹.toEuclideanLin y := by
  rw [ContinuousLinearEquiv.symm_apply_eq, toEuclideanCLE_apply]
  simp only [← coe_toEuclideanCLM_eq_toEuclideanLin, ContinuousLinearMap.coe_coe]
  rw [← mul_apply_eq_comp, ← map_mul, mul_nonsing_inv _ hA, map_one, one_apply_eq_self]

/-- The determinant of the equivalence is the determinant of the matrix. -/
@[simp]
theorem det_toEuclideanCLE (A : Matrix ι ι 𝕜) (hA : IsUnit A.det) :
    LinearMap.det (A.toEuclideanCLE hA : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι) = A.det := by
  have hcoe : (A.toEuclideanCLE hA : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι)
      = A.toEuclideanLin := LinearMap.ext fun x => A.toEuclideanCLE_apply hA x
  rw [hcoe, LinearMap.det_toLpLin]

end Invertible

end Matrix
