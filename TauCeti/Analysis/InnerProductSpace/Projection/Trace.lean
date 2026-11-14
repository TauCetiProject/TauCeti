/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.Matrix.EuclideanLin
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.Matrix.Frobenius
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Traces and matrix norms of orthogonal projections

`Submodule.trace_starProjection` identifies the trace of an orthogonal projection with the
dimension of its range. In orthonormal coordinates, the same dimension is the sum of the squared
entry norms (`Submodule.sum_norm_sq_toMatrix_starProjection`). These identities identify the
mean and the Frobenius parameter in quadratic-form estimates for distances to subspaces.
The Euclidean-coordinate forms identify the trace and quadratic form of the matrix representing
the projection onto the orthogonal complement.

## References

* R. Vershynin, *High-Dimensional Probability*, 2018, §6.3.
-/

public section

noncomputable section

namespace Submodule

open scoped Matrix

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  (U : Submodule 𝕜 E)

variable [FiniteDimensional 𝕜 E]

/-- The trace of the orthogonal projection onto `U` is its dimension. -/
@[simp]
theorem trace_starProjection :
    LinearMap.trace 𝕜 E U.starProjection.toLinearMap = (Module.finrank 𝕜 U : 𝕜) := by
  have hU : IsIdempotentElem U.starProjection.toLinearMap :=
    U.isSymmetricProjection_starProjection.isIdempotentElem
  have hr : LinearMap.range U.starProjection.toLinearMap = U := U.range_starProjection
  have h := (LinearMap.IsIdempotentElem.isProj_range _ hU).trace
  rwa [hr] at h

omit [FiniteDimensional 𝕜 E] in
/-- In an orthonormal basis, the squared Frobenius norm of an orthogonal projection is the
dimension of its range. -/
theorem sum_norm_sq_toMatrix_starProjection [U.HasOrthogonalProjection] [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, ∑ j, ‖LinearMap.toMatrix b.toBasis b.toBasis U.starProjection.toLinearMap i j‖ ^ 2 =
      (Module.finrank 𝕜 U : ℝ) := by
  have : FiniteDimensional 𝕜 E := b.toBasis.finiteDimensional_of_finite
  let A := LinearMap.toMatrix b.toBasis b.toBasis U.starProjection.toLinearMap
  have hA : A.IsHermitian := (LinearMap.isHermitian_toMatrix_iff b).2 U.starProjection_isSymmetric
  have hAA : A * A = A := by
    rw [← LinearMap.toMatrix_mul]
    rw [U.isSymmetricProjection_starProjection.isIdempotentElem.eq]
  rw [← Matrix.re_trace_mul_conjTranspose_self, hA.eq, hAA,
    ← LinearMap.trace_eq_matrix_trace, trace_starProjection]
  simp

/-- The trace of the Euclidean matrix of an orthogonal projection is its dimension. -/
@[simp]
theorem trace_toEuclideanCLM_symm_starProjection [Fintype ι] [DecidableEq ι]
    (U : Submodule 𝕜 (EuclideanSpace 𝕜 ι)) :
    ((Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm U.starProjection).trace =
      (Module.finrank 𝕜 U : 𝕜) := by
  rw [ContinuousLinearMap.toEuclideanCLM_symm_eq_toMatrix,
    ← LinearMap.trace_eq_matrix_trace, U.trace_starProjection]

/-- The squared Frobenius norm of the Euclidean matrix of an orthogonal projection is the
dimension of its range. -/
theorem sum_norm_sq_toEuclideanCLM_symm_starProjection [Fintype ι] [DecidableEq ι]
    (U : Submodule 𝕜 (EuclideanSpace 𝕜 ι)) :
    ∑ i, ∑ j, ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm U.starProjection i j‖ ^ 2 =
      (Module.finrank 𝕜 U : ℝ) := by
  rw [ContinuousLinearMap.toEuclideanCLM_symm_eq_toMatrix]
  exact U.sum_norm_sq_toMatrix_starProjection (EuclideanSpace.basisFun ι 𝕜)

open scoped Matrix.Norms.L2Operator in
/-- The Euclidean operator norm of the matrix of an orthogonal projection is at most one. -/
theorem l2_opNorm_toEuclideanCLM_symm_starProjection_le [Fintype ι] [DecidableEq ι]
    (U : Submodule 𝕜 (EuclideanSpace 𝕜 ι)) :
    ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm U.starProjection‖ ≤ 1 := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM, StarAlgEquiv.apply_symm_apply]
  exact U.starProjection_norm_le

/-- The quadratic form of the Euclidean matrix of the orthogonal-complement projection is
squared distance to the subspace. -/
theorem re_star_dotProduct_toEuclideanCLM_symm_starProjection_orthogonal
    [Fintype ι] [DecidableEq ι] (U : Submodule 𝕜 (EuclideanSpace 𝕜 ι)) (x : ι → 𝕜) :
    RCLike.re (star x ⬝ᵥ (Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm
      Uᗮ.starProjection *ᵥ x) = Metric.infDist (WithLp.toLp 2 x) (U : Set _) ^ 2 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp,
    ← Matrix.toEuclideanCLM_toLp, StarAlgEquiv.apply_symm_apply]
  exact U.re_inner_starProjection_orthogonal_eq_infDist_sq _

end Submodule
