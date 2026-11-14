/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.Matrix.Frobenius
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Quadratic forms of orthogonal projections

`Submodule.trace_starProjection` identifies the trace of an orthogonal projection with the
dimension of its range. In orthonormal coordinates, the same dimension is the sum of the squared
entry norms (`Submodule.sum_norm_sq_toMatrix_starProjection`). These identities identify the
mean and the Frobenius parameter in quadratic-form estimates for distances to subspaces.
`Submodule.re_inner_starProjection_orthogonal_eq_infDist_sq` represents squared distance as the
quadratic form of the orthogonal-complement projection.

## References

* R. Vershynin, *High-Dimensional Probability*, 2018, §6.3.
-/

public section

noncomputable section

namespace Submodule

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  (U : Submodule 𝕜 E)

/-- Squared distance is the quadratic form of the orthogonal-complement projection. -/
theorem re_inner_starProjection_orthogonal_eq_infDist_sq [U.HasOrthogonalProjection] (x : E) :
    RCLike.re (inner 𝕜 x (Uᗮ.starProjection x)) = Metric.infDist x (U : Set E) ^ 2 := by
  have hn : ‖Uᗮ.orthogonalProjectionOnto x‖ = Metric.infDist x (U : Set E) := by
    rw [← Submodule.norm_coe, coe_orthogonalProjectionOnto_apply,
      norm_starProjection_eq_infDist, orthogonal_orthogonal]
  rw [← Uᗮ.inner_starProjection_left_eq_right]
  simpa only [hn] using Uᗮ.re_inner_starProjection_eq_normSq x

variable [FiniteDimensional 𝕜 E]

/-- The trace of the orthogonal projection onto `U` is its dimension. -/
@[simp]
theorem trace_starProjection :
    LinearMap.trace 𝕜 E U.starProjection.toLinearMap = (Module.finrank 𝕜 U : 𝕜) := by
  have hU : IsIdempotentElem U.starProjection.toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap U.isIdempotentElem_starProjection
  have hr : LinearMap.range U.starProjection.toLinearMap = U := U.range_starProjection
  have h := (LinearMap.IsIdempotentElem.isProj_range _ hU).trace
  rwa [hr] at h

/-- In an orthonormal basis, the squared Frobenius norm of an orthogonal projection is the
dimension of its range. -/
theorem sum_norm_sq_toMatrix_starProjection [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, ∑ j, ‖LinearMap.toMatrix b.toBasis b.toBasis U.starProjection.toLinearMap i j‖ ^ 2 =
      (Module.finrank 𝕜 U : ℝ) := by
  let A := LinearMap.toMatrix b.toBasis b.toBasis U.starProjection.toLinearMap
  have hA : A.IsHermitian := (LinearMap.isHermitian_toMatrix_iff b).2 U.starProjection_isSymmetric
  have hAA : A * A = A := by
    rw [← LinearMap.toMatrix_mul]
    exact congrArg (LinearMap.toMatrix b.toBasis b.toBasis)
      (congrArg ContinuousLinearMap.toLinearMap U.isIdempotentElem_starProjection)
  rw [← Matrix.re_trace_mul_conjTranspose_self, hA.eq, hAA,
    ← LinearMap.trace_eq_matrix_trace, trace_starProjection]
  simp

end Submodule
