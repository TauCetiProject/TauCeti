/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.HermitianDilation.Basic
public import TauCeti.Analysis.InnerProductSpace.Adjoint

/-!
# The operator norm of a Hermitian dilation

For a rectangular linear map `A` between finite-dimensional real or complex inner product
spaces, its Hermitian dilation on `WithLp 2 (E × F)` preserves the operator norm.
In particular, the difference of two dilations has exactly the same operator norm as the
difference of the rectangular maps.

Moreover, a nonnegative pointwise norm bound holds for `A` if and only if it holds for
its Hermitian dilation.

## References

* Y. Yu, T. Wang, and R. J. Samworth, *A useful variant of the Davis--Kahan theorem for
  statisticians*, Biometrika 102 (2015), 315--323.
* AIQ-Kitware DKPS formalization (Apache-2.0):
  https://github.com/AIQ-Kitware/aiq-dkps-formalization
  (`YuWangSamworth2015/YuWangSamworth2015/Core/SingularSubspace.lean`).
-/

public section

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The square of the dilation's norm is the sum of the squared norms of its block outputs. -/
theorem norm_hermitianDilation_apply_sq (A : E →ₗ[𝕜] F) (z : WithLp 2 (E × F)) :
    ‖A.hermitianDilation z‖ ^ 2 = ‖A z.fst‖ ^ 2 + ‖A.adjoint z.snd‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [hermitianDilation_apply, WithLp.toLp_fst, WithLp.toLp_snd,
    WithLp.ofLp_fst, WithLp.ofLp_snd]
  ring

/-- Every nonnegative pointwise norm bound for a rectangular linear map also bounds its
Hermitian dilation on the Hilbert direct sum. -/
theorem norm_hermitianDilation_apply_le (A : E →ₗ[𝕜] F) {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ x : E, ‖A x‖ ≤ c * ‖x‖) (z : WithLp 2 (E × F)) :
    ‖A.hermitianDilation z‖ ≤ c * ‖z‖ := by
  have hA_sq : ‖A z.fst‖ ^ 2 ≤ (c * ‖z.fst‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).2 (hA z.fst)
  have hAdj_sq : ‖A.adjoint z.snd‖ ^ 2 ≤ (c * ‖z.snd‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).2
      (LinearMap.norm_adjoint_apply_le hc hA z.snd)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).1
  rw [A.norm_hermitianDilation_apply_sq, mul_pow, WithLp.prod_norm_sq_eq_of_L2 z]
  nlinarith [hA_sq, hAdj_sq]

/-- A pointwise norm bound for a Hermitian dilation also bounds the underlying map. -/
theorem norm_apply_le_of_hermitianDilation (A : E →ₗ[𝕜] F) {c : ℝ}
    (hD : ∀ z : WithLp 2 (E × F), ‖A.hermitianDilation z‖ ≤ c * ‖z‖)
    (x : E) : ‖A x‖ ≤ c * ‖x‖ := by
  -- On the first summand, the dilation sends (x, 0) to (0, A x).
  have hnorm :
      ‖A.hermitianDilation (WithLp.toLp 2 (x, (0 : F)))‖ = ‖A x‖ := by
    simp [hermitianDilation_apply, WithLp.norm_toLp_snd]
  simpa only [hnorm, WithLp.norm_toLp_fst] using
    (hD (WithLp.toLp 2 (x, (0 : F))))

/-- A nonnegative pointwise norm bound holds for a rectangular map if and only if it holds
for its Hermitian dilation. -/
theorem norm_hermitianDilation_apply_le_iff (A : E →ₗ[𝕜] F) {c : ℝ} (hc : 0 ≤ c) :
    (∀ z : WithLp 2 (E × F), ‖A.hermitianDilation z‖ ≤ c * ‖z‖) ↔
      (∀ x : E, ‖A x‖ ≤ c * ‖x‖) := by
  constructor
  · exact A.norm_apply_le_of_hermitianDilation
  · exact A.norm_hermitianDilation_apply_le hc

/-- Hermitian dilation is an isometry for the operator norm. Continuous linear maps give
operator norms to the finite-dimensional algebraic linear maps on both sides. -/
@[simp]
theorem norm_toContinuousLinearMap_hermitianDilation (A : E →ₗ[𝕜] F) :
    ‖A.hermitianDilation.toContinuousLinearMap‖ = ‖A.toContinuousLinearMap‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    simpa only [LinearMap.coe_toContinuousLinearMap'] using
      (A.norm_hermitianDilation_apply_le (norm_nonneg _)
        (fun x => by simpa only [LinearMap.coe_toContinuousLinearMap'] using
          A.toContinuousLinearMap.le_opNorm x) z)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa only [LinearMap.coe_toContinuousLinearMap'] using
      (A.norm_apply_le_of_hermitianDilation
        (fun z => by simpa only [LinearMap.coe_toContinuousLinearMap'] using
          A.hermitianDilation.toContinuousLinearMap.le_opNorm z) x)

/-- The operator norm of the difference of Hermitian dilations equals the operator norm
of the original rectangular perturbation. -/
@[simp]
theorem norm_toContinuousLinearMap_hermitianDilation_sub (A B : E →ₗ[𝕜] F) :
    ‖A.hermitianDilation.toContinuousLinearMap - B.hermitianDilation.toContinuousLinearMap‖ =
      ‖A.toContinuousLinearMap - B.toContinuousLinearMap‖ := by
  simpa only [← map_sub, ← hermitianDilation_sub] using
    (norm_toContinuousLinearMap_hermitianDilation (A - B))

end LinearMap
