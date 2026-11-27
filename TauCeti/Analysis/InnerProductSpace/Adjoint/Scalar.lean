/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Adjoints of scalar operators

On the scalar field `𝕜`, viewed as a one-dimensional inner product space over itself, the adjoint
of an operator `T : 𝕜 →L[𝕜] 𝕜` is its conjugate, `T† w = star (T (star w))`
(`ContinuousLinearMap.adjoint_apply_eq_star_apply_star`). So on scalar operators the
Hilbert-space adjoint agrees with Mathlib's intrinsic star `LinearMap.intrinsicStar`.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The adjoint of a scalar operator `T : 𝕜 →L[𝕜] 𝕜` is its conjugate,
`T† w = star (T (star w))`. -/
theorem adjoint_apply_eq_star_apply_star (T : 𝕜 →L[𝕜] 𝕜) (w : 𝕜) :
    adjoint T w = star (T (star w)) := by
  have h : star (adjoint T w) = T 1 * star w := by
    simpa only [RCLike.inner_apply, mul_one, one_mul, starRingEnd_apply] using
      adjoint_inner_left T 1 w
  have hT : T (star w) = T 1 * star w := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [hT, ← h, star_star]

end ContinuousLinearMap
