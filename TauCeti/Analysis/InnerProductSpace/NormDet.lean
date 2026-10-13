/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Continuity of the Jacobian `normDet`

For finite-dimensional real inner product spaces `U` and `V`, the `m`-dimensional Jacobian
`LinearMap.normDet` of a linear map `U →L[ℝ] V`, `m = dim U`, depends continuously on the map.
This follows from `normDet² = det (A† A)` (`ContinuousLinearMap.normDet_sq`).

## Main declarations

* `ContinuousLinearMap.continuous_normDet`: the Jacobian `normDet` is continuous.
-/

public section

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The `m`-dimensional Jacobian `normDet` of a linear map `U →L[ℝ] V`, `m = dim U`, depends
continuously on the map. -/
theorem ContinuousLinearMap.continuous_normDet :
    Continuous fun A : U →L[ℝ] V => A.normDet := by
  have h (A : U →L[ℝ] V) : A.normDet = √((ContinuousLinearMap.adjoint A ∘L A).det) := by
    rw [← A.normDet_sq, RCLike.ofReal_real_eq_id, id, Real.sqrt_sq A.normDet_nonneg]
  simp_rw [h]
  exact (ContinuousLinearMap.continuous_det.comp
    (ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id)).sqrt
