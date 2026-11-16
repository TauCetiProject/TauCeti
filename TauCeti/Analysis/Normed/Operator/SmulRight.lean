/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The norm of a rank-one map

For a continuous linear map `c` valued in a normed algebra `𝕜'` over the scalars and a vector `f`
of a normed `𝕜'`-space, the rank-one map `c.smulRight f : x ↦ c x • f` has norm at most `‖c‖ ‖f‖`
(`ContinuousLinearMap.norm_smulRight_le`). Mathlib's `ContinuousLinearMap.norm_smulRight_apply`
is the equality for scalar-valued `c`; the inequality applies for instance to the real-linear maps
`(ContinuousLinearMap.id ℝ ℂ).smulRight f` into a complex normed space.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 𝕜' E F : Type*} [NontriviallyNormedField 𝕜] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

/-- The rank-one map `x ↦ c x • f` has norm at most `‖c‖ ‖f‖`. -/
theorem norm_smulRight_le (c : E →L[𝕜] 𝕜') (f : F) : ‖c.smulRight f‖ ≤ ‖c‖ * ‖f‖ :=
  opNorm_le_bound _ (by positivity) fun x ↦ by
    rw [smulRight_apply, norm_smul, mul_right_comm]
    gcongr
    exact c.le_opNorm x

end ContinuousLinearMap
