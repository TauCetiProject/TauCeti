/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The determinant along a scalar shift

The determinant of a continuous endomorphism `A + t • id` of a normed space depends
continuously on `t`.

## Main results

* `ContinuousLinearMap.tendsto_det_add_smul_id`: `det (A + t • id) → det A` as `t → 0`.
-/

public section

open Filter Topology

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- `det (A + t • id) → det A` as `t → 0`. -/
theorem tendsto_det_add_smul_id (A : E →L[𝕜] E) :
    Tendsto (fun t : 𝕜 => (A + t • ContinuousLinearMap.id 𝕜 E).det) (𝓝 0) (𝓝 A.det) := by
  have : Continuous fun t : 𝕜 => (A + t • ContinuousLinearMap.id 𝕜 E).det :=
    ContinuousLinearMap.continuous_det.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  simpa using this.tendsto 0

end ContinuousLinearMap
