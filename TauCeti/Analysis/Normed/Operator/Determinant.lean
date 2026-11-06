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

The determinant of a continuous endomorphism `A + t • id` of a real normed space depends
continuously on `t`. Hence a strict inequality between `det A` and a real number `a` persists for
all small shifts `t`.

## Main results

* `ContinuousLinearMap.tendsto_det_add_smul_id`: `det (A + t • id) → det A` as `t → 0`.
* `ContinuousLinearMap.eventually_lt_det_add_smul_id`: if `a < det A`, then `a < det (A + t • id)`
  for all small `t`.
* `ContinuousLinearMap.eventually_det_add_smul_id_lt`: if `det A < a`, then `det (A + t • id) < a`
  for all small `t`.
-/

public section

open Filter Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `det (A + t • id) → det A` as `t → 0`. -/
theorem tendsto_det_add_smul_id (A : E →L[ℝ] E) :
    Tendsto (fun t : ℝ => (A + t • ContinuousLinearMap.id ℝ E).det) (𝓝 0) (𝓝 A.det) := by
  have : Continuous fun t : ℝ => (A + t • ContinuousLinearMap.id ℝ E).det :=
    ContinuousLinearMap.continuous_det.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  simpa using this.tendsto 0

/-- If `a < det A`, then `a < det (A + t • id)` for all small `t`. -/
theorem eventually_lt_det_add_smul_id {A : E →L[ℝ] E} {a : ℝ} (h : a < A.det) :
    ∀ᶠ t : ℝ in 𝓝 0, a < (A + t • ContinuousLinearMap.id ℝ E).det :=
  (tendsto_det_add_smul_id A).eventually (lt_mem_nhds h)

/-- If `det A < a`, then `det (A + t • id) < a` for all small `t`. -/
theorem eventually_det_add_smul_id_lt {A : E →L[ℝ] E} {a : ℝ} (h : A.det < a) :
    ∀ᶠ t : ℝ in 𝓝 0, (A + t • ContinuousLinearMap.id ℝ E).det < a :=
  (tendsto_det_add_smul_id A).eventually (gt_mem_nhds h)

end ContinuousLinearMap
