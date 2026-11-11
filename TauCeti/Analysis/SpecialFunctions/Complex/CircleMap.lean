/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Circles in punctured discs

## Main results

* `TauCeti.circleMap_mem_ball_diff_singleton`: the circle of radius `r < R` about `z₀` lies in the
  punctured disc of radius `R`.
-/

public section

namespace TauCeti

open Complex Metric Set

/-- The circle of radius `0 < r < R` about `z₀` lies in the punctured disc of radius `R`. -/
theorem circleMap_mem_ball_diff_singleton {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (θ : ℝ) : circleMap z₀ r θ ∈ ball z₀ R \ {z₀} := by
  have hsph := mem_sphere.1 (circleMap_mem_sphere z₀ hr.le θ)
  refine ⟨mem_ball.2 (hsph.trans_lt hrR), fun h => ?_⟩
  rw [mem_singleton_iff.1 h, dist_self] at hsph
  exact hr.ne hsph

end TauCeti
