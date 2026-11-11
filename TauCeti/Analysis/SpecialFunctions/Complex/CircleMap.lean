/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Circles in punctured discs, and powers of circle maps

## Main results

* `TauCeti.circleMap_mem_ball_diff_singleton`: the circle of radius `r < R` about `z₀` lies in the
  punctured disc of radius `R`.
* `TauCeti.contDiff_circleMap_zpow`: the integer powers `θ ↦ (R e^{iθ}) ^ k` are smooth.
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

/-- The integer powers `θ ↦ (R e^{iθ}) ^ k = R ^ k e^{ikθ}` of a circle about the origin are
smooth. -/
theorem contDiff_circleMap_zpow (R : ℝ) (k : ℤ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun θ ↦ circleMap 0 R θ ^ k := by
  have : (fun θ : ℝ ↦ circleMap 0 R θ ^ k) = fun θ : ℝ ↦ (R : ℂ) ^ k * exp (k * ((θ : ℂ) * I)) := by
    ext θ
    simp [circleMap, mul_zpow, ← exp_int_mul]
  rw [this]
  exact contDiff_const.mul (contDiff_exp.comp (contDiff_const.mul (ofRealCLM.contDiff.mul
    contDiff_const)))

end TauCeti
