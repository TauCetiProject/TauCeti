/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circles in punctured discs and half-annuli, and powers of circle maps

## Main results

* `TauCeti.circleMap_mem_ball_diff_singleton`: the circle of radius `r < R` about `z₀` lies in the
  punctured disc of radius `R`.
* `TauCeti.circleMap_zero_angle`, `TauCeti.circleMap_pi`: the circle of radius `r` about `z₀`
  passes through `z₀ + r` at angle `0` and through `z₀ - r` at angle `π`, the two ends of the
  diameter bounding the upper half-disc.
* `TauCeti.circleMap_mem_halfAnnulus`: a point of a circle of radius `r ∈ [a, b]` at an angle in
  `[0, π]` lies in the closed upper half-annulus of radii `a` and `b`.
* `TauCeti.contDiff_circleMap_zpow`: the integer powers `θ ↦ (R e^{iθ}) ^ k` are smooth.
-/

public section

open scoped Real

namespace TauCeti

open Complex Metric Set

/-- The circle of radius `0 < r < R` about `z₀` lies in the punctured disc of radius `R`. -/
theorem circleMap_mem_ball_diff_singleton {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (θ : ℝ) : circleMap z₀ r θ ∈ ball z₀ R \ {z₀} := by
  have hsph := mem_sphere.1 (circleMap_mem_sphere z₀ hr.le θ)
  refine ⟨mem_ball.2 (hsph.trans_lt hrR), fun h => ?_⟩
  rw [mem_singleton_iff.1 h, dist_self] at hsph
  exact hr.ne hsph

/-- The circle of radius `r` about `z₀` starts at `z₀ + r`, the right end of the diameter
bounding the upper half-disc. -/
@[simp]
theorem circleMap_zero_angle (z₀ : ℂ) (r : ℝ) : circleMap z₀ r 0 = z₀ + r := by
  simp [circleMap]

/-- The circle of radius `r` about `z₀` reaches `z₀ - r`, the left end of the diameter bounding
the upper half-disc, at angle `π`. -/
@[simp]
theorem circleMap_pi (z₀ : ℂ) (r : ℝ) : circleMap z₀ r π = z₀ - r := by
  simp [circleMap, Complex.exp_pi_mul_I, ← sub_eq_add_neg]

/-- A point of a circle of radius `r ∈ [a, b]`, `a ≥ 0`, about `z₀` at an angle `θ ∈ [0, π]` lies in
the closed upper half-annulus of radii `a` and `b` about `z₀`. -/
theorem circleMap_mem_halfAnnulus (z₀ : ℂ) {a b r θ : ℝ} (ha : 0 ≤ a) (hr : r ∈ Icc a b)
    (hθ : θ ∈ Icc 0 π) :
    circleMap z₀ r θ ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b ∧ 0 ≤ (z - z₀).im} := by
  have hr0 : 0 ≤ r := ha.trans hr.1
  refine ⟨?_, ?_, ?_⟩
  · simpa [abs_of_nonneg hr0] using hr.1
  · simpa [abs_of_nonneg hr0] using hr.2
  · simpa [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] using
      mul_nonneg hr0 (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)

/-- The integer powers `θ ↦ (R e^{iθ}) ^ k = R ^ k e^{ikθ}` of a circle about the origin are
smooth. -/
theorem contDiff_circleMap_zpow (R : ℝ) (k : ℤ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun θ ↦ circleMap 0 R θ ^ k := by
  simp_rw [circleMap_zero_zpow]
  exact (contDiff_circleMap 0 (R ^ k)).comp (contDiff_const.mul contDiff_id)

end TauCeti
