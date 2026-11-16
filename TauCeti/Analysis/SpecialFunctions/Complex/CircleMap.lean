/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circles in punctured discs, arclength circles, and powers of circle maps

## Main results

* `TauCeti.circleMap_mem_ball_diff_singleton`: the circle of radius `r < R` about `z₀` lies in the
  punctured disc of radius `R`.
* `TauCeti.hasDerivAt_circleMap_div`: the circle of radius `R` parametrized by arclength,
  `s ↦ c + R e^{i s / R}`, has unit velocity `e^{i s / R} i`.
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

/-- The circle of radius `R ≠ 0` about `c`, parametrized by arclength as
`s ↦ c + R e^{i s / R}`, has velocity `e^{i s / R} i`. -/
theorem hasDerivAt_circleMap_div (c : ℂ) {R : ℝ} (hR : R ≠ 0) (s : ℝ) :
    HasDerivAt (fun s : ℝ ↦ circleMap c R (s / R)) (circleMap 0 1 (s / R) * I) s := by
  refine ((hasDerivAt_circleMap c R (s / R)).scomp s
    ((hasDerivAt_id s).div_const R)).congr_deriv ?_
  rw [circleMap_zero, circleMap_zero, real_smul]
  push_cast
  field_simp [ofReal_ne_zero.2 hR]

/-- The integer powers `θ ↦ (R e^{iθ}) ^ k = R ^ k e^{ikθ}` of a circle about the origin are
smooth. -/
theorem contDiff_circleMap_zpow (R : ℝ) (k : ℤ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun θ ↦ circleMap 0 R θ ^ k := by
  simp_rw [circleMap_zero_zpow]
  exact (contDiff_circleMap 0 (R ^ k)).comp (contDiff_const.mul contDiff_id)

end TauCeti
