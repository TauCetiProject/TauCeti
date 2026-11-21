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
import TauCeti.Analysis.Complex.SlitPlane

/-!
# Circles in annuli and punctured discs, arclength circles, and powers of circle maps

## Main results

* `TauCeti.norm_circleMap_sub_center`: the circle of radius `R ≥ 0` about `c` has distance `R`
  from `c`.
* `TauCeti.re_one_sub_mul_circleMap_pos`: a scaled circle subtracted from `1` lies in the right
  half-plane when its radius after scaling is less than `1`.
* `TauCeti.circleMap_norm_arg`, `TauCeti.circleMap_norm_sub_arg_sub`: polar coordinates about
  `c`, so every point `w` is `circleMap c ‖w - c‖ (arg (w - c))`.
* `TauCeti.hasDerivAt_circleMap_radius`: along the ray at angle `θ`, the radius derivative of
  `circleMap c R θ` is `e^{iθ}`.
* `TauCeti.circleMap_mem_setOf_le_norm_sub_le`: a circle of radius `r ∈ [a, b]`, `0 ≤ a`, about
  `z₀` lies in the closed annulus `a ≤ |z - z₀| ≤ b`.
* `TauCeti.circleMap_mem_ball_diff_singleton`: the circle of radius `r < R` about `z₀` lies in the
  punctured disc of radius `R`.
* `TauCeti.hasDerivAt_circleMap_div`: the circle of radius `R` parametrized by arclength,
  `s ↦ c + R e^{i s / R}`, has unit velocity `e^{i s / R} i`.
* `TauCeti.contDiff_circleMap_zpow`: the integer powers `θ ↦ (R e^{iθ}) ^ k` are smooth.
-/

public section

namespace TauCeti

open Complex Metric Set

/-- The circle of radius `R ≥ 0` about `c` has distance `R` from `c`. -/
theorem norm_circleMap_sub_center (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) :
    ‖circleMap c R θ - c‖ = R := by
  rw [circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg hR]

/-- Subtracting a point of the scaled circle `z * circleMap 0 ρ θ` from `1` gives a point
in the open right half-plane whenever the scaled radius is less than `1`. -/
theorem re_one_sub_mul_circleMap_pos {z : ℂ} {ρ : ℝ} (hzρ : ‖z‖ * |ρ| < 1) (θ : ℝ) :
    0 < (1 - z * circleMap 0 ρ θ).re := by
  apply re_pos_of_norm_sub_one_lt_one
  simpa [norm_mul, norm_circleMap_zero] using hzρ

/-- Polar coordinates about `c`: the point at radius `‖w‖` and angle `arg w` about `c` is
`c + w`. -/
theorem circleMap_norm_arg (c w : ℂ) : circleMap c ‖w‖ (arg w) = c + w := by
  rw [circleMap, norm_mul_exp_arg_mul_I]

/-- Polar coordinates about `c`: every point `w` lies on the circle of radius `‖w - c‖` about `c`,
at the angle `arg (w - c)`. -/
theorem circleMap_norm_sub_arg_sub (c w : ℂ) : circleMap c ‖w - c‖ (arg (w - c)) = w := by
  rw [circleMap_norm_arg, add_sub_cancel]

/-- Along the ray at angle `θ` about `c`, the derivative of `R ↦ circleMap c R θ` is
`e^{iθ}`. -/
theorem hasDerivAt_circleMap_radius (c : ℂ) (R θ : ℝ) :
    HasDerivAt (fun R : ℝ ↦ circleMap c R θ) (exp (θ * I)) R := by
  have hfun : (fun R : ℝ ↦ circleMap c R θ) = fun R : ℝ ↦ c + (R : ℂ) * exp (θ * I) := by
    funext R
    rw [circleMap]
  rw [hfun]
  simpa only [ofReal_one, one_mul] using
    ((hasDerivAt_id' R).ofReal_comp.mul_const (exp (θ * I))).const_add c

/-- A circle of radius `r ∈ [a, b]` about `z₀`, with `0 ≤ a`, lies in the closed annulus
`a ≤ |z - z₀| ≤ b`. -/
theorem circleMap_mem_setOf_le_norm_sub_le {z₀ : ℂ} {a b r : ℝ} (ha : 0 ≤ a) (hr : r ∈ Icc a b)
    (θ : ℝ) : circleMap z₀ r θ ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} := by
  rw [mem_ofPred_eq, norm_circleMap_sub_center z₀ (ha.trans hr.1)]
  exact hr

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
