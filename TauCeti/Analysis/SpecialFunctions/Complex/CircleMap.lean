/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circles in annuli and punctured discs, arclength circles, and powers of circle maps

## Main results

* `TauCeti.norm_circleMap_sub_center`: the circle of radius `R ≥ 0` about `c` has distance `R`
  from `c`.
* `TauCeti.circleMap_norm_arg`, `TauCeti.circleMap_norm_sub_arg_sub`: polar coordinates about
  `c`, so every point `w` is `circleMap c ‖w - c‖ (arg (w - c))`.
* `TauCeti.hasDerivAt_circleMap_radius`: along the ray at angle `θ`, the radius derivative of
  `circleMap c R θ` is `e^{iθ}`.
* `TauCeti.circleMap_mem_setOf_le_norm_sub_le`: a circle of radius `r ∈ [a, b]`, `0 ≤ a`, about
  `z₀` lies in the closed annulus `a ≤ |z - z₀| ≤ b`.
* `TauCeti.circleMap_im`: the imaginary part of `circleMap c r θ` is `c.im + r sin θ`.
* `TauCeti.isClosed_upperHalfAnnulus`: the closed upper half of the annulus `a ≤ |z - z₀| ≤ b` is
  closed.
* `TauCeti.circleMap_mem_upperHalfAnnulus`: for `θ ∈ [0, π]`, the point at angle `θ` of a circle
  of radius `r ∈ [a, b]`, `0 ≤ a`, about `z₀` lies in the closed upper half of the annulus.
* `TauCeti.circleMap_mem_ball_diff_singleton`: the circle of radius `r < R` about `z₀` lies in the
  punctured disc of radius `R`.
* `TauCeti.hasDerivAt_circleMap_div`: the circle of radius `R` parametrized by arclength,
  `s ↦ c + R e^{i s / R}`, has unit velocity `e^{i s / R} i`.
* `TauCeti.contDiff_circleMap_zpow`: the integer powers `θ ↦ (R e^{iθ}) ^ k` are smooth.
* `TauCeti.circleMap_pi_sub_two_arctan`: rational Cayley parametrization of the unit circle via
  `π - 2 * arctan (a / b)`.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped Real

/-- The circle of radius `R ≥ 0` about `c` has distance `R` from `c`. -/
theorem norm_circleMap_sub_center (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) :
    ‖circleMap c R θ - c‖ = R := by
  rw [circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg hR]

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

/-- The imaginary part of the point at angle `θ` of the circle of radius `r` about `c`. -/
theorem circleMap_im (c : ℂ) (r θ : ℝ) : (circleMap c r θ).im = c.im + r * Real.sin θ := by
  rw [← circleMap_zero_im, ← add_im, ← circleMap_sub_center c, add_sub_cancel]

/-- The closed upper half `{z | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}` of the annulus of
radii `a` and `b` about `z₀` is closed. -/
theorem isClosed_upperHalfAnnulus (z₀ : ℂ) (a b : ℝ) :
    IsClosed {z : ℂ | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} := by
  have hn : Continuous (fun z : ℂ ↦ ‖z - z₀‖) := by fun_prop
  exact (isClosed_le continuous_const continuous_im).inter
    ((isClosed_le continuous_const hn).inter (isClosed_le hn continuous_const))

/-- For `θ ∈ [0, π]`, the point at angle `θ` of a circle of radius `r ∈ [a, b]` about `z₀`, with
`0 ≤ a`, lies in the closed upper half of the annulus `a ≤ |z - z₀| ≤ b`. -/
theorem circleMap_mem_upperHalfAnnulus {z₀ : ℂ} {a b r θ : ℝ} (ha : 0 ≤ a) (hr : r ∈ Icc a b)
    (hθ : θ ∈ Icc 0 π) :
    circleMap z₀ r θ ∈ {z : ℂ | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} := by
  refine ⟨?_, circleMap_mem_setOf_le_norm_sub_le ha hr θ⟩
  rw [circleMap_im, le_add_iff_nonneg_right]
  exact mul_nonneg (ha.trans hr.1) (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)

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

/-- Rational Cayley parametrization of the unit circle: for `b ≠ 0`,
`circleMap 0 1 (π - 2 * arctan (a / b)) = (a + b I) / (a - b I)`. -/
theorem circleMap_pi_sub_two_arctan {a b : ℝ} (hb : b ≠ 0) :
    circleMap 0 1 (Real.pi - 2 * Real.arctan (a / b)) = ((a : ℂ) + b * I) / ((a : ℂ) - b * I) := by
  set β := Real.arctan (a / b)
  have htan := Real.tan_arctan (a / b)
  rw [Real.tan_eq_sin_div_cos, div_eq_div_iff (Real.cos_arctan_pos _).ne' hb] at htan
  have hsin' : (b : ℂ) * Real.sin β = a * Real.cos β := by exact_mod_cast (by linarith : b * _ = _)
  have hden₂ : (a : ℂ) - b * I ≠ 0 := fun h ↦ hb <| by
    simpa using (congrArg Complex.im (sub_eq_zero.1 h)).symm
  have harg : ((Real.pi - 2 * β : ℝ) : ℂ) * I =
      ↑Real.pi * I + (((-β : ℝ) : ℂ) * I - (β : ℂ) * I) := by
    push_cast; ring
  have hexp : circleMap 0 1 (Real.pi - 2 * β) = -exp (((-β : ℝ) : ℂ) * I) / exp ((β : ℂ) * I) := by
    simp only [circleMap, zero_add, ofReal_one, one_mul]
    rw [harg, Complex.exp_add, exp_pi_mul_I, Complex.exp_sub]; ring
  rw [hexp, div_eq_div_iff (Complex.exp_ne_zero _) hden₂, exp_ofReal_mul_I, exp_ofReal_mul_I,
    Real.cos_neg, Real.sin_neg, ofReal_neg]
  linear_combination 2 * hsin' - (2 * b * Real.sin β : ℂ) * I_mul_I

end TauCeti
