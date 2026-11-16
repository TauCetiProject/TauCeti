/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Circle integrals: linear maps, the angle interval and the radius

This file records that continuous linear maps commute with Mathlib's circle integrals
`∮ z in C(c, R), f z`, the circle-integral analogue of
`ContinuousLinearMap.intervalIntegral_comp_comm`. It also writes a circle integral over the angle
interval `[-π, π]` instead of `[0, 2π]`, and shows that for `f` continuous on a closed disc the
circle integrals over the concentric circles depend continuously on the radius up to the
boundary circle. By periodicity of `circleMap` a circle integral may also be computed over
any parameter interval `[a, a + 2π]`.

## Main results

* `ContinuousLinearMap.circleIntegral_comp_comm`: continuous linear maps commute with circle
  integrals.
* `TauCeti.circleIntegral_eq_intervalIntegral_add_two_pi`: a circle integral may be computed over
  any parameter interval of length `2π`.
* `TauCeti.integral_neg_pi_pi_eq_circleIntegral`: a circle integral as an integral over
  `[-π, π]`.
* `ContinuousOn.continuousOn_circleIntegral`: for `f` continuous on the closed disc
  `|z - c| ≤ R`, the map `r ↦ ∮ z in C(c, r), f z` is continuous on `[0, R]`.
-/

public section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Continuous linear maps commute with circle integrals. -/
theorem ContinuousLinearMap.circleIntegral_comp_comm [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R) :
    ∮ z in C(c, R), L (f z) = L (∮ z in C(c, R), f z) := by
  rw [circleIntegral, circleIntegral, ← L.intervalIntegral_comp_comm hf.out]
  simp only [map_smul]

open Complex Metric Set
open scoped Real

/-- By periodicity of `circleMap`, a circle integral may be computed over any parameter interval
`[a, a + 2π]` instead of `[0, 2π]`. -/
theorem TauCeti.circleIntegral_eq_intervalIntegral_add_two_pi (f : ℂ → E) (c : ℂ) (R a : ℝ) :
    (∮ z in C(c, R), f z) = ∫ θ in a..a + 2 * π, deriv (circleMap c R) θ • f (circleMap c R θ) := by
  have hper : Function.Periodic
      (fun θ ↦ deriv (circleMap c R) θ • f (circleMap c R θ)) (2 * π) := fun θ ↦ by
    simp only [deriv_circleMap, periodic_circleMap 0 R θ, periodic_circleMap c R θ]
  simpa [circleIntegral] using hper.intervalIntegral_add_eq 0 a

/-- A circle integral written over the angle interval `[-π, π]`. -/
theorem TauCeti.integral_neg_pi_pi_eq_circleIntegral (f : ℂ → E) (c : ℂ) (R : ℝ) :
    (∫ θ in -π..π, (circleMap 0 R θ * I) • f (circleMap c R θ)) = ∮ z in C(c, R), f z := by
  rw [TauCeti.circleIntegral_eq_intervalIntegral_add_two_pi f c R (-π),
    show -π + 2 * π = π by ring]
  simp only [deriv_circleMap]

/-- For `f` continuous on the closed disc `|z - c| ≤ R`, the circle integrals
`r ↦ ∮ z in C(c, r), f z` over the concentric circles are continuous in the radius on `[0, R]`,
including at the boundary circle. -/
theorem ContinuousOn.continuousOn_circleIntegral {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : ContinuousOn f (closedBall c R)) :
    ContinuousOn (fun r ↦ ∮ z in C(c, r), f z) (Icc 0 R) := by
  rcases lt_or_ge R 0 with hR | hR
  · simp [Icc_eq_empty_of_lt hR]
  -- Clamp the radius to `[0, R]`, so that the circles stay in the closed disc.
  set ρ : ℝ → ℝ := fun r ↦ max 0 (min r R) with hρ
  have hmem (r θ : ℝ) : circleMap c (ρ r) θ ∈ closedBall c R := by
    rw [mem_closedBall, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
      abs_of_nonneg (le_max_left _ _)]
    exact max_le hR (min_le_right _ _)
  have hG : Continuous fun p : ℝ × ℝ ↦
      deriv (circleMap c (ρ p.1)) p.2 • f (circleMap c (ρ p.1) p.2) := by
    simp only [deriv_circleMap]
    have hcm : Continuous fun p : ℝ × ℝ ↦ circleMap c (ρ p.1) p.2 := by
      unfold circleMap
      fun_prop
    have hcm0 : Continuous fun p : ℝ × ℝ ↦ circleMap 0 (ρ p.1) p.2 := by
      unfold circleMap
      fun_prop
    exact (hcm0.mul continuous_const).smul (hf.comp_continuous hcm fun p ↦ hmem p.1 p.2)
  have hcont : Continuous fun r ↦ ∮ z in C(c, ρ r), f z :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG 0 (2 * π)
  refine hcont.continuousOn.congr fun r hr ↦ ?_
  simp [hρ, hr.1, hr.2]
