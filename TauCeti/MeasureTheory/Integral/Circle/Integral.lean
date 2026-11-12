/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circle integrals and continuous linear maps

This file records that continuous linear maps commute with Mathlib's circle integrals
`∮ z in C(c, R), f z`, the circle-integral analogue of
`ContinuousLinearMap.intervalIntegral_comp_comm`, and that by periodicity of `circleMap` a circle
integral may be computed over any parameter interval `[a, a + 2π]`.

## Main results

* `ContinuousLinearMap.circleIntegral_comp_comm`: continuous linear maps commute with circle
  integrals.
* `circleIntegral_eq_intervalIntegral_add_two_pi`: a circle integral may be computed over any
  parameter interval of length `2π`.
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

open Real in
/-- By periodicity of `circleMap`, a circle integral may be computed over any parameter interval
`[a, a + 2π]` instead of `[0, 2π]`. -/
theorem circleIntegral_eq_intervalIntegral_add_two_pi (f : ℂ → E) (c : ℂ) (R a : ℝ) :
    (∮ z in C(c, R), f z) = ∫ θ in a..a + 2 * π, deriv (circleMap c R) θ • f (circleMap c R θ) := by
  have hper : Function.Periodic
      (fun θ ↦ deriv (circleMap c R) θ • f (circleMap c R θ)) (2 * π) := fun θ ↦ by
    simp only [deriv_circleMap, periodic_circleMap 0 R θ, periodic_circleMap c R θ]
  simpa [circleIntegral] using hper.intervalIntegral_add_eq 0 a
