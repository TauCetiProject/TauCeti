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
`ContinuousLinearMap.intervalIntegral_comp_comm`.

## Main results

* `ContinuousLinearMap.circleIntegral_comp_comm`: continuous linear maps commute with circle
  integrals.
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
