/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Traces of full circular traversals

The trace of a circular parametrization over `[0,2π]` is the sphere, for arbitrary signed radii.
-/

public section

open Set Metric

namespace Complex

/-- The full circular trace over `[0,2π]` is exactly the circle. -/
theorem image_circleMap_uIcc (c : ℂ) (R : ℝ) :
    circleMap c R '' uIcc 0 (2 * Real.pi) = sphere c |R| := by
  rw [uIcc_of_le Real.two_pi_pos.le]
  simpa only [zero_add, range_circleMap] using
    (periodic_circleMap c R).image_Icc (a := 0) Real.two_pi_pos

end Complex
