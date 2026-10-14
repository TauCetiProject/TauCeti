/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Full circular traversals as absolutely continuous curves

Circular parametrizations are absolutely continuous on every finite angular interval. A full
traversal is closed and its trace is the sphere, for arbitrary signed radii.
-/

public section

open Set Metric

namespace Complex

/-- Every circular parameterization is absolutely continuous on every finite angular interval. -/
theorem absolutelyContinuousOnInterval_circleMap (c : ℂ) (R a b : ℝ) :
    AbsolutelyContinuousOnInterval (circleMap c R) a b :=
  (lipschitzWith_circleMap c R).lipschitzOnWith.absolutelyContinuousOnInterval

/-- A full circular traversal is closed. -/
theorem circleMap_zero_eq_two_pi (c : ℂ) (R : ℝ) :
    circleMap c R 0 = circleMap c R (2 * Real.pi) := by
  simpa only [zero_add] using (periodic_circleMap c R 0).symm


/-- The full circular trace over `[0,2π]` is exactly the circle. -/
theorem image_circleMap_uIcc (c : ℂ) (R : ℝ) :
    circleMap c R '' uIcc 0 (2 * Real.pi) = sphere c |R| := by
  apply Subset.antisymm
  · exact (image_subset_range _ _).trans_eq (range_circleMap c R)
  · rw [← image_circleMap_Ioc c R]
    exact image_mono (by rw [uIcc_of_le Real.two_pi_pos.le]; exact Ioc_subset_Icc_self)

end Complex
