/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Complex quotients under a proximity inequality

If `y` is closer to `x` than `x` is to `w`, the quotient `(y-w)/(x-w)` lies in the slit plane.
This geometric fact does not depend on curve regularity.
-/

public section

open Complex

namespace TauCeti

/-- The quotient under the proximity inequality lies in the slit plane. -/
theorem _root_.TauCeti.div_sub_mem_slitPlane_of_dist_lt_dist
    {x y w : ℂ} (h : dist y x < dist x w) :
    (y - w) / (x - w) ∈ slitPlane := by
  have hne : x - w ≠ 0 := sub_ne_zero.mpr
    (dist_pos.mp (lt_of_le_of_lt dist_nonneg h))
  have hsub : (y - w) / (x - w) - 1 = (y - x) / (x - w) := by
    field_simp
    ring
  apply Complex.ball_one_subset_slitPlane
  rw [Metric.mem_ball, dist_eq_norm, hsub, norm_div, div_lt_one (norm_pos_iff.mpr hne)]
  simpa only [dist_eq_norm] using h

end TauCeti
