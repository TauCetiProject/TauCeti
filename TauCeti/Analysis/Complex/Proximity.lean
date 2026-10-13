/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Complex quotients under a proximity inequality

If `y` is closer to `x` than `x` is to `w`, the quotient `(y-w)/(x-w)` has positive real part.
In particular it lies in the slit plane. This geometric fact does not depend on curve regularity.
-/

public section

open Complex

namespace TauCeti

/-- A relative displacement smaller than the distance to the pole gives a quotient with positive
real part. -/
theorem _root_.TauCeti.re_div_sub_pos_of_dist_lt_dist
    {x y w : ℂ} (h : dist y x < dist x w) :
    0 < ((y - w) / (x - w)).re := by
  have hne : x - w ≠ 0 := sub_ne_zero.mpr
    (dist_pos.mp (lt_of_le_of_lt dist_nonneg h))
  have hsub : (y - w) / (x - w) - 1 = (y - x) / (x - w) := by
    field_simp
    ring
  have hn : ‖(y - w) / (x - w) - 1‖ < 1 := by
    rw [hsub, norm_div, div_lt_one (norm_pos_iff.mpr hne)]
    simpa only [dist_eq_norm] using h
  have hre := re_le_norm (1 - (y - w) / (x - w))
  rw [norm_sub_rev] at hre
  simp only [sub_re, one_re] at hre
  linarith

/-- The quotient under the proximity inequality lies in the slit plane. -/
theorem _root_.TauCeti.div_sub_mem_slitPlane_of_dist_lt_dist
    {x y w : ℂ} (h : dist y x < dist x w) :
    (y - w) / (x - w) ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (TauCeti.re_div_sub_pos_of_dist_lt_dist h))

end TauCeti
