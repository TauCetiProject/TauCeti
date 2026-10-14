/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Absolute continuity of square root

The real square-root function is absolutely continuous on every finite interval, including
intervals meeting zero where its derivative is unbounded. This supplies the regularity needed
for square-root changes of parameter without a Lipschitz assumption.
-/

public section

open MeasureTheory Set

/-- Square root is absolutely continuous on every finite interval. -/
theorem Real.absolutelyContinuousOnInterval_sqrt (a b : ℝ) :
    AbsolutelyContinuousOnInterval Real.sqrt a b := by
  -- Real powers at negative inputs vanish for exponents ±1/2, since their cosine factor is zero.
  -- The power primitive therefore agrees with square root even at negative endpoints.
  let m : ℝ → ℝ := fun t ↦ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ))
  have hm : IntervalIntegrable m volume a b :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).const_mul _
  apply ((isometry_add_right (Real.sqrt a)).lipschitzWith.comp_absolutelyContinuousOnInterval
    (hm.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)).congr
  intro t _
  dsimp only [m, Function.comp_apply]
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))),
    Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  norm_num
  -- The remaining identity is
  -- `1/2 * ((t^(1/2) - a^(1/2))/(1/2)) + a^(1/2) = t^(1/2)`.
  ring
