/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Absolute continuity of positive real powers

Positive real powers are absolutely continuous on every finite interval, including intervals
meeting zero where the derivative may be unbounded. Square root is the exponent `1/2` case.
These results supply the regularity of power changes of parameter without a Lipschitz assumption.
-/

public section

open MeasureTheory Set

/-- A positive real power is absolutely continuous on every finite interval. -/
theorem Real.absolutelyContinuousOnInterval_rpow {p : ℝ} (hp : 0 < p) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x : ℝ ↦ x ^ p) a b := by
  let m : ℝ → ℝ := fun t ↦ p * t ^ (p - 1)
  have hexp : (-1 : ℝ) < p - 1 := by linarith
  have hm : IntervalIntegrable m volume a b :=
    (intervalIntegral.intervalIntegrable_rpow' hexp).const_mul _
  apply ((isometry_add_right (a ^ p)).lipschitzWith.comp_absolutelyContinuousOnInterval
    (hm.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)).congr
  intro t _
  dsimp only [m, Function.comp_apply]
  -- Mathlib's power primitive includes the cosine convention at negative real bases.
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hexp), sub_add_cancel]
  -- The remaining identity is `p * ((t^p - a^p)/p) + a^p = t^p`; `p ≠ 0` cancels its denominator.
  field_simp [hp.ne']
  ring

/-- Square root is absolutely continuous on every finite interval. -/
theorem Real.absolutelyContinuousOnInterval_sqrt (a b : ℝ) :
    AbsolutelyContinuousOnInterval Real.sqrt a b :=
  (Real.absolutelyContinuousOnInterval_rpow (p := 1 / 2) (by norm_num) a b).congr
    (fun t _ ↦ (Real.sqrt_eq_rpow t).symm)
