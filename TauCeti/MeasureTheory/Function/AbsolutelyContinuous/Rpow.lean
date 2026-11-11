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
# Absolute continuity of real powers

A real power `x ↦ x ^ p` is absolutely continuous on a finite interval as soon as the exponent is
nonnegative or the interval avoids zero. For `0 < p < 1` this includes intervals meeting zero,
where the derivative is unbounded. Square root is the exponent `1/2` case.
These results supply the regularity of power changes of parameter without a Lipschitz assumption.
-/

public section

open MeasureTheory Set
open scoped Interval

/-- A real power is absolutely continuous on a finite interval, provided the exponent is
nonnegative or the interval avoids zero. -/
theorem Real.absolutelyContinuousOnInterval_rpow_const {p a b : ℝ}
    (h : 0 ≤ p ∨ (0 : ℝ) ∉ [[a, b]]) :
    AbsolutelyContinuousOnInterval (fun x : ℝ ↦ x ^ p) a b := by
  obtain rfl | hp := eq_or_ne p 0
  · simpa only [Real.rpow_zero] using
      (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
        (a := a) (b := b)
  have hexp : -1 < p - 1 ∨ p - 1 ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]] :=
    h.imp (fun h ↦ by linarith [h.lt_of_ne' hp]) (fun h ↦ ⟨by simpa using hp, h⟩)
  have hm : IntervalIntegrable (fun t : ℝ ↦ p * t ^ (p - 1)) volume a b :=
    (hexp.elim intervalIntegral.intervalIntegrable_rpow'
      fun h ↦ intervalIntegral.intervalIntegrable_rpow (.inr h.2)).const_mul _
  apply ((isometry_add_right (a ^ p)).lipschitzWith.comp_absolutelyContinuousOnInterval
    (hm.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)).congr
  intro t ht
  -- Mathlib's power primitive includes the cosine convention at negative real bases.
  rw [Function.comp_apply, intervalIntegral.integral_const_mul,
    integral_rpow (hexp.imp_right fun h ↦ ⟨h.1, fun h0 ↦ h.2 (uIcc_subset_uIcc_left ht h0)⟩),
    sub_add_cancel, mul_div_cancel₀ _ hp, sub_add_cancel]

/-- Square root is absolutely continuous on every finite interval. -/
theorem Real.absolutelyContinuousOnInterval_sqrt (a b : ℝ) :
    AbsolutelyContinuousOnInterval Real.sqrt a b :=
  (Real.absolutelyContinuousOnInterval_rpow_const (p := 1 / 2) (.inl (by positivity))).congr
    (fun t _ ↦ (Real.sqrt_eq_rpow t).symm)
