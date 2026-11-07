/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrals of shifted reciprocal powers

The positive reciprocal-square kernel has the antiderivative `-(a+t)⁻¹`. Its integral from zero
to a nonnegative endpoint is a difference of reciprocals, giving bounds for integrable tails.
-/

public section

open Set MeasureTheory intervalIntegral

namespace Real

/-- The reciprocal-square kernel has an elementary integral on each nonnegative interval. -/
theorem integral_one_div_add_sq {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∫ t : ℝ in 0..b, 1 / (a + t) ^ 2 = a⁻¹ - (a + b)⁻¹ := by
  have hd (t : ℝ) (ht : t ∈ uIcc 0 b) :
      HasDerivAt (fun u : ℝ ↦ -(a + u)⁻¹) (1 / (a + t) ^ 2) t := by
    rw [uIcc_of_le hb] at ht
    have h := (((hasDerivAt_id t).const_add a).inv
      (by linarith [ht.1] : a + t ≠ 0)).neg
    convert h using 1
    · ext u
      rfl
    · simp [neg_div]
  have hc : ContinuousOn (fun t : ℝ ↦ 1 / (a + t) ^ 2) (Icc 0 b) :=
    continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
      (fun t ht ↦ pow_ne_zero _ (by linarith [ht.1] : a + t ≠ 0))
  simpa [sub_eq_add_neg, add_comm] using integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable_of_Icc hb)

end Real
