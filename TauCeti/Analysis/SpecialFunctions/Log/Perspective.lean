/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import TauCeti.Analysis.Convex.Perspective

/-!
# Monotonicity of a logarithmic perspective

The logarithmic penalty `u log (1 + H/u)` increases with the scale `u` for a fixed
nonnegative `H`. The statement includes `u = 0`, where the penalty is zero.
-/

public section

namespace Real

/-- The perspective of `log (1 + ·)` increases in its scale on the nonnegative half-line. -/
theorem monotoneOn_mul_log_one_add_div {H : ℝ} (hH : 0 ≤ H) :
    MonotoneOn (fun u : ℝ ↦ u * log (1 + H / u)) (Set.Ici 0) := by
  intro u hu v hv huv
  rcases hu.eq_or_lt with hu | hu
  · subst u
    exact (zero_mul _).trans_le
      (mul_nonneg hv (log_nonneg (le_add_of_nonneg_right (div_nonneg hH hv))))
  have hconv : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ ↦ -log (1 + x)) := by
    have heq : (fun x : ℝ ↦ -log (1 + x)) = (-log) ∘ (fun x ↦ x + 1) := by
      ext x
      simp only [Function.comp_apply, Pi.neg_apply, add_comm]
    rw [heq]
    exact ((strictConcaveOn_log_Ioi.concaveOn.translate_left 1).subset
      (fun x hx ↦ add_pos_of_pos_of_nonneg zero_lt_one hx) (convex_Ici (0 : ℝ))).neg
  have h := hconv.antitoneOn_mul_map_div (by simp) hH hu (hu.trans_le huv) huv
  simpa only [mul_neg, neg_le_neg_iff] using h

end Real
