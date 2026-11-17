/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Continuity of real norm-power radial maps

For any real seminormed space `E` and exponent `α > -1`, the radial vector field
`x ↦ ‖x‖ ^ α • x` is continuous everywhere, including at points of zero seminorm: away from zero
seminorm it is a product of continuous maps, and near `‖x‖ = 0` its seminorm equals `‖y‖ ^ (α + 1)`
with `α + 1 > 0`, which tends to zero.

## Main declarations

* `TauCeti.continuous_norm_rpow_smul`: continuity of `x ↦ ‖x‖ ^ α • x` on any real seminormed space
  for `-1 < α`.
-/

public section

namespace TauCeti

open Filter Topology

/-- For `-1 < α`, the radial power map `x ↦ ‖x‖ ^ α • x` is continuous on every real seminormed
space, including where `‖x‖ = 0`. -/
theorem continuous_norm_rpow_smul {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} (hα : -1 < α) : Continuous (fun x : E => ‖x‖ ^ α • x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : ‖x‖ = 0
  · rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hx_smul : ‖‖x‖ ^ α • x‖ = 0 := by rw [norm_smul, hx, mul_zero]
    have hcont : Continuous (fun y : E => ‖y‖ ^ (α + 1)) :=
      (continuous_norm (E := E)).rpow_const fun _ => Or.inr (by linarith : 0 ≤ α + 1)
    have hpow : Tendsto (fun y : E => ‖y‖ ^ (α + 1)) (𝓝 x) (𝓝 0) := by
      have ht := (hcont.continuousAt (x := x)).tendsto
      rwa [hx, Real.zero_rpow (by linarith : α + 1 ≠ 0)] at ht
    refine squeeze_zero (fun _ => norm_nonneg _) (fun y => ?_) hpow
    calc ‖‖y‖ ^ α • y - ‖x‖ ^ α • x‖
        ≤ ‖‖y‖ ^ α • y‖ + ‖‖x‖ ^ α • x‖ := norm_sub_le _ _
      _ = ‖‖y‖ ^ α • y‖ := by rw [hx_smul, add_zero]
      _ = ‖y‖ ^ (α + 1) := by
          by_cases hy : ‖y‖ = 0
          · rw [norm_smul, hy, mul_zero, Real.zero_rpow (by linarith : α + 1 ≠ 0)]
          · rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg y) α),
              Real.rpow_add_one hy]
  · exact (continuous_norm.continuousAt.rpow_const (Or.inl hx)).smul continuousAt_id

end TauCeti
