/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# A regularized reciprocal

The functions `x ↦ x / (x² + ε)` converge pointwise to the totalized reciprocal as positive `ε`
tends to zero. Unlike the reciprocal, each regularizing function is continuous everywhere.
This limit is useful for regularizing inverses through functional calculus, including at zero.
-/

public section

open Filter Topology

namespace Real

/-- As positive `ε` tends to zero, `x / (x² + ε)` tends to `x⁻¹`, also when `x = 0`. -/
theorem tendsto_div_sq_add_nhdsGT_zero (x : ℝ) :
    Tendsto (fun ε : ℝ ↦ x / (x ^ 2 + ε)) (𝓝[>] 0) (𝓝 x⁻¹) := by
  by_cases hx : x = 0
  · simp [hx]
  · have he : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) :=
      continuousWithinAt_id.tendsto
    convert (tendsto_const_nhds (x := x)).div
      ((tendsto_const_nhds (x := x ^ 2)).add he)
      (by simpa using pow_ne_zero 2 hx) using 1
    simp [div_eq_mul_inv, pow_two, hx]

end Real
