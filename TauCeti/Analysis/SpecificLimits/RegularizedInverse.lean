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

The functions `a ↦ a / (a + e)²` regularize the reciprocal of a nonnegative `a` in the same way:
for `a, e ≥ 0` they are bounded by `a⁻¹`, and they tend to `a⁻¹` as `e → 0`, also at `a = 0`
(`Real.div_add_sq_le_inv`, `Real.tendsto_div_add_sq_nhds_zero`). With `a = ‖x‖²` they are the
squared norms of the regularized shrinkage fields `(‖x‖² + e)⁻¹ x` of the James–Stein estimator.
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

/-- For `a, e ≥ 0`, the regularized reciprocal `a / (a + e)²` is at most `a⁻¹`; at `a = 0` both
sides are `0`. -/
theorem div_add_sq_le_inv {a e : ℝ} (ha : 0 ≤ a) (he : 0 ≤ e) : a / (a + e) ^ 2 ≤ a⁻¹ := by
  rcases ha.eq_or_lt with rfl | ha
  · simp
  rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ ha]
  nlinarith

/-- As `e` tends to zero, `a / (a + e)²` tends to `a⁻¹`, also when `a = 0`. -/
theorem tendsto_div_add_sq_nhds_zero (a : ℝ) :
    Tendsto (fun e : ℝ ↦ a / (a + e) ^ 2) (𝓝 0) (𝓝 a⁻¹) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have h : Tendsto (fun e : ℝ ↦ (a + e) ^ 2) (𝓝 0) (𝓝 ((a + 0) ^ 2)) :=
    (tendsto_const_nhds.add tendsto_id).pow 2
  convert tendsto_const_nhds.div h (by simpa using ha) using 2
  rw [add_zero, sq, div_mul_cancel_left₀ ha]

end Real
