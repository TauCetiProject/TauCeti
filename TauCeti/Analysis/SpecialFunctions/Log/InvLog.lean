/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The inverse logarithm and the iterated logarithm near the origin

This file complements Mathlib's `Mathlib.Analysis.SpecialFunctions.Log.InvLog`, which records the
discontinuities of `x ↦ (log x)⁻¹` at `±1`, with its behaviour at the origin, and bounds the
iterated logarithm `log log (1 / x)` near the origin:

* `Real.continuousAt_inv_log_zero`: `(log x)⁻¹ → 0` as `x → 0`, so with Mathlib's conventions
  `log 0 = 0` and `0⁻¹ = 0` the function `x ↦ (log x)⁻¹` is continuous at the origin;
* `Real.abs_log_log_inv_le`: for `0 ≤ x < e⁻¹`, `|log log (1 / x)| ≤ log (1 / x)`;
* `Real.tendsto_log_div_nhdsGT_zero`: for `δ > 0`, `log (δ / ε) → ∞` as `ε → 0⁺`.

The logarithmic quotient limit is adapted from Giada Franz’s formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory),
`ForTauCeti/Geometry/Manifold/Riemannian/Surface/LogCutoff/Tendsto.lean`.
-/

public section

open Filter Topology

namespace Real

/-- The function `x ↦ (log x)⁻¹` is continuous at the origin, where it takes the value `0`. -/
theorem continuousAt_inv_log_zero : ContinuousAt (fun x ↦ (log x)⁻¹) 0 := by
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
  simpa [Function.comp_def] using tendsto_inv_atBot_zero.comp tendsto_log_nhdsNE_zero

/-- For `0 ≤ x < e⁻¹`, `|log log (1 / x)| ≤ log (1 / x)`. -/
theorem abs_log_log_inv_le {x : ℝ} (hx : 0 ≤ x) (hx1 : x < exp (-1)) :
    |log (log x⁻¹)| ≤ -log x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have hlog : log x < -1 := (log_lt_iff_lt_exp hx).2 hx1
  have hx' : 1 < log x⁻¹ := by rw [log_inv]; linarith
  rw [abs_of_pos (log_pos hx')]
  have := log_le_sub_one_of_pos (zero_lt_one.trans hx')
  rw [log_inv] at this ⊢
  linarith

/-- For fixed `δ > 0`, the logarithmic scale `log (δ / ε)` tends to infinity as `ε → 0⁺`. -/
theorem tendsto_log_div_nhdsGT_zero {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ε ↦ Real.log (δ / ε)) (𝓝[>] 0) atTop := by
  have h := tendsto_atTop_add_const_left _ (Real.log δ)
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Function.comp_apply, Real.log_div hδ.ne' (ne_of_gt hε)]
  ring

end Real
