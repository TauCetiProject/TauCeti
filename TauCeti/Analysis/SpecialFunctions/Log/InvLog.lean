/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.InvLog

/-!
# The inverse logarithm and the iterated logarithm near the origin

This file complements Mathlib's `Mathlib.Analysis.SpecialFunctions.Log.InvLog`, which records the
discontinuities of `x ↦ (log x)⁻¹` at `±1`, with its behaviour at the origin, and bounds the
iterated logarithm `log log (1 / x)` near the origin:

* `Real.continuousAt_inv_log_zero`: `(log x)⁻¹ → 0` as `x → 0`, so with Mathlib's conventions
  `log 0 = 0` and `0⁻¹ = 0` the function `x ↦ (log x)⁻¹` is continuous at the origin;
* `Real.abs_log_log_inv_le`: for `0 ≤ x < e⁻¹`, `|log log (1 / x)| ≤ log (1 / x)`.

It also records the calculus of the radial profile `r ↦ log log (c / r)`, which has a logarithmic
singularity at the origin:

* `Real.log_div_pos`: for `0 < r < c` the inner logarithm `log (c / r)` is positive;
* `Real.hasDerivAt_log_log_div`: the derivative of `log log (c / r)` is `-(r log (c / r))⁻¹`
  wherever `c / r ∉ {0, 1, -1}`;
* `Real.tendsto_log_log_div`: `log log (c / r) → ∞` as `r → 0`, for `c ≠ 0`.
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

/-- For `0 < r < c` the logarithm `log (c / r)` is positive. -/
theorem log_div_pos {c r : ℝ} (h0 : 0 < r) (hr : r < c) : 0 < log (c / r) :=
  log_pos ((one_lt_div h0).2 hr)

/-- The derivative of the radial profile: `d/dr log log (c / r) = -(r log (c / r))⁻¹` wherever
`c / r ∉ {0, 1, -1}`. -/
theorem hasDerivAt_log_log_div {c r : ℝ} (hc : c ≠ 0) (hr : r ≠ 0) (hrc : r ≠ c)
    (hrc' : r ≠ -c) :
    HasDerivAt (fun s : ℝ => log (log (c / s))) (-(r * log (c / r))⁻¹) r := by
  have hdiv : HasDerivAt (fun s : ℝ => c / s) (-(c / r ^ 2)) r := by
    simpa only [div_eq_mul_inv, neg_mul_eq_mul_neg, ← inv_pow] using
      (hasDerivAt_inv hr).const_mul c
  have h1 : c / r ≠ 1 := fun h => hrc ((div_eq_one_iff_eq hr).1 h).symm
  have h2 : c / r ≠ -1 := fun h => hrc' (by rw [div_eq_iff hr] at h; linarith)
  refine ((hasDerivAt_log_log (div_ne_zero hc hr) h1 h2).comp r hdiv).congr_deriv ?_
  field_simp

/-- The radial profile `log log (c / r)` tends to `∞` as `r → 0`, for `c ≠ 0`. -/
theorem tendsto_log_log_div {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun r : ℝ => log (log (c / r))) (𝓝[≠] 0) atTop := by
  have h : Tendsto (fun r : ℝ => log c + -log r) (𝓝[≠] 0) atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_neg_atBot_atTop.comp tendsto_log_nhdsNE_zero)
  refine tendsto_log_atTop.comp (h.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [log_div hc hr, sub_eq_add_neg]

end Real
