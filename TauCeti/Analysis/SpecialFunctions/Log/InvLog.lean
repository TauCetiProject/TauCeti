/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LHopital
import TauCeti.Analysis.SpecialFunctions.Log.Deriv

/-!
# The inverse logarithm and the iterated logarithm near the origin

This file complements Mathlib's `Mathlib.Analysis.SpecialFunctions.Log.InvLog`, which records the
discontinuities of `x ↦ (log x)⁻¹` at `±1`, with its behaviour at the origin, the continuous
extension of `(log t)⁻¹ - (t - 1)⁻¹` across `t = 1`, and bounds on the iterated logarithm
`log log (1 / x)` near the origin:

* `Real.continuousAt_inv_log_zero`: `(log x)⁻¹ → 0` as `x → 0`, so with Mathlib's conventions
  `log 0 = 0` and `0⁻¹ = 0` the function `x ↦ (log x)⁻¹` is continuous at the origin;
* `Real.continuousAt_inv_log_sub_inv_sub_one_zero`,
  `Real.tendsto_inv_log_sub_inv_sub_one_nhdsNE_one`,
  `Real.continuousOn_update_inv_log_sub_inv_sub_one`: `(log t)⁻¹ - (t - 1)⁻¹` is continuous at
  `0` (with value `1`), tends to `1 / 2` as `t → 1`, `t ≠ 1`, and extends continuously across
  `t = 1` on `[0, ∞)`;
* `Real.abs_log_log_inv_le`: for `0 ≤ x < e⁻¹`, `|log log (1 / x)| ≤ log (1 / x)`.

It also records the calculus of the radial profile `r ↦ log log (c / r)`, which for `c ≠ 0` has
an iterated-logarithmic singularity at the origin:

* `Real.hasDerivAt_log_log_const_div`: the derivative of `log log (c / r)` is `-(r log (c / r))⁻¹`
  wherever `r ∉ {0, c, -c}`;
* `Real.tendsto_log_log_const_div_nhdsNE_zero`: `log log (c / r) → ∞` as `r → 0`, for `c ≠ 0`.
-/

public section

open Filter Set Topology

namespace Real

/-- The function `x ↦ (log x)⁻¹` is continuous at the origin, where it takes the value `0`. -/
theorem continuousAt_inv_log_zero : ContinuousAt (fun x ↦ (log x)⁻¹) 0 := by
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
  simpa [Function.comp_def] using tendsto_inv_atBot_zero.comp tendsto_log_nhdsNE_zero

/-- `t ↦ (log t)⁻¹ - (t - 1)⁻¹` is continuous at `0`, where it takes the value `1`. -/
theorem continuousAt_inv_log_sub_inv_sub_one_zero :
    ContinuousAt (fun t : ℝ ↦ (log t)⁻¹ - (t - 1)⁻¹) 0 :=
  continuousAt_inv_log_zero.sub (by fun_prop (disch := norm_num))

/-- `(log t)⁻¹ - (t - 1)⁻¹ → 1 / 2` as `t → 1`, `t ≠ 1`. -/
theorem tendsto_inv_log_sub_inv_sub_one_nhdsNE_one :
    Tendsto (fun t : ℝ ↦ (log t)⁻¹ - (t - 1)⁻¹) (𝓝[≠] 1) (𝓝 (1 / 2)) := by
  have hnum : Tendsto (fun t : ℝ ↦ (t - 1 - log t) / (t - 1) ^ 2) (𝓝[≠] 1) (𝓝 (1 / 2)) := by
    refine HasDerivAt.lhopital_zero_nhdsNE (f' := fun t : ℝ ↦ 1 - t⁻¹)
      (g' := fun t : ℝ ↦ 2 * (t - 1)) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds one_pos)] with t ht
      exact ((hasDerivAt_id' t).sub_const 1).sub (hasDerivAt_log ht.ne')
    · filter_upwards with t
      simpa using ((hasDerivAt_id' t).sub_const 1).fun_pow 2
    · filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 1)
      exact mul_ne_zero two_ne_zero (sub_ne_zero.mpr ht)
    · have hc : ContinuousAt (fun t : ℝ ↦ t - 1 - log t) 1 :=
        (continuousAt_id.sub continuousAt_const).sub (continuousAt_log one_ne_zero)
      simpa [log_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · have hc : ContinuousAt (fun t : ℝ ↦ (t - 1) ^ 2) 1 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · have hc : ContinuousAt (fun t : ℝ ↦ (2 * t)⁻¹) 1 := by fun_prop (disch := norm_num)
      have hlim : Tendsto (fun t : ℝ ↦ (2 * t)⁻¹) (𝓝[≠] 1) (𝓝 (1 / 2)) := by
        simpa [one_div] using hc.tendsto.mono_left nhdsWithin_le_nhds
      refine hlim.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds one_pos), self_mem_nhdsWithin]
        with t ht0 (ht1 : t ≠ 1)
      have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
      field_simp [ht0.ne', hsub]
  have hden : Tendsto (fun t : ℝ ↦ log t / (t - 1)) (𝓝[≠] 1) (𝓝 1) := by
    have hd : HasDerivAt log 1 1 := by simpa using hasDerivAt_log one_ne_zero
    exact hd.tendsto_slope.congr fun t ↦ by simp [slope_def_field, log_one]
  have hq : Tendsto
      (fun t : ℝ ↦ ((t - 1 - log t) / (t - 1) ^ 2) / (log t / (t - 1)))
      (𝓝[≠] 1) (𝓝 (1 / 2)) := by
    simpa [Pi.div_def] using hnum.div hden one_ne_zero
  refine hq.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds one_pos), self_mem_nhdsWithin] with t ht0 ht1
  have hlt : log t ≠ 0 := log_ne_zero_of_pos_of_ne_one ht0 ht1
  have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  field_simp [hlt, hsub]

/-- Updating `t ↦ (log t)⁻¹ - (t - 1)⁻¹` by `1 / 2` at `t = 1` gives a continuous function on
`[0, ∞)`. -/
theorem continuousOn_update_inv_log_sub_inv_sub_one :
    ContinuousOn (Function.update (fun t : ℝ ↦ (log t)⁻¹ - (t - 1)⁻¹) 1 (1 / 2)) (Ici 0) := by
  rw [continuousOn_update_iff]
  refine ⟨fun t ⟨ht0, ht1⟩ ↦ ?_, fun _ ↦
    tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.mono_left
      (nhdsWithin_mono 1 fun _ h ↦ h.2)⟩
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · exact continuousAt_inv_log_sub_inv_sub_one_zero.continuousWithinAt
  · have htne : t ≠ 0 := htpos.ne'
    have hlt : log t ≠ 0 := log_ne_zero_of_pos_of_ne_one htpos ht1
    have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
    exact (by fun_prop (disch := assumption) :
      ContinuousAt (fun u : ℝ ↦ (log u)⁻¹ - (u - 1)⁻¹) t).continuousWithinAt

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

/-- The derivative of the radial profile: `d/dr log log (c / r) = -(r log (c / r))⁻¹` wherever
`r ∉ {0, c, -c}`. For `c = 0` both sides vanish. -/
theorem hasDerivAt_log_log_const_div {c r : ℝ} (hr : r ≠ 0) (hrc : r ≠ c) (hrc' : r ≠ -c) :
    HasDerivAt (fun s : ℝ => log (log (c / s))) (-(r * log (c / r))⁻¹) r := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using hasDerivAt_const r (0 : ℝ)
  have h1 : c / r ≠ 1 := fun h => hrc ((div_eq_one_iff_eq hr).1 h).symm
  have h2 : c / r ≠ -1 := fun h => hrc' (by rw [div_eq_iff hr] at h; linarith)
  have hL : log (c / r) ≠ 0 := log_ne_zero.2 ⟨div_ne_zero hc hr, h1, h2⟩
  refine ((hasDerivAt_log_const_div hc hr).log hL).congr_deriv ?_
  field_simp

/-- The radial profile `log log (c / r)` tends to `∞` as `r → 0`, for `c ≠ 0`. -/
theorem tendsto_log_log_const_div_nhdsNE_zero {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun r : ℝ => log (log (c / r))) (𝓝[≠] 0) atTop := by
  have h : Tendsto (fun r : ℝ => log c + -log r) (𝓝[≠] 0) atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_neg_atBot_atTop.comp tendsto_log_nhdsNE_zero)
  refine tendsto_log_atTop.comp (h.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [log_div hc hr, sub_eq_add_neg]

end Real
