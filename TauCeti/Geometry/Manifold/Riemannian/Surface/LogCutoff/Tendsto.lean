/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.LogCutoff.Profile
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Order.Field

/-!
# The logarithmic cutoff profile as `ε → 0`

For fixed `δ > 0`, the logarithmic scale `log (δ / ε)` tends to infinity as `ε → 0⁺`, and the
logarithmic cutoff profile `ψ_ε(r)` tends to `1` at every radius `r > 0`, with
`0 ≤ 1 - ψ_ε(r) ≤ |log (2δ / r)| / log (δ / ε)`.
-/

public section

open Real Set Filter
open scoped Topology

namespace TauCeti

variable {δ : ℝ}

/-- For fixed `δ > 0`, the logarithmic scale `log (δ / ε)` tends to infinity as `ε → 0⁺`. -/
theorem tendsto_log_div_nhdsGT_zero (hδ : 0 < δ) :
    Tendsto (fun ε ↦ Real.log (δ / ε)) (𝓝[>] 0) atTop := by
  have h := tendsto_atTop_add_const_left _ (Real.log δ)
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Function.comp_apply, Real.log_div hδ.ne' (ne_of_gt hε)]
  ring

/-- For fixed `δ > 0`, eventually as `ε → 0⁺` we have `0 < ε` and `4ε ≤ δ`. -/
theorem eventually_pos_and_four_mul_le (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ 4 * ε ≤ δ := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (gt_mem_nhds (by linarith : (0 : ℝ) < δ / 4))] with ε hε hεδ
  exact ⟨hε, by linarith [show ε < δ / 4 from hεδ]⟩

/-- The defect `1 - ψ_ε(r)` is at most `|log (2δ / r)| / log (δ / ε)` at every radius `r > 0`. -/
theorem one_sub_logCutoffProfile_le_abs {ε r : ℝ} (hε : 0 < ε) (hεδ : 4 * ε ≤ δ) (hr : 0 < r) :
    1 - logCutoffProfile ε δ r ≤ |Real.log (2 * δ / r)| / Real.log (δ / ε) := by
  have hΛ : 0 ≤ Real.log (δ / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).2 (by linarith))
  rcases le_or_gt r δ with hrδ | hrδ
  · exact (one_sub_logCutoffProfile_le hε hεδ hr hrδ).trans
      (div_le_div_of_nonneg_right (le_abs_self _) hΛ)
  · rw [logCutoffProfile_eq_one_of_le hε hεδ hrδ.le, sub_self]
    positivity

/-- At every radius `r > 0`, the logarithmic cutoff profile tends to `1` as `ε → 0⁺`. -/
theorem tendsto_logCutoffProfile_nhdsGT_zero (hδ : 0 < δ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε ↦ logCutoffProfile ε δ r) (𝓝[>] 0) (𝓝 1) := by
  have hlim : Tendsto (fun ε ↦ |Real.log (2 * δ / r)| / Real.log (δ / ε)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_log_div_nhdsGT_zero hδ)
  have hsq : Tendsto (fun ε ↦ 1 - logCutoffProfile ε δ r) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    · filter_upwards [eventually_pos_and_four_mul_le hδ] with ε hε
      exact sub_nonneg.2 (logCutoffProfile_le_one hε.1 hε.2 r)
    · filter_upwards [eventually_pos_and_four_mul_le hδ] with ε hε
      exact one_sub_logCutoffProfile_le_abs hε.1 hε.2 hr
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hsq

end TauCeti
