/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Limits of the logarithm

The logarithmic scale of a fixed nonzero numerator divided by a variable approaching zero
tends to infinity. This supplies the diverging scale in logarithmic cutoff estimates.

## Main results

* `Real.tendsto_log_div_nhdsNE_zero`: for `δ ≠ 0`, `log (δ / ε) → ∞` as `ε → 0`, `ε ≠ 0`.
* `Real.tendsto_log_nhdsNE_one_nhdsNE_zero`: `log x → 0` through nonzero values as `x → 1`, `x ≠ 1`.
* `Real.tendsto_log_one_add_div_neg_log_one_sub`: `log (1 + ε) / (-log (1 - ε)) → 1` as `ε → 0⁺`.

Adapted from Giada Franz’s formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory),
`ForTauCeti/Geometry/Manifold/Riemannian/Surface/LogCutoff/Tendsto.lean`.
-/

public section

open Filter Topology

namespace Real

/-- For fixed `δ ≠ 0`, the scale `log (δ / ε)` tends to infinity as `ε → 0`
through nonzero values. -/
theorem tendsto_log_div_nhdsNE_zero {δ : ℝ} (hδ : δ ≠ 0) :
    Tendsto (fun ε ↦ Real.log (δ / ε)) (𝓝[≠] 0) atTop := by
  have h := tendsto_atTop_add_const_left _ (Real.log δ)
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsNE_zero)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Function.comp_apply, Real.log_div hδ hε]
  ring

/-- As `x → 1` with `x ≠ 1`, `log x → 0` through nonzero values. -/
theorem tendsto_log_nhdsNE_one_nhdsNE_zero :
    Tendsto Real.log (𝓝[≠] 1) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa using (Real.continuousAt_log one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_gt_nhds zero_lt_one)] with x hx hx0
    exact Real.log_ne_zero_of_pos_of_ne_one hx0 hx

/-- Ratio `log (1 + ε) / (-log (1 - ε)) → 1` as `ε → 0⁺`. -/
theorem tendsto_log_one_add_div_neg_log_one_sub :
    Tendsto (fun ε : ℝ ↦ Real.log (1 + ε) / (-Real.log (1 - ε))) (𝓝[>] 0) (𝓝 1) := by
  have hslope : Tendsto (fun ε : ℝ ↦ Real.log (1 + ε) / ε) (𝓝[≠] 0) (𝓝 1) := by
    have hd : HasDerivAt (fun ε : ℝ ↦ Real.log (1 + ε)) 1 0 :=
      ((Real.hasDerivAt_log (by norm_num)).comp 0
        ((hasDerivAt_id (0 : ℝ)).const_add 1)).congr_deriv (by norm_num)
    simpa [div_eq_inv_mul] using hd.tendsto_slope_zero
  have hslope_add : Tendsto (fun ε : ℝ ↦ Real.log (1 + ε) / ε) (𝓝[>] 0) (𝓝 1) :=
    hslope.mono_left (nhdsGT_le_nhdsNE 0)
  have hneg : Tendsto (fun ε : ℝ ↦ -ε) (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨by simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds,
       eventually_nhdsWithin_of_forall fun _ hε ↦ neg_ne_zero.mpr (ne_of_gt hε)⟩
  have hslope_sub : Tendsto (fun ε : ℝ ↦ -Real.log (1 - ε) / ε) (𝓝[>] 0) (𝓝 1) :=
    (hslope.comp hneg).congr fun ε ↦ by simp [sub_eq_add_neg, div_neg, neg_div]
  have hq := hslope_add.div hslope_sub one_ne_zero
  rw [div_one] at hq
  refine hq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact div_div_div_cancel_right₀ hε.ne' _ _

end Real
