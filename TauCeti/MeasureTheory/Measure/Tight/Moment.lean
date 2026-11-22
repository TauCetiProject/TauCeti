/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Tightness from a uniform moment bound

On a proper normed group, a set of measures whose absolute moments `∫⁻ ‖x‖ₑ ^ p` of some order
`p > 0` are bounded by a common finite constant `C` is tight. By Markov's inequality, every
member puts mass at most `C / r ^ p` outside the closed ball of radius `r`, and this bound
tends to zero as `r → ∞` uniformly over the set.

Bounded second moments are how tightness enters the method of moments on the real line: a family
of probability measures whose moments converge has eventually bounded second moments, so it is
tight and Prokhorov's theorem applies.

## Main results

* `TauCeti.isTightMeasureSet_of_lintegral_enorm_rpow_le`: uniformly bounded `p`-th absolute
  moments give tightness.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]

/-- **Tightness from a uniform moment bound.** On a proper normed group, a set of measures whose
`p`-th absolute moments `∫⁻ ‖x‖ₑ ^ p`, for some `p > 0`, are bounded by a common finite
constant `C` is tight: each member puts mass at most `C / r ^ p` on `{x | r < ‖x‖}`. -/
theorem isTightMeasureSet_of_lintegral_enorm_rpow_le [ProperSpace E] {S : Set (Measure E)}
    {p : ℝ} (hp : 0 < p) {C : ℝ≥0∞} (hC : C ≠ ∞) (h : ∀ μ ∈ S, ∫⁻ x, ‖x‖ₑ ^ p ∂μ ≤ C) :
    IsTightMeasureSet S := by
  refine isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  have hlim : Tendsto (fun r : ℝ ↦ ENNReal.ofReal (C.toReal / r ^ p)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hp))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  refine iSup₂_le fun μ hμ ↦ ?_
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr p
  calc μ {x | r < ‖x‖}
      ≤ μ {x | ENNReal.ofReal (r ^ p) ≤ ‖x‖ₑ ^ p} := by
        refine measure_mono fun x hx ↦ ?_
        rw [mem_ofPred_eq, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg x)
          hp.le]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hr.le (le_of_lt hx) hp.le)
    _ ≤ (∫⁻ x, ‖x‖ₑ ^ p ∂μ) / ENNReal.ofReal (r ^ p) :=
        meas_ge_le_lintegral_div (measurable_eNorm.pow_const p).aemeasurable
          (by simpa using hrp) ENNReal.ofReal_ne_top
    _ ≤ C / ENNReal.ofReal (r ^ p) := by gcongr; exact h μ hμ
    _ = ENNReal.ofReal (C.toReal / r ^ p) := by
        rw [ENNReal.ofReal_div_of_pos hrp, ENNReal.ofReal_toReal hC]

end TauCeti
