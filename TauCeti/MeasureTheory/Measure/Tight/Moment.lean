/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Tightness from a uniform moment bound

On a proper pseudometric space, a set of measures whose moments `∫⁻ edist x a ^ p` about a
center `a`, of some order `p > 0`, are bounded by a common finite constant `C` is tight. By
Markov's inequality, for every radius `r > 0` each member puts mass at most `C / r ^ p` outside
the closed ball of radius `r` about `a`, and this bound tends to zero as `r → ∞` uniformly over
the set.

Bounded second moments are how tightness enters the method of moments on the real line: a family
of probability measures whose moments converge has eventually bounded second moments, so the
family restricted to an eventual set of indices is tight and Prokhorov's theorem applies there.

## Main results

* `TauCeti.isTightMeasureSet_of_lintegral_edist_rpow_le`: uniformly bounded `p`-th moments about
  a center give tightness.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- **Tightness from a uniform moment bound.** On a proper pseudometric space, a set of measures
whose `p`-th moments `∫⁻ edist x a ^ p` about a center `a`, for some `p > 0`, are bounded by a
common finite constant `C` is tight: for every `r > 0` each member puts mass at most `C / r ^ p`
outside the closed ball of radius `r` about `a`. -/
theorem isTightMeasureSet_of_lintegral_edist_rpow_le [ProperSpace X] {S : Set (Measure X)}
    (a : X) {p : ℝ} (hp : 0 < p) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∀ μ ∈ S, ∫⁻ x, edist x a ^ p ∂μ ≤ C) :
    IsTightMeasureSet S := by
  refine isTightMeasureSet_of_tendsto_measure_compl_closedBall (x := a) ?_
  have hlim : Tendsto (fun r : ℝ ↦ ENNReal.ofReal (C.toReal / r ^ p)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hp))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  refine iSup₂_le fun μ hμ ↦ ?_
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr p
  calc μ (Metric.closedBall a r)ᶜ
      ≤ μ {x | ENNReal.ofReal (r ^ p) ≤ edist x a ^ p} := by
        refine measure_mono fun x hx ↦ ?_
        rw [mem_compl_iff, Metric.mem_closedBall, not_le] at hx
        rw [mem_ofPred_eq, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp.le]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hr.le hx.le hp.le)
    _ ≤ (∫⁻ x, edist x a ^ p ∂μ) / ENNReal.ofReal (r ^ p) :=
        meas_ge_le_lintegral_div
          ((continuous_id.edist continuous_const).measurable.pow_const p).aemeasurable
          (by simpa using hrp) ENNReal.ofReal_ne_top
    _ ≤ C / ENNReal.ofReal (r ^ p) := by gcongr; exact h μ hμ
    _ = ENNReal.ofReal (C.toReal / r ^ p) := by
        rw [ENNReal.ofReal_div_of_pos hrp, ENNReal.ofReal_toReal hC]

end TauCeti
