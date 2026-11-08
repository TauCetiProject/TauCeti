/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# The measure of a set in concentric balls

Let `μ` be a measure finite on compact sets on a proper metric space, and write
`m(ρ) = μ(s ∩ ball x₀ ρ)` for the measure of a set `s` in the balls about `x₀`. The function `m`
is monotone in the radius (`TauCeti.monotone_measureReal_inter_ball`), so it is differentiable at
almost every radius. Where `m` has a right derivative at `r`, the measures
`μ(s ∩ (ball x₀ (r + h) \ ball x₀ r)) / h` of `s` in thin shells tend to it as `h → 0⁺`
(`TauCeti.tendsto_measure_inter_ball_sdiff_ball_div_of_hasDerivWithinAt`). These are the
difference quotients produced by cutting a set by balls with radial cutoffs.

For an arbitrary measure, a bound `μ (closedBall x r) ≤ f r` on concentric closed balls holding
for radii arbitrarily close to `ρ` from the right holds at `ρ` when `f` is right-continuous there
(`MeasureTheory.Measure.measure_closedBall_le_of_frequently_le`).

The balls about a point `z` have measures tending to `μ {z}` as the radius decreases to `0`,
once one of them has finite measure (`TauCeti.tendsto_measure_ball_nhdsGT_zero`).

## Main results

* `TauCeti.monotone_measureReal_inter_ball`: `ρ ↦ μ(s ∩ ball x₀ ρ)` is monotone.
* `TauCeti.tendsto_measure_inter_ball_sdiff_ball_div_of_hasDerivWithinAt`: the lower difference
  quotient of `m` is its right derivative, where that exists.
* `MeasureTheory.Measure.measure_closedBall_le_of_frequently_le`: a closed-ball bound for radii
  arbitrarily close to `ρ` from the right extends to `ρ` for a right-continuous gauge.
* `TauCeti.tendsto_measure_ball_nhdsGT_zero`: shrinking balls about `z` have measures tending to
  `μ {z}`.
-/

public section

namespace TauCeti

open MeasureTheory Metric Filter Set
open scoped ENNReal Topology

variable {E : Type*} [PseudoMetricSpace E] [ProperSpace E] [MeasurableSpace E]

/-- For a measure finite on compact sets, the measure `m(ρ) = μ(s ∩ ball x₀ ρ)` of `s` in the
balls about `x₀` is monotone in the radius. -/
theorem monotone_measureReal_inter_ball (μ : Measure E) [IsFiniteMeasureOnCompacts μ] (s : Set E)
    (x₀ : E) : Monotone fun ρ => μ.real (s ∩ ball x₀ ρ) := fun _ _ h =>
  measureReal_mono (inter_subset_inter_right _ (ball_subset_ball h))
    (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne)

/-- The difference quotients `μ(s ∩ (ball x₀ (r + h) \ ball x₀ r)) / h` of
`m(ρ) = μ(s ∩ ball x₀ ρ)` tend, as `h → 0⁺`, to the right derivative of `m` at `r`, when it
exists. Only finiteness of `μ` on balls is used. -/
theorem tendsto_measure_inter_ball_sdiff_ball_div_of_hasDerivWithinAt [OpensMeasurableSpace E]
    {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] {s : Set E} {x₀ : E} {r : ℝ} (hs : NullMeasurableSet s μ)
    {D : ℝ} (hD : HasDerivWithinAt (fun ρ => μ.real (s ∩ ball x₀ ρ)) D (Ioi r) r) :
    Tendsto (fun h => μ (s ∩ (ball x₀ (r + h) \ ball x₀ r)) / ENNReal.ofReal h) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal D)) := by
  -- The quotient is the slope of `m`, written in `ℝ≥0∞`.
  have hshift : Tendsto (fun h => r + h) (𝓝[>] 0) (𝓝[>] r) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun h (hh : 0 < h) =>
      lt_add_of_pos_right r hh⟩
    exact ((continuous_const.add continuous_id).tendsto' 0 r (add_zero r)).mono_left
      nhdsWithin_le_nhds
  have hslope := ((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl r)).1 hD).comp hshift
  refine ((ENNReal.continuous_ofReal.tendsto D).comp hslope).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  have hsub : s ∩ ball x₀ r ⊆ s ∩ ball x₀ (r + h) :=
    inter_subset_inter_right _ (ball_subset_ball (by linarith))
  have hfin : μ (s ∩ ball x₀ (r + h)) ≠ (∞ : ℝ≥0∞) :=
    measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne
  rw [Function.comp_apply, Function.comp_apply, slope_def_field, add_sub_cancel_left,
    ENNReal.ofReal_div_of_pos hh, ENNReal.ofReal_sub _ measureReal_nonneg, ofReal_measureReal hfin,
    ofReal_measureReal (measure_ne_top_of_subset hsub hfin), inter_sdiff_distrib_left,
    measure_sdiff hsub (hs.inter measurableSet_ball.nullMeasurableSet)
      (measure_ne_top_of_subset hsub hfin)]

end TauCeti

namespace MeasureTheory.Measure

open Metric Filter Set
open scoped ENNReal Topology

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- A bound `μ (closedBall x r) ≤ f r` holding for radii `r` arbitrarily close to `ρ` from the
right extends to the radius `ρ` itself when the gauge `f` is right-continuous at `ρ`, since
`closedBall x ρ ⊆ closedBall x r` for `ρ ≤ r`. -/
theorem measure_closedBall_le_of_frequently_le (μ : Measure X) {f : ℝ → ℝ≥0∞} {x : X} {ρ : ℝ}
    (hf : ContinuousWithinAt f (Ioi ρ) ρ) (h : ∃ᶠ r in 𝓝[>] ρ, μ (closedBall x r) ≤ f r) :
    μ (closedBall x ρ) ≤ f ρ :=
  isClosed_Ici.mem_of_frequently_of_tendsto (h.mp (eventually_nhdsWithin_of_forall
    fun r (hr : ρ < r) hle => (measure_mono (closedBall_subset_closedBall hr.le)).trans hle)) hf

end MeasureTheory.Measure

namespace TauCeti

open MeasureTheory Metric Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}

/-- The balls about a point `z`, one of which has finite measure, have measures tending to the
measure of `{z}` as the radius decreases to `0`. -/
theorem tendsto_measure_ball_nhdsGT_zero {z : X} (hfin : ∃ R > 0, μ (ball z R) ≠ ⊤) :
    Tendsto (fun r ↦ μ (ball z r)) (𝓝[>] 0) (𝓝 (μ {z})) := by
  simpa [thickening_singleton] using
    tendsto_measure_thickening (μ := μ) (s := {z}) (by simpa [thickening_singleton] using hfin)

end TauCeti
