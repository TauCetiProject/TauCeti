/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# The measure of a set in concentric balls

Let `μ` be a measure finite on compact sets on a proper metric space, and write
`m(ρ) = μ(s ∩ ball x₀ ρ)` for the measure of a set `s` in the balls about `x₀`. The function `m`
is monotone in the radius (`TauCeti.monotone_measureReal_inter_ball`), and two concentric balls of
the same measure agree up to a null set (`TauCeti.ball_ae_eq_ball_of_measure_eq`); more generally,
the measure of their symmetric difference is at most that of any two sets with the same measures
(`TauCeti.measure_ball_symmDiff_ball_le`). Monotonicity
makes `m` differentiable at almost every radius. Where `m` has a right derivative at `r`, the
measures `μ(s ∩ (ball x₀ (r + h) \ ball x₀ r)) / h` of `s` in thin shells tend to it as `h → 0⁺`
(`TauCeti.tendsto_measure_inter_ball_sdiff_ball_div_of_hasDerivWithinAt`). These are the
difference quotients produced by cutting a set by balls with radial cutoffs.

For an arbitrary measure, a bound `μ (closedBall x r) ≤ f r` on concentric closed balls holding
for radii arbitrarily close to `ρ` from the right holds at `ρ` when `f` is right-continuous there
(`MeasureTheory.Measure.measure_closedBall_le_of_frequently_le`).

The balls about a point `z` have measures tending to `μ {z}` as the radius decreases to `0`,
once one of them has finite measure (`TauCeti.tendsto_measure_ball_nhdsGT_zero`). Dually, the
integrals of a function integrable on a ball over the concentric balls of smaller radius tend to
its integral over the ball (`MeasureTheory.IntegrableOn.tendsto_integral_ball_nhdsLT`).

A rectangle in `ℝ × ℝ` with sides of length at least one meets the ball of radius one about each
of its points, a square for the sup norm, in a set of area at least one
(`TauCeti.one_le_volume_Ioo_prod_Ioo_inter_ball`), however long the rectangle is. This is the
uniform lower bound on the local measure of a domain under which Sobolev estimates on rectangles
of unbounded length have uniform constants.

## Main results

* `TauCeti.monotone_measureReal_inter_ball`: `ρ ↦ μ(s ∩ ball x₀ ρ)` is monotone.
* `TauCeti.ball_ae_eq_ball_of_measure_eq`: concentric balls of equal measure agree a.e.
* `TauCeti.measure_ball_symmDiff_ball_le`: concentric balls are no farther apart in measure than
  any two sets with the same measures.
* `TauCeti.tendsto_measure_inter_ball_sdiff_ball_div_of_hasDerivWithinAt`: the lower difference
  quotient of `m` is its right derivative, where that exists.
* `MeasureTheory.Measure.measure_closedBall_le_of_frequently_le`: a closed-ball bound for radii
  arbitrarily close to `ρ` from the right extends to `ρ` for a right-continuous gauge.
* `MeasureTheory.Measure.measure_ball_le_of_forall_lt`: a bound on the measures of the open balls
  of radius less than `ρ` bounds the open ball of radius `ρ`.
* `TauCeti.tendsto_measure_ball_nhdsGT_zero`: shrinking balls about `z` have measures tending to
  `μ {z}`.
* `MeasureTheory.IntegrableOn.tendsto_integral_ball_nhdsLT`: as `r → R⁻`, the integral over
  `ball x r` tends to the integral over `ball x R`.
* `TauCeti.one_le_volume_Ioo_prod_Ioo_inter_ball`: a rectangle with sides of length at least one
  meets the unit ball about each of its points in a set of area at least one.
-/

public section

namespace TauCeti

open MeasureTheory Metric Filter Set
open scoped ENNReal Topology symmDiff

variable {E : Type*} [PseudoMetricSpace E] [ProperSpace E] [MeasurableSpace E]

/-- For a measure finite on compact sets, the measure `m(ρ) = μ(s ∩ ball x₀ ρ)` of `s` in the
balls about `x₀` is monotone in the radius. -/
theorem monotone_measureReal_inter_ball (μ : Measure E) [IsFiniteMeasureOnCompacts μ] (s : Set E)
    (x₀ : E) : Monotone fun ρ => μ.real (s ∩ ball x₀ ρ) := fun _ _ h =>
  measureReal_mono (inter_subset_inter_right _ (ball_subset_ball h))
    (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne)

/-- For a measure finite on compact sets, two concentric open balls of the same measure agree up
to a null set, since the smaller one is contained in the larger. -/
theorem ball_ae_eq_ball_of_measure_eq [OpensMeasurableSpace E] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] {x₀ : E} {r r' : ℝ} (h : μ (ball x₀ r) = μ (ball x₀ r')) :
    ball x₀ r =ᵐ[μ] ball x₀ r' := by
  rcases le_total r r' with hrr | hrr
  · exact ae_eq_of_subset_of_measure_ge (ball_subset_ball hrr) h.ge
      measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne
  · exact (ae_eq_of_subset_of_measure_ge (ball_subset_ball hrr) h.le
      measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne).symm

/-- For a measure finite on compact sets, the measure of the symmetric difference of two
concentric open balls is at most that of any two sets with the same measures, since the smaller
ball is contained in the larger. -/
theorem measure_ball_symmDiff_ball_le [OpensMeasurableSpace E] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] {x₀ : E} {r r' : ℝ} {s t : Set E} (hs : μ (ball x₀ r) = μ s)
    (ht : μ (ball x₀ r') = μ t) : μ (ball x₀ r ∆ ball x₀ r') ≤ μ (s ∆ t) := by
  wlog hrr : r ≤ r' generalizing r r' s t
  · rw [symmDiff_comm, symmDiff_comm s]
    exact this ht hs (le_of_not_ge hrr)
  rw [symmDiff_of_le (ball_subset_ball hrr), measure_sdiff (ball_subset_ball hrr)
    measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne, hs, ht, symmDiff_comm]
  exact le_measure_symmDiff

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

/-- An open ball is exhausted by the concentric balls of smaller radius, so a bound on the measures
of the smaller balls bounds the measure of the ball. -/
theorem measure_ball_le_of_forall_lt (μ : Measure X) {x : X} {ρ : ℝ} {B : ℝ≥0∞}
    (h : ∀ r < ρ, μ (ball x r) ≤ B) : μ (ball x ρ) ≤ B := by
  obtain ⟨r, hr, hrρ, hlim⟩ := exists_seq_strictMono_tendsto ρ
  have hU : ⋃ n, ball x (r n) = ball x ρ :=
    (iUnion_subset fun n => ball_subset_ball (hrρ n).le).antisymm fun z hz =>
      mem_iUnion.2 (hlim.eventually (lt_mem_nhds hz)).exists
  rw [← hU, Monotone.measure_iUnion fun i j hij => ball_subset_ball (hr.monotone hij)]
  exact iSup_le fun n => h _ (hrρ n)

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

namespace MeasureTheory.IntegrableOn

open Metric Filter Set
open scoped Topology

variable {X F : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure X}

/-- The integrals of a function integrable on an open ball over the concentric balls of smaller
radius tend to its integral over the ball, by dominated convergence. -/
theorem tendsto_integral_ball_nhdsLT {f : X → F} {x : X} {R : ℝ}
    (hf : IntegrableOn f (ball x R) μ) :
    Tendsto (fun r ↦ ∫ z in ball x r, f z ∂μ) (𝓝[<] R) (𝓝 (∫ z in ball x R, f z ∂μ)) := by
  simp_rw [← integral_indicator measurableSet_ball]
  refine tendsto_integral_filter_of_dominated_convergence
    ((ball x R).indicator fun z ↦ ‖f z‖) ?_ ?_
    (IntegrableOn.integrable_indicator hf.norm measurableSet_ball) ?_
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact ((hf.mono_set (ball_subset_ball (le_of_lt hr))).integrable_indicator
      measurableSet_ball).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with r hr
    refine Eventually.of_forall fun z ↦ ?_
    rw [norm_indicator_eq_indicator_norm]
    exact indicator_le_indicator_of_subset (ball_subset_ball (le_of_lt hr))
      (fun _ ↦ norm_nonneg _) z
  · refine Eventually.of_forall fun z ↦ ?_
    by_cases hz : z ∈ ball x R
    · rw [indicator_of_mem hz]
      refine tendsto_const_nhds.congr' ?_
      have : dist z x < R := hz
      filter_upwards [Ioo_mem_nhdsLT this] with r hr
      rw [indicator_of_mem (show dist z x < r from hr.1)]
    · rw [indicator_of_notMem hz]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [indicator_of_notMem fun h ↦ hz (ball_subset_ball (le_of_lt hr) h)]

end MeasureTheory.IntegrableOn

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal

/-- An open interval of length at least one meets the interval of radius one about each of its
points in a set of length at least one. -/
theorem one_le_volume_Ioo_inter_ball {a b x : ℝ} (hab : 1 ≤ b - a) (hx : x ∈ Ioo a b) :
    1 ≤ volume (Ioo a b ∩ ball x 1) := by
  rw [Real.ball_eq_Ioo, Ioo_inter_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have h : a ⊔ (x - 1) + 1 ≤ b ⊓ (x + 1) :=
    le_inf (add_le_of_le_sub_right (sup_le (by linarith) (by linarith [hx.2])))
      (by linarith [sup_le (show a ≤ x by linarith [hx.1]) (show x - 1 ≤ x by linarith)])
  linarith

/-- A rectangle in `ℝ × ℝ` with sides of length at least one meets the ball of radius one about
each of its points in a set of area at least one, whatever the lengths of its sides. For the sup
norm of `ℝ × ℝ` this ball is the square `(x - 1, x + 1) × (y - 1, y + 1)`. -/
theorem one_le_volume_Ioo_prod_Ioo_inter_ball {a b c d : ℝ} (hab : 1 ≤ b - a) (hcd : 1 ≤ d - c)
    {z : ℝ × ℝ} (hz : z ∈ Ioo a b ×ˢ Ioo c d) : 1 ≤ volume (Ioo a b ×ˢ Ioo c d ∩ ball z 1) := by
  obtain ⟨x, y⟩ := z
  rw [← ball_prod_same, prod_inter_prod, Measure.volume_eq_prod, Measure.prod_prod]
  calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
    _ ≤ _ := mul_le_mul' (one_le_volume_Ioo_inter_ball hab hz.1)
      (one_le_volume_Ioo_inter_ball hcd hz.2)

end TauCeti
