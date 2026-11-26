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
public import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# The measure of a set in concentric balls

Let `μ` be a measure finite on compact sets on a proper metric space, and write
`m(ρ) = μ(s ∩ ball x₀ ρ)` for the measure of a set `s` in the balls about `x₀`. The function `m`
is monotone in the radius (`TauCeti.monotone_measureReal_inter_ball`); for closed balls it is
continuous at every radius at which `μ(closedBall x₀ ρ)` is
(`TauCeti.continuousAt_measureReal_inter_closedBall`), for every set `s`. Two concentric balls of
the same measure agree up to a null set (`TauCeti.ball_ae_eq_ball_of_measure_eq`); more generally,
the measure of their symmetric difference is at most that of any two sets with the same measures
(`TauCeti.measure_ball_symmDiff_ball_le`). Monotonicity
makes `m` differentiable at almost every radius. Where `m` has a right derivative at `r`, the
measures `μ(s ∩ (ball x₀ (r + h) \ ball x₀ r)) / h` of `s` in thin shells tend to it as `h → 0⁺`
(`TauCeti.tendsto_measure_inter_ball_sdiff_ball_div_of_hasDerivWithinAt`). These are the
difference quotients produced by cutting a set by balls with radial cutoffs.

For an arbitrary measure, a bound `μ (closedBall x r) ≤ f r` on concentric closed balls holding
for radii arbitrarily close to `ρ` from the right holds at `ρ` when `f` is right-continuous there
(`MeasureTheory.Measure.measure_closedBall_le_of_frequently_le`). On an extended metric space, the
measure of the open ball `B_r(x)` is the supremum of the measures of the concentric balls of
smaller radius (`MeasureTheory.Measure.measure_eball_eq_iSup_lt`), and it is a lower
semicontinuous function of its centre `x`
(`MeasureTheory.Measure.lowerSemicontinuous_measure_eball`).

The balls and closed balls about a point `z` have measures tending to `μ {z}` as the radius
decreases to `0`, once one of them has finite measure (`TauCeti.tendsto_measure_ball_nhdsGT_zero`,
`TauCeti.tendsto_measure_closedBall_nhdsGE_zero`), while punctured closed balls
`closedBall z r \ {z}` have measures tending to `0` at `0` once one of them has finite measure
(`TauCeti.tendsto_measure_closedBall_sdiff_singleton_nhds_zero`). Dually, the integrals of a
function integrable on a ball over the concentric balls of smaller radius tend to its integral over
the ball (`MeasureTheory.IntegrableOn.tendsto_integral_ball_nhdsLT`), and, for a locally finite
measure vanishing on points, the integrals of a function integrable on a set `S` over the parts of
`S` in the balls about a point tend to `0` with the radius
(`MeasureTheory.IntegrableOn.tendsto_setIntegral_ball_nhds_zero`).

## Main results

* `TauCeti.measure_ball_inter_ne_top`: the intersection of a ball with any set has finite
  measure.
* `TauCeti.monotone_measureReal_inter_ball`: `ρ ↦ μ(s ∩ ball x₀ ρ)` is monotone.
* `TauCeti.continuousAt_measureReal_inter_closedBall`: `ρ ↦ μ(s ∩ closedBall x₀ ρ)` is
  continuous wherever `ρ ↦ μ(closedBall x₀ ρ)` is.
* `TauCeti.ball_ae_eq_ball_of_measure_eq`: concentric balls of equal measure agree a.e.
* `TauCeti.measure_ball_symmDiff_ball_le`: concentric balls are no farther apart in measure than
  any two sets with the same measures.
* `TauCeti.tendsto_measure_inter_ball_sdiff_ball_div_of_hasDerivWithinAt`: the lower difference
  quotient of `m` is its right derivative, where that exists.
* `MeasureTheory.Measure.measure_closedBall_le_of_frequently_le`: a closed-ball bound for radii
  arbitrarily close to `ρ` from the right extends to `ρ` for a right-continuous gauge.
* `MeasureTheory.Measure.measure_ball_le_of_forall_lt`: a bound on the measures of the open balls
  of radius less than `ρ` bounds the open ball of radius `ρ`.
* `TauCeti.isClosed_setOf_forall_measure_inter_ball_le`: the points around which a set fills at
  most `K r` of every open ball of radius `r < ρ` form a closed set.
* `MeasureTheory.Measure.measure_eball_eq_iSup_lt`: the measure of an open ball is the supremum of
  the measures of the concentric balls of smaller radius.
* `MeasureTheory.Measure.lowerSemicontinuous_measure_eball`: for every measure on an extended
  metric space, the measure of an open ball is a lower semicontinuous function of its centre.
* `TauCeti.tendsto_measure_ball_nhdsGT_zero`, `TauCeti.tendsto_measure_closedBall_nhdsGE_zero`,
  `TauCeti.tendsto_measure_closedBall_sdiff_singleton_nhds_zero`: shrinking balls and closed balls
  about `z` have measures tending to `μ {z}`, and punctured closed balls tend in measure to `0`.
* `MeasureTheory.IntegrableOn.tendsto_integral_ball_nhdsLT`: as `r → R⁻`, the integral over
  `ball x r` tends to the integral over `ball x R`.
* `MeasureTheory.IntegrableOn.tendsto_setIntegral_ball_nhds_zero`: as `ρ → 0`, the integral over
  `S ∩ ball x ρ` of a function integrable on `S` tends to `0`.
-/

public section

namespace TauCeti

open MeasureTheory Metric Filter Set
open scoped ENNReal Topology symmDiff

variable {E : Type*} [PseudoMetricSpace E] [ProperSpace E] [MeasurableSpace E]

/-- The intersection of a ball with any set has finite measure, for a measure that is finite on
compact sets of a proper space. -/
theorem measure_ball_inter_ne_top {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {x : E} {r : ℝ}
    {s : Set E} : μ (ball x r ∩ s) ≠ ⊤ :=
  (measure_inter_lt_top_of_left_ne_top measure_ball_lt_top.ne).ne

/-- For a measure finite on compact sets, the measure `m(ρ) = μ(s ∩ ball x₀ ρ)` of `s` in the
balls about `x₀` is monotone in the radius. -/
theorem monotone_measureReal_inter_ball (μ : Measure E) [IsFiniteMeasureOnCompacts μ] (s : Set E)
    (x₀ : E) : Monotone fun ρ => μ.real (s ∩ ball x₀ ρ) := fun _ _ h =>
  measureReal_mono (inter_subset_inter_right _ (ball_subset_ball h))
    (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne)

/-- For a measure finite on compact sets, if the measures of the closed balls about `x` depend
continuously on the radius at `r₀`, then so do the measures `μ(s ∩ closedBall x r)` of the parts
of any set `s` in these balls, measurable or not: enlarging the radius adds at most the measure of
the shell between the two balls. -/
theorem continuousAt_measureReal_inter_closedBall (μ : Measure E) [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts μ] (s : Set E) {x : E} {r₀ : ℝ}
    (h : ContinuousAt (fun r => μ.real (closedBall x r)) r₀) :
    ContinuousAt (fun r => μ.real (s ∩ closedBall x r)) r₀ := by
  set N : ℝ → ℝ := fun r => μ.real (s ∩ closedBall x r)
  set D : ℝ → ℝ := fun r => μ.real (closedBall x r)
  -- Growing the radius increases `N` by at most the increase of `D`.
  have hgrow {r r' : ℝ} (hrr : r ≤ r') : N r ≤ N r' ∧ N r' ≤ N r + (D r' - D r) := by
    refine ⟨measureReal_mono (inter_subset_inter_right _ (closedBall_subset_closedBall hrr))
      (measure_ne_top_of_subset inter_subset_right measure_closedBall_lt_top.ne), ?_⟩
    have hsub : s ∩ closedBall x r' ⊆ (s ∩ closedBall x r) ∪ (closedBall x r' \ closedBall x r) :=
      fun z hz => (em (z ∈ closedBall x r)).elim (fun h => .inl ⟨hz.1, h⟩)
        fun h => .inr ⟨hz.2, h⟩
    calc N r' ≤ μ.real ((s ∩ closedBall x r) ∪ (closedBall x r' \ closedBall x r)) :=
          measureReal_mono hsub (measure_ne_top_of_subset (union_subset
            (inter_subset_right.trans (closedBall_subset_closedBall hrr)) sdiff_subset)
              measure_closedBall_lt_top.ne)
      _ ≤ N r + μ.real (closedBall x r' \ closedBall x r) := measureReal_union_le _ _
      _ = N r + (D r' - D r) := by
        rw [measureReal_sdiff (closedBall_subset_closedBall hrr) measurableSet_closedBall
          measure_closedBall_lt_top.ne]
  have hdist (r : ℝ) : |N r - N r₀| ≤ |D r - D r₀| := by
    rcases le_total r₀ r with hrr | hrr
    · obtain ⟨h₁, h₂⟩ := hgrow hrr
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · obtain ⟨h₁, h₂⟩ := hgrow hrr
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun r => ?_)
    (tendsto_iff_dist_tendsto_zero.1 h))
  simpa only [Real.dist_eq] using hdist r

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

variable {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X]

/-- An open ball is exhausted by the concentric balls of smaller radius, so its measure is the
supremum of their measures. -/
theorem measure_eball_eq_iSup_lt (μ : Measure X) (x : X) (r : ℝ≥0∞) :
    μ (eball x r) = ⨆ r' < r, μ (eball x r') := by
  refine le_antisymm ?_ (iSup₂_le fun r' hr' ↦ measure_mono (eball_subset_eball hr'.le))
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  -- The ball `B_r(x)` is the increasing union of balls `B_{u n}(x)` with `u n ↑ r`.
  obtain ⟨u, hu_mono, hu_mem, hu_lim⟩ := exists_seq_strictMono_tendsto' (pos_iff_ne_zero.2 hr)
  have hunion : eball x r = ⋃ n, eball x (u n) :=
    (iUnion_subset fun n ↦ eball_subset_eball (hu_mem n).2.le).antisymm' fun y hy ↦
      mem_iUnion.2 (hu_lim.eventually (lt_mem_nhds (mem_eball.1 hy))).exists
  have hmono : Monotone fun n ↦ eball x (u n) := fun m n hmn ↦
    eball_subset_eball (hu_mono.monotone hmn)
  rw [hunion, hmono.measure_iUnion]
  exact iSup_le fun n ↦ le_iSup₂_of_le (u n) (hu_mem n).2 le_rfl

/-- For every measure on an extended metric space, the measure of the open ball `B_r(x)` is a
lower semicontinuous function of its centre `x`. -/
theorem lowerSemicontinuous_measure_eball (μ : Measure X) (r : ℝ≥0∞) :
    LowerSemicontinuous fun x ↦ μ (eball x r) := by
  intro x a ha
  beta_reduce at ha ⊢
  rw [measure_eball_eq_iSup_lt] at ha
  obtain ⟨r', hr'⟩ := lt_iSup_iff.1 ha
  obtain ⟨hr', hn⟩ := lt_iSup_iff.1 hr'
  -- Points `y` with `edist x y < r - r'` have `B_{r'}(x) ⊆ B_r(y)`.
  have hpos : 0 < r - r' := tsub_pos_of_lt hr'
  filter_upwards [eball_mem_nhds x hpos] with y hy
  have hxy : edist x y < r - r' := mem_eball'.1 hy
  refine hn.trans_le (measure_mono (eball_subset ?_ hxy.ne_top))
  calc edist x y + r' ≤ (r - r') + r' := by gcongr
    _ = r := tsub_add_cancel_of_le hr'.le

end MeasureTheory.Measure

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
  rw [← eball_ofReal, measure_eball_eq_iSup_lt]
  refine iSup₂_le fun r hr ↦ ?_
  rw [← ENNReal.ofReal_toReal hr.ne_top, eball_ofReal]
  exact h _ (ENNReal.toReal_lt_of_lt_ofReal hr)

end MeasureTheory.Measure


namespace TauCeti

open MeasureTheory Metric Filter Set
open scoped ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}

/-- The balls about a point `z`, one of which has finite measure, have measures tending to the
measure of `{z}` as the radius decreases to `0`. -/
theorem tendsto_measure_ball_nhdsGT_zero {z : X} (hfin : ∃ R > 0, μ (ball z R) ≠ ⊤) :
    Tendsto (fun r ↦ μ (ball z r)) (𝓝[>] 0) (𝓝 (μ {z})) := by
  simpa [thickening_singleton] using
    tendsto_measure_thickening (μ := μ) (s := {z}) (by simpa [thickening_singleton] using hfin)

/-- The closed balls about a point `z`, one of positive radius having finite measure, have measures
tending to `μ {z}` as the radius approaches `0` from the right. -/
theorem tendsto_measure_closedBall_nhdsGE_zero {z : X} (hfin : ∃ R > 0, μ (closedBall z R) ≠ ⊤) :
    Tendsto (fun r ↦ μ (closedBall z r)) (𝓝[≥] 0) (𝓝 (μ {z})) := by
  obtain ⟨R, hR, hRfin⟩ := hfin
  have hlim := tendsto_measure_cthickening_of_isClosed (μ := μ) (s := {z})
    ⟨R, hR, by rwa [cthickening_singleton z hR.le]⟩ isClosed_singleton
  exact (hlim.mono_left nhdsWithin_le_nhds).congr' <|
    eventually_nhdsWithin_of_forall fun r (hr : 0 ≤ r) ↦
      congrArg μ (cthickening_singleton z hr)

/-- Punctured closed balls `closedBall z r \ {z}` about `z` have measures tending to `0` at `0`
whenever one of positive radius has finite measure. -/
theorem tendsto_measure_closedBall_sdiff_singleton_nhds_zero {z : X}
    (hfin : ∃ R > 0, μ (closedBall z R \ {z}) ≠ ⊤) :
    Tendsto (fun r ↦ μ (closedBall z r \ {z})) (𝓝 0) (𝓝 0) := by
  have hgt : Tendsto (fun r ↦ μ (closedBall z r \ {z})) (𝓝[>] 0) (𝓝 0) := by
    have hiInter : ⋂ r > (0 : ℝ), closedBall z r \ {z} = ∅ := by
      refine subset_empty_iff.1 <| Subset.trans
        (b := (⋂ r > (0 : ℝ), closedBall z r) \ {z})
        (fun y hy ↦ ⟨mem_iInter₂.2 fun r hr ↦ (mem_iInter₂.1 hy r hr).1,
          (mem_iInter₂.1 hy 1 one_pos).2⟩) ?_
      simp [biInter_gt_closedBall]
    simpa only [Function.comp_def, hiInter, measure_empty] using
      tendsto_measure_biInter_gt
        (fun r _ ↦ (measurableSet_closedBall.diff (measurableSet_singleton z)).nullMeasurableSet)
        (fun _ _ _ hij ↦ sdiff_subset_sdiff_left (closedBall_subset_closedBall hij)) hfin
  have hle : Tendsto (fun r ↦ μ (closedBall z r \ {z})) (𝓝[≤] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' <| eventually_nhdsWithin_of_forall fun r (hr : r ≤ 0) ↦ ?_
    have hempty : closedBall z r \ {z} = ∅ := eq_empty_iff_forall_notMem.2 fun y ⟨hy, hyz⟩ ↦
      hyz (mem_singleton_iff.2 (dist_le_zero.1 ((mem_closedBall.1 hy).trans hr)))
    simp [hempty]
  rw [← nhdsLE_sup_nhdsGT 0]
  exact hle.sup hgt

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

namespace MeasureTheory.IntegrableOn

open Metric Filter
open scoped Topology

variable {X F : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure X}

/-- For a locally finite measure vanishing on points, the integrals of a function integrable on `S`
over the parts of `S` in the balls about `x` tend to `0` as the radius tends to `0`. -/
theorem tendsto_setIntegral_ball_nhds_zero [IsLocallyFiniteMeasure μ] [NullSingletonClass μ]
    {f : X → F} {S : Set X} (hf : IntegrableOn f S μ) (x : X) :
    Tendsto (fun ρ ↦ ∫ z in ball x ρ, f z ∂μ.restrict S) (𝓝 0) (𝓝 0) := by
  refine Integrable.tendsto_setIntegral_nhds_zero hf ?_
  -- Some closed ball about `x` has finite measure, so the closed balls shrink to `μ {x} = 0`.
  obtain ⟨o, hxo, ho, hμo⟩ := μ.exists_isOpen_measure_lt_top x
  obtain ⟨ε, hε, hεo⟩ := Metric.isOpen_iff.1 ho x hxo
  have hfin : μ (cthickening (ε / 2) {x}) ≠ ⊤ := by
    rw [cthickening_singleton x (half_pos hε).le]
    exact ((measure_mono ((closedBall_subset_ball (half_lt_self hε)).trans hεo)).trans_lt
      hμo).ne
  have h := tendsto_measure_cthickening_of_isClosed ⟨ε / 2, half_pos hε, hfin⟩
    (isClosed_singleton (x := x))
  rw [measure_singleton] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le)
    fun ρ ↦ (Measure.restrict_apply_le _ _).trans <| measure_mono fun y hy ↦
      mem_cthickening_of_dist_le y x ρ _ rfl (mem_ball.1 hy).le

end MeasureTheory.IntegrableOn

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The points around which a set fills at most a prescribed amount `K r` of every open ball of
radius `r < ρ` form a closed set. -/
theorem isClosed_setOf_forall_measure_inter_ball_le (μ : Measure X) (A : Set X) (ρ : ℝ)
    (K : ℝ → ℝ≥0∞) : IsClosed {x | ∀ r ∈ Ioo 0 ρ, μ (A ∩ ball x r) ≤ K r} := by
  refine closure_subset_iff_isClosed.1 fun x hx r hr => ?_
  have hrestr (z : X) (ρ' : ℝ) : μ (A ∩ ball z ρ') = μ.restrict A (ball z ρ') := by
    rw [Measure.restrict_apply measurableSet_ball, inter_comm]
  rw [hrestr]
  refine Measure.measure_ball_le_of_forall_lt _ fun r' hr' => ?_
  obtain ⟨x', hx', hxx'⟩ := Metric.mem_closure_iff.1 hx (r - r') (sub_pos.2 hr')
  rw [← hrestr]
  calc μ (A ∩ ball x r') ≤ μ (A ∩ ball x' r) :=
        measure_mono (inter_subset_inter_right _ (ball_subset_ball' (by linarith)))
    _ ≤ K r := hx' r hr

end TauCeti
