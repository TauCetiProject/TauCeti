/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
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
once one of them has finite measure (`TauCeti.tendsto_measure_ball_nhdsGT_zero`). More generally,
as `ρ → r⁺` the measures, Bochner integrals, and averages over preimages `g ⁻¹' closedBall x ρ`
are right-continuous in the radius
(`MeasureTheory.Measure.tendsto_measure_preimage_closedBall_nhdsGT`,
`MeasureTheory.IntegrableOn.tendsto_integral_preimage_closedBall_nhdsGT`,
`MeasureTheory.IntegrableOn.tendsto_setAverage_preimage_closedBall_nhdsGT`). Dually, the integrals
of a function integrable on an open ball over concentric balls of smaller radius tend to its
integral over the ball (`MeasureTheory.IntegrableOn.tendsto_integral_ball_nhdsLT`).

When `X` is second-countable and `μ` is `s`-finite, the measure, Bochner integral, and average over
`g ⁻¹' closedBall x r` are measurable (resp. strongly measurable) as functions of the centre `x`
(`MeasureTheory.Measure.measurable_preimage_closedBall`,
`MeasureTheory.AEStronglyMeasurable.integral_preimage_closedBall`,
`MeasureTheory.AEStronglyMeasurable.setAverage_preimage_closedBall`).

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
* `MeasureTheory.Measure.tendsto_measure_preimage_closedBall_nhdsGT` and
  `MeasureTheory.Measure.tendsto_measure_closedBall_nhdsGT`: right-continuity of closed-ball
  measures in the radius.
* `MeasureTheory.Measure.measurable_preimage_closedBall` and
  `MeasureTheory.Measure.measurable_closedBall`: measurability of closed-ball measures in the
  centre.
* `TauCeti.tendsto_measure_ball_nhdsGT_zero`: shrinking balls about `z` have measures tending to
  `μ {z}`.
* `MeasureTheory.IntegrableOn.tendsto_integral_ball_nhdsLT`: as `r → R⁻`, the integral over
  `ball x r` tends to the integral over `ball x R`.
* `MeasureTheory.IntegrableOn.tendsto_integral_preimage_closedBall_nhdsGT` and
  `MeasureTheory.IntegrableOn.tendsto_setAverage_preimage_closedBall_nhdsGT`: right-continuity of
  closed-ball integrals and averages in the radius.
* `MeasureTheory.AEStronglyMeasurable.integral_preimage_closedBall` and
  `MeasureTheory.AEStronglyMeasurable.setAverage_preimage_closedBall`: strong measurability of
  closed-ball integrals and averages in the centre.
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

/-- For an a.e.-measurable map `g : Y → X`, as `ρ → r⁺` the measures of `g ⁻¹' closedBall x ρ`
tend to the measure of `g ⁻¹' closedBall x r`, provided some larger closed ball has finite
preimage measure. -/
theorem tendsto_measure_preimage_closedBall_nhdsGT {Y : Type*} [OpensMeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure Y) {g : Y → X} (hg : AEMeasurable g μ) {x : X} {r : ℝ}
    (hfin : ∃ R > r, μ (g ⁻¹' closedBall x R) ≠ ∞) :
    Tendsto (fun ρ => μ (g ⁻¹' closedBall x ρ)) (𝓝[>] r) (𝓝 (μ (g ⁻¹' closedBall x r))) := by
  have hInter : (⋂ ρ > r, g ⁻¹' closedBall x ρ) = g ⁻¹' closedBall x r := by
    ext y
    simp only [mem_iInter, mem_preimage, mem_closedBall]
    refine ⟨fun h => ?_, fun h _ hρ => h.trans hρ.le⟩
    by_contra hlt
    obtain ⟨ρ, hrρ, hρy⟩ := exists_between (not_le.1 hlt)
    exact hρy.not_ge (h ρ hrρ)
  rw [← hInter]
  exact tendsto_measure_biInter_gt
    (fun _ _ => hg.nullMeasurable measurableSet_closedBall)
    (fun _ _ _ hij => preimage_mono (closedBall_subset_closedBall hij)) hfin

/-- As `ρ → r⁺`, the measures of `closedBall x ρ` tend to the measure of `closedBall x r`,
provided some larger closed ball has finite measure. -/
theorem tendsto_measure_closedBall_nhdsGT [OpensMeasurableSpace X] (μ : Measure X) {x : X} {r : ℝ}
    (hfin : ∃ R > r, μ (closedBall x R) ≠ ∞) :
    Tendsto (fun ρ => μ (closedBall x ρ)) (𝓝[>] r) (𝓝 (μ (closedBall x r))) :=
  μ.tendsto_measure_preimage_closedBall_nhdsGT aemeasurable_id hfin

/-- For an `s`-finite measure `μ` and an a.e.-measurable map `g : Y → X` into a second-countable
pseudometric space, the measure of `g ⁻¹' closedBall x r` is a measurable function of `x`. -/
theorem measurable_preimage_closedBall {Y : Type*} [SecondCountableTopology X]
    [OpensMeasurableSpace X] [MeasurableSpace Y] (μ : Measure Y) [SFinite μ] {g : Y → X}
    (hg : AEMeasurable g μ) (r : ℝ) : Measurable fun x : X => μ (g ⁻¹' closedBall x r) := by
  let S : Set (X × Y) := {p | dist (hg.mk g p.2) p.1 ≤ r}
  have hS : MeasurableSet S :=
    measurableSet_le ((hg.measurable_mk.comp measurable_snd).dist measurable_fst) measurable_const
  have heq : (fun x : X => μ (g ⁻¹' closedBall x r)) =
      fun x : X => μ (hg.mk g ⁻¹' closedBall x r) := funext fun x =>
    measure_congr (hg.ae_eq_mk.mono fun y hy => by simp [hy])
  rw [heq]
  exact measurable_measure_prodMk_left hS

/-- For an `s`-finite measure on a second-countable pseudometric space, the measure of
`closedBall x r` is a measurable function of `x`. -/
theorem measurable_closedBall [SecondCountableTopology X] [OpensMeasurableSpace X] (μ : Measure X)
    [SFinite μ] (r : ℝ) : Measurable fun x : X => μ (closedBall x r) :=
  μ.measurable_preimage_closedBall aemeasurable_id r

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
open scoped ENNReal Topology

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

/-- For an a.e.-measurable map `g : Y → X` and a function `f` integrable on `g ⁻¹' closedBall x R`,
the integrals of `f` over `g ⁻¹' closedBall x ρ` tend to its integral over `g ⁻¹' closedBall x r`
as `ρ → r⁺`, for every `r < R`. -/
theorem tendsto_integral_preimage_closedBall_nhdsGT {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} {g : Y → X} {f : Y → F} {x : X} {r R : ℝ}
    (hf : IntegrableOn f (g ⁻¹' closedBall x R) μ) (hg : AEMeasurable g μ) (hrR : r < R) :
    Tendsto (fun ρ => ∫ y in g ⁻¹' closedBall x ρ, f y ∂μ) (𝓝[>] r)
      (𝓝 (∫ y in g ⁻¹' closedBall x r, f y ∂μ)) := by
  have hset (ρ : ℝ) : g ⁻¹' closedBall x ρ =ᵐ[μ] hg.mk g ⁻¹' closedBall x ρ :=
    hg.ae_eq_mk.mono fun y hy => by simp [hy]
  have hf' : IntegrableOn f (hg.mk g ⁻¹' closedBall x R) μ := hf.congr_set_ae (hset R).symm
  have hm (ρ : ℝ) : MeasurableSet (hg.mk g ⁻¹' closedBall x ρ) :=
    measurableSet_closedBall.preimage hg.measurable_mk
  simp_rw [setIntegral_congr_set (hset _), ← integral_indicator (hm _)]
  refine tendsto_integral_filter_of_dominated_convergence
    ((hg.mk g ⁻¹' closedBall x R).indicator fun y => ‖f y‖) ?_ ?_
    (IntegrableOn.integrable_indicator hf'.norm (hm R)) ?_
  · filter_upwards [Ioo_mem_nhdsGT hrR] with ρ hρ
    exact ((hf'.mono_set
      (preimage_mono (closedBall_subset_closedBall hρ.2.le))).integrable_indicator
      (hm ρ)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT hrR] with ρ hρ
    refine Eventually.of_forall fun y => ?_
    rw [norm_indicator_eq_indicator_norm]
    exact indicator_le_indicator_of_subset (preimage_mono (closedBall_subset_closedBall hρ.2.le))
      (fun _ => norm_nonneg _) y
  · refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ hg.mk g ⁻¹' closedBall x r
    · rw [indicator_of_mem hy]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact (indicator_of_mem
        (preimage_mono (closedBall_subset_closedBall (le_of_lt hρ)) hy) f).symm
    · rw [indicator_of_notMem hy]
      refine tendsto_const_nhds.congr' ?_
      have hlt : r < dist (hg.mk g y) x := not_le.1 hy
      filter_upwards [Ioo_mem_nhdsGT hlt] with ρ hρ
      exact (indicator_of_notMem (fun h => hρ.2.not_ge h) f).symm

/-- For a function integrable on `closedBall x R`, its integrals over `closedBall x ρ` tend to its
integral over `closedBall x r` as `ρ → r⁺`, for every `r < R`. -/
theorem tendsto_integral_closedBall_nhdsGT {f : X → F} {x : X} {r R : ℝ}
    (hf : IntegrableOn f (closedBall x R) μ) (hrR : r < R) :
    Tendsto (fun ρ => ∫ y in closedBall x ρ, f y ∂μ) (𝓝[>] r)
      (𝓝 (∫ y in closedBall x r, f y ∂μ)) :=
  hf.tendsto_integral_preimage_closedBall_nhdsGT aemeasurable_id hrR

/-- For an a.e.-measurable map `g : Y → X` and a function `f` integrable on `g ⁻¹' closedBall x R`
where that preimage has finite measure and `g ⁻¹' closedBall x r` has positive measure, the
averages of `f` over `g ⁻¹' closedBall x ρ` are right-continuous at `r` for `r < R`. -/
theorem tendsto_setAverage_preimage_closedBall_nhdsGT {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} {g : Y → X} {f : Y → F} {x : X} {r R : ℝ}
    (hf : IntegrableOn f (g ⁻¹' closedBall x R) μ) (hg : AEMeasurable g μ) (hrR : r < R)
    (hfin : μ (g ⁻¹' closedBall x R) ≠ ∞) (hpos : μ (g ⁻¹' closedBall x r) ≠ 0) :
    Tendsto (fun ρ => ⨍ y in g ⁻¹' closedBall x ρ, f y ∂μ) (𝓝[>] r)
      (𝓝 (⨍ y in g ⁻¹' closedBall x r, f y ∂μ)) := by
  have hfin_r : μ (g ⁻¹' closedBall x r) ≠ ∞ :=
    measure_ne_top_of_subset (preimage_mono (closedBall_subset_closedBall hrR.le)) hfin
  have hm : Tendsto (fun ρ => μ.real (g ⁻¹' closedBall x ρ)) (𝓝[>] r)
      (𝓝 (μ.real (g ⁻¹' closedBall x r))) :=
    (ENNReal.tendsto_toReal hfin_r).comp
      (μ.tendsto_measure_preimage_closedBall_nhdsGT hg ⟨R, hrR, hfin⟩)
  simp_rw [setAverage_eq]
  exact (hm.inv₀ (ENNReal.toReal_ne_zero.2 ⟨hpos, hfin_r⟩)).smul
    (hf.tendsto_integral_preimage_closedBall_nhdsGT hg hrR)

/-- For a function integrable on `closedBall x R` of finite measure with `μ (closedBall x r) ≠ 0`,
its averages over `closedBall x ρ` are right-continuous at `r` for `r < R`. -/
theorem tendsto_setAverage_closedBall_nhdsGT {f : X → F} {x : X} {r R : ℝ}
    (hf : IntegrableOn f (closedBall x R) μ) (hrR : r < R)
    (hfin : μ (closedBall x R) ≠ ∞) (hpos : μ (closedBall x r) ≠ 0) :
    Tendsto (fun ρ => ⨍ y in closedBall x ρ, f y ∂μ) (𝓝[>] r)
      (𝓝 (⨍ y in closedBall x r, f y ∂μ)) :=
  hf.tendsto_setAverage_preimage_closedBall_nhdsGT aemeasurable_id hrR hfin hpos

end MeasureTheory.IntegrableOn

namespace MeasureTheory.AEStronglyMeasurable

open Metric Set

variable {X Y F : Type*} [PseudoMetricSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [MeasurableSpace Y] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For an `s`-finite measure `μ`, an a.e.-measurable map `g : Y → X` into a second-countable
pseudometric space, and an a.e.-strongly measurable function `f`, the integral of `f` over
`g ⁻¹' closedBall x r` is a strongly measurable function of `x`. -/
theorem integral_preimage_closedBall {μ : Measure Y} [SFinite μ] {g : Y → X} {f : Y → F}
    (hf : AEStronglyMeasurable f μ) (hg : AEMeasurable g μ) (r : ℝ) :
    StronglyMeasurable fun x : X => ∫ y in g ⁻¹' closedBall x r, f y ∂μ := by
  let S : Set (X × Y) := {p | dist (hg.mk g p.2) p.1 ≤ r}
  have hS : MeasurableSet S :=
    _root_.measurableSet_le ((hg.measurable_mk.comp measurable_snd).dist measurable_fst)
      measurable_const
  have heq : (fun x : X => ∫ y in g ⁻¹' closedBall x r, f y ∂μ) =
      fun x : X => ∫ y in hg.mk g ⁻¹' closedBall x r, hf.mk f y ∂μ := funext fun x => by
    have hset : g ⁻¹' closedBall x r =ᵐ[μ] hg.mk g ⁻¹' closedBall x r :=
      hg.ae_eq_mk.mono fun y hy => by simp [hy]
    rw [setIntegral_congr_set hset]
    exact integral_congr_ae (ae_restrict_of_ae hf.ae_eq_mk)
  rw [heq]
  simp_rw [← integral_indicator (measurableSet_closedBall.preimage hg.measurable_mk)]
  exact ((hf.stronglyMeasurable_mk.comp_measurable measurable_snd).indicator
    hS).integral_prod_right'

/-- For an `s`-finite measure on a second-countable pseudometric space and an a.e.-strongly
measurable function `f`, the integral of `f` over `closedBall x r` is strongly measurable in
`x`. -/
theorem integral_closedBall {μ : Measure X} [SFinite μ] {f : X → F}
    (hf : AEStronglyMeasurable f μ) (r : ℝ) :
    StronglyMeasurable fun x : X => ∫ y in closedBall x r, f y ∂μ :=
  hf.integral_preimage_closedBall aemeasurable_id r

/-- For an `s`-finite measure `μ`, an a.e.-measurable map `g : Y → X` into a second-countable
pseudometric space, and an a.e.-strongly measurable function `f`, the average of `f` over
`g ⁻¹' closedBall x r` is a strongly measurable function of `x`. -/
theorem setAverage_preimage_closedBall {μ : Measure Y} [SFinite μ] {g : Y → X} {f : Y → F}
    (hf : AEStronglyMeasurable f μ) (hg : AEMeasurable g μ) (r : ℝ) :
    StronglyMeasurable fun x : X => ⨍ y in g ⁻¹' closedBall x r, f y ∂μ := by
  simp_rw [setAverage_eq]
  exact ((μ.measurable_preimage_closedBall hg r).ennreal_toReal.inv.stronglyMeasurable).smul
    (hf.integral_preimage_closedBall hg r)

/-- For an `s`-finite measure on a second-countable pseudometric space and an a.e.-strongly
measurable function `f`, the average of `f` over `closedBall x r` is strongly measurable in
`x`. -/
theorem setAverage_closedBall {μ : Measure X} [SFinite μ] {f : X → F}
    (hf : AEStronglyMeasurable f μ) (r : ℝ) :
    StronglyMeasurable fun x : X => ⨍ y in closedBall x r, f y ∂μ :=
  hf.setAverage_preimage_closedBall aemeasurable_id r

end MeasureTheory.AEStronglyMeasurable
