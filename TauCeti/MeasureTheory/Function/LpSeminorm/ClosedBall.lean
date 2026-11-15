/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Normed.Group.Indicator
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Small `Lᵖ` seminorms on small closed balls

For `p < ∞`, the `Lᵖ` seminorm of an `Lᵖ` function on the closed ball of radius `r` about a point
of measure zero tends to zero as `r → 0` (`TauCeti.tendsto_eLpNorm_indicator_closedBall`), by
dominated convergence: off the centre, the restrictions vanish once the radius is small. So the
seminorm is arbitrarily small on small enough closed balls
(`TauCeti.exists_eLpNorm_indicator_closedBall_le`). This chooses the small discs on which an `Lᵖ`
coefficient of a linear elliptic equation is small, as in the similarity principle with `Lᵖ`
coefficients.
-/

public section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace TauCeti

variable {X F : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [NormedAddCommGroup F]

/-- For `p < ∞`, the `Lᵖ` seminorm of an `Lᵖ` function on the closed ball of radius `r` about a
point of measure zero tends to zero as `r → 0`. -/
theorem tendsto_eLpNorm_indicator_closedBall {G : X → F} {p : ℝ≥0∞} (hp : p ≠ ∞)
    (hG : MemLp G p μ) {x₀ : X} (h₀ : μ {x₀} = 0) :
    Tendsto (fun r ↦ eLpNorm ((closedBall x₀ r).indicator G) p μ) (𝓝 0) (𝓝 0) := by
  have h := tendsto_eLpNorm_sub_of_ae_tendsto (l := 𝓝 (0 : ℝ))
    (f := fun r ↦ (closedBall x₀ r).indicator G) (C := 1) (g := 0) hp
    (.of_forall fun r ↦ hG.aestronglyMeasurable.indicator measurableSet_closedBall) hG
    (.of_forall fun r ↦ .of_forall fun x ↦ by
      simpa using eNorm_indicator_le_eNorm_self G x)
    ((measure_eq_zero_iff_ae_notMem.1 h₀).mono fun x hx ↦ ?_)
  · simpa using h
  -- off the centre, `x` lies outside every small enough closed ball
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [gt_mem_nhds (dist_pos.2 hx)] with r hr
  rw [indicator_of_notMem (not_le.2 hr), Pi.zero_apply]

/-- For `p < ∞`, an `Lᵖ` function has arbitrarily small `Lᵖ` seminorm on small enough closed balls
about a point of measure zero. -/
theorem exists_eLpNorm_indicator_closedBall_le {G : X → F} {p : ℝ≥0∞}
    (hp : p ≠ ∞) (hG : MemLp G p μ) {x₀ : X} (h₀ : μ {x₀} = 0) {R : ℝ} {ε : ℝ≥0∞} (hR : 0 < R)
    (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r ≤ R ∧ eLpNorm ((closedBall x₀ r).indicator G) p μ ≤ ε :=
  ((Filter.eventually_mem_set.2 (Ioc_mem_nhdsGT hR)).and (nhdsWithin_le_nhds
    ((tendsto_eLpNorm_indicator_closedBall hp hG h₀).eventually (ge_mem_nhds hε)))).exists.imp
    fun _ ⟨⟨hr, hrR⟩, h⟩ ↦ ⟨hr, hrR, h⟩

end TauCeti
