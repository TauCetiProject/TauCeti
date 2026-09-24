/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Measure
public import TauCeti.MeasureTheory.Measure.Glue

/-!
# The Riemannian volume measure

A continuous Riemannian metric on a manifold `M` determines a measure on `M`: in each chart it is
coordinate Lebesgue measure weighted by the square root of the metric Gram determinant, the
local measure `TauCeti.chartRiemannianVolume`. These local measures agree on chart overlaps, so
when countably many chart sources cover `M` (for instance when `M` is second countable, or
`σ`-compact) they glue to a unique measure on the Borel `σ`-algebra of `M`,
`TauCeti.riemannianVolume I M`.

The construction needs no orientation and applies to manifolds with boundary or corners. The
Riemannian volume is locally finite, so it is a finite measure on a compact manifold; this is the
measure against which the total volume of a closed Riemannian manifold is taken.

The construction follows J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer
GTM 176 (2018), Proposition 2.44 and the discussion of the Riemannian density following it.

## Main definitions

* `TauCeti.riemannianVolume`: the Riemannian volume measure of a manifold with a continuous
  Riemannian metric.

## Main results

* `TauCeti.riemannianVolume_restrict_source`: on the source of each preferred chart, the
  Riemannian volume is the chart volume.
* `TauCeti.eq_riemannianVolume_iff`: this property characterizes the Riemannian volume.
* `TauCeti.riemannianVolume_apply_of_subset`: the volume of a subset of a chart source is its
  chart volume.
* `TauCeti.isLocallyFiniteMeasure_riemannianVolume`: the Riemannian volume is locally finite.
-/

public section

open Bundle MeasureTheory Set
open scoped Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- The chart volume measures glue to a unique measure on the manifold. -/
private theorem existsUnique_restrict_eq_chartRiemannianVolume :
    ∃! ν : Measure M, ∀ α : M,
      ν.restrict (chartAt H α).source = chartRiemannianVolume (I := I) α := by
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover (fun x : M ↦ (chartAt H x).source)
    fun x ↦ chart_source_mem_nhds H x
  simpa only [chartRiemannianVolume_restrict_source] using
    Measure.existsUnique_restrict_eq (μ := chartRiemannianVolume (I := I))
      (fun α : M ↦ (chartAt H α).open_source.measurableSet) ht hcover fun α β ↦ by
        simpa only [extChartAt_source] using chartRiemannianVolume_restrict_overlap (I := I) α β

variable (I M) in
/-- The **Riemannian volume measure** of a manifold `M` with a continuous Riemannian metric: the
unique measure whose restriction to the source of each preferred chart is the chart volume
`TauCeti.chartRiemannianVolume`, coordinate Lebesgue measure weighted by the square root of the
metric Gram determinant. It is characterized by `TauCeti.eq_riemannianVolume_iff`. -/
def riemannianVolume : Measure M :=
  (existsUnique_restrict_eq_chartRiemannianVolume I M).exists.choose

/-- On the source of each preferred chart, the Riemannian volume is the chart volume. -/
@[simp]
theorem riemannianVolume_restrict_source (α : M) :
    (riemannianVolume I M).restrict (chartAt H α).source = chartRiemannianVolume (I := I) α :=
  (existsUnique_restrict_eq_chartRiemannianVolume I M).exists.choose_spec α

/-- The Riemannian volume is the only measure agreeing with the chart volume on the source of
every preferred chart. -/
theorem eq_riemannianVolume_iff {ν : Measure M} :
    ν = riemannianVolume I M ↔
      ∀ α : M, ν.restrict (chartAt H α).source = chartRiemannianVolume (I := I) α := by
  refine ⟨fun h ↦ h ▸ riemannianVolume_restrict_source, fun h ↦ ?_⟩
  exact (existsUnique_restrict_eq_chartRiemannianVolume I M).unique h
    riemannianVolume_restrict_source

/-- The Riemannian volume of a subset of a chart source is its chart volume. -/
theorem riemannianVolume_apply_of_subset {α : M} {s : Set M} (hs : s ⊆ (chartAt H α).source) :
    riemannianVolume I M s = chartRiemannianVolume (I := I) α s := by
  rw [← riemannianVolume_restrict_source α, Measure.restrict_eq_self _ hs]

/-- The Riemannian volume is locally finite: every point has a neighbourhood of finite volume. In
particular, the Riemannian volume of a compact manifold is a finite measure. -/
instance isLocallyFiniteMeasure_riemannianVolume :
    IsLocallyFiniteMeasure (riemannianVolume I M) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨s, hs, hfin⟩ :=
    chartRiemannianVolume_finiteAtFilter_nhds (I := I) x (mem_chart_source H x)
  refine ⟨s ∩ (chartAt H x).source, Filter.inter_mem hs (chart_source_mem_nhds H x), ?_⟩
  rw [riemannianVolume_apply_of_subset inter_subset_right]
  exact (measure_mono inter_subset_left).trans_lt hfin

end TauCeti
