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
* `TauCeti.setLIntegral_riemannianVolume_of_subset`: integration over a subset of a chart source
  in coordinates, and `TauCeti.setLIntegral_riemannianVolume_inter_preimage`, its form over the
  chart preimage of an open coordinate set.
* `TauCeti.setLIntegral_comp_extChartAt_symm_le_mul_lintegral`: where the chart density is at
  least `m > 0`, coordinate integrals are at most `m⁻¹` times Riemannian integrals.
* `TauCeti.isLocallyFiniteMeasure_riemannianVolume`: the Riemannian volume is locally finite.
-/

public section

open Bundle MeasureTheory Set
open scoped ENNReal Manifold Topology

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
    existsUnique_restrict_eq (μ := chartRiemannianVolume (I := I))
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

section Coordinates

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- **Integration in coordinates** against the Riemannian volume: over a measurable subset of a
chart source, the integral of `φ` is the coordinate integral of `φ` read in the chart times the
chart density. -/
theorem setLIntegral_riemannianVolume_of_subset {α : M} {s : Set M}
    (hs : s ⊆ (chartAt H α).source) (hs' : MeasurableSet s) (φ : M → ℝ≥0∞) :
    ∫⁻ x in s, φ x ∂riemannianVolume I M =
      ∫⁻ y in (extChartAt I α) '' s,
        ENNReal.ofReal (chartVolumeDensity (I := I) α ((extChartAt I α).symm y)) *
          φ ((extChartAt I α).symm y) ∂(Module.finBasis ℝ E).addHaar := by
  rw [← Measure.restrict_restrict_of_subset hs, riemannianVolume_restrict_source,
    setLIntegral_chartRiemannianVolume α hs', inter_eq_left.2 (by rwa [extChartAt_source])]

/-- **Integration in coordinates over an open coordinate set**: for an open set `Ω` of the chart
target, the integral of `φ` over the chart preimage of `Ω` is the integral over `Ω` of `φ` read in
the chart times the chart density. -/
theorem setLIntegral_riemannianVolume_inter_preimage (α : M) {Ω : Set E} (hΩ : IsOpen Ω)
    (hΩt : Ω ⊆ (extChartAt I α).target) (φ : M → ℝ≥0∞) :
    ∫⁻ x in (extChartAt I α).source ∩ extChartAt I α ⁻¹' Ω, φ x ∂riemannianVolume I M =
      ∫⁻ y in Ω, ENNReal.ofReal (chartVolumeDensity (I := I) α ((extChartAt I α).symm y)) *
        φ ((extChartAt I α).symm y) ∂(Module.finBasis ℝ E).addHaar := by
  have himage : extChartAt I α '' ((extChartAt I α).source ∩ extChartAt I α ⁻¹' Ω) = Ω := by
    rw [PartialEquiv.image_source_inter_eq',
      PartialEquiv.target_inter_inv_preimage_preimage, inter_eq_right.2 hΩt]
  have hsub : (extChartAt I α).source ∩ extChartAt I α ⁻¹' Ω ⊆ (chartAt H α).source := by
    rw [← extChartAt_source (I := I)]
    exact inter_subset_left
  rw [setLIntegral_riemannianVolume_of_subset hsub
    (isOpen_extChartAt_preimage' α hΩ).measurableSet, himage]

/-- **Coordinate integrals are controlled by Riemannian integrals** where the chart density is
bounded below: if the density is at least `m > 0` on an open set `Ω` of the chart target, then the
integral over `Ω` of `φ` read in the chart is at most `m⁻¹` times the integral of `φ` over `M`. -/
theorem setLIntegral_comp_extChartAt_symm_le_mul_lintegral (α : M) {Ω : Set E} (hΩ : IsOpen Ω)
    (hΩt : Ω ⊆ (extChartAt I α).target) {m : ℝ} (hm : 0 < m)
    (hρ : ∀ y ∈ Ω, m ≤ chartVolumeDensity (I := I) α ((extChartAt I α).symm y)) (φ : M → ℝ≥0∞) :
    ∫⁻ y in Ω, φ ((extChartAt I α).symm y) ∂(Module.finBasis ℝ E).addHaar ≤
      ENNReal.ofReal m⁻¹ * ∫⁻ x, φ x ∂riemannianVolume I M := by
  calc ∫⁻ y in Ω, φ ((extChartAt I α).symm y) ∂(Module.finBasis ℝ E).addHaar
      ≤ ∫⁻ y in Ω, ENNReal.ofReal m⁻¹ *
          (ENNReal.ofReal (chartVolumeDensity (I := I) α ((extChartAt I α).symm y)) *
            φ ((extChartAt I α).symm y)) ∂(Module.finBasis ℝ E).addHaar := by
        refine setLIntegral_mono' hΩ.measurableSet fun y hy ↦ ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        refine le_mul_of_one_le_left bot_le (ENNReal.one_le_ofReal.2 ?_)
        rw [inv_mul_eq_div, one_le_div hm]
        exact hρ y hy
    _ = ENNReal.ofReal m⁻¹ *
          ∫⁻ x in (extChartAt I α).source ∩ extChartAt I α ⁻¹' Ω, φ x ∂riemannianVolume I M := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          setLIntegral_riemannianVolume_inter_preimage α hΩ hΩt]
    _ ≤ ENNReal.ofReal m⁻¹ * ∫⁻ x, φ x ∂riemannianVolume I M :=
        mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) bot_le

end Coordinates

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
