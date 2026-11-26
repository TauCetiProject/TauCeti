/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Measures read in the charts of a manifold

A measure `μ` on a manifold is read in the preferred chart at `x` as the pushforward by
`extChartAt I x` of `μ` restricted to the chart source. This file collects the basic facts about
these chart pushforwards, and two estimates for measures on the model seen through a chart.

It also integrates in an arbitrary chart `e : OpenPartialHomeomorph M E` in which `μ` reads as a
weighted measure `w(y) dν(y)` on the chart target: integrals over the chart source become weighted
integrals over the chart target, and functions supported in the preimage of a compact subset of
the target are integrable.

## Main results

* `TauCeti.map_restrict_extChartAt_source_apply_image`: the chart pushforward gives the chart
  image of a measurable subset of the source the measure of the subset.
* `TauCeti.restrict_extChartAt_source_eq_of_map_eq`: two measures with the same chart pushforward
  agree on the chart source.
* `TauCeti.map_withDensity_restrict_extChartAt_source`: reweighting by a continuous function read
  in the chart multiplies a chart density by that function.
* `TauCeti.measure_image_extChartAt_inter_source_pos`: the chart image of the part of an open set
  in the chart source has positive measure when that part is nonempty, even at boundary or corner
  points.
* `TauCeti.exists_isOpen_setLIntegral_image_extChartAt_lt_top`: a function continuous on the chart
  target has finite integral over the chart image of a small open neighbourhood of `x`.
* `OpenPartialHomeomorph.setIntegral_source_eq_setIntegral_target_smul`: for a measure that reads
  in a chart `e` as `w(y) dν(y)`, the integral over the chart source is computed in coordinates,
  `∫_{e.source} F dμ = ∫_{e.target} w(y) F(e⁻¹ y) dν(y)`.
* `OpenPartialHomeomorph.integral_eq_setIntegral_target_smul`: the same formula for the integral
  over `M` of a function continuous on the chart source and vanishing off it.
* `OpenPartialHomeomorph.integrable_of_support_subset_symm_image`: for such a measure, a function
  continuous on the chart source and supported in the preimage of a compact subset of the chart
  target is integrable.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Measures on the model seen through a chart -/

/-- The chart image of the part of an open set `U` in the source of the preferred chart at `x`
has positive measure, when that part is nonempty, for every measure on the model that is positive
on nonempty open sets. This holds also at boundary or corner points, where the chart image need not
be open. -/
theorem measure_image_extChartAt_inter_source_pos {U : Set M} (hU : IsOpen U) {x : M}
    (hne : (U ∩ (extChartAt I x).source).Nonempty) (ν : Measure E) [ν.IsOpenPosMeasure] :
    0 < ν (extChartAt I x '' (U ∩ (extChartAt I x).source)) := by
  let e := extChartAt I x
  obtain ⟨z, hzU, hz⟩ := hne
  rw [inter_comm U, e.image_source_inter_eq', inter_comm]
  -- The chart image of `U ∩ e.source` contains `e z` in the closure of its interior.
  refine Measure.measure_pos_of_nonempty_interior _ (Nonempty.of_closure ⟨e z, ?_⟩)
  exact extChartAt_mem_closure_interior (I := I) (x₀ := x)
    (subset_closure (mem_interior_iff_mem_nhds.2 (hU.mem_nhds hzU))) hz

/-- A function continuous on the target of the preferred chart at `x` has finite integral, for a
measure on a finite-dimensional model that is finite on compact sets, over the chart image of a
small open neighbourhood of `x` in the chart source. -/
theorem exists_isOpen_setLIntegral_image_extChartAt_lt_top [FiniteDimensional ℝ E] {g : E → ℝ}
    {x : M} (hg : ContinuousOn g (extChartAt I x).target) (ν : Measure E)
    [IsFiniteMeasureOnCompacts ν] :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ (extChartAt I x).source ∧
      ∫⁻ y in extChartAt I x '' U, ENNReal.ofReal (g y) ∂ν < ∞ := by
  let e := extChartAt I x
  have hxe : x ∈ e.source := mem_extChartAt_source x
  -- Near `e x` in the model, the function stays below `g (e x) + 1`.
  let V := {y | g y < g (e x) + 1} ∩ Metric.ball (e x) 1
  have hV : V ∈ 𝓝[range I] (e x) := by
    refine Filter.inter_mem ?_ (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ one_pos))
    rw [← nhdsWithin_extChartAt_target_eq' hxe]
    exact (hg (e x) (e.map_source hxe)).eventually_lt_const (lt_add_one _)
  have hU : e.source ∩ e ⁻¹' V ∈ 𝓝 x := Filter.inter_mem (extChartAt_source_mem_nhds' hxe)
    (extChartAt_preimage_mem_nhds_of_mem_nhdsWithin hxe hV)
  refine ⟨interior (e.source ∩ e ⁻¹' V), isOpen_interior, mem_interior_iff_mem_nhds.2 hU,
    interior_subset.trans inter_subset_left, ?_⟩
  have himage : e '' interior (e.source ∩ e ⁻¹' V) ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact (interior_subset hz).2
  refine setLIntegral_lt_top_of_le_nnreal ?_ ⟨(g (e x) + 1).toNNReal, fun y hy ↦ ?_⟩
  · exact ((measure_mono (himage.trans inter_subset_right)).trans_lt measure_ball_lt_top).ne
  · exact ENNReal.ofReal_le_ofReal (himage hy).1.le

/-! ### Chart pushforwards of measures on the manifold -/

variable [MeasurableSpace M] [BorelSpace M] [BorelSpace E] {μ : Measure M}

/-- The pushforward of `μ` restricted to a chart source gives a measurable set of the model the
measure of its preimage in the chart source. -/
theorem map_restrict_extChartAt_source_apply (x : M) {A : Set E} (hA : MeasurableSet A) :
    (μ.restrict (extChartAt I x).source).map (extChartAt I x) A =
      μ ((extChartAt I x) ⁻¹' A ∩ (extChartAt I x).source) := by
  have hsrc : MeasurableSet (extChartAt I x).source := (isOpen_extChartAt_source x).measurableSet
  rw [Measure.map_apply_of_aemeasurable ((continuousOn_extChartAt x).aemeasurable hsrc) hA,
    Measure.restrict_apply' hsrc]

/-- The pushforward of `μ` restricted to a chart source gives the coordinate image of a measurable
subset of the source the measure that `μ` gives the subset. -/
theorem map_restrict_extChartAt_source_apply_image {x : M} {s : Set M} (hs : MeasurableSet s)
    (hsub : s ⊆ (extChartAt I x).source) :
    (μ.restrict (extChartAt I x).source).map (extChartAt I x) ((extChartAt I x) '' s) = μ s := by
  rw [map_restrict_extChartAt_source_apply x (hs.image_extChartAt x hsub),
    (extChartAt I x).injOn.preimage_image_inter hsub]

/-- Two measures with the same pushforward from a chart source agree on that source. -/
theorem restrict_extChartAt_source_eq_of_map_eq {x : M} {α β : Measure M}
    (h : (α.restrict (extChartAt I x).source).map (extChartAt I x) =
      (β.restrict (extChartAt I x).source).map (extChartAt I x)) :
    α.restrict (extChartAt I x).source = β.restrict (extChartAt I x).source := by
  have hsrc : MeasurableSet (extChartAt I x).source := (isOpen_extChartAt_source x).measurableSet
  ext B hB
  rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
    ← map_restrict_extChartAt_source_apply_image (hB.inter hsrc) inter_subset_right, h,
    map_restrict_extChartAt_source_apply_image (hB.inter hsrc) inter_subset_right]

/-- In a chart where `μ` has a continuous density `w`, reweighting `μ` by a nonnegative continuous
function `h` read in the chart multiplies the chart density by `h`. -/
theorem map_withDensity_restrict_extChartAt_source {x : M} {ν : Measure E}
    {w h : E → ℝ} (hwc : ContinuousOn w (extChartAt I x).target)
    (hhc : ContinuousOn h (extChartAt I x).target) (hh : ∀ y ∈ (extChartAt I x).target, 0 ≤ h y)
    (hw : (μ.restrict (extChartAt I x).source).map (extChartAt I x) =
      (ν.restrict (extChartAt I x).target).withDensity fun y ↦ ENNReal.ofReal (w y)) :
    ((μ.restrict (extChartAt I x).source).withDensity
        fun z ↦ ENNReal.ofReal (h (extChartAt I x z))).map (extChartAt I x) =
      (ν.restrict (extChartAt I x).target).withDensity fun y ↦ ENNReal.ofReal (h y * w y) := by
  let e := extChartAt I x
  have hsrc : MeasurableSet e.source := (isOpen_extChartAt_source x).measurableSet
  have htgt : MeasurableSet e.target := measurableSet_extChartAt_target x
  -- The weight `h`, extended measurably by zero off the target.
  classical
  let g : E → ℝ≥0∞ := e.target.piecewise (fun y ↦ ENNReal.ofReal (h y)) 0
  have hg : Measurable g :=
    (ENNReal.continuous_ofReal.comp_continuousOn hhc).measurable_piecewise continuousOn_const htgt
  have hae : AEMeasurable e (μ.restrict e.source) := (continuousOn_extChartAt x).aemeasurable hsrc
  have hcomp : (fun z ↦ ENNReal.ofReal (h (e z))) =ᵐ[μ.restrict e.source] g ∘ hae.mk e := by
    refine Filter.EventuallyEq.trans ?_ (hae.ae_eq_mk.fun_comp g)
    filter_upwards [ae_restrict_mem hsrc] with z hz
    have hgz : g (e z) = ENNReal.ofReal (h (e z)) := piecewise_eq_of_mem _ _ _ (e.map_source hz)
    rw [Function.comp_apply, hgz]
  rw [withDensity_congr_ae hcomp,
    Measure.map_congr ((withDensity_absolutelyContinuous _ _).ae_le hae.ae_eq_mk),
    Measure.map_withDensity_comp hae.measurable_mk.aemeasurable hg.aemeasurable,
    ← Measure.map_congr hae.ae_eq_mk, hw,
    ← withDensity_mul₀ (f := fun y ↦ ENNReal.ofReal (w y))
      ((ENNReal.continuous_ofReal.comp_continuousOn hwc).aemeasurable htgt) hg.aemeasurable]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem htgt] with y hy
  have hgy : g y = ENNReal.ofReal (h y) := piecewise_eq_of_mem _ _ _ hy
  rw [Pi.mul_apply, hgy, mul_comm, ENNReal.ofReal_mul (hh y hy)]

end TauCeti

/-! ### Integrals read in a chart -/

namespace OpenPartialHomeomorph

variable {M E G : Type*} [TopologicalSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {e : OpenPartialHomeomorph M E} {μ : Measure M} {ν : Measure E} {w : E → ℝ}

/-- **Integrals in a chart.** Let `μ` read in the chart `e` as the measure `w(y) dν(y)` on the
chart target, with `w` measurable and nonnegative there. A function `F` whose reading `F ∘ e⁻¹` is
measurable on the chart target has integral over the chart source
`∫_{e.source} F dμ = ∫_{e.target} w(y) F(e⁻¹ y) dν(y)`. -/
theorem setIntegral_source_eq_setIntegral_target_smul
    (hμ : (μ.restrict e.source).map e =
      (ν.restrict e.target).withDensity fun y ↦ ENNReal.ofReal (w y))
    (hw : AEMeasurable w (ν.restrict e.target)) (hw0 : ∀ y ∈ e.target, 0 ≤ w y) {F : M → G}
    (hF : AEStronglyMeasurable (F ∘ e.symm) (ν.restrict e.target)) :
    ∫ x in e.source, F x ∂μ = ∫ y in e.target, w y • F (e.symm y) ∂ν := by
  have hsrc : MeasurableSet e.source := e.open_source.measurableSet
  have htgt : MeasurableSet e.target := e.open_target.measurableSet
  have he : AEMeasurable e (μ.restrict e.source) := e.continuousOn.aemeasurable hsrc
  rw [integral_congr_ae (g := fun x ↦ (F ∘ e.symm) (e x)) ((ae_restrict_mem hsrc).mono fun x hx ↦ by
      simp [e.left_inv hx]),
    ← integral_map he (hμ ▸ hF.mono_ac (withDensity_absolutelyContinuous _ _)), hμ,
    integral_withDensity_eq_integral_toReal_smul₀ (f := fun y ↦ ENNReal.ofReal (w y))
      hw.ennreal_ofReal (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun htgt fun y hy ↦ ?_
  simp [ENNReal.toReal_ofReal (hw0 y hy)]

/-- Let `μ` read in the chart `e` as the measure `w(y) dν(y)` on the chart target, with `w`
measurable and nonnegative there. A function `F` continuous on the chart source and vanishing off
it has integral `∫ F dμ = ∫_{e.target} w(y) F(e⁻¹ y) dν(y)`. -/
theorem integral_eq_setIntegral_target_smul [SecondCountableTopology E]
    (hμ : (μ.restrict e.source).map e =
      (ν.restrict e.target).withDensity fun y ↦ ENNReal.ofReal (w y))
    (hw : AEMeasurable w (ν.restrict e.target)) (hw0 : ∀ y ∈ e.target, 0 ≤ w y) {F : M → G}
    (hF : ContinuousOn F e.source) (hF0 : ∀ x ∉ e.source, F x = 0) :
    ∫ x, F x ∂μ = ∫ y in e.target, w y • F (e.symm y) ∂ν := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hF0]
  exact setIntegral_source_eq_setIntegral_target_smul hμ hw hw0
    ((hF.comp e.continuousOn_symm e.mapsTo_symm).aestronglyMeasurable e.open_target.measurableSet)

/-- A function continuous on the chart source and supported in the preimage `e⁻¹(K)` of a compact
subset `K` of the chart target is integrable for `μ`, when `μ` reads in the chart as a measure
finite on compact sets with a continuous density. -/
theorem integrable_of_support_subset_symm_image [T2Space E] [IsFiniteMeasureOnCompacts ν]
    (hμ : (μ.restrict e.source).map e =
      (ν.restrict e.target).withDensity fun y ↦ ENNReal.ofReal (w y))
    (hw : ContinuousOn w e.target) {F : M → G} (hF : ContinuousOn F e.source) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ e.target) (hFK : Function.support F ⊆ e.symm '' K) :
    Integrable F μ := by
  have hsrc : MeasurableSet e.source := e.open_source.measurableSet
  have htgt : MeasurableSet e.target := e.open_target.measurableSet
  have hKs : e.symm '' K ⊆ e.source := (image_mono hKt).trans e.symm_image_target_eq_source.le
  have hG : ContinuousOn (F ∘ e.symm) e.target := hF.comp e.continuousOn_symm e.mapsTo_symm
  have hwG : ContinuousOn (fun y ↦ (ENNReal.ofReal (w y)).toReal • (F ∘ e.symm) y) e.target := by
    simp only [ENNReal.toReal_ofReal']
    exact ((continuous_id.max continuous_const).comp_continuousOn hw).smul hG
  -- Read in the chart, the weighted function is continuous on the target and supported in `K`.
  have hint : Integrable (F ∘ e.symm) ((ν.restrict e.target).withDensity
      fun y ↦ ENNReal.ofReal (w y)) := by
    rw [integrable_withDensity_iff_integrable_smul₀' (f := fun y ↦ ENNReal.ofReal (w y))
      ((ENNReal.continuous_ofReal.comp_continuousOn hw).aemeasurable htgt)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    refine IntegrableOn.integrable_of_ae_notMem_eq_zero (s := K) ?_ ?_
    · rw [IntegrableOn, Measure.restrict_restrict_of_subset hKt]
      exact (hwG.mono hKt).integrableOn_compact hK
    filter_upwards [ae_restrict_mem htgt] with y hy hyK
    -- At a point of the target outside `K`, `F ∘ e⁻¹` vanishes.
    have : F (e.symm y) = 0 := by
      by_contra h
      obtain ⟨x, hxK, hxy⟩ := hFK h
      exact hyK (e.symm.injOn (by simpa using hKt hxK) (by simpa using hy) hxy ▸ hxK)
    simp [this]
  have hmap : Integrable (F ∘ e.symm) ((μ.restrict e.source).map e) := by rwa [hμ]
  rw [← integrableOn_iff_integrable_of_support_subset (hFK.trans hKs), IntegrableOn]
  refine ((integrable_map_measure hmap.aestronglyMeasurable
    (e.continuousOn.aemeasurable hsrc)).1 hmap).congr ?_
  filter_upwards [ae_restrict_mem hsrc] with x hx
  simp [e.left_inv hx]

end OpenPartialHomeomorph
