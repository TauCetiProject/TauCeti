/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Measures read in the preferred charts of a manifold

A measure `μ` on a manifold is read in the preferred chart at `x` as the pushforward by
`extChartAt I x` of `μ` restricted to the chart source. This file collects the basic facts about
these chart pushforwards, two estimates for measures on the model seen through a chart, and the
integral of a kernel read in a chart against a measure with a density in that chart.

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
* `TauCeti.integral_mul_eq_setIntegral_target`: if `μ` has the density `ρ` in a chart `e`,
  `K(x, y) = F(e x, e y)` on the product of the chart sources, `K` vanishes elsewhere, and `F(z, w)`
  vanishes for `w` outside a compact subset of the chart target, then
  `∫ K(x, y) u(y) dμ(y) = ∫_{e.target} ρ(w) F(e x, w) u(e⁻¹ w) dν(w)`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Manifold Topology

namespace TauCeti

section ExtChart

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

end ExtChart

/-! ### Integrals against a measure with a density in a chart -/

section ChartDensity

variable {M E : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M] {μ : Measure M}
  [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] {ν : Measure E}
  {e : OpenPartialHomeomorph M E}

/-- **A kernel read in a chart.** Let `μ` have the density `ρ` in the chart `e`, and let `K` be a
continuous function on `M × M` equal to `F (e x, e y)` on the product of the chart sources and to
`0` elsewhere, where `F (z, w)` vanishes for `w` outside a compact subset of the chart target. Then
`∫ K(x, y) u(y) dμ(y) = ∫_{e.target} ρ(w) F(e x, w) u(e⁻¹ w) dν(w)` at points `x` of the chart
source. -/
theorem integral_mul_eq_setIntegral_target {ρ : E → ℝ}
    (hint : ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
      ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y) ∂ν)
    {K : M × M → ℂ} (hK : Continuous K) {F : E × E → ℂ}
    (hKF : ∀ p ∈ e.source ×ˢ e.source, K p = F (e p.1, e p.2))
    (hK0 : ∀ p ∉ e.source ×ˢ e.source, K p = 0) {B : Set E} (hB : IsCompact B)
    (hBt : B ⊆ e.target) (hFB : ∀ z, ∀ w ∉ B, F (z, w) = 0) {u : M → ℂ} (hu : Continuous u)
    {x : M} (hx : x ∈ e.source) :
    ∫ y, K (x, y) * u y ∂μ = ∫ w in e.target, (ρ w : ℂ) * F (e x, w) * u (e.symm w) ∂ν := by
  -- The integrand vanishes off the compact set `e⁻¹(B)` inside the chart source.
  have hB' : IsCompact (e.symm '' B) := hB.image_of_continuousOn (e.continuousOn_symm.mono hBt)
  have hfB : ∀ y ∉ e.symm '' B, K (x, y) * u y = 0 := fun y hy ↦ by
    by_cases hys : y ∈ e.source
    · rw [hKF (x, y) ⟨hx, hys⟩, hFB _ _ fun h ↦ hy ⟨_, h, e.left_inv hys⟩, zero_mul]
    · rw [hK0 (x, y) fun h ↦ hys h.2, zero_mul]
  rw [hint (fun y ↦ K (x, y) * u y) ((hK.comp (continuous_const.prodMk continuous_id)).mul hu)
    (HasCompactSupport.intro hB' hfB) ((closure_minimal (Function.support_subset_iff'.2 hfB)
      hB'.isClosed).trans (image_subset_iff.2 fun w hw ↦ e.map_target (hBt hw)))]
  refine setIntegral_congr_fun e.open_target.measurableSet fun w hw ↦ ?_
  simp only [hKF (x, e.symm w) ⟨hx, e.map_target hw⟩, e.right_inv hw, mul_assoc]

end ChartDensity

end TauCeti
