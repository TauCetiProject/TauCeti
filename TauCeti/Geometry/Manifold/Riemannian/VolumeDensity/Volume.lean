/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Measure
public import TauCeti.Geometry.Manifold.Measure.PositiveDensity
public import TauCeti.MeasureTheory.Measure.Glue
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

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
* `TauCeti.setLIntegral_riemannianVolume_of_subset`,
  `TauCeti.setIntegral_riemannianVolume_of_subset`,
  `TauCeti.setIntegral_riemannianVolume_std_of_subset`: integration over a subset of a chart source
  in coordinates, and `TauCeti.setLIntegral_riemannianVolume_inter_preimage`, its form over the
  chart preimage of an open coordinate set.
* `TauCeti.setLIntegral_comp_extChartAt_symm_le_mul_lintegral`: where the chart density is at
  least `m > 0`, coordinate integrals are at most `m⁻¹` times Riemannian integrals, and
  `TauCeti.setLIntegral_inter_preimage_le_mul_setLIntegral_comp_extChartAt_symm`: where it is at
  most `m`, Riemannian integrals over a chart preimage are at most `m` times coordinate integrals.
* `TauCeti.lintegral_riemannianVolume_eq_of_support_subset`: integration in coordinates of a
  function supported in the chart preimage of an open coordinate set, and
  `TauCeti.integral_riemannianVolume_le_mul_integral_of_support_subset`, the resulting upper bound
  on the Riemannian integral of such a function by a pointwise bound in coordinates.
* `TauCeti.mul_integral_le_integral_riemannianVolume_of_support_subset`: the lower bound for any
  nonnegative integrable function from a coordinate lower bound supported in a subset of the chart
  target.
* `TauCeti.isPositiveDensityMeasure_riemannianVolume`: the Riemannian volume is a positive
  continuous density measure: in each chart it is Haar measure weighted by the chart volume
  density, which is continuous and positive.
* `TauCeti.isLocallyFiniteMeasure_riemannianVolume`: the Riemannian volume is locally finite.
* `TauCeti.riemannianVolume_eq_count_of_subsingleton`: on a zero-dimensional Riemannian manifold,
  the Riemannian volume measure is counting measure.
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
      (fun α : M ↦ (chartAt H α).open_source.measurableSet) ht hcover fun α _ β ↦ by
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

/-- **Integration in coordinates** against the Riemannian volume, for Bochner integrals: over a
measurable subset of a chart source, the integral of `φ` is the coordinate integral of `φ` read in
the chart weighted by the chart density. -/
theorem setIntegral_riemannianVolume_of_subset {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {α : M} {s : Set M} (hs : s ⊆ (chartAt H α).source)
    (hs' : MeasurableSet s) (φ : M → F) :
    ∫ x in s, φ x ∂riemannianVolume I M =
      ∫ y in (extChartAt I α) '' s,
        chartVolumeDensity (I := I) α ((extChartAt I α).symm y) • φ ((extChartAt I α).symm y)
          ∂(Module.finBasis ℝ E).addHaar := by
  rw [← Measure.restrict_restrict_of_subset hs, riemannianVolume_restrict_source,
    setIntegral_chartRiemannianVolume α hs', inter_eq_left.2 (by rwa [extChartAt_source])]

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

/-- **Riemannian integrals are controlled by coordinate integrals** where the chart density is
bounded above: if the density is at most `m` on an open set `Ω` of the chart target, then the
integral of `φ` over the chart preimage of `Ω` is at most `m` times the integral over `Ω` of `φ`
read in the chart. -/
theorem setLIntegral_inter_preimage_le_mul_setLIntegral_comp_extChartAt_symm (α : M) {Ω : Set E}
    (hΩ : IsOpen Ω) (hΩt : Ω ⊆ (extChartAt I α).target) {m : ℝ}
    (hρ : ∀ y ∈ Ω, chartVolumeDensity (I := I) α ((extChartAt I α).symm y) ≤ m)
    (φ : M → ℝ≥0∞) :
    ∫⁻ x in (extChartAt I α).source ∩ extChartAt I α ⁻¹' Ω, φ x ∂riemannianVolume I M ≤
      ENNReal.ofReal m *
        ∫⁻ y in Ω, φ ((extChartAt I α).symm y) ∂(Module.finBasis ℝ E).addHaar := by
  rw [setLIntegral_riemannianVolume_inter_preimage α hΩ hΩt,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hΩ.measurableSet fun y hy ↦ ?_
  gcongr
  exact hρ y hy

/-- **Integration in coordinates of a function supported in a chart**: if `φ` vanishes outside
the chart preimage of an open set `Ω` of the chart target, its integral over `M` is the integral
over `Ω` of `φ` read in the chart times the chart density. -/
theorem lintegral_riemannianVolume_eq_of_support_subset (α : M) {Ω : Set E} (hΩ : IsOpen Ω)
    (hΩt : Ω ⊆ (extChartAt I α).target) {φ : M → ℝ≥0∞}
    (hφ : Function.support φ ⊆ (extChartAt I α).source ∩ extChartAt I α ⁻¹' Ω) :
    ∫⁻ x, φ x ∂riemannianVolume I M =
      ∫⁻ y in Ω, ENNReal.ofReal (chartVolumeDensity (I := I) α ((extChartAt I α).symm y)) *
        φ ((extChartAt I α).symm y) ∂(Module.finBasis ℝ E).addHaar := by
  rw [← setLIntegral_riemannianVolume_inter_preimage α hΩ hΩt,
    setLIntegral_eq_of_support_subset hφ]

/-- **Real integrals of nonnegative functions supported in a chart, in coordinates**: if a
nonnegative integrable `f` vanishes outside the chart preimage of an open set `Ω` of the chart
target, then `ENNReal.ofReal (∫ f dV)` is the lower integral over `Ω` of the chart density times
`f` read in the chart. -/
theorem ofReal_integral_riemannianVolume_eq_of_support_subset (α : M) {Ω : Set E}
    (hΩ : IsOpen Ω) (hΩt : Ω ⊆ (extChartAt I α).target) {f : M → ℝ} (hf0 : 0 ≤ f)
    (hfi : Integrable f (riemannianVolume I M))
    (hf : Function.support f ⊆ (extChartAt I α).source ∩ extChartAt I α ⁻¹' Ω) :
    ENNReal.ofReal (∫ x, f x ∂riemannianVolume I M) =
      ∫⁻ y in Ω, ENNReal.ofReal (chartVolumeDensity (I := I) α ((extChartAt I α).symm y) *
        f ((extChartAt I α).symm y)) ∂(Module.finBasis ℝ E).addHaar := by
  simp_rw [ENNReal.ofReal_mul (chartVolumeDensity_nonneg _ _)]
  rw [ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0),
    lintegral_riemannianVolume_eq_of_support_subset α hΩ hΩt fun x hx ↦
      hf fun h ↦ hx (by simp [h])]

/-- **Upper bounds in coordinates for Riemannian integrals**: if a nonnegative integrable `f`
vanishes outside the chart preimage of an open set `Ω` of the chart target, and on `Ω` the
density times `f` read in the chart is at most `c k` for a nonnegative integrable `k`, then
`∫ f dV ≤ c ∫ k`. -/
theorem integral_riemannianVolume_le_mul_integral_of_support_subset (α : M) {Ω : Set E}
    (hΩ : IsOpen Ω) (hΩt : Ω ⊆ (extChartAt I α).target) {f : M → ℝ} (hf0 : 0 ≤ f)
    (hfi : Integrable f (riemannianVolume I M))
    (hf : Function.support f ⊆ (extChartAt I α).source ∩ extChartAt I α ⁻¹' Ω)
    {k : E → ℝ} (hk0 : 0 ≤ k) (hki : Integrable k (Module.finBasis ℝ E).addHaar) {c : ℝ}
    (hc : 0 ≤ c) (hfk : ∀ y ∈ Ω,
      chartVolumeDensity (I := I) α ((extChartAt I α).symm y) * f ((extChartAt I α).symm y) ≤
        c * k y) :
    ∫ x, f x ∂riemannianVolume I M ≤ c * ∫ y, k y ∂(Module.finBasis ℝ E).addHaar := by
  rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc (integral_nonneg hk0)),
    ofReal_integral_riemannianVolume_eq_of_support_subset α hΩ hΩt hf0 hfi hf,
    ← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hki.const_mul c)
      (ae_of_all _ fun y ↦ mul_nonneg hc (hk0 y))]
  exact (setLIntegral_mono' hΩ.measurableSet fun y hy ↦
    ENNReal.ofReal_le_ofReal (hfk y hy)).trans (setLIntegral_le_lintegral _ _)

/-- **Lower bounds in coordinates for Riemannian integrals**: if `f` is a nonnegative integrable
function, and on a subset `Ω` of the chart target the density times `f` read in the chart is at
least `c k` for a function `k` vanishing outside `Ω`, then `c ∫ k ≤ ∫ f dV`. -/
theorem mul_integral_le_integral_riemannianVolume_of_support_subset (α : M) {Ω : Set E}
    (hΩt : Ω ⊆ (extChartAt I α).target) {f : M → ℝ} (hf0 : 0 ≤ f)
    (hfi : Integrable f (riemannianVolume I M)) {k : E → ℝ} (hk : Function.support k ⊆ Ω)
    {c : ℝ} (hfk : ∀ y ∈ Ω,
      c * k y ≤
        chartVolumeDensity (I := I) α ((extChartAt I α).symm y) * f ((extChartAt I α).symm y)) :
    c * ∫ y, k y ∂(Module.finBasis ℝ E).addHaar ≤ ∫ x, f x ∂riemannianVolume I M := by
  have hsrc : (chartAt H α).source = (extChartAt I α).source := (extChartAt_source I α).symm
  have himage : extChartAt I α '' (chartAt H α).source = (extChartAt I α).target := by
    rw [hsrc, PartialEquiv.image_source_eq_target]
  rw [← integral_const_mul, ← ENNReal.ofReal_le_ofReal_iff (integral_nonneg hf0),
    ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0)]
  refine TauCeti.MeasureTheory.ofReal_integral_le_lintegral_ofReal.trans ?_
  rw [← setLIntegral_eq_of_support_subset (s := (extChartAt I α).target) fun y hy ↦
    hΩt (hk fun h ↦ hy (by simp [h]))]
  calc ∫⁻ y in (extChartAt I α).target, ENNReal.ofReal (c * k y) ∂(Module.finBasis ℝ E).addHaar
      ≤ ∫⁻ y in (extChartAt I α).target,
          ENNReal.ofReal (chartVolumeDensity (I := I) α ((extChartAt I α).symm y)) *
            ENNReal.ofReal (f ((extChartAt I α).symm y)) ∂(Module.finBasis ℝ E).addHaar := by
        refine lintegral_mono fun y ↦ ?_
        by_cases hy : y ∈ Ω
        · rw [← ENNReal.ofReal_mul (chartVolumeDensity_nonneg _ _)]
          exact ENNReal.ofReal_le_ofReal (hfk y hy)
        · simp [Function.notMem_support.1 fun h ↦ hy (hk h)]
    _ = ∫⁻ x in (chartAt H α).source, ENNReal.ofReal (f x) ∂riemannianVolume I M := by
        rw [setLIntegral_riemannianVolume_of_subset subset_rfl
          (hsrc ▸ (isOpen_extChartAt_source α).measurableSet), himage]
    _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂riemannianVolume I M := setLIntegral_le_lintegral _ _

end Coordinates

/-- **Integration in coordinates** against the Riemannian volume using Lebesgue measure on
`EuclideanSpace ℝ (Fin m)` and `TauCeti.stdChartVolumeDensity`. -/
theorem setIntegral_riemannianVolume_std_of_subset {m : ℕ} {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin m)) H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin m)) (fun x : M ↦ TangentSpace I x)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : M} {s : Set M} (hs : s ⊆ (chartAt H α).source) (hs' : MeasurableSet s) (φ : M → F) :
    ∫ x in s, φ x ∂riemannianVolume I M = ∫ z in (extChartAt I α) '' s,
      stdChartVolumeDensity (I := I) α ((extChartAt I α).symm z) •
        φ ((extChartAt I α).symm z) ∂volume := by
  rw [setIntegral_riemannianVolume_of_subset hs hs' φ,
    Module.Basis.setIntegral_addHaar_congr_measurableSpace
      (Module.finBasis ℝ (EuclideanSpace ℝ (Fin m))) ((extChartAt I α) '' s)
      (fun z ↦
        chartVolumeDensity (I := I) α ((extChartAt I α).symm z) • φ ((extChartAt I α).symm z))
      (@extChartAtMeasurableSpaceE (EuclideanSpace ℝ (Fin m)) _) inferInstance
      (@extChartAtBorelSpaceE (EuclideanSpace ℝ (Fin m)) _) inferInstance,
    EuclideanSpace.finBasis_addHaar_eq_smul_volume m, Measure.restrict_smul,
    integral_smul_measure, ENNReal.toReal_ofReal (EuclideanSpace.finBasisAddHaarFactor_pos m).le,
    ← integral_smul]
  simp_rw [smul_smul, stdChartVolumeDensity_def]

section PositiveDensity

variable [MeasurableSpace E] [BorelSpace E] in
/-- The Riemannian volume of a continuous metric is a positive continuous density measure. -/
theorem isPositiveDensityMeasure_riemannianVolume :
    IsPositiveDensityMeasure I (riemannianVolume I M) := by
  obtain rfl : ‹MeasurableSpace E› = extChartAtMeasurableSpaceE := BorelSpace.measurable_eq
  let : MeasurableSpace E := extChartAtMeasurableSpaceE
  rw [isPositiveDensityMeasure_iff_of_isAddHaarMeasure (Module.finBasis ℝ E).addHaar]
  intro x
  let e := extChartAt I x
  refine ⟨fun y ↦ chartVolumeDensity (I := I) x (e.symm y),
    continuousOn_chartVolumeDensity_extChartAt_symm x, fun y hy ↦ chartVolumeDensity_pos x ?_, ?_⟩
  · simpa only [TangentBundle.trivializationAt_baseSet, e, extChartAt_source] using e.map_target hy
  ext A hA
  have hsrc : MeasurableSet e.source := (isOpen_extChartAt_source x).measurableSet
  have hpre : MeasurableSet (e ⁻¹' A ∩ e.source) :=
    (continuousOn_extChartAt x).measurableSet_preimage_inter hsrc hA
  have hsub : e ⁻¹' A ∩ e.source ⊆ (chartAt H x).source := by
    simpa only [e, extChartAt_source] using inter_subset_right
  rw [map_restrict_extChartAt_source_apply x hA, riemannianVolume_apply_of_subset hsub,
    chartRiemannianVolume_apply x hpre, withDensity_apply _ hA, Measure.restrict_restrict hA,
    inter_assoc, inter_self, image_preimage_inter, e.image_source_eq_target]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- The Riemannian volume is locally finite: every point has a neighbourhood of finite volume. In
particular, the Riemannian volume of a compact manifold is a finite measure. -/
instance isLocallyFiniteMeasure_riemannianVolume :
    IsLocallyFiniteMeasure (riemannianVolume I M) :=
  isPositiveDensityMeasure_riemannianVolume.isLocallyFiniteMeasure

end PositiveDensity

/-- On a zero-dimensional Riemannian manifold, the Riemannian volume measure is counting measure,
giving mass `1` to every point. -/
theorem riemannianVolume_eq_count_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] :
    riemannianVolume I M = Measure.count := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have _ : Subsingleton H := I.injective.subsingleton
  have _ : DiscreteTopology M := ChartedSpace.discreteTopology H M
  have _ : Countable M := countable_of_Lindelof_of_discrete
  have hsource (x : M) : (chartAt H x).source = {x} := by
    simpa only [extChartAt_source] using (extChartAt_source_zeroDim (I := I) x)
  refine Measure.ext_of_singleton fun x ↦ ?_
  have _ : IsEmpty (Fin (Module.finrank ℝ E)) :=
    Module.finrank_zero_of_subsingleton (R := ℝ) (M := E) ▸ inferInstanceAs (IsEmpty (Fin 0))
  have hx_meas : MeasurableSet ({x} : Set M) := (isOpen_discrete {x}).measurableSet
  rw [Measure.count_singleton' hx_meas, riemannianVolume_apply_of_subset (hsource x).symm.subset,
    chartRiemannianVolume_apply x hx_meas, Module.Basis.addHaar_eq_dirac, extChartAt_source,
    hsource x, inter_self, image_singleton, Subsingleton.elim (extChartAt I x x) 0,
    setLIntegral_dirac]
  simp [chartVolumeDensity_def, Matrix.det_isEmpty]

end TauCeti
