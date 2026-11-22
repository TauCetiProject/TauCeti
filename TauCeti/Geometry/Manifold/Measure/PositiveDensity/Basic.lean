/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Geometry.Manifold.ExtChartAt.Measure
import TauCeti.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Measure.Subtype
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Positive continuous density measures on manifolds

A Borel measure `μ` on a finite-dimensional real `C¹` manifold `M` (possibly with boundary or
corners) is a *positive continuous density measure* (`TauCeti.IsPositiveContinuousDensity I μ`)
when, in every chart `e` of the `C¹` maximal atlas and relative to every additive Haar measure `ν`
on the model space `E`, the pushforward `(μ.restrict e.source).map (e.extend I)` has a strictly
positive continuous real density `w` with respect to `ν.restrict (e.extend I).target`.

The chart weight `w` is uniquely determined on `(e.extend I).target`, scales by
`Measure.addHaarScalarFactor` under a change of additive Haar measure, and transforms by the
absolute Jacobian determinant of coordinate changes. Consequently, checking the condition on any
single covering `C¹` atlas and any single additive Haar measure suffices.

Existence via partitions of unity and measure-theoretic consequences (local finiteness, full
support, and null-set agreement with `TauCeti.Manifold.ae`) are proved in
`TauCeti.Geometry.Manifold.Measure.PositiveDensity.Existence`.

## Main definitions

* `TauCeti.IsPositiveContinuousDensity`: predicate for positive continuous density measures.
* `TauCeti.IsPositiveContinuousDensity.chartWeight`: the canonical strictly positive continuous
  coordinate weight of a positive continuous density measure in a chart of the maximal atlas.

## Main results

* `TauCeti.IsPositiveContinuousDensity.chartWeight_eqOn_target_of_map_restrict_eq`: uniqueness of
  the continuous chart weight on the extended chart target.
* `TauCeti.IsPositiveContinuousDensity.chartWeight_eq_addHaarScalarFactor_mul`: scaling of chart
  weights under a change of additive Haar measure.
* `TauCeti.IsPositiveContinuousDensity.chartWeight_changeChart`: Jacobian transformation rule for
  chart weights across overlapping charts of the `C¹` maximal atlas.
* `TauCeti.isPositiveContinuousDensity_of_atlas`,
  `TauCeti.isPositiveContinuousDensity_iff_forall_chartAt`: one covering `C¹` atlas and one
  additive Haar measure suffice to verify `IsPositiveContinuousDensity`.
-/

public section

open Filter Function MeasureTheory Set
open scoped ENNReal Manifold Topology

noncomputable section

namespace TauCeti

/-! ### Auxiliary chart-measure lemmas -/

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M]

/-- Pulling an additive Haar measure back to a relatively open subset of `range I` yields a
measure positive on nonempty relatively open subsets. -/
private theorem isOpenPosMeasure_comap_range_inter
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure]
    {U : Set H} (hU : IsOpen U) :
    (ν.comap (Subtype.val : (I.symm ⁻¹' U ∩ range I : Set E) → E)).IsOpenPosMeasure := by
  set V : Set E := I.symm ⁻¹' U ∩ range I
  have hV : MeasurableSet V :=
    (hU.preimage I.continuous_symm).measurableSet.inter I.isClosed_range.measurableSet
  refine ⟨fun W hW ⟨⟨y, hyV⟩, hyW⟩ ↦ ?_⟩
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.1 hW
  have hyO : y ∈ O := by simpa [← hOW] using hyW
  have hO' : IsOpen (O ∩ I.symm ⁻¹' U) := hO.inter (hU.preimage I.continuous_symm)
  obtain ⟨z, hz⟩ := mem_closure_iff_nhds.1 (I.range_subset_closure_interior hyV.2)
    (O ∩ I.symm ⁻¹' U) (hO'.mem_nhds ⟨hyO, hyV.1⟩)
  have hopen : IsOpen ((O ∩ I.symm ⁻¹' U) ∩ interior (range I)) := hO'.inter isOpen_interior
  have hsub : (O ∩ I.symm ⁻¹' U) ∩ interior (range I) ⊆ Subtype.val '' W := by
    rintro w ⟨⟨hwO, hwU⟩, hwI⟩
    exact ⟨⟨w, ⟨hwU, interior_subset hwI⟩⟩, by simpa [← hOW] using hwO, rfl⟩
  rw [(MeasurableEmbedding.subtypeVal hV).comap_apply]
  exact ((hopen.measure_pos ν ⟨z, hz⟩).trans_le (measure_mono hsub)).ne'

/-- Continuous nonnegative real densities presenting the same weighted Haar measure on a
relatively open subset of `range I` agree pointwise there. -/
private theorem eqOn_of_withDensity_ofReal_eq [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [ν.IsAddHaarMeasure]
    {U : Set H} (hU : IsOpen U) {w₁ w₂ : E → ℝ}
    (hw₁ : ContinuousOn w₁ (I.symm ⁻¹' U ∩ range I))
    (hw₂ : ContinuousOn w₂ (I.symm ⁻¹' U ∩ range I))
    (h1 : ∀ y ∈ I.symm ⁻¹' U ∩ range I, 0 ≤ w₁ y)
    (h2 : ∀ y ∈ I.symm ⁻¹' U ∩ range I, 0 ≤ w₂ y)
    (heq : (ν.restrict (I.symm ⁻¹' U ∩ range I)).withDensity (fun y ↦ ENNReal.ofReal (w₁ y)) =
      (ν.restrict (I.symm ⁻¹' U ∩ range I)).withDensity (fun y ↦ ENNReal.ofReal (w₂ y))) :
    EqOn w₁ w₂ (I.symm ⁻¹' U ∩ range I) := by
  set V : Set E := I.symm ⁻¹' U ∩ range I
  have hV : MeasurableSet V :=
    (hU.preimage I.continuous_symm).measurableSet.inter I.isClosed_range.measurableSet
  have hval : MeasurableEmbedding (Subtype.val : V → E) := .subtypeVal hV
  have : (ν.comap (Subtype.val : V → E)).IsOpenPosMeasure :=
    isOpenPosMeasure_comap_range_inter (I := I) ν hU
  have hcomap (w : E → ℝ) :
      ((ν.restrict V).withDensity (fun y ↦ ENNReal.ofReal (w y))).comap (Subtype.val : V → E) =
        (ν.comap (Subtype.val : V → E)).withDensity fun y ↦ ENNReal.ofReal (w y.val) := by
    ext A hA
    rw [hval.comap_apply, withDensity_apply _ (hval.measurableSet_image' hA),
      withDensity_apply _ hA, Measure.restrict_restrict (hval.measurableSet_image' hA),
      inter_eq_left.2 (Subtype.coe_image_subset V A),
      hval.restrict_comap, ← hval.lintegral_map (fun y ↦ ENNReal.ofReal (w y)), hval.map_comap,
      Subtype.range_coe, Measure.restrict_restrict hV,
      inter_eq_right.2 (Subtype.coe_image_subset V A)]
  have hsubEq :
      (ν.comap (Subtype.val : V → E)).withDensity (fun y ↦ ENNReal.ofReal (w₁ y.val)) =
        (ν.comap (Subtype.val : V → E)).withDensity fun y ↦ ENNReal.ofReal (w₂ y.val) := by
    rw [← hcomap w₁, ← hcomap w₂, heq]
  have hfun := MeasureTheory.continuous_eq_of_withDensity_ofReal_eq
    (continuousOn_iff_continuous_domRestrict.1 hw₁)
    (continuousOn_iff_continuous_domRestrict.1 hw₂)
    (fun y ↦ h1 y.val y.property) (fun y ↦ h2 y.val y.property) hsubEq
  exact fun y hy ↦ congrFun hfun ⟨y, hy⟩

private theorem comap_restrict_eq_comap_withDensity [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] {e : OpenPartialHomeomorph M H}
    {μ : Measure M} {ν : Measure E} {w : E → ℝ}
    (hmap : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y)) :
    (μ.restrict e.source).comap (Subtype.val : e.source → M) =
      ((ν.restrict (e.extend I).target).withDensity (fun y ↦ ENNReal.ofReal (w y))).comap
        (e.source.domRestrict (e.extend I)) := by
  have hR := e.measurableEmbedding_extend_restrict I
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    .subtypeVal e.open_source.measurableSet
  ext B hB
  have hBs : MeasurableSet (Subtype.val '' B : Set M) := hval.measurableSet_image' hB
  have hBim : MeasurableSet (e.source.domRestrict (e.extend I) '' B) := hR.measurableSet_image' hB
  rw [hval.comap_apply, hR.comap_apply, ← hmap, e.map_restrict_extend_apply I μ hBim,
    Measure.restrict_apply hBs, inter_eq_left.2 (Subtype.coe_image_subset e.source B)]
  congr 1
  ext x
  refine ⟨fun ⟨z, hzB, hzx⟩ ↦ ?_, fun ⟨⟨z, hzB, hzx⟩, hxe⟩ ↦ ?_⟩
  · subst hzx
    exact ⟨⟨z, hzB, rfl⟩, z.property⟩
  · have hzs : z.val ∈ (e.extend I).source := by simpa only [e.extend_source] using z.property
    have hxs : x ∈ (e.extend I).source := by rwa [e.extend_source]
    exact ⟨z, hzB, (e.extend I).injOn hzs hxs hzx⟩

/-- Converting a chart pushforward identity into an integral identity over measurable subsets of
the chart source, without measurability of the integrand. -/
private theorem setLIntegral_eq_of_map_restrict_eq [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] {e : OpenPartialHomeomorph M H}
    {μ : Measure M} {ν : Measure E} {w : E → ℝ} (hw : ContinuousOn w (e.extend I).target)
    (hmap : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y))
    {s : Set M} (hs : MeasurableSet s) (hsub : s ⊆ e.source) (f : M → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ =
      ∫⁻ y in e.extend I '' s, ENNReal.ofReal (w y) * f ((e.extend I).symm y) ∂ν := by
  have hR := e.measurableEmbedding_extend_restrict I
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    .subtypeVal e.open_source.measurableSet
  have hT := e.measurableSet_extend_target I
  have hA := e.measurableSet_image_extend I hs hsub
  have hAT : e.extend I '' s ⊆ (e.extend I).target := (image_mono hsub).trans
    (by rw [← e.extend_source (I := I)]; exact (e.extend I).image_source_eq_target.subset)
  have hrestrict : μ.restrict s =
      ((((ν.restrict (e.extend I).target).withDensity (fun y ↦ ENNReal.ofReal (w y))).comap
        (e.source.domRestrict (e.extend I))).restrict (Subtype.val ⁻¹' s)).map Subtype.val := by
    rw [← comap_restrict_eq_comap_withDensity hmap, ← hval.restrict_map, hval.map_comap,
      Subtype.range_coe, Measure.restrict_restrict e.open_source.measurableSet, inter_self,
      Measure.restrict_restrict hs, inter_eq_left.2 hsub]
  have him : e.source.domRestrict (e.extend I) '' (Subtype.val ⁻¹' s) = e.extend I '' s := by
    rw [image_domRestrict, inter_eq_left.2 hsub]
  have hcongr (ρ : Measure e.source) :
      ∫⁻ z, f z ∂ρ =
        ∫⁻ z, (fun y ↦ f ((e.extend I).symm y)) (e.source.domRestrict (e.extend I) z) ∂ρ :=
    lintegral_congr fun z ↦ by
      have hz : z.val ∈ (e.extend I).source := by simpa only [e.extend_source] using z.property
      simp only [domRestrict_apply, (e.extend I).left_inv hz]
  rw [hrestrict, hval.lintegral_map, hR.restrict_comap, him, hcongr]
  refine (hR.lintegral_map (fun y ↦ f ((e.extend I).symm y))).symm.trans ?_
  have hw_ae : AEMeasurable (fun y ↦ ENNReal.ofReal (w y))
      ((ν.restrict (e.extend I).target).restrict (e.extend I '' s)) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn hw).aemeasurable hT).mono_measure
      Measure.restrict_le_self
  rw [hR.map_comap, Measure.restrict_restrict hR.measurableSet_range,
    inter_eq_right.2 (him ▸ image_subset_range _ _),
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ hw_ae _ hA
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
    Measure.restrict_restrict hA, inter_eq_left.2 hAT]
  rfl

end Helpers

/-! ### Positive continuous density measures -/

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]

/-- A Borel measure `μ` on a manifold `M` is a **positive continuous density measure** when, in
every chart `e` of the `C¹` maximal atlas and relative to every additive Haar measure `ν` on the
model space, the pushforward `(μ.restrict e.source).map (e.extend I)` has a strictly positive
continuous real density with respect to `ν.restrict (e.extend I).target`. -/
def IsPositiveContinuousDensity (μ : Measure M) : Prop :=
  ∀ e ∈ IsManifold.maximalAtlas I 1 M, ∀ (ν : Measure E) [ν.IsAddHaarMeasure],
    ∃ w : E → ℝ, ContinuousOn w (e.extend I).target ∧
      (∀ y ∈ (e.extend I).target, 0 < w y) ∧
      (μ.restrict e.source).map (e.extend I) =
        (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y)

theorem isPositiveContinuousDensity_iff {μ : Measure M} :
    IsPositiveContinuousDensity I μ ↔
      ∀ e ∈ IsManifold.maximalAtlas I 1 M, ∀ (ν : Measure E) [ν.IsAddHaarMeasure],
        ∃ w : E → ℝ, ContinuousOn w (e.extend I).target ∧
          (∀ y ∈ (e.extend I).target, 0 < w y) ∧
          (μ.restrict e.source).map (e.extend I) =
            (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y) :=
  Iff.rfl

variable {I}

/-- The coordinate density of a positive continuous density measure `μ` in a chart `e` of the `C¹`
maximal atlas, relative to an additive Haar measure `ν` on the model space. When `E` is
finite-dimensional with `BorelSpace E`, its values on `(e.extend I).target` are uniquely
determined by `μ`, `e`, and `ν`; see
`IsPositiveContinuousDensity.chartWeight_eqOn_target_of_map_restrict_eq`. -/
def IsPositiveContinuousDensity.chartWeight {μ : Measure M}
    (hμ : IsPositiveContinuousDensity I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure] : E → ℝ :=
  (hμ e he ν).choose

theorem IsPositiveContinuousDensity.continuousOn_chartWeight {μ : Measure M}
    (hμ : IsPositiveContinuousDensity I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure] :
    ContinuousOn (hμ.chartWeight he ν) (e.extend I).target :=
  (hμ e he ν).choose_spec.1

theorem IsPositiveContinuousDensity.chartWeight_pos {μ : Measure M}
    (hμ : IsPositiveContinuousDensity I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure]
    {y : E} (hy : y ∈ (e.extend I).target) :
    0 < hμ.chartWeight he ν y :=
  (hμ e he ν).choose_spec.2.1 y hy

theorem IsPositiveContinuousDensity.map_restrict_eq_withDensity_chartWeight {μ : Measure M}
    (hμ : IsPositiveContinuousDensity I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure] :
    (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦
        ENNReal.ofReal (hμ.chartWeight he ν y) :=
  (hμ e he ν).choose_spec.2.2

/-- Uniqueness of the continuous chart weight: any continuous nonnegative function on
`(e.extend I).target` presenting `(μ.restrict e.source).map (e.extend I)` against `ν` agrees with
`hμ.chartWeight he ν` on `(e.extend I).target`. -/
theorem IsPositiveContinuousDensity.chartWeight_eqOn_target_of_map_restrict_eq
    [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure M} (hμ : IsPositiveContinuousDensity I μ)
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (ν : Measure E) [ν.IsAddHaarMeasure] {w : E → ℝ}
    (hw : ContinuousOn w (e.extend I).target) (hw0 : ∀ y ∈ (e.extend I).target, 0 ≤ w y)
    (hmap : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y)) :
    EqOn (hμ.chartWeight he ν) w (e.extend I).target := by
  have heq :
      (ν.restrict (e.extend I).target).withDensity
          (fun y ↦ ENNReal.ofReal (hμ.chartWeight he ν y)) =
        (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y) :=
    (hμ.map_restrict_eq_withDensity_chartWeight he ν).symm.trans hmap
  rw [e.extend_target] at heq hw hw0 ⊢
  exact eqOn_of_withDensity_ofReal_eq (I := I) e.open_target
    (by simpa only [e.extend_target] using hμ.continuousOn_chartWeight he ν) hw
    (fun y hy ↦ (hμ.chartWeight_pos he ν (by simpa only [e.extend_target] using hy)).le) hw0 heq

/-- Changing the reference additive Haar measure from `ν₁` to `ν₂` multiplies the chart weight by
`Measure.addHaarScalarFactor ν₁ ν₂`. -/
theorem IsPositiveContinuousDensity.chartWeight_eq_addHaarScalarFactor_mul
    [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure M} (hμ : IsPositiveContinuousDensity I μ)
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (ν₁ ν₂ : Measure E) [ν₁.IsAddHaarMeasure] [ν₂.IsAddHaarMeasure]
    {y : E} (hy : y ∈ (e.extend I).target) :
    hμ.chartWeight he ν₂ y =
      (Measure.addHaarScalarFactor ν₁ ν₂ : ℝ) * hμ.chartWeight he ν₁ y := by
  have hmap : (μ.restrict e.source).map (e.extend I) =
      (ν₂.restrict (e.extend I).target).withDensity fun z ↦
        ENNReal.ofReal ((Measure.addHaarScalarFactor ν₁ ν₂ : ℝ) * hμ.chartWeight he ν₁ z) := by
    rw [hμ.map_restrict_eq_withDensity_chartWeight he ν₁, ← restrict_withDensity',
      Measure.withDensity_eq_withDensity_addHaarScalarFactor ν₁ ν₂, restrict_withDensity']
    refine congrArg (ν₂.restrict (e.extend I).target).withDensity (funext fun z ↦ ?_)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
  exact hμ.chartWeight_eqOn_target_of_map_restrict_eq he ν₂
    (continuousOn_const.mul (hμ.continuousOn_chartWeight he ν₁))
    (fun z hz ↦ mul_nonneg (Measure.addHaarScalarFactor ν₁ ν₂).coe_nonneg
      (hμ.chartWeight_pos he ν₁ hz).le) hmap hy

/-- Integration in coordinates against a positive continuous density measure over a measurable
subset of a chart source. No measurability of `f` is required. -/
theorem IsPositiveContinuousDensity.setLIntegral_of_subset [BorelSpace E] [BorelSpace M]
    {μ : Measure M} (hμ : IsPositiveContinuousDensity I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure]
    {s : Set M} (hs : MeasurableSet s) (hsub : s ⊆ e.source) (f : M → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ =
      ∫⁻ y in e.extend I '' s,
        ENNReal.ofReal (hμ.chartWeight he ν y) * f ((e.extend I).symm y) ∂ν :=
  setLIntegral_eq_of_map_restrict_eq (I := I) (hμ.continuousOn_chartWeight he ν)
    (hμ.map_restrict_eq_withDensity_chartWeight he ν) hs hsub f

/-- Measuring a measurable subset of a chart source in coordinates. -/
theorem IsPositiveContinuousDensity.measure_apply_of_subset [BorelSpace E] [BorelSpace M]
    {μ : Measure M} (hμ : IsPositiveContinuousDensity I μ) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (ν : Measure E) [ν.IsAddHaarMeasure]
    {s : Set M} (hs : MeasurableSet s) (hsub : s ⊆ e.source) :
    μ s = ∫⁻ y in e.extend I '' s, ENNReal.ofReal (hμ.chartWeight he ν y) ∂ν := by
  simpa only [mul_one, setLIntegral_one] using
    hμ.setLIntegral_of_subset he ν hs hsub (fun _ ↦ 1)

end Defs

/-! ### Jacobian transformation rule and one-atlas sufficiency -/

section Atlas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace M] [BorelSpace M]

/-- Helper transferring a measurable subset `B ⊆ (I.extendCoordChange e e').source` back to `M`
and comparing the pushforward integrals in charts `e` and `e'`. -/
private theorem setLIntegral_overlap_eq {μ : Measure M} {ν : Measure E} [ν.IsAddHaarMeasure]
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    {w w' : E → ℝ}
    (hw : ContinuousOn w (e.extend I).target) (hw' : ContinuousOn w' (e'.extend I).target)
    (hmap : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y))
    (hmap' : (μ.restrict e'.source).map (e'.extend I) =
      (ν.restrict (e'.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w' y))
    {B : Set E} (hB : MeasurableSet B) (hBsub : B ⊆ (I.extendCoordChange e e').source) :
    ∫⁻ y in B, ENNReal.ofReal (w y) ∂ν =
      ∫⁻ y in B,
        ENNReal.ofReal (|(fderivWithin ℝ (I.extendCoordChange e e') (range I) y).det| *
          w' (I.extendCoordChange e e' y)) ∂ν := by
  set Φ := I.extendCoordChange e e'
  set s := e.extend I ⁻¹' B ∩ e.source
  have hs_meas : MeasurableSet s := e.measurableSet_preimage_extend_inter I hB
  have hse' : s ⊆ e'.source := by
    rintro x ⟨hxB, hxe⟩
    have hxe' : x ∈ (e.extend I).source := by rwa [e.extend_source]
    have h2 : (e.extend I).symm (e.extend I x) ∈ (e'.extend I).source := (hBsub hxB).2
    rwa [(e.extend I).left_inv hxe', e'.extend_source] at h2
  have him_e : e.extend I '' s = B := by
    ext y
    refine ⟨fun ⟨_, ⟨hxB, _⟩, hxy⟩ ↦ hxy ▸ hxB, fun hyB ↦ ?_⟩
    have hyT : y ∈ (e.extend I).target := (hBsub hyB).1
    refine ⟨(e.extend I).symm y,
      ⟨by rw [mem_preimage, (e.extend I).right_inv hyT]; exact hyB, ?_⟩,
      (e.extend I).right_inv hyT⟩
    simpa only [← e.extend_source (I := I)] using (e.extend I).map_target hyT
  have him_e' : e'.extend I '' s = Φ '' B := by
    rw [← him_e, image_image]
    refine image_congr fun x hx ↦ ?_
    have hxe_s : x ∈ (e.extend I).source := by rw [e.extend_source]; exact hx.2
    simp only [Φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
      (e.extend I).left_inv hxe_s]
  have h1 := setLIntegral_eq_of_map_restrict_eq (I := I) hw hmap hs_meas inter_subset_right
    (fun _ ↦ 1)
  have h2 := setLIntegral_eq_of_map_restrict_eq (I := I) hw' hmap' hs_meas hse' (fun _ ↦ 1)
  simp only [mul_one, setLIntegral_one] at h1 h2
  conv_lhs => rw [← him_e]
  rw [← h1, h2, him_e', ν.setLIntegral_extendCoordChange (I := I) he he' hB hBsub]
  exact setLIntegral_congr_fun hB fun y _ ↦ (ENNReal.ofReal_mul (abs_nonneg _)).symm

/-- Shared Jacobian identity for two chart densities presenting the same measure on their
overlap. -/
private theorem eqOn_abs_det_mul_of_map_restrict_eq
    {μ : Measure M} {ν : Measure E} [ν.IsAddHaarMeasure]
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    {w w' : E → ℝ}
    (hw : ContinuousOn w (e.extend I).target) (hw' : ContinuousOn w' (e'.extend I).target)
    (hw0 : ∀ y ∈ (e.extend I).target, 0 ≤ w y) (hw'0 : ∀ y ∈ (e'.extend I).target, 0 ≤ w' y)
    (hmap : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y))
    (hmap' : (μ.restrict e'.source).map (e'.extend I) =
      (ν.restrict (e'.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w' y)) :
    EqOn w (fun y ↦ |(fderivWithin ℝ (I.extendCoordChange e e') (range I) y).det| *
      w' (I.extendCoordChange e e' y)) (I.extendCoordChange e e').source := by
  set Φ := I.extendCoordChange e e'
  have hΦ_src : Φ.source = I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I := by
    rw [I.extendCoordChange_source, I.image_eq]
  have hΦ_meas : MeasurableSet Φ.source := e.measurableSet_extendCoordChange_source e' I
  have hsubT : Φ.source ⊆ (e.extend I).target := fun _ hy ↦ hy.1
  have hmeq :
      (ν.restrict Φ.source).withDensity (fun y ↦ ENNReal.ofReal (w y)) =
        (ν.restrict Φ.source).withDensity fun y ↦
          ENNReal.ofReal (|(fderivWithin ℝ Φ (range I) y).det| * w' (Φ y)) := by
    ext A hA
    rw [withDensity_apply _ hA, withDensity_apply _ hA, Measure.restrict_restrict hA]
    exact setLIntegral_overlap_eq he he' hw hw' hmap hmap' (hA.inter hΦ_meas) inter_subset_right
  have hcont_rhs : ContinuousOn
      (fun y ↦ |(fderivWithin ℝ Φ (range I) y).det| * w' (Φ y)) Φ.source :=
    (continuousOn_abs_det_fderivWithin_extendCoordChange (I := I) he he').mul
      (hw'.comp (I.contDiffOn_extendCoordChange he he').continuousOn fun _ hy ↦
        (Φ.map_source hy).1)
  rw [hΦ_src] at hmeq hcont_rhs ⊢
  exact eqOn_of_withDensity_ofReal_eq (I := I) (e.symm ≫ₕ e').open_source
    (hw.mono (hΦ_src ▸ hsubT)) hcont_rhs
    (fun y hy ↦ hw0 y (hsubT (hΦ_src.symm ▸ hy)))
    (fun y hy ↦ mul_nonneg (abs_nonneg _) (hw'0 _ (Φ.map_source (hΦ_src.symm ▸ hy)).1)) hmeq

/-- **Jacobian change-of-variables rule for chart weights.** On the overlap of two charts `e, e'`
of the `C¹` maximal atlas, the weight in `e` equals the absolute Jacobian determinant of the
transition `e' ∘ e⁻¹` times the weight in `e'`. -/
theorem IsPositiveContinuousDensity.chartWeight_changeChart {μ : Measure M}
    (hμ : IsPositiveContinuousDensity I μ) {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    (ν : Measure E) [ν.IsAddHaarMeasure]
    {y : E} (hy : y ∈ (I.extendCoordChange e e').source) :
    hμ.chartWeight he ν y =
      |(fderivWithin ℝ (I.extendCoordChange e e') (range I) y).det| *
        hμ.chartWeight he' ν (I.extendCoordChange e e' y) :=
  eqOn_abs_det_mul_of_map_restrict_eq (I := I) he he'
    (hμ.continuousOn_chartWeight he ν) (hμ.continuousOn_chartWeight he' ν)
    (fun _ hz ↦ (hμ.chartWeight_pos he ν hz).le)
    (fun _ hz ↦ (hμ.chartWeight_pos he' ν hz).le)
    (hμ.map_restrict_eq_withDensity_chartWeight he ν)
    (hμ.map_restrict_eq_withDensity_chartWeight he' ν) hy

/-- Boundaryless specialization of the Jacobian transformation law for chart weights. -/
theorem IsPositiveContinuousDensity.chartWeight_changeChart_modelWithCornersSelf
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N]
    [MeasurableSpace N] [BorelSpace N] {μ : Measure N}
    (hμ : IsPositiveContinuousDensity 𝓘(ℝ, E) μ) {e e' : OpenPartialHomeomorph N E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 N)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 N)
    (ν : Measure E) [ν.IsAddHaarMeasure] {y : E} (hy : y ∈ (e.symm.trans e').source) :
    hμ.chartWeight he ν y =
      |(fderiv ℝ (e' ∘ e.symm) y).det| * hμ.chartWeight he' ν (e' (e.symm y)) := by
  have hy' : y ∈ (𝓘(ℝ, E).extendCoordChange e e').source := by
    rw [ModelWithCorners.extendCoordChange_source]
    simpa only [modelWithCornersSelf_coe, image_id] using hy
  have hfun : ⇑(𝓘(ℝ, E).extendCoordChange e e') = e' ∘ e.symm := by
    ext z
    simp [ModelWithCorners.extendCoordChange]
  have h := hμ.chartWeight_changeChart he he' ν hy'
  rw [hfun, modelWithCornersSelf_coe, range_id, fderivWithin_univ] at h
  exact h

/-- Overlap compatibility of chart weights pulled back from an atlas to a chart `e`. -/
private theorem atlasPullbackWeight_eq {μ : Measure M} {ν : Measure E} [ν.IsAddHaarMeasure]
    {ι : Type*} {φ : ι → OpenPartialHomeomorph M H}
    (hφ : ∀ i, φ i ∈ IsManifold.maximalAtlas I 1 M)
    {w : ι → E → ℝ} (hw_cont : ∀ i, ContinuousOn (w i) ((φ i).extend I).target)
    (hw_pos : ∀ i, ∀ y ∈ ((φ i).extend I).target, 0 < w i y)
    (hw_map : ∀ i, (μ.restrict (φ i).source).map ((φ i).extend I) =
      (ν.restrict ((φ i).extend I).target).withDensity fun y ↦ ENNReal.ofReal (w i y))
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    {i j : ι} {y : E}
    (hyi : y ∈ (I.extendCoordChange e (φ i)).source)
    (hyj : y ∈ (I.extendCoordChange e (φ j)).source) :
    |(fderivWithin ℝ (I.extendCoordChange e (φ i)) (range I) y).det| *
        w i (I.extendCoordChange e (φ i) y) =
      |(fderivWithin ℝ (I.extendCoordChange e (φ j)) (range I) y).det| *
        w j (I.extendCoordChange e (φ j) y) := by
  set x := (e.extend I).symm y
  have hxe : x ∈ e.source := by
    simpa only [← e.extend_source (I := I)] using (e.extend I).map_target hyi.1
  have hxi : x ∈ (φ i).source := (φ i).extend_source (I := I) ▸ hyi.2
  have hxj : x ∈ (φ j).source := (φ j).extend_source (I := I) ▸ hyj.2
  have hzij : (φ i).extend I x ∈ (I.extendCoordChange (φ i) (φ j)).source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter (f := φ i) (f' := φ j)]
    exact mem_image_of_mem _ ⟨hxi, hxj⟩
  have htr := eqOn_abs_det_mul_of_map_restrict_eq (I := I) (hφ i) (hφ j)
    (hw_cont i) (hw_cont j) (fun _ hz ↦ (hw_pos i _ hz).le) (fun _ hz ↦ (hw_pos j _ hz).le)
    (hw_map i) (hw_map j) hzij
  dsimp only at htr
  have hchain := abs_det_fderivWithin_extendCoordChange_comp (I := I) he (hφ i) (hφ j) hxe hxi hxj
  have hΦij : I.extendCoordChange (φ i) (φ j) ((φ i).extend I x) = (φ j).extend I x := by
    have hxi' : x ∈ ((φ i).extend I).source := by rwa [(φ i).extend_source]
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
      ((φ i).extend I).left_inv hxi']
  have hyx : e.extend I x = y := (e.extend I).right_inv hyi.1
  have hΦi : I.extendCoordChange e (φ i) y = (φ i).extend I x :=
    PartialEquiv.trans_apply (e.extend I).symm ((φ i).extend I)
  have hΦj : I.extendCoordChange e (φ j) y = (φ j).extend I x :=
    PartialEquiv.trans_apply (e.extend I).symm ((φ j).extend I)
  rw [hΦi, hΦj, htr, hΦij, ← hyx, hchain]
  ring

/-- Local pushforward verification on a measurable subset of one chart overlap. -/
private theorem atlasPullback_map_piece {μ : Measure M} {ν : Measure E} [ν.IsAddHaarMeasure]
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    {w' w0 : E → ℝ} (hw' : ContinuousOn w' (e'.extend I).target)
    (hmap' : (μ.restrict e'.source).map (e'.extend I) =
      (ν.restrict (e'.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w' y))
    (hw0_eq : EqOn w0 (fun y ↦ |(fderivWithin ℝ (I.extendCoordChange e e') (range I) y).det| *
      w' (I.extendCoordChange e e' y)) (I.extendCoordChange e e').source)
    {A : Set E} (hA : MeasurableSet A) (hAsub : A ⊆ (I.extendCoordChange e e').source) :
    ((μ.restrict e.source).map (e.extend I)) A = ∫⁻ y in A, ENNReal.ofReal (w0 y) ∂ν := by
  rw [e.map_restrict_extend_apply I μ hA]
  set s := e.extend I ⁻¹' A ∩ e.source
  have hs_meas : MeasurableSet s := e.measurableSet_preimage_extend_inter I hA
  have hs_e' : s ⊆ e'.source := by
    rintro x ⟨hxA, hxe⟩
    have hxe' : x ∈ (e.extend I).source := by rwa [e.extend_source]
    have h2 : (e.extend I).symm (e.extend I x) ∈ (e'.extend I).source := (hAsub hxA).2
    rwa [(e.extend I).left_inv hxe', e'.extend_source] at h2
  have him : e'.extend I '' s = I.extendCoordChange e e' '' A := by
    ext z
    refine ⟨fun ⟨x, ⟨hxA, hxe⟩, hxz⟩ ↦ ?_, fun ⟨y, hyA, hyz⟩ ↦ ?_⟩
    · have hxe' : x ∈ (e.extend I).source := by rwa [e.extend_source]
      exact ⟨e.extend I x, hxA, by
        simpa only [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
          (e.extend I).left_inv hxe'] using hxz⟩
    · have hyT : y ∈ (e.extend I).target := (hAsub hyA).1
      refine ⟨(e.extend I).symm y,
        ⟨by rw [mem_preimage, (e.extend I).right_inv hyT]; exact hyA, ?_⟩, hyz⟩
      simpa only [← e.extend_source (I := I)] using (e.extend I).map_target hyT
  have h1 := setLIntegral_eq_of_map_restrict_eq (I := I) hw' hmap' hs_meas hs_e' (fun _ ↦ 1)
  simp only [mul_one, setLIntegral_one] at h1
  rw [h1, him, ν.setLIntegral_extendCoordChange (I := I) he he' hA hAsub]
  exact setLIntegral_congr_fun hA fun y hy ↦ by
    rw [hw0_eq (hAsub hy), ENNReal.ofReal_mul (abs_nonneg _)]

omit [MeasurableSpace E] [BorelSpace E] [ChartedSpace H M]
  [MeasurableSpace M] [BorelSpace M] in
/-- Extract a countable subcover of `(e.extend I).target` by chart-overlap domains. -/
private theorem exists_countable_coordChange_cover {ι : Type*} {φ : ι → OpenPartialHomeomorph M H}
    {e : OpenPartialHomeomorph M H}
    (hcov_e : ∀ y ∈ (e.extend I).target, ∃ i, y ∈ (I.extendCoordChange e (φ i)).source) :
    ∃ t : Set ι, t.Countable ∧
      (e.extend I).target ⊆ ⋃ i ∈ t, (I.extendCoordChange e (φ i)).source := by
  have hopen (i : ι) : IsOpen (I.symm ⁻¹' (e.symm ≫ₕ φ i).source) :=
    (e.symm ≫ₕ φ i).open_source.preimage I.continuous_symm
  obtain ⟨t, ht, htcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof (e.extend I).target).elim_countable_subcover
      (fun i ↦ I.symm ⁻¹' (e.symm ≫ₕ φ i).source) hopen fun y hy ↦ by
        obtain ⟨i, hyi⟩ := hcov_e y hy
        rw [I.extendCoordChange_source, I.image_eq] at hyi
        exact mem_iUnion.2 ⟨i, hyi.1⟩
  refine ⟨t, ht, fun y hy ↦ ?_⟩
  obtain ⟨i, hit, hyi⟩ := mem_iUnion₂.1 (htcover hy)
  refine mem_iUnion₂.2 ⟨i, hit, ?_⟩
  rw [I.extendCoordChange_source, I.image_eq]
  exact ⟨hyi, e.extend_target_subset_range hy⟩

omit [ChartedSpace H M] in
/-- Glue local pushforward identities on a covering of `(e.extend I).target` by chart overlaps. -/
private theorem atlasPullback_map_eq {μ : Measure M} {ν : Measure E}
    {ι : Type*} {φ : ι → OpenPartialHomeomorph M H} {e : OpenPartialHomeomorph M H}
    (hcov_e : ∀ y ∈ (e.extend I).target, ∃ i, y ∈ (I.extendCoordChange e (φ i)).source)
    {w0 : E → ℝ}
    (hpiece : ∀ i, ∀ {A : Set E}, MeasurableSet A → A ⊆ (I.extendCoordChange e (φ i)).source →
      ((μ.restrict e.source).map (e.extend I)) A = ∫⁻ y in A, ENNReal.ofReal (w0 y) ∂ν) :
    (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w0 y) := by
  have hT_meas := e.measurableSet_extend_target I
  obtain ⟨t, ht, htcover'⟩ := exists_countable_coordChange_cover (I := I) hcov_e
  ext A hA
  rw [withDensity_apply _ hA, Measure.restrict_restrict hA]
  have hAT_eq : ((μ.restrict e.source).map (e.extend I)) A =
      ((μ.restrict e.source).map (e.extend I)) (A ∩ (e.extend I).target) := by
    rw [e.map_restrict_extend_apply I μ hA, e.map_restrict_extend_apply I μ (hA.inter hT_meas)]
    congr 1; ext x
    refine ⟨fun ⟨hxA, hxe⟩ ↦ ⟨⟨hxA, ?_⟩, hxe⟩, fun ⟨⟨hxA, _⟩, hxe⟩ ↦ ⟨hxA, hxe⟩⟩
    exact (e.extend I).map_source (by rwa [e.extend_source])
  rw [hAT_eq]
  rcases t.eq_empty_or_nonempty with rfl | htne
  · have hTe : (e.extend I).target = ∅ := subset_empty_iff.1 (by simpa using htcover')
    rw [hTe, inter_empty, measure_empty, Measure.restrict_empty, lintegral_zero_measure]
  obtain ⟨f, rfl⟩ := ht.exists_eq_range htne
  set U : ℕ → Set E := fun n ↦ (I.extendCoordChange e (φ (f n))).source
  have hU_meas (n : ℕ) : MeasurableSet (U n) := e.measurableSet_extendCoordChange_source _ I
  set d : ℕ → Set E := fun n ↦ A ∩ (e.extend I).target ∩ disjointed U n
  have hd_meas (n : ℕ) : MeasurableSet (d n) :=
    (hA.inter hT_meas).inter (MeasurableSet.disjointed hU_meas n)
  have hd_disj : Pairwise (Disjoint on d) :=
    (disjoint_disjointed U).mono fun _ _ hmn ↦ hmn.mono inter_subset_right inter_subset_right
  have hd_union : ⋃ n, d n = A ∩ (e.extend I).target := by
    rw [← inter_iUnion, iUnion_disjointed, inter_eq_left]
    exact inter_subset_right.trans (by simpa only [biUnion_range] using htcover')
  rw [← hd_union, measure_iUnion hd_disj hd_meas, lintegral_iUnion hd_meas hd_disj]
  exact tsum_congr fun n ↦
    hpiece (f n) (hd_meas n) (inter_subset_right.trans (disjointed_subset U n))

/-- **One-atlas sufficiency.** To verify that `μ` is a positive continuous density measure, it
suffices that `μ` has a strictly positive continuous density against a single additive Haar measure
in each chart of some covering `C¹` atlas. Neither the atlas nor the manifold need be countable or
Lindelöf. -/
theorem isPositiveContinuousDensity_of_atlas {μ : Measure M}
    (ν : Measure E) [ν.IsAddHaarMeasure]
    {ι : Type*} {φ : ι → OpenPartialHomeomorph M H}
    (hφ : ∀ i, φ i ∈ IsManifold.maximalAtlas I 1 M)
    (hcover : ⋃ i, (φ i).source = univ)
    (h : ∀ i, ∃ w : E → ℝ, ContinuousOn w ((φ i).extend I).target ∧
      (∀ y ∈ ((φ i).extend I).target, 0 < w y) ∧
      (μ.restrict (φ i).source).map ((φ i).extend I) =
        (ν.restrict ((φ i).extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y)) :
    IsPositiveContinuousDensity I μ := by
  classical
  choose w hw_cont hw_pos hw_map using h
  intro e he ν' _
  have hcov_e : ∀ y ∈ (e.extend I).target, ∃ i, y ∈ (I.extendCoordChange e (φ i)).source := by
    intro y hy
    have hxe : (e.extend I).symm y ∈ e.source := by
      simpa only [← e.extend_source (I := I)] using (e.extend I).map_target hy
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcover ▸ mem_univ ((e.extend I).symm y))
    refine ⟨i, ?_⟩
    rw [← OpenPartialHomeomorph.extend_image_source_inter (f := e) (f' := φ i)]
    exact ⟨(e.extend I).symm y, ⟨hxe, hi⟩, (e.extend I).right_inv hy⟩
  let g (i : ι) (y : E) : ℝ :=
    |(fderivWithin ℝ (I.extendCoordChange e (φ i)) (range I) y).det| *
      w i (I.extendCoordChange e (φ i) y)
  let w0 (y : E) : ℝ := if hy : y ∈ (e.extend I).target then g (hcov_e y hy).choose y else 0
  have hw0_eq (i : ι) : EqOn w0 (g i) (I.extendCoordChange e (φ i)).source := fun y hy ↦ by
    have hyT : y ∈ (e.extend I).target := hy.1
    dsimp only [w0]; rw [dite_eq_left hyT]
    exact atlasPullbackWeight_eq hφ hw_cont hw_pos hw_map he (hcov_e y hyT).choose_spec hy
  have hw0_cont : ContinuousOn w0 (e.extend I).target := fun y hy ↦ by
    obtain ⟨i, hyi⟩ := hcov_e y hy
    have hmem : (I.extendCoordChange e (φ i)).source ∈ 𝓝[(e.extend I).target] y :=
      nhdsWithin_mono y e.extend_target_subset_range (I.extendCoordChange_source_mem_nhdsWithin hyi)
    have hgi : ContinuousOn (g i) (I.extendCoordChange e (φ i)).source :=
      (continuousOn_abs_det_fderivWithin_extendCoordChange (I := I) he (hφ i)).mul
        ((hw_cont i).comp (I.contDiffOn_extendCoordChange he (hφ i)).continuousOn
          fun _ hz ↦ ((I.extendCoordChange e (φ i)).map_source hz).1)
    exact ((hgi y hyi).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem hmem fun z hz ↦ hw0_eq i hz) (hw0_eq i hyi)
  have hw0_pos : ∀ y ∈ (e.extend I).target, 0 < w0 y := fun y hy ↦ by
    obtain ⟨i, hyi⟩ := hcov_e y hy
    rw [hw0_eq i hyi]
    exact mul_pos (abs_det_fderivWithin_extendCoordChange_pos (I := I) he (hφ i) hyi)
      (hw_pos i _ ((I.extendCoordChange e (φ i)).map_source hyi).1)
  have hmap_nu := atlasPullback_map_eq (I := I) (μ := μ) (ν := ν) hcov_e fun i _ hA hAsub ↦
    atlasPullback_map_piece he (hφ i) (hw_cont i) (hw_map i) (hw0_eq i) hA hAsub
  refine ⟨fun y ↦ (Measure.addHaarScalarFactor ν ν' : ℝ) * w0 y,
    continuousOn_const.mul hw0_cont,
    fun y hy ↦ mul_pos (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν ν') (hw0_pos y hy),
    ?_⟩
  rw [hmap_nu, ← restrict_withDensity',
    Measure.withDensity_eq_withDensity_addHaarScalarFactor ν ν', restrict_withDensity']
  refine congrArg (ν'.restrict (e.extend I).target).withDensity (funext fun y ↦ ?_)
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]

/-- A Borel measure is a positive continuous density measure iff it has a strictly positive
continuous density against a fixed additive Haar measure in every preferred extended chart. -/
theorem isPositiveContinuousDensity_iff_forall_chartAt [IsManifold I 1 M] {μ : Measure M}
    (ν : Measure E) [ν.IsAddHaarMeasure] :
    IsPositiveContinuousDensity I μ ↔
      ∀ x : M, ∃ w : E → ℝ, ContinuousOn w (extChartAt I x).target ∧
        (∀ y ∈ (extChartAt I x).target, 0 < w y) ∧
        (μ.restrict (chartAt H x).source).map (extChartAt I x) =
          (ν.restrict (extChartAt I x).target).withDensity fun y ↦ ENNReal.ofReal (w y) :=
  ⟨fun hμ x ↦ hμ (chartAt H x) (IsManifold.chart_mem_maximalAtlas x) ν,
    isPositiveContinuousDensity_of_atlas (I := I) ν
      (φ := fun x : M ↦ chartAt H x) (fun x ↦ IsManifold.chart_mem_maximalAtlas x)
      (iUnion_eq_univ_iff.2 fun x ↦ ⟨x, mem_chart_source H x⟩)⟩

end Atlas

end TauCeti
