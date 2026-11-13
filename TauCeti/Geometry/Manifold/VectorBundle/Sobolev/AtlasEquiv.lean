/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Independence of the Sobolev space of sections from the bundle atlas

Let `M` be a `C¹` manifold without boundary modelled on a finite-dimensional real inner product
space `E`, let `V → M` be a real vector bundle with finite-dimensional model fibre `F`, and let `A`,
`A'` be two finite bundle atlases. The Sobolev spaces `W^{k,p}(V)` of
`TauCeti.SobolevSection A μ p k` and `TauCeti.SobolevSection A' μ p k` consist of tuples of
chartwise components of sections in the charts of `A` and of `A'`. This file shows that, whenever
every section with `W^{k,p}` components in the charts of `A` also has `W^{k,p}` components in the
charts of `A'` (`TauCeti.SobolevSection.TransfersTo A A' μ p k`), sending an element to the element
of the other atlas with the same section is a continuous linear map
(`TauCeti.SobolevSection.changeAtlas`). When the property holds in both directions the two spaces
are isomorphic Banach spaces (`TauCeti.SobolevSection.atlasEquiv`), so their norms are equivalent.

The map is well defined because chart transitions between the two atlases carry null sets to
null sets: a property of the points of `M` holding almost everywhere in every chart of `A` holds
almost everywhere in every chart of `A'`
(`TauCeti.FiniteBundleAtlas.ae_restrict_image_symm_of_ae`). Two sections whose readings agree
almost everywhere in the charts of `A` therefore agree almost everywhere in the charts of `A'`.
Continuity follows from the closed graph theorem: both spaces are complete, and if `w m → w` and
`changeAtlas w m → v`, then along a subsequence the chart data converge almost everywhere, and
on the overlap of a chart of `A` and a chart of `A'` the readings are related by the coordinate
changes of the bundle, which are continuous, so the chart data of `v` are the readings in `A'` of
the section of `w`.

For surfaces, `M` modelled on `ℂ` with the Lebesgue measure, and a `C¹` bundle, the transfer
property holds at orders `k ≤ 1` (`TauCeti.SobolevSection.transfersTo_of_le_one`), by the
localization of Sobolev sections in arbitrary charts and trivializations of
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart`. Every localization result at a higher order
gives the corresponding transfer property and hence the atlas independence at that order.

## Main definitions

* `TauCeti.SobolevSection.TransfersTo A A' μ p k`: every section with `W^{k,p}` components in the
  charts of `A` has `W^{k,p}` components in the charts of `A'`.
* `TauCeti.SobolevSection.changeAtlas`: the continuous linear map between the Sobolev spaces of two
  atlases sending an element to the element with the same section.
* `TauCeti.SobolevSection.atlasEquiv`: the isomorphism of Banach spaces between them.

## Main results

* `TauCeti.FiniteBundleAtlas.ae_restrict_image_symm_of_ae`: almost everywhere statements on `M` do
  not depend on the atlas.
* `TauCeti.FiniteBundleAtlas.coord_ae_eq_of_coord_ae_eq`: sections whose readings agree almost
  everywhere in one atlas agree almost everywhere in every other atlas.
* `TauCeti.SobolevSection.chartValueL_changeAtlas_ae`: the chart data of `changeAtlas h w` are the
  readings in `A'` of any section of `w`.
* `TauCeti.SobolevSection.transfersTo_of_le_one`: the transfer property for surfaces at orders
  `k ≤ 1`.
* `TauCeti.SobolevSection.exists_norm_le_of_le_one`: for surfaces and orders `k ≤ 1` the norms of
  two finite bundle atlases are equivalent.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev spaces of sections).
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Set TopologicalSpace
open scoped Manifold Topology ENNReal

universe u

namespace TauCeti

section Atlas

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A A' : FiniteBundleAtlas E M F V) {μ : Measure E} [μ.IsAddHaarMeasure]

namespace FiniteBundleAtlas

omit [NormedSpace ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] in
/-- **Change of atlas preserves null sets, chartwise.** If a property `P` of points of `E` holds
almost everywhere on the image of chart `i` of `A`, then almost everywhere on the image of chart
`i'` of `A'` it holds at the reading in chart `i` of the corresponding point of `M`, wherever that
point lies in the domain of chart `i`. The chart transition from `A'` to `A` is a `C¹`
diffeomorphism between open sets, whose inverse carries null sets to null sets. -/
theorem ae_restrict_image_chart_symm {i : Fin A.n} (i' : Fin A'.n) {P : E → Prop}
    (h : ∀ᵐ z ∂μ.restrict (A.image i), P z) :
    ∀ᵐ y ∂μ.restrict (A'.image i'), (A'.chart i').symm y ∈ A.dom i →
      P (A.chart i ((A'.chart i').symm y)) := by
  rw [ae_restrict_iff' (A.image i).isOpen.measurableSet] at h
  have hN : μ ({z | ¬P z} ∩ A.image i) = 0 := by
    rw [ae_iff] at h
    exact measure_mono_null (fun z hz ↦ fun h' ↦ hz.1 (h' hz.2)) h
  -- The chart transition from `A` to `A'` is differentiable on its source.
  have hd := ((contDiffOn_ext_coord_change (I := 𝓘(ℝ, E)) (A'.center i')
    (A.center i)).differentiableOn one_ne_zero).mono
      (inter_subset_right (s := {z | ¬P z} ∩ A.image i))
  have himage := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ hd
    (measure_mono_null inter_subset_left hN)
  rw [ae_iff, Measure.restrict_apply' (A'.image i').isOpen.measurableSet]
  refine measure_mono_null (fun y hy ↦ ?_) himage
  simp only [not_imp, mem_inter_iff, mem_ofPred_eq] at hy
  obtain ⟨⟨hdom, hP⟩, hy'⟩ := hy
  set x := (A'.chart i').symm y
  have hx : x ∈ (A.chart i).source := A.dom_subset_chart_source i hdom
  have hx' : x ∈ (A'.chart i').source := A'.dom_subset_chart_source i' (A'.symm_mem_dom hy')
  refine ⟨A.chart i x, ⟨⟨hP, A.mem_image.2 ⟨x, hdom, rfl⟩⟩, ?_⟩, ?_⟩
  · simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff, mem_preimage,
      extChartAt_target, extChartAt_source, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq, range_id, inter_univ,
      preimage_id_eq]
    exact ⟨(A.chart i).map_source hx, by rwa [(A.chart i).left_inv hx]⟩
  · simp only [Function.comp_apply, extChartAt_coe_symm, extChartAt_coe,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq]
    rw [(A.chart i).left_inv hx,
      (A'.chart i').right_inv (A'.closure_image_subset_target i' (subset_closure hy'))]

omit [NormedSpace ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] in
/-- **Almost everywhere statements on `M` do not depend on the atlas.** A property of points of `M`
that holds almost everywhere in every chart of `A` holds almost everywhere in every chart of
`A'`. -/
theorem ae_restrict_image_symm_of_ae {P : M → Prop}
    (h : ∀ i, ∀ᵐ z ∂μ.restrict (A.image i), P ((A.chart i).symm z)) (i' : Fin A'.n) :
    ∀ᵐ y ∂μ.restrict (A'.image i'), P ((A'.chart i').symm y) := by
  have hall := ae_all_iff.2 fun i ↦ A.ae_restrict_image_chart_symm A' i' (h i)
  filter_upwards [hall] with y hy
  obtain ⟨i, hi⟩ := A.exists_mem_dom ((A'.chart i').symm y)
  simpa only [(A.chart i).left_inv (A.dom_subset_chart_source i hi)] using hy i hi

omit [NormedSpace ℝ F] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] in
/-- Sections whose readings agree almost everywhere in every chart of one finite bundle atlas agree
almost everywhere in every chart of any other. -/
theorem coord_ae_eq_of_coord_ae_eq {s t : ∀ x, V x}
    (h : ∀ i, A.coord i s =ᵐ[μ.restrict (A.image i)] A.coord i t) (i' : Fin A'.n) :
    A'.coord i' s =ᵐ[μ.restrict (A'.image i')] A'.coord i' t := by
  have hst := A.ae_restrict_image_symm_of_ae A' (P := fun x ↦ s x = t x) (fun i ↦ by
    filter_upwards [h i, ae_restrict_mem (A.image i).isOpen.measurableSet] with z hz hzU
    have hb := A.dom_subset_baseSet i (A.symm_mem_dom hzU)
    rw [← (A.triv i).symm_apply_apply_mk hb (s _), ← (A.triv i).symm_apply_apply_mk hb (t _)]
    rw [A.coord_def, A.coord_def] at hz
    exact congrArg _ hz) i'
  filter_upwards [hst] with y hy
  simp only [coord_def, hy]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsManifold 𝓘(ℝ, E) 1 M] in
/-- On the overlap of the domains of chart `i` of `A` and chart `i'` of `A'`, the reading of a
section in chart `i'` of `A'` is the coordinate change of the bundle applied to its reading in
chart `i` of `A`. -/
theorem coord_eq_coordChangeL_coord {i : Fin A.n} {i' : Fin A'.n} (s : ∀ x, V x) {y : E}
    (hy : y ∈ A'.image i') (hi : (A'.chart i').symm y ∈ A.dom i) :
    A'.coord i' s y = (A.triv i).coordChangeL ℝ (A'.triv i') ((A'.chart i').symm y)
      (A.coord i s (A.chart i ((A'.chart i').symm y))) := by
  have hb : (A'.chart i').symm y ∈ (A.triv i).baseSet ∩ (A'.triv i').baseSet :=
    ⟨A.dom_subset_baseSet i hi, A'.dom_subset_baseSet i' (A'.symm_mem_dom hy)⟩
  rw [A.coord_chart s hi, Trivialization.coordChangeL_apply _ _ hb,
    (A.triv i).symm_apply_apply_mk hb.1]
  exact A'.coord_def i' s y

end FiniteBundleAtlas

end Atlas

section Sobolev

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A A' : FiniteBundleAtlas E M F V) (μ : Measure E) [μ.IsAddHaarMeasure]

namespace SobolevSection

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- **Transfer of Sobolev sections between atlases.** Every section whose chart data in the charts
of `A` are those of an element of `W^{k,p}(V)` for `A` also has chart data in the charts of `A'`
that are those of an element of `W^{k,p}(V)` for `A'`. For surfaces this holds at orders `k ≤ 1`
(`TauCeti.SobolevSection.transfersTo_of_le_one`). -/
def TransfersTo : Prop :=
  ∀ (w : SobolevSection A μ p k) (s : ∀ x, V x),
    (∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) →
      ∃ w' : SobolevSection A' μ p k,
        ∀ i', A'.sectionChartData.chartValueL μ p k i' w' =ᵐ[μ.restrict (A'.image i')]
          A'.coord i' s

variable {A A' μ p k}

/-- Every element of `W^{k,p}(V)` consists of the chartwise components of a section, read in the
charts of `A` as `A.coord i s`. -/
theorem exists_ae_eq_coord (w : SobolevSection A μ p k) :
    ∃ s : ∀ x, V x, ∀ i,
      A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s := by
  obtain ⟨s, hs⟩ := SectionChartData.exists_section _ μ p k w
  exact ⟨s, fun i ↦ (hs i).trans (A.sectionChartData_coord_ae_eq μ i s)⟩

theorem transfersTo_refl : TransfersTo A A μ p k :=
  fun w _ hs ↦ ⟨w, hs⟩

theorem TransfersTo.trans {A'' : FiniteBundleAtlas E M F V} (h : TransfersTo A A' μ p k)
    (h' : TransfersTo A' A'' μ p k) : TransfersTo A A'' μ p k := fun w s hs ↦
  let ⟨w', hw'⟩ := h w s hs
  h' w' s hw'

/-- The chart data of a sum are almost everywhere the readings of the sum of the sections. -/
private theorem chartValueL_add_ae {w w' : SobolevSection A μ p k} {s t : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (ht : ∀ i, A.sectionChartData.chartValueL μ p k i w' =ᵐ[μ.restrict (A.image i)] A.coord i t)
    (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p k i (w + w' : SobolevSection A μ p k)
      =ᵐ[μ.restrict (A.image i)] A.coord i (s + t) := by
  filter_upwards [hs i, ht i, ae_restrict_mem (A.image i).isOpen.measurableSet,
    Lp.coeFn_add (A.sectionChartData.chartValueL μ p k i w)
      (A.sectionChartData.chartValueL μ p k i w')] with y hy hy' hyU hadd
  rw [Submodule.coe_add, map_add, hadd, Pi.add_apply, hy, hy', A.coord_add i s t hyU]

/-- The chart data of a multiple are almost everywhere the readings of the multiple of the
section. -/
private theorem chartValueL_smul_ae (c : ℝ) {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p k i (c • w : SobolevSection A μ p k)
      =ᵐ[μ.restrict (A.image i)] A.coord i (c • s) := by
  filter_upwards [hs i, ae_restrict_mem (A.image i).isOpen.measurableSet,
    Lp.coeFn_smul c (A.sectionChartData.chartValueL μ p k i w)] with y hy hyU hsmul
  rw [Submodule.coe_smul, map_smul, hsmul, Pi.smul_apply, hy, A.coord_smul i c s hyU]

/-- The element of `W^{k,p}(V)` for `A'` with the same section as `w`, before continuity is
established. -/
private def changeAtlasAux (h : TransfersTo A A' μ p k) (w : SobolevSection A μ p k) :
    SobolevSection A' μ p k :=
  (h w _ (exists_ae_eq_coord w).choose_spec).choose

variable [IsManifold 𝓘(ℝ, E) 1 M]

private theorem chartValueL_changeAtlasAux_ae (h : TransfersTo A A' μ p k)
    {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (i' : Fin A'.n) :
    A'.sectionChartData.chartValueL μ p k i' (changeAtlasAux h w)
      =ᵐ[μ.restrict (A'.image i')] A'.coord i' s :=
  ((h w _ (exists_ae_eq_coord w).choose_spec).choose_spec i').trans <|
    A.coord_ae_eq_of_coord_ae_eq A'
      (fun i ↦ ((exists_ae_eq_coord w).choose_spec i).symm.trans (hs i)) i'

/-- The element of `W^{k,p}(V)` for `A'` with the same section, as a linear map. -/
private def changeAtlasₗ (h : TransfersTo A A' μ p k) :
    SobolevSection A μ p k →ₗ[ℝ] SobolevSection A' μ p k where
  toFun := changeAtlasAux h
  map_add' w w' := by
    obtain ⟨s, hs⟩ := exists_ae_eq_coord w
    obtain ⟨t, ht⟩ := exists_ae_eq_coord w'
    exact eq_of_ae_eq_coord (chartValueL_changeAtlasAux_ae h (chartValueL_add_ae hs ht))
      (chartValueL_add_ae (chartValueL_changeAtlasAux_ae h hs)
        (chartValueL_changeAtlasAux_ae h ht))
  map_smul' c w := by
    obtain ⟨s, hs⟩ := exists_ae_eq_coord w
    exact eq_of_ae_eq_coord (chartValueL_changeAtlasAux_ae h (chartValueL_smul_ae c hs))
      (chartValueL_smul_ae c (chartValueL_changeAtlasAux_ae h hs))

/-- **The graph of the change of atlas is closed.** If `w m → w` in `W^{k,p}(V)` for `A` and the
corresponding elements for `A'` converge to `v`, then in each chart of `A'` the chart data of `v`
are the readings of the section of `w`, almost everywhere on the part lying over the domain of
chart `i` of `A`. -/
private theorem chartValueL_ae_of_tendsto (h : TransfersTo A A' μ p k)
    {u : ℕ → SobolevSection A μ p k} {w : SobolevSection A μ p k} {v : SobolevSection A' μ p k}
    (hu : Tendsto u atTop (𝓝 w)) (hv : Tendsto (changeAtlasₗ h ∘ u) atTop (𝓝 v))
    {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (i : Fin A.n) (i' : Fin A'.n) :
    ∀ᵐ y ∂μ.restrict (A'.image i'), (A'.chart i').symm y ∈ A.dom i →
      A'.sectionChartData.chartValueL μ p k i' v y = A'.coord i' s y := by
  choose t ht using fun m ↦ exists_ae_eq_coord (u m)
  have hc : Tendsto (fun m ↦ A.sectionChartData.chartValueL μ p k i (u m)) atTop
      (𝓝 (A.sectionChartData.chartValueL μ p k i w)) :=
    ((A.sectionChartData.chartValueL μ p k i).continuous.tendsto _).comp
      ((continuous_subtype_val.tendsto w).comp hu)
  have hc' : Tendsto (fun m ↦ A'.sectionChartData.chartValueL μ p k i' (changeAtlasₗ h (u m)))
      atTop (𝓝 (A'.sectionChartData.chartValueL μ p k i' v)) :=
    ((A'.sectionChartData.chartValueL μ p k i').continuous.tendsto _).comp
      ((continuous_subtype_val.tendsto v).comp hv)
  -- Almost everywhere convergence of the chart-`i'` data of the images along a subsequence, then
  -- of the chart-`i` data along a further subsequence.
  obtain ⟨ns, hns, hae'⟩ := (tendstoInMeasure_of_tendsto_Lp hc').exists_seq_tendsto_ae
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp
    (hc.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  -- In chart `i` of `A`: the chart data are the readings, and they converge along the subsequence.
  have hA : ∀ᵐ z ∂μ.restrict (A.image i), (∀ m, A.sectionChartData.chartValueL μ p k i (u m) z =
      A.coord i (t m) z) ∧ Tendsto (fun m ↦ A.sectionChartData.chartValueL μ p k i
        (u (ns (ms m))) z) atTop (𝓝 (A.coord i s z)) := by
    filter_upwards [ae_all_iff.2 fun m ↦ ht m i, hae, hs i] with z hz hz' hzs
    exact ⟨hz, hzs ▸ hz'⟩
  have himg : ∀ᵐ y ∂μ.restrict (A'.image i'), ∀ m,
      A'.sectionChartData.chartValueL μ p k i' (changeAtlasₗ h (u m)) y = A'.coord i' (t m) y :=
    ae_all_iff.2 fun m ↦ chartValueL_changeAtlasAux_ae h (ht m) i'
  filter_upwards [A.ae_restrict_image_chart_symm A' i' hA, himg, hae',
    ae_restrict_mem (A'.image i').isOpen.measurableSet] with y hy himg hae' hyU hdom
  obtain ⟨hyA, hyT⟩ := hy hdom
  refine tendsto_nhds_unique (hae'.comp hms.tendsto_atTop) ?_
  rw [A.coord_eq_coordChangeL_coord A' s hyU hdom]
  refine ((((A.triv i).coordChangeL ℝ (A'.triv i') ((A'.chart i').symm y)).continuous.tendsto
    _).comp hyT).congr fun m ↦ ?_
  simp only [Function.comp_apply]
  rw [himg, hyA, A.coord_eq_coordChangeL_coord A' _ hyU hdom]

/-- **Change of atlas.** Given the transfer property `h` from `A` to `A'`, the continuous linear map
from `W^{k,p}(V)` for `A` to `W^{k,p}(V)` for `A'` sending an element to the element whose chart
data are the readings of the same section (`TauCeti.SobolevSection.chartValueL_changeAtlas_ae`).
Continuity is the closed graph theorem. -/
def changeAtlas (h : TransfersTo A A' μ p k) :
    SobolevSection A μ p k →L[ℝ] SobolevSection A' μ p k :=
  ContinuousLinearMap.ofSeqClosedGraph (g := changeAtlasₗ h) fun u w v hu hv ↦ by
    obtain ⟨s, hs⟩ := exists_ae_eq_coord w
    refine eq_of_ae_eq_coord (s := s) (fun i' ↦ ?_) (chartValueL_changeAtlasAux_ae h hs)
    filter_upwards [ae_all_iff.2 fun i ↦ chartValueL_ae_of_tendsto h hu hv hs i i'] with y hy
    obtain ⟨i, hi⟩ := A.exists_mem_dom ((A'.chart i').symm y)
    exact hy i hi

/-- The chart data of `changeAtlas h w` are the readings in the charts of `A'` of any section whose
readings in the charts of `A` are the chart data of `w`. -/
theorem chartValueL_changeAtlas_ae (h : TransfersTo A A' μ p k) {w : SobolevSection A μ p k}
    {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (i' : Fin A'.n) :
    A'.sectionChartData.chartValueL μ p k i' (changeAtlas h w)
      =ᵐ[μ.restrict (A'.image i')] A'.coord i' s :=
  chartValueL_changeAtlasAux_ae h hs i'

/-- **Characterization of the change of atlas.** An element `w'` for `A'` is the image of `w`
exactly when its chart data are the readings of a section of `w`. -/
theorem changeAtlas_eq_of_ae_eq_coord (h : TransfersTo A A' μ p k) {w : SobolevSection A μ p k}
    {w' : SobolevSection A' μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (hs' : ∀ i', A'.sectionChartData.chartValueL μ p k i' w'
      =ᵐ[μ.restrict (A'.image i')] A'.coord i' s) :
    changeAtlas h w = w' :=
  eq_of_ae_eq_coord (chartValueL_changeAtlas_ae h hs) hs'

@[simp]
theorem changeAtlas_refl (w : SobolevSection A μ p k) :
    changeAtlas (transfersTo_refl (A := A) (μ := μ) (p := p) (k := k)) w = w := by
  obtain ⟨s, hs⟩ := exists_ae_eq_coord w
  exact changeAtlas_eq_of_ae_eq_coord _ hs hs

theorem changeAtlas_changeAtlas {A'' : FiniteBundleAtlas E M F V} (h : TransfersTo A A' μ p k)
    (h' : TransfersTo A' A'' μ p k) (w : SobolevSection A μ p k) :
    changeAtlas h' (changeAtlas h w) = changeAtlas (h.trans h') w := by
  obtain ⟨s, hs⟩ := exists_ae_eq_coord w
  exact (changeAtlas_eq_of_ae_eq_coord h' (chartValueL_changeAtlas_ae h hs)
    (chartValueL_changeAtlas_ae (h.trans h') hs))

theorem changeAtlas_comp {A'' : FiniteBundleAtlas E M F V} (h : TransfersTo A A' μ p k)
    (h' : TransfersTo A' A'' μ p k) :
    (changeAtlas h').comp (changeAtlas h) = changeAtlas (h.trans h') :=
  ContinuousLinearMap.ext (changeAtlas_changeAtlas h h')

/-- **Independence of the atlas.** If sections transfer between `A` and `A'` in both directions,
the Sobolev spaces of sections for the two atlases are isomorphic Banach spaces, an element
corresponding to the element with the same section. In particular their norms are equivalent. -/
@[expose] def atlasEquiv (h : TransfersTo A A' μ p k) (h' : TransfersTo A' A μ p k) :
    SobolevSection A μ p k ≃L[ℝ] SobolevSection A' μ p k :=
  ContinuousLinearEquiv.equivOfInverse (changeAtlas h) (changeAtlas h')
    (fun w ↦ (changeAtlas_changeAtlas h h' w).trans (changeAtlas_refl w))
    (fun w ↦ (changeAtlas_changeAtlas h' h w).trans (changeAtlas_refl w))

@[simp]
theorem atlasEquiv_apply (h : TransfersTo A A' μ p k) (h' : TransfersTo A' A μ p k)
    (w : SobolevSection A μ p k) : atlasEquiv h h' w = changeAtlas h w :=
  rfl

@[simp]
theorem atlasEquiv_symm_apply (h : TransfersTo A A' μ p k) (h' : TransfersTo A' A μ p k)
    (w : SobolevSection A' μ p k) : (atlasEquiv h h').symm w = changeAtlas h' w :=
  rfl

theorem atlasEquiv_symm (h : TransfersTo A A' μ p k) (h' : TransfersTo A' A μ p k) :
    (atlasEquiv h h').symm = atlasEquiv h' h :=
  ContinuousLinearEquiv.ext (funext fun w ↦ atlasEquiv_symm_apply h h' w)

@[simp]
theorem atlasEquiv_refl :
    atlasEquiv (transfersTo_refl (A := A) (μ := μ) (p := p) (k := k)) transfersTo_refl =
      ContinuousLinearEquiv.refl ℝ _ :=
  ContinuousLinearEquiv.ext (funext changeAtlas_refl)

theorem atlasEquiv_trans {A'' : FiniteBundleAtlas E M F V} (h₁ : TransfersTo A A' μ p k)
    (h₁' : TransfersTo A' A μ p k) (h₂ : TransfersTo A' A'' μ p k)
    (h₂' : TransfersTo A'' A' μ p k) :
    (atlasEquiv h₁ h₁').trans (atlasEquiv h₂ h₂') = atlasEquiv (h₁.trans h₂) (h₂'.trans h₁') :=
  ContinuousLinearEquiv.ext (funext (changeAtlas_changeAtlas h₁ h₂))

end SobolevSection

end Sobolev

namespace SobolevSection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V 𝓘(ℝ, ℂ)] {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- **Transfer at orders at most one over surfaces.** For a `C¹` bundle over a `C¹` surface, every
element of `W^{k,p}(V)` for one finite bundle atlas, `k ≤ 1`, defines an element for any other: its
expressions in the charts and trivializations of the first atlas are in the local Sobolev classes,
and these determine an element for the second. -/
theorem transfersTo_of_le_one (hk : k ≤ 1) (A A' : FiniteBundleAtlas ℂ M F V) :
    TransfersTo A A' volume p k := fun w s hs ↦
  exists_ae_eq_coord_of_memWkpLoc_trivialization_comp_chart_symm hk A.chart
    (fun _ ↦ IsManifold.chart_mem_maximalAtlas _) A.triv (fun i ↦ A.image i)
    (fun i ↦ (A.image i).isOpen)
    (fun x ↦ let ⟨i, hi⟩ := A.exists_mem_dom x
      ⟨i, A.dom_subset_chart_source i hi, A.dom_subset_baseSet i hi, A.mem_image.2 ⟨_, hi, rfl⟩⟩)
    fun i ↦ by simpa only [funext (A.coord_def i s)] using memWkpLoc_coord w hs i

/-- **Equivalence of norms at orders at most one over surfaces.** The norms of `W^{k,p}(V)`,
`k ≤ 1`, for two finite bundle atlases are equivalent: there is a constant `C` bounding the norm
of each element by `C` times the norm of the element of the other atlas with the same section. -/
theorem exists_norm_le_of_le_one (hk : k ≤ 1) (A A' : FiniteBundleAtlas ℂ M F V) :
    ∃ C : ℝ, ∀ w : SobolevSection A volume p k,
      ‖changeAtlas (transfersTo_of_le_one hk A A') w‖ ≤ C * ‖w‖ ∧
        ‖w‖ ≤ C * ‖changeAtlas (transfersTo_of_le_one hk A A') w‖ := by
  set T := changeAtlas (transfersTo_of_le_one (p := p) hk A A')
  set S := changeAtlas (transfersTo_of_le_one (p := p) hk A' A)
  refine ⟨max ‖T‖ ‖S‖, fun w ↦ ⟨(T.le_opNorm w).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg w)), ?_⟩⟩
  calc ‖w‖ = ‖S (T w)‖ := by rw [(changeAtlas_changeAtlas _ _ w).trans (changeAtlas_refl w)]
    _ ≤ ‖S‖ * ‖T w‖ := S.le_opNorm _
    _ ≤ max ‖T‖ ‖S‖ * ‖T w‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

end SobolevSection

end TauCeti
