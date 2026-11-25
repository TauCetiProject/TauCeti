/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Measure

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

The construction is made once for two chart data `C`, `C'` on the same type of sections
(`TauCeti.SectionChartData.changeAtlas`), so that it also serves bases with boundary
(`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Atlas.Equiv`). It needs that the readings
in the charts of `C'` are read off from those of `C` (`TauCeti.SectionChartData.ReadsFrom`): almost
everywhere on the image of a chart of `C'`, the reading of a section is a continuous linear map
applied to its reading in some chart of `C` at a point given by a map carrying null sets to null
sets. Then two sections whose readings agree almost everywhere in the charts of `C` agree almost
everywhere in the charts of `C'` (`TauCeti.SectionChartData.ReadsFrom.coord_ae_eq`), so the map is
well defined. Continuity follows from the closed graph theorem: both spaces are complete, and if
`w m → w` and `changeAtlas w m → v`, then along a subsequence the chart data converge almost
everywhere, and the readings in `C'` are continuous linear images of those in `C`, so the chart data
of `v` are the readings in `C'` of the section of `w`. For two finite bundle atlases
(`TauCeti.FiniteBundleAtlas.readsFrom_sectionChartData`) the linear maps are the coordinate changes
of the bundle and the maps carrying null sets to null sets are the chart transitions
(`TauCeti.FiniteBundleAtlas.ae_restrict_image_chart_symm`, in
`TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Measure`).

For surfaces, `M` modelled on `ℂ` with the Lebesgue measure, and a `Cⁿ` bundle, `n ≠ 0`, the
transfer property holds at every order `k ≤ n`
(`TauCeti.SobolevSection.transfersTo`), by the localization of Sobolev sections in arbitrary charts
and trivializations of `TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart.Basic`. For a smooth
(`C^∞`) bundle over a smooth Hausdorff manifold modelled on any finite-dimensional real inner
product space, the transfer property holds between any two finite bundle atlases, for every order
`k` and every `1 ≤ p ≤ ∞` (`TauCeti.SobolevSection.transfersTo_of_contMDiffVectorBundle`, in
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Atlas.Transfer`).

## Main definitions

* `TauCeti.SectionChartData.ReadsFrom C C' μ`: the readings in the charts of `C'` are read off from
  those of `C`.
* `TauCeti.SectionChartData.TransfersTo`, `TauCeti.SectionChartData.changeAtlas`: the transfer
  property and the change of chart data.
* `TauCeti.SobolevSection.TransfersTo A A' μ p k`: every section with `W^{k,p}` components in the
  charts of `A` has `W^{k,p}` components in the charts of `A'`.
* `TauCeti.SobolevSection.changeAtlas`: the continuous linear map between the Sobolev spaces of two
  atlases sending an element to the element with the same section.
* `TauCeti.SobolevSection.atlasEquiv`: the isomorphism of Banach spaces between them.

## Main results

* `TauCeti.SobolevSection.chartValueL_changeAtlas_ae`: the chart data of `changeAtlas h w` are the
  readings in `A'` of any section of `w`.
* `TauCeti.SobolevSection.exists_norm_changeAtlas_le`: when sections transfer in both directions the
  norms of the two atlases are equivalent.
* `TauCeti.SobolevSection.transfersTo`: the transfer property for `Cⁿ` bundles over surfaces at
  orders `k ≤ n`.
* `TauCeti.SobolevSection.exists_norm_changeAtlas_le_of_surface`: for such bundles and orders the
  norms of two finite bundle atlases are equivalent.

The transfer property for smooth bundles in every dimension,
`TauCeti.SobolevSection.transfersTo_of_contMDiffVectorBundle`, is proved in
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Atlas.Transfer`.

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

section ChartData

/-! ### Change of chart data -/

namespace SectionChartData

section Related

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {S : Type*} [AddCommGroup S] [Module ℝ S]
  (C C' : SectionChartData E F S) (μ : Measure E)

/-- **The readings of `C'` are read off from those of `C`.** For each pair of charts `i` of `C`
and `i'` of `C'` there are a set `D i i'`, a map `τ i i'` and a field of continuous linear maps
`L i i'` such that almost every point of the image of chart `i'` lies in some `D i i'`; a property
holding almost everywhere on the image of chart `i` holds at `τ i i' y` for almost every `y` of
the image of chart `i'` lying in `D i i'`; and at such `y` the reading of every section in chart
`i'` is `L i i' y` applied to its reading in chart `i` at `τ i i' y`. For two finite bundle
atlases of the same bundle, `D i i'` is the part of the image of chart `i'` lying over the domain
of chart `i`, `τ i i'` the chart transition and `L i i'` the coordinate change of the bundle. -/
@[expose] def ReadsFrom : Prop :=
  ∃ (D : Fin C.n → Fin C'.n → Set E) (τ : Fin C.n → Fin C'.n → E → E)
    (L : Fin C.n → Fin C'.n → E → F →L[ℝ] F),
    (∀ i', ∀ᵐ y ∂μ.restrict (C'.image i'), ∃ i, y ∈ D i i') ∧
    (∀ i i' ⦃P : E → Prop⦄, (∀ᵐ z ∂μ.restrict (C.image i), P z) →
      ∀ᵐ y ∂μ.restrict (C'.image i'), y ∈ D i i' → P (τ i i' y)) ∧
    ∀ i i' (s : S), ∀ᵐ y ∂μ.restrict (C'.image i'), y ∈ D i i' →
      C'.coord i' s y = L i i' y (C.coord i s (τ i i' y))

/-- Chart data read off from themselves, each chart from itself. -/
theorem readsFrom_refl : C.ReadsFrom C μ :=
  ⟨fun i i' ↦ {_y | i = i'}, fun _ _ ↦ id, fun _ _ _ ↦ 1,
    fun i' ↦ ae_of_all _ fun _ ↦ ⟨i', rfl⟩,
    fun i i' P h ↦ by
      obtain rfl | hii := eq_or_ne i i'
      · filter_upwards [h] with y hy _ using hy
      · exact ae_of_all _ fun _ hy ↦ absurd hy hii,
    fun i i' s ↦ ae_of_all _ fun _ hy ↦ by
      obtain rfl : i = i' := hy
      rfl⟩

variable {C C' μ}

/-- Sections whose readings agree almost everywhere in every chart of `C` agree almost everywhere
in every chart of chart data `C'` read off from `C`. -/
theorem ReadsFrom.coord_ae_eq (hC : C.ReadsFrom C' μ) {s t : S}
    (h : ∀ i, C.coord i s =ᵐ[μ.restrict (C.image i)] C.coord i t) (i' : Fin C'.n) :
    C'.coord i' s =ᵐ[μ.restrict (C'.image i')] C'.coord i' t := by
  obtain ⟨D, τ, L, hcov, hnull, hrel⟩ := hC
  filter_upwards [hcov i', ae_all_iff.2 fun i ↦ hnull i i' (h i), ae_all_iff.2 fun i ↦ hrel i i' s,
    ae_all_iff.2 fun i ↦ hrel i i' t] with y ⟨i, hi⟩ hst hs ht
  rw [hs i hi, ht i hi, hst i hi]

end Related

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {S : Type*} [AddCommGroup S] [Module ℝ S]
  (C C' : SectionChartData E F S) (μ : Measure E) [μ.IsAddHaarMeasure]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- **Transfer of Sobolev sections between chart data.** Every section whose readings in the
charts of `C` are the chart data of an element of `W^{k,p}` for `C` also has readings in the
charts of `C'` that are the chart data of an element of `W^{k,p}` for `C'`. -/
@[expose] def TransfersTo : Prop :=
  ∀ (w : C.sobolevSections μ p k) (s : S),
    (∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s) →
      ∃ w' : C'.sobolevSections μ p k,
        ∀ i', C'.chartValueL μ p k i' w' =ᵐ[μ.restrict (C'.image i')] C'.coord i' s

variable {C C' μ p k}

theorem transfersTo_refl : C.TransfersTo C μ p k :=
  fun w _ hs ↦ ⟨w, hs⟩

theorem TransfersTo.trans {C'' : SectionChartData E F S} (h : C.TransfersTo C' μ p k)
    (h' : C'.TransfersTo C'' μ p k) : C.TransfersTo C'' μ p k := fun w s hs ↦
  let ⟨w', hw'⟩ := h w s hs
  h' w' s hw'

/-- The element of `W^{k,p}` for `C'` with the same section as `w`, before continuity is
established. -/
private def changeAtlasAux (h : C.TransfersTo C' μ p k) (w : C.sobolevSections μ p k) :
    C'.sobolevSections μ p k :=
  (h w _ (C.exists_section μ p k w).choose_spec).choose

private theorem chartValueL_changeAtlasAux_ae (hC : C.ReadsFrom C' μ) (h : C.TransfersTo C' μ p k)
    {w : C.sobolevSections μ p k} {s : S}
    (hs : ∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s) (i' : Fin C'.n) :
    C'.chartValueL μ p k i' (changeAtlasAux h w) =ᵐ[μ.restrict (C'.image i')] C'.coord i' s :=
  ((h w _ (C.exists_section μ p k w).choose_spec).choose_spec i').trans <|
    hC.coord_ae_eq (fun i ↦ ((C.exists_section μ p k w).choose_spec i).symm.trans (hs i)) i'

/-- The element of `W^{k,p}` for `C'` with the same section, as a linear map. -/
private def changeAtlasₗ (hC : C.ReadsFrom C' μ) (h : C.TransfersTo C' μ p k) :
    C.sobolevSections μ p k →ₗ[ℝ] C'.sobolevSections μ p k where
  toFun := changeAtlasAux h
  map_add' w w' := by
    obtain ⟨s, hs⟩ := C.exists_section μ p k w
    obtain ⟨t, ht⟩ := C.exists_section μ p k w'
    exact eq_of_ae_eq_coord
      (chartValueL_changeAtlasAux_ae hC h fun i ↦ chartValueL_add_ae_coord (hs i) (ht i))
      fun i' ↦ chartValueL_add_ae_coord (chartValueL_changeAtlasAux_ae hC h hs i')
        (chartValueL_changeAtlasAux_ae hC h ht i')
  map_smul' c w := by
    obtain ⟨s, hs⟩ := C.exists_section μ p k w
    exact eq_of_ae_eq_coord
      (chartValueL_changeAtlasAux_ae hC h fun i ↦ chartValueL_smul_ae_coord c (hs i))
      fun i' ↦ chartValueL_smul_ae_coord c (chartValueL_changeAtlasAux_ae hC h hs i')

/-- **The graph of the change of chart data is closed.** If `w m → w` in `W^{k,p}` for `C` and the
corresponding elements for `C'` converge to `v`, then in each chart `i'` of `C'` the chart data of
`v` are the readings of the section of `w`, almost everywhere on the part `D i i'` read off from
chart `i` of `C`. -/
private theorem chartValueL_ae_of_tendsto {D : Fin C.n → Fin C'.n → Set E}
    {τ : Fin C.n → Fin C'.n → E → E} {L : Fin C.n → Fin C'.n → E → F →L[ℝ] F}
    (hnull : ∀ i i' ⦃P : E → Prop⦄, (∀ᵐ z ∂μ.restrict (C.image i), P z) →
      ∀ᵐ y ∂μ.restrict (C'.image i'), y ∈ D i i' → P (τ i i' y))
    (hrel : ∀ i i' (s : S), ∀ᵐ y ∂μ.restrict (C'.image i'), y ∈ D i i' →
      C'.coord i' s y = L i i' y (C.coord i s (τ i i' y)))
    (hC : C.ReadsFrom C' μ) (h : C.TransfersTo C' μ p k) {u : ℕ → C.sobolevSections μ p k}
    {w : C.sobolevSections μ p k} {v : C'.sobolevSections μ p k} (hu : Tendsto u atTop (𝓝 w))
    (hv : Tendsto (changeAtlasₗ hC h ∘ u) atTop (𝓝 v)) {s : S}
    (hs : ∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s)
    (i : Fin C.n) (i' : Fin C'.n) :
    ∀ᵐ y ∂μ.restrict (C'.image i'), y ∈ D i i' → C'.chartValueL μ p k i' v y = C'.coord i' s y := by
  choose t ht using fun m ↦ C.exists_section μ p k (u m)
  have hc : Tendsto (fun m ↦ C.chartValueL μ p k i (u m)) atTop (𝓝 (C.chartValueL μ p k i w)) :=
    ((C.chartValueL μ p k i).continuous.tendsto _).comp ((continuous_subtypeVal.tendsto w).comp hu)
  have hc' : Tendsto (fun m ↦ C'.chartValueL μ p k i' (changeAtlasₗ hC h (u m))) atTop
      (𝓝 (C'.chartValueL μ p k i' v)) :=
    ((C'.chartValueL μ p k i').continuous.tendsto _).comp
      ((continuous_subtypeVal.tendsto v).comp hv)
  -- Almost everywhere convergence of the chart-`i'` data of the images along a subsequence, then
  -- of the chart-`i` data along a further subsequence.
  obtain ⟨ns, hns, hae'⟩ := (tendstoInMeasure_of_tendsto_Lp hc').exists_seq_tendsto_ae
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp
    (hc.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  -- In chart `i` of `C`: the chart data are the readings, and they converge along the subsequence.
  have hA : ∀ᵐ z ∂μ.restrict (C.image i), (∀ m, C.chartValueL μ p k i (u m) z =
      C.coord i (t m) z) ∧ Tendsto (fun m ↦ C.chartValueL μ p k i (u (ns (ms m))) z) atTop
        (𝓝 (C.coord i s z)) := by
    filter_upwards [ae_all_iff.2 fun m ↦ ht m i, hae, hs i] with z hz hz' hzs
    exact ⟨hz, hzs ▸ hz'⟩
  have himg : ∀ᵐ y ∂μ.restrict (C'.image i'), ∀ m,
      C'.chartValueL μ p k i' (changeAtlasₗ hC h (u m)) y = C'.coord i' (t m) y :=
    ae_all_iff.2 fun m ↦ chartValueL_changeAtlasAux_ae hC h (ht m) i'
  filter_upwards [hnull i i' hA, himg, hae', hrel i i' s, ae_all_iff.2 fun m ↦ hrel i i' (t m)]
    with y hy himg hae' hys hyt hD
  obtain ⟨hyA, hyT⟩ := hy hD
  refine tendsto_nhds_unique (hae'.comp hms.tendsto_atTop) ?_
  rw [hys hD]
  refine (((L i i' y).continuous.tendsto _).comp hyT).congr fun m ↦ ?_
  simp only [Function.comp_apply]
  rw [himg, hyA, hyt _ hD]

/-- **Change of chart data.** For chart data `C'` read off from `C` and the transfer property `h`
from `C` to `C'`, the continuous linear map from `W^{k,p}` for `C` to `W^{k,p}` for `C'` sending an
element to the element whose chart data are the readings of the same section
(`TauCeti.SectionChartData.chartValueL_changeAtlas_ae`). Continuity is the closed graph
theorem. -/
def changeAtlas [CompleteSpace (C.sobolevSections μ p k)] [CompleteSpace (C'.sobolevSections μ p k)]
    (hC : C.ReadsFrom C' μ) (h : C.TransfersTo C' μ p k) :
    C.sobolevSections μ p k →L[ℝ] C'.sobolevSections μ p k :=
  ContinuousLinearMap.ofSeqClosedGraph (g := changeAtlasₗ hC h) fun u w v hu hv ↦ by
    obtain ⟨s, hs⟩ := C.exists_section μ p k w
    obtain ⟨D, τ, L, hcov, hnull, hrel⟩ := id hC
    refine eq_of_ae_eq_coord (s := s) (fun i' ↦ ?_) (chartValueL_changeAtlasAux_ae hC h hs)
    filter_upwards [hcov i', ae_all_iff.2 fun i ↦
      chartValueL_ae_of_tendsto hnull hrel hC h hu hv hs i i'] with y ⟨i, hi⟩ hy
    exact hy i hi

variable [CompleteSpace (C.sobolevSections μ p k)] [CompleteSpace (C'.sobolevSections μ p k)]

/-- The chart data of `changeAtlas hC h w` are the readings in the charts of `C'` of any section
whose readings in the charts of `C` are the chart data of `w`. -/
theorem chartValueL_changeAtlas_ae (hC : C.ReadsFrom C' μ) (h : C.TransfersTo C' μ p k)
    {w : C.sobolevSections μ p k} {s : S}
    (hs : ∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s) (i' : Fin C'.n) :
    C'.chartValueL μ p k i' (changeAtlas hC h w) =ᵐ[μ.restrict (C'.image i')] C'.coord i' s :=
  chartValueL_changeAtlasAux_ae hC h hs i'

/-- **Identification of the change of chart data.** An element `w'` for `C'` whose chart data are
the readings in the charts of `C'` of a section of `w` is the image of `w`. -/
theorem changeAtlas_eq_of_ae_eq_coord (hC : C.ReadsFrom C' μ) (h : C.TransfersTo C' μ p k)
    {w : C.sobolevSections μ p k} {w' : C'.sobolevSections μ p k} {s : S}
    (hs : ∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s)
    (hs' : ∀ i', C'.chartValueL μ p k i' w' =ᵐ[μ.restrict (C'.image i')] C'.coord i' s) :
    changeAtlas hC h w = w' :=
  eq_of_ae_eq_coord (chartValueL_changeAtlas_ae hC h hs) hs'

theorem changeAtlas_refl_apply (w : C.sobolevSections μ p k) :
    changeAtlas (C.readsFrom_refl μ) (transfersTo_refl (C := C) (μ := μ) (p := p) (k := k)) w =
      w := by
  obtain ⟨s, hs⟩ := C.exists_section μ p k w
  exact changeAtlas_eq_of_ae_eq_coord _ _ hs hs

theorem changeAtlas_changeAtlas {C'' : SectionChartData E F S}
    [CompleteSpace (C''.sobolevSections μ p k)] (hC : C.ReadsFrom C' μ) (hC' : C'.ReadsFrom C'' μ)
    (hC'' : C.ReadsFrom C'' μ) (h : C.TransfersTo C' μ p k) (h' : C'.TransfersTo C'' μ p k)
    (w : C.sobolevSections μ p k) :
    changeAtlas hC' h' (changeAtlas hC h w) = changeAtlas hC'' (h.trans h') w := by
  obtain ⟨s, hs⟩ := C.exists_section μ p k w
  exact changeAtlas_eq_of_ae_eq_coord hC' h' (chartValueL_changeAtlas_ae hC h hs)
    (chartValueL_changeAtlas_ae hC'' (h.trans h') hs)

/-- The change of chart data is injective when `C` is also read off from `C'`: two sections with
the same readings almost everywhere in the charts of `C'` have the same readings almost everywhere
in the charts of `C`. -/
theorem changeAtlas_injective (hC : C.ReadsFrom C' μ) (hC' : C'.ReadsFrom C μ)
    (h : C.TransfersTo C' μ p k) : Function.Injective (changeAtlas hC h) := by
  intro w v hwv
  obtain ⟨s, hs⟩ := C.exists_section μ p k w
  obtain ⟨t, ht⟩ := C.exists_section μ p k v
  have hst := hC'.coord_ae_eq fun i' ↦
    (chartValueL_changeAtlas_ae hC h hs i').symm.trans (hwv ▸ chartValueL_changeAtlas_ae hC h ht i')
  exact eq_of_ae_eq_coord hs fun i ↦ (ht i).trans (hst i).symm

/-- The change of chart data commutes with forgetting the highest derivative. -/
theorem lowerOrderL_changeAtlas [CompleteSpace (C.sobolevSections μ p (k + 1))]
    [CompleteSpace (C'.sobolevSections μ p (k + 1))] (hC : C.ReadsFrom C' μ)
    (h : C.TransfersTo C' μ p (k + 1)) (h₀ : C.TransfersTo C' μ p k)
    (w : C.sobolevSections μ p (k + 1)) :
    C'.lowerOrderL μ p k (changeAtlas hC h w) = changeAtlas hC h₀ (C.lowerOrderL μ p k w) := by
  obtain ⟨s, hs⟩ := C.exists_section μ p (k + 1) w
  refine eq_of_ae_eq_coord (s := s) (fun i' ↦ ?_) (chartValueL_changeAtlas_ae hC h₀ fun i ↦ ?_)
  · rw [chartValueL_coe_lowerOrderL]
    exact chartValueL_changeAtlas_ae hC h hs i'
  · rw [chartValueL_coe_lowerOrderL]
    exact hs i

/-- **Equivalence of norms.** If chart data are read off from each other and sections transfer
between them in both directions, there is a positive constant `C₀` bounding the norm of each
element by `C₀` times the norm of the element for the other chart data with the same section. -/
theorem exists_norm_changeAtlas_le (hC : C.ReadsFrom C' μ) (hC' : C'.ReadsFrom C μ)
    (h : C.TransfersTo C' μ p k) (h' : C'.TransfersTo C μ p k) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ w : C.sobolevSections μ p k,
      ‖changeAtlas hC h w‖ ≤ C₀ * ‖w‖ ∧ ‖w‖ ≤ C₀ * ‖changeAtlas hC h w‖ := by
  set T := changeAtlas hC h
  set R := changeAtlas hC' h'
  refine ⟨max 1 (max ‖T‖ ‖R‖), lt_max_of_lt_left one_pos, fun w ↦ ⟨(T.le_opNorm w).trans
    (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) (norm_nonneg w)), ?_⟩⟩
  calc ‖w‖ = ‖R (T w)‖ := by
        rw [changeAtlas_changeAtlas hC hC' (C.readsFrom_refl μ), changeAtlas_refl_apply]
    _ ≤ ‖R‖ * ‖T w‖ := R.le_opNorm _
    _ ≤ max 1 (max ‖T‖ ‖R‖) * ‖T w‖ :=
      mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) (norm_nonneg _)

end SectionChartData

end ChartData

section Sobolev

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A A' : FiniteBundleAtlas E M F V) (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ F] in
/-- The chart data of a finite bundle atlas are read off from those of any other: on the part of
the image of chart `i'` of `A'` lying over the domain of chart `i` of `A`, the reading in chart
`i'` is the coordinate change of the bundle applied to the reading in chart `i` at the chart
transition, which carries null sets to null sets. -/
theorem FiniteBundleAtlas.readsFrom_sectionChartData [IsManifold 𝓘(ℝ, E) 1 M] :
    A.sectionChartData.ReadsFrom A'.sectionChartData μ :=
  ⟨fun i i' ↦ {y | (A'.chart i').symm y ∈ A.dom i}, fun i i' y ↦ A.chart i ((A'.chart i').symm y),
    fun i i' y ↦ (A.triv i).coordChangeL ℝ (A'.triv i') ((A'.chart i').symm y),
    fun _ ↦ ae_of_all _ fun _ ↦ A.exists_mem_dom _,
    fun _ i' _ h ↦ A.ae_restrict_image_chart_symm A' i' h,
    fun i i' s ↦ by
      filter_upwards [ae_restrict_mem (A'.image i').isOpen.measurableSet] with y hyU hdom
      rw [A'.sectionChartData_coord_of_mem s hyU,
        A.sectionChartData_coord_of_mem s (A.mem_image.2 ⟨_, hdom, rfl⟩)]
      exact A.coord_eq_coordChangeL_coord A' s (A'.dom_subset_baseSet i' (A'.symm_mem_dom hyU))
        hdom⟩

namespace SobolevSection

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- **Transfer of Sobolev sections between atlases.** Every section whose chart data in the charts
of `A` are those of an element of `W^{k,p}(V)` for `A` also has chart data in the charts of `A'`
that are those of an element of `W^{k,p}(V)` for `A'` (`TauCeti.SobolevSection.transfersTo_iff`).
For `Cⁿ` bundles over surfaces this holds at orders `k ≤ n` (`TauCeti.SobolevSection.transfersTo`).
For smooth bundles over smooth Hausdorff manifolds in every dimension it holds at every order and
every `1 ≤ p ≤ ∞` (`TauCeti.SobolevSection.transfersTo_of_contMDiffVectorBundle`). -/
@[expose] def TransfersTo : Prop :=
  A.sectionChartData.TransfersTo A'.sectionChartData μ p k

variable {A A' μ p k}

/-- Unfolding `TauCeti.SobolevSection.TransfersTo` in terms of the readings `A.coord i s`, for
establishing and using the transfer property outside this file. -/
theorem transfersTo_iff : TransfersTo A A' μ p k ↔
    ∀ (w : SobolevSection A μ p k) (s : ∀ x, V x),
      (∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) →
        ∃ w' : SobolevSection A' μ p k,
          ∀ i', A'.sectionChartData.chartValueL μ p k i' w' =ᵐ[μ.restrict (A'.image i')]
            A'.coord i' s := by
  refine forall₂_congr fun w s ↦ ?_
  refine imp_congr (forall_congr' fun i ↦ ?_) (exists_congr fun w' ↦ forall_congr' fun i' ↦ ?_)
  · exact ⟨fun h ↦ h.trans (A.sectionChartData_coord_ae_eq μ i s),
      fun h ↦ h.trans (A.sectionChartData_coord_ae_eq μ i s).symm⟩
  · exact ⟨fun h ↦ h.trans (A'.sectionChartData_coord_ae_eq μ i' s),
      fun h ↦ h.trans (A'.sectionChartData_coord_ae_eq μ i' s).symm⟩

theorem transfersTo_refl : TransfersTo A A μ p k :=
  SectionChartData.transfersTo_refl

theorem TransfersTo.trans {A'' : FiniteBundleAtlas E M F V} (h : TransfersTo A A' μ p k)
    (h' : TransfersTo A' A'' μ p k) : TransfersTo A A'' μ p k :=
  SectionChartData.TransfersTo.trans h h'

variable [IsManifold 𝓘(ℝ, E) 1 M]

/-- **Change of atlas.** Given the transfer property `h` from `A` to `A'`, the continuous linear map
from `W^{k,p}(V)` for `A` to `W^{k,p}(V)` for `A'` sending an element to the element whose chart
data are the readings of the same section (`TauCeti.SobolevSection.chartValueL_changeAtlas_ae`).
It is `TauCeti.SectionChartData.changeAtlas` for the chart data of the two atlases. -/
def changeAtlas (h : TransfersTo A A' μ p k) :
    SobolevSection A μ p k →L[ℝ] SobolevSection A' μ p k :=
  SectionChartData.changeAtlas (A.readsFrom_sectionChartData A' μ) h

/-- The chart data of `changeAtlas h w` are the readings in the charts of `A'` of any section whose
readings in the charts of `A` are the chart data of `w`. -/
theorem chartValueL_changeAtlas_ae (h : TransfersTo A A' μ p k) {w : SobolevSection A μ p k}
    {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (i' : Fin A'.n) :
    A'.sectionChartData.chartValueL μ p k i' (changeAtlas h w)
      =ᵐ[μ.restrict (A'.image i')] A'.coord i' s :=
  (SectionChartData.chartValueL_changeAtlas_ae _ h
    (fun i ↦ (hs i).trans (A.sectionChartData_coord_ae_eq μ i s).symm) i').trans
      (A'.sectionChartData_coord_ae_eq μ i' s)

/-- **Identification of the change of atlas.** An element `w'` for `A'` whose chart data are the
readings in the charts of `A'` of a section of `w` is the image of `w`. -/
theorem changeAtlas_eq_of_ae_eq_coord (h : TransfersTo A A' μ p k) {w : SobolevSection A μ p k}
    {w' : SobolevSection A' μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (hs' : ∀ i', A'.sectionChartData.chartValueL μ p k i' w'
      =ᵐ[μ.restrict (A'.image i')] A'.coord i' s) :
    changeAtlas h w = w' :=
  eq_of_ae_eq_coord (chartValueL_changeAtlas_ae h hs) hs'

theorem changeAtlas_refl_apply (w : SobolevSection A μ p k) :
    changeAtlas (transfersTo_refl (A := A) (μ := μ) (p := p) (k := k)) w = w :=
  SectionChartData.changeAtlas_refl_apply w

@[simp]
theorem changeAtlas_refl :
    changeAtlas (transfersTo_refl (A := A) (μ := μ) (p := p) (k := k)) =
      ContinuousLinearMap.id ℝ _ :=
  ContinuousLinearMap.ext changeAtlas_refl_apply

@[simp]
theorem changeAtlas_changeAtlas {A'' : FiniteBundleAtlas E M F V} (h : TransfersTo A A' μ p k)
    (h' : TransfersTo A' A'' μ p k) (w : SobolevSection A μ p k) :
    changeAtlas h' (changeAtlas h w) = changeAtlas (h.trans h') w :=
  SectionChartData.changeAtlas_changeAtlas _ _ _ h h' w

@[simp]
theorem changeAtlas_comp {A'' : FiniteBundleAtlas E M F V} (h : TransfersTo A A' μ p k)
    (h' : TransfersTo A' A'' μ p k) :
    (changeAtlas h').comp (changeAtlas h) = changeAtlas (h.trans h') :=
  ContinuousLinearMap.ext (changeAtlas_changeAtlas h h')

/-- The change of atlas is injective: two sections with the same readings almost everywhere in the
charts of `A'` have the same readings almost everywhere in the charts of `A`. -/
theorem changeAtlas_injective (h : TransfersTo A A' μ p k) :
    Function.Injective (changeAtlas h) :=
  SectionChartData.changeAtlas_injective _ (A'.readsFrom_sectionChartData A μ) h

/-- The change of atlas commutes with forgetting the highest derivative. -/
theorem lowerOrderL_changeAtlas (h : TransfersTo A A' μ p (k + 1)) (h₀ : TransfersTo A A' μ p k)
    (w : SobolevSection A μ p (k + 1)) :
    A'.sectionChartData.lowerOrderL μ p k (changeAtlas h w) =
      changeAtlas h₀ (A.sectionChartData.lowerOrderL μ p k w) :=
  SectionChartData.lowerOrderL_changeAtlas _ h h₀ w

/-- The change of atlas sends the Sobolev section of a `Cᵏ` section for `A` to the Sobolev section
of the same `Cᵏ` section for `A'`. -/
@[simp]
theorem changeAtlas_ofContMDiffSection [IsManifold 𝓘(ℝ, E) k M]
    [ContMDiffVectorBundle k F V 𝓘(ℝ, E)] (h : TransfersTo A A' μ p k)
    (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) :
    changeAtlas h (ofContMDiffSection A μ p k s) = ofContMDiffSection A' μ p k s :=
  changeAtlas_eq_of_ae_eq_coord h (chartValueL_ofContMDiffSection_ae A μ p k s)
    (chartValueL_ofContMDiffSection_ae A' μ p k s)

/-- **Independence of the atlas.** If sections transfer between `A` and `A'` in both directions,
the Sobolev spaces of sections for the two atlases are isomorphic Banach spaces, an element
corresponding to the element with the same section. In particular their norms are equivalent. -/
def atlasEquiv (h : TransfersTo A A' μ p k) (h' : TransfersTo A' A μ p k) :
    SobolevSection A μ p k ≃L[ℝ] SobolevSection A' μ p k :=
  ContinuousLinearEquiv.ofContinuousLinearMap (changeAtlas h) (changeAtlas h')
    (ContinuousLinearMap.ext fun w ↦
      (changeAtlas_changeAtlas h' h w).trans (changeAtlas_refl_apply w))
    (ContinuousLinearMap.ext fun w ↦
      (changeAtlas_changeAtlas h h' w).trans (changeAtlas_refl_apply w))

@[simp]
theorem toContinuousLinearMap_atlasEquiv (h : TransfersTo A A' μ p k)
    (h' : TransfersTo A' A μ p k) :
    (atlasEquiv h h' : SobolevSection A μ p k →L[ℝ] SobolevSection A' μ p k) = changeAtlas h :=
  (rfl)

@[simp]
theorem atlasEquiv_apply (h : TransfersTo A A' μ p k) (h' : TransfersTo A' A μ p k)
    (w : SobolevSection A μ p k) : atlasEquiv h h' w = changeAtlas h w :=
  (rfl)

theorem atlasEquiv_symm_apply (h : TransfersTo A A' μ p k) (h' : TransfersTo A' A μ p k)
    (w : SobolevSection A' μ p k) : (atlasEquiv h h').symm w = changeAtlas h' w :=
  (rfl)

@[simp]
theorem atlasEquiv_symm (h : TransfersTo A A' μ p k) (h' : TransfersTo A' A μ p k) :
    (atlasEquiv h h').symm = atlasEquiv h' h :=
  ContinuousLinearEquiv.ext (funext fun w ↦ atlasEquiv_symm_apply h h' w)

@[simp]
theorem atlasEquiv_refl :
    atlasEquiv (transfersTo_refl (A := A) (μ := μ) (p := p) (k := k)) transfersTo_refl =
      ContinuousLinearEquiv.refl ℝ _ :=
  ContinuousLinearEquiv.ext (funext changeAtlas_refl_apply)

@[simp]
theorem atlasEquiv_trans {A'' : FiniteBundleAtlas E M F V} (h₁ : TransfersTo A A' μ p k)
    (h₁' : TransfersTo A' A μ p k) (h₂ : TransfersTo A' A'' μ p k)
    (h₂' : TransfersTo A'' A' μ p k) :
    (atlasEquiv h₁ h₁').trans (atlasEquiv h₂ h₂') = atlasEquiv (h₁.trans h₂) (h₂'.trans h₁') :=
  ContinuousLinearEquiv.ext (funext (changeAtlas_changeAtlas h₁ h₂))

/-- **Equivalence of norms.** If sections transfer between `A` and `A'` in both directions, the
norms of the Sobolev spaces of sections for the two atlases are equivalent: there is a positive
constant `C` bounding the norm of each element by `C` times the norm of the element of the other
atlas with the same section. -/
theorem exists_norm_changeAtlas_le (h : TransfersTo A A' μ p k) (h' : TransfersTo A' A μ p k) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : SobolevSection A μ p k,
      ‖changeAtlas h w‖ ≤ C * ‖w‖ ∧ ‖w‖ ≤ C * ‖changeAtlas h w‖ :=
  SectionChartData.exists_norm_changeAtlas_le _ (A'.readsFrom_sectionChartData A μ) h h'

end SobolevSection

end Sobolev

namespace SobolevSection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {n : WithTop ℕ∞}
  [IsManifold 𝓘(ℝ, ℂ) n M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle n F V 𝓘(ℝ, ℂ)] {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- **Transfer over surfaces.** For a `Cⁿ` bundle over a `Cⁿ` surface, `n ≠ 0`, and an order
`k ≤ n`, every element of `W^{k,p}(V)` for one finite bundle atlas defines
an element for any other: its expressions in the charts and trivializations of the first atlas are
in the local Sobolev classes, and these determine an element for the second. -/
theorem transfersTo (hn : n ≠ 0) (hkn : (k : WithTop ℕ∞) ≤ n)
    (A A' : FiniteBundleAtlas ℂ M F V) : TransfersTo A A' volume p k :=
  transfersTo_iff.2 fun w s hs ↦
  haveI : IsManifold 𝓘(ℝ, ℂ) 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  exists_ae_eq_coord_of_memWkpLoc_trivialization_comp_chart_symm A.chart
    (fun _ ↦ IsManifold.chart_mem_maximalAtlas _) A.triv (fun i ↦ A.image i)
    (fun i ↦ (A.image i).isOpen)
    (fun x ↦ let ⟨i, hi⟩ := A.exists_mem_dom x
      ⟨i, A.dom_subset_chart_source i hi, A.dom_subset_baseSet i hi, A.mem_image.2 ⟨_, hi, rfl⟩⟩)
    (fun i ↦ by simpa only [funext (A.coord_def i s)] using memWkpLoc_coord w hs i) hn hkn

/-- **Equivalence of norms over surfaces.** For a `Cⁿ` bundle over a `Cⁿ` surface, `n ≠ 0`, and an
order `k ≤ n`, the norms of `W^{k,p}(V)` for two finite bundle atlases are
equivalent: there is a positive constant `C` bounding the norm of each element by `C` times the
norm of the element of the other atlas with the same section. -/
theorem exists_norm_changeAtlas_le_of_surface [IsManifold 𝓘(ℝ, ℂ) 1 M] (hn : n ≠ 0)
    (hkn : (k : WithTop ℕ∞) ≤ n) (A A' : FiniteBundleAtlas ℂ M F V) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : SobolevSection A volume p k,
      ‖changeAtlas (transfersTo hn hkn A A') w‖ ≤ C * ‖w‖ ∧
        ‖w‖ ≤ C * ‖changeAtlas (transfersTo hn hkn A A') w‖ :=
  exists_norm_changeAtlas_le (transfersTo hn hkn A A') (transfersTo hn hkn A' A)

end SobolevSection

end TauCeti
