/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Change of chart data for Sobolev spaces of sections

Let `C`, `C'` be two section chart data (`TauCeti.SectionChartData`) on the same type `S` of
sections, for instance those of two finite bundle atlases of a vector bundle, over a base with or
without boundary. Their Sobolev spaces `C.sobolevSections μ p k` and `C'.sobolevSections μ p k`
consist of tuples of chartwise Sobolev components of sections. Assume that both spaces are complete
(this is taken as instance arguments here; it holds for `TauCeti.SobolevSection` and for the Sobolev
sections over bases with boundary of
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Basic`, for `C¹` manifolds), and that the
readings in the charts of `C'` are read off from those of `C` (`TauCeti.SectionChartData.ReadsFrom`,
explained below). This file shows that, whenever every section with `W^{k,p}` components for
`C` also has `W^{k,p}` components for `C'` (`TauCeti.SectionChartData.TransfersTo C C' μ p k`),
sending an element to the element for `C'` with the same section is a continuous linear map
(`TauCeti.SectionChartData.changeAtlas`). When `ReadsFrom` and the transfer property hold in both
directions the two spaces are isomorphic Banach spaces (`TauCeti.SectionChartData.atlasEquiv`), so
their norms are equivalent (`TauCeti.SectionChartData.exists_norm_changeAtlas_le`).

The construction needs that the readings in the charts of `C'` are read off from those of `C`
(`TauCeti.SectionChartData.ReadsFrom`): almost everywhere on the image of a chart of `C'`, the
reading of a section is a continuous linear map applied to its reading in some chart of `C`, at a
point given by a map carrying null sets to null sets. Then two sections whose readings agree almost
everywhere in the charts of `C` agree almost everywhere in the charts of `C'`
(`TauCeti.SectionChartData.ReadsFrom.coord_ae_eq`), so the map is well defined. Continuity follows
from the closed graph theorem, using the assumed completeness: if `w m → w` and
`changeAtlas w m → v`, then along a subsequence the chart data converge almost everywhere, and the
readings in `C'` are continuous linear images of those in `C`, so the chart data of `v` are the
readings in `C'` of the section of `w`.

For two finite bundle atlases the linear maps are the coordinate changes of the bundle and the maps
carrying null sets to null sets are the chart transitions; the instances are in
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Atlas.Equiv` (bases without boundary) and
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Atlas.Equiv` (bases with boundary).

## Main definitions

* `TauCeti.SectionChartData.ReadsFrom C C' μ`: the readings in the charts of `C'` are read off from
  those of `C`.
* `TauCeti.SectionChartData.TransfersTo C C' μ p k`: every section with `W^{k,p}` components for
  `C` has `W^{k,p}` components for `C'`.
* `TauCeti.SectionChartData.changeAtlas`: the continuous linear map sending an element to the
  element with the same section.
* `TauCeti.SectionChartData.atlasEquiv`: the isomorphism of Banach spaces.

## Main results

* `TauCeti.SectionChartData.chartValueL_changeAtlas_ae`: the chart data of `changeAtlas hC h w` are
  the readings for `C'` of any section of `w`.
* `TauCeti.SectionChartData.exists_norm_changeAtlas_le`: the norms are equivalent.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal

universe u

namespace TauCeti

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
def ReadsFrom : Prop :=
  ∃ (D : Fin C.n → Fin C'.n → Set E) (τ : Fin C.n → Fin C'.n → E → E)
    (L : Fin C.n → Fin C'.n → E → F →L[ℝ] F),
    (∀ i', ∀ᵐ y ∂μ.restrict (C'.image i'), ∃ i, y ∈ D i i') ∧
    (∀ i i' ⦃P : E → Prop⦄, (∀ᵐ z ∂μ.restrict (C.image i), P z) →
      ∀ᵐ y ∂μ.restrict (C'.image i'), y ∈ D i i' → P (τ i i' y)) ∧
    ∀ i i' (s : S), ∀ᵐ y ∂μ.restrict (C'.image i'), y ∈ D i i' →
      C'.coord i' s y = L i i' y (C.coord i s (τ i i' y))

/-- Unfolding `TauCeti.SectionChartData.ReadsFrom`. -/
theorem readsFrom_iff : C.ReadsFrom C' μ ↔
    ∃ (D : Fin C.n → Fin C'.n → Set E) (τ : Fin C.n → Fin C'.n → E → E)
      (L : Fin C.n → Fin C'.n → E → F →L[ℝ] F),
      (∀ i', ∀ᵐ y ∂μ.restrict (C'.image i'), ∃ i, y ∈ D i i') ∧
      (∀ i i' ⦃P : E → Prop⦄, (∀ᵐ z ∂μ.restrict (C.image i), P z) →
        ∀ᵐ y ∂μ.restrict (C'.image i'), y ∈ D i i' → P (τ i i' y)) ∧
      ∀ i i' (s : S), ∀ᵐ y ∂μ.restrict (C'.image i'), y ∈ D i i' →
        C'.coord i' s y = L i i' y (C.coord i s (τ i i' y)) :=
  Iff.rfl

variable {C C' μ} in
/-- **Establishing `TauCeti.SectionChartData.ReadsFrom`** from the sets `D i i'`, the maps
`τ i i'` and the linear maps `L i i'`. -/
theorem ReadsFrom.intro (D : Fin C.n → Fin C'.n → Set E) (τ : Fin C.n → Fin C'.n → E → E)
    (L : Fin C.n → Fin C'.n → E → F →L[ℝ] F)
    (hcov : ∀ i', ∀ᵐ y ∂μ.restrict (C'.image i'), ∃ i, y ∈ D i i')
    (hnull : ∀ i i' ⦃P : E → Prop⦄, (∀ᵐ z ∂μ.restrict (C.image i), P z) →
      ∀ᵐ y ∂μ.restrict (C'.image i'), y ∈ D i i' → P (τ i i' y))
    (hrel : ∀ i i' (s : S), ∀ᵐ y ∂μ.restrict (C'.image i'), y ∈ D i i' →
      C'.coord i' s y = L i i' y (C.coord i s (τ i i' y))) :
    C.ReadsFrom C' μ :=
  ⟨D, τ, L, hcov, hnull, hrel⟩

/-- Chart data read off from themselves, each chart from itself. -/
theorem readsFrom_refl : C.ReadsFrom C μ :=
  .intro (fun i i' ↦ {_y | i = i'}) (fun _ _ ↦ id) (fun _ _ _ ↦ 1)
    (fun i' ↦ ae_of_all _ fun _ ↦ ⟨i', rfl⟩)
    (fun i i' P h ↦ by
      obtain rfl | hii := eq_or_ne i i'
      · filter_upwards [h] with y hy _ using hy
      · exact ae_of_all _ fun _ hy ↦ absurd hy hii)
    fun i i' s ↦ ae_of_all _ fun _ hy ↦ by
      obtain rfl : i = i' := hy
      simp

variable {C C' μ}

/-- Sections whose readings agree almost everywhere in every chart of `C` agree almost everywhere
in every chart of chart data `C'` read off from `C`. -/
theorem ReadsFrom.coord_ae_eq (hC : C.ReadsFrom C' μ) {s t : S}
    (h : ∀ i, C.coord i s =ᵐ[μ.restrict (C.image i)] C.coord i t) (i' : Fin C'.n) :
    C'.coord i' s =ᵐ[μ.restrict (C'.image i')] C'.coord i' t := by
  obtain ⟨D, τ, L, hcov, hnull, hrel⟩ := (readsFrom_iff _ _ _).1 hC
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
def TransfersTo : Prop :=
  ∀ (w : C.sobolevSections μ p k) (s : S),
    (∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s) →
      ∃ w' : C'.sobolevSections μ p k,
        ∀ i', C'.chartValueL μ p k i' w' =ᵐ[μ.restrict (C'.image i')] C'.coord i' s

variable {C C' μ p k}

/-- Unfolding `TauCeti.SectionChartData.TransfersTo`. -/
theorem transfersTo_iff : C.TransfersTo C' μ p k ↔
    ∀ (w : C.sobolevSections μ p k) (s : S),
      (∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s) →
        ∃ w' : C'.sobolevSections μ p k,
          ∀ i', C'.chartValueL μ p k i' w' =ᵐ[μ.restrict (C'.image i')] C'.coord i' s :=
  Iff.rfl

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
    obtain ⟨D, τ, L, hcov, hnull, hrel⟩ := (readsFrom_iff _ _ _).1 hC
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

@[simp]
theorem changeAtlas_refl :
    changeAtlas (C.readsFrom_refl μ) (transfersTo_refl (C := C) (μ := μ) (p := p) (k := k)) =
      ContinuousLinearMap.id ℝ _ :=
  ContinuousLinearMap.ext changeAtlas_refl_apply

theorem changeAtlas_comp {C'' : SectionChartData E F S} [CompleteSpace (C''.sobolevSections μ p k)]
    (hC : C.ReadsFrom C' μ) (hC' : C'.ReadsFrom C'' μ) (hC'' : C.ReadsFrom C'' μ)
    (h : C.TransfersTo C' μ p k) (h' : C'.TransfersTo C'' μ p k) :
    (changeAtlas hC' h').comp (changeAtlas hC h) = changeAtlas hC'' (h.trans h') :=
  ContinuousLinearMap.ext (changeAtlas_changeAtlas hC hC' hC'' h h')

/-- **Independence of the chart data.** If chart data are read off from each other and sections
transfer between them in both directions, their Sobolev spaces of sections are isomorphic Banach
spaces, an element corresponding to the element with the same section. -/
def atlasEquiv (hC : C.ReadsFrom C' μ) (hC' : C'.ReadsFrom C μ) (h : C.TransfersTo C' μ p k)
    (h' : C'.TransfersTo C μ p k) : C.sobolevSections μ p k ≃L[ℝ] C'.sobolevSections μ p k :=
  ContinuousLinearEquiv.ofContinuousLinearMap (changeAtlas hC h) (changeAtlas hC' h')
    (ContinuousLinearMap.ext fun w ↦
      (changeAtlas_changeAtlas hC' hC (C'.readsFrom_refl μ) h' h w).trans
        (changeAtlas_refl_apply w))
    (ContinuousLinearMap.ext fun w ↦
      (changeAtlas_changeAtlas hC hC' (C.readsFrom_refl μ) h h' w).trans
        (changeAtlas_refl_apply w))

@[simp]
theorem toContinuousLinearMap_atlasEquiv (hC : C.ReadsFrom C' μ) (hC' : C'.ReadsFrom C μ)
    (h : C.TransfersTo C' μ p k) (h' : C'.TransfersTo C μ p k) :
    (atlasEquiv hC hC' h h' : C.sobolevSections μ p k →L[ℝ] C'.sobolevSections μ p k) =
      changeAtlas hC h :=
  (rfl)

@[simp]
theorem atlasEquiv_apply (hC : C.ReadsFrom C' μ) (hC' : C'.ReadsFrom C μ)
    (h : C.TransfersTo C' μ p k) (h' : C'.TransfersTo C μ p k) (w : C.sobolevSections μ p k) :
    atlasEquiv hC hC' h h' w = changeAtlas hC h w :=
  (rfl)

theorem atlasEquiv_symm_apply (hC : C.ReadsFrom C' μ) (hC' : C'.ReadsFrom C μ)
    (h : C.TransfersTo C' μ p k) (h' : C'.TransfersTo C μ p k) (w : C'.sobolevSections μ p k) :
    (atlasEquiv hC hC' h h').symm w = changeAtlas hC' h' w :=
  (rfl)

@[simp]
theorem atlasEquiv_symm (hC : C.ReadsFrom C' μ) (hC' : C'.ReadsFrom C μ)
    (h : C.TransfersTo C' μ p k) (h' : C'.TransfersTo C μ p k) :
    (atlasEquiv hC hC' h h').symm = atlasEquiv hC' hC h' h :=
  ContinuousLinearEquiv.ext (funext fun w ↦ atlasEquiv_symm_apply hC hC' h h' w)

@[simp]
theorem atlasEquiv_refl :
    atlasEquiv (C.readsFrom_refl μ) (C.readsFrom_refl μ)
      (transfersTo_refl (C := C) (μ := μ) (p := p) (k := k)) transfersTo_refl =
      ContinuousLinearEquiv.refl ℝ _ :=
  ContinuousLinearEquiv.ext (funext changeAtlas_refl_apply)

theorem atlasEquiv_trans {C'' : SectionChartData E F S}
    [CompleteSpace (C''.sobolevSections μ p k)] (hC₁ : C.ReadsFrom C' μ)
    (hC₁' : C'.ReadsFrom C μ) (hC₂ : C'.ReadsFrom C'' μ) (hC₂' : C''.ReadsFrom C' μ)
    (hC : C.ReadsFrom C'' μ) (hC' : C''.ReadsFrom C μ) (h₁ : C.TransfersTo C' μ p k)
    (h₁' : C'.TransfersTo C μ p k) (h₂ : C'.TransfersTo C'' μ p k)
    (h₂' : C''.TransfersTo C' μ p k) :
    (atlasEquiv hC₁ hC₁' h₁ h₁').trans (atlasEquiv hC₂ hC₂' h₂ h₂') =
      atlasEquiv hC hC' (h₁.trans h₂) (h₂'.trans h₁') :=
  ContinuousLinearEquiv.ext (funext (changeAtlas_changeAtlas hC₁ hC₂ hC h₁ h₂))

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

end TauCeti
