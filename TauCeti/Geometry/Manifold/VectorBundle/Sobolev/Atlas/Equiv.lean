/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart
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

The map is well defined because chart transitions between the two atlases carry null sets to
null sets: a property of the points of `M` holding almost everywhere in every chart of `A` holds
almost everywhere in every chart of `A'`
(`TauCeti.FiniteBundleAtlas.ae_restrict_image_symm_of_ae`), so two sections whose readings agree
almost everywhere in the charts of `A` agree almost everywhere in the charts of `A'`
(`TauCeti.FiniteBundleAtlas.coord_ae_eq_of_coord_ae_eq`); both are proved in
`TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Measure`.
Continuity follows from the closed graph theorem: both spaces are complete, and if `w m → w` and
`changeAtlas w m → v`, then along a subsequence the chart data converge almost everywhere, and
on the overlap of a chart of `A` and a chart of `A'` the readings are related by the coordinate
changes of the bundle, which are continuous, so the chart data of `v` are the readings in `A'` of
the section of `w`.

For surfaces, `M` modelled on `ℂ` with the Lebesgue measure, and a `Cⁿ` bundle, `n ≠ 0`, the
transfer property holds at every order `k ≤ n`
(`TauCeti.SobolevSection.transfersTo`), by the localization of Sobolev sections in arbitrary charts
and trivializations of `TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart`. For a smooth
(`C^∞`) bundle over a smooth Hausdorff manifold modelled on any finite-dimensional real inner
product space, the transfer property holds between any two finite bundle atlases, for every order
`k` and every `1 ≤ p ≤ ∞` (`TauCeti.SobolevSection.transfersTo_of_contMDiffVectorBundle`, in
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Atlas.Transfer`).

## Main definitions

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
that are those of an element of `W^{k,p}(V)` for `A'`. For `Cⁿ` bundles over surfaces this holds
at orders `k ≤ n` (`TauCeti.SobolevSection.transfersTo`). For smooth bundles over smooth Hausdorff
manifolds in every dimension it holds at every order and every `1 ≤ p ≤ ∞`
(`TauCeti.SobolevSection.transfersTo_of_contMDiffVectorBundle`). -/
def TransfersTo : Prop :=
  ∀ (w : SobolevSection A μ p k) (s : ∀ x, V x),
    (∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) →
      ∃ w' : SobolevSection A' μ p k,
        ∀ i', A'.sectionChartData.chartValueL μ p k i' w' =ᵐ[μ.restrict (A'.image i')]
          A'.coord i' s

variable {A A' μ p k}

/-- Unfolding `TauCeti.SobolevSection.TransfersTo`, for establishing and using the transfer
property outside this file. -/
theorem transfersTo_iff : TransfersTo A A' μ p k ↔
    ∀ (w : SobolevSection A μ p k) (s : ∀ x, V x),
      (∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) →
        ∃ w' : SobolevSection A' μ p k,
          ∀ i', A'.sectionChartData.chartValueL μ p k i' w' =ᵐ[μ.restrict (A'.image i')]
            A'.coord i' s :=
  Iff.rfl

theorem transfersTo_refl : TransfersTo A A μ p k :=
  fun w _ hs ↦ ⟨w, hs⟩

theorem TransfersTo.trans {A'' : FiniteBundleAtlas E M F V} (h : TransfersTo A A' μ p k)
    (h' : TransfersTo A' A'' μ p k) : TransfersTo A A'' μ p k := fun w s hs ↦
  let ⟨w', hw'⟩ := h w s hs
  h' w' s hw'

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
    exact eq_of_ae_eq_coord
      (chartValueL_changeAtlasAux_ae h fun i ↦ chartValueL_add_ae_coord (hs i) (ht i))
      fun i' ↦ chartValueL_add_ae_coord (chartValueL_changeAtlasAux_ae h hs i')
        (chartValueL_changeAtlasAux_ae h ht i')
  map_smul' c w := by
    obtain ⟨s, hs⟩ := exists_ae_eq_coord w
    exact eq_of_ae_eq_coord
      (chartValueL_changeAtlasAux_ae h fun i ↦ chartValueL_smul_ae_coord c (hs i))
      fun i' ↦ chartValueL_smul_ae_coord c (chartValueL_changeAtlasAux_ae h hs i')

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
      ((continuous_subtypeVal.tendsto w).comp hu)
  have hc' : Tendsto (fun m ↦ A'.sectionChartData.chartValueL μ p k i' (changeAtlasₗ h (u m)))
      atTop (𝓝 (A'.sectionChartData.chartValueL μ p k i' v)) :=
    ((A'.sectionChartData.chartValueL μ p k i').continuous.tendsto _).comp
      ((continuous_subtypeVal.tendsto v).comp hv)
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
    changeAtlas (transfersTo_refl (A := A) (μ := μ) (p := p) (k := k)) w = w := by
  obtain ⟨s, hs⟩ := exists_ae_eq_coord w
  exact changeAtlas_eq_of_ae_eq_coord _ hs hs

@[simp]
theorem changeAtlas_refl :
    changeAtlas (transfersTo_refl (A := A) (μ := μ) (p := p) (k := k)) =
      ContinuousLinearMap.id ℝ _ :=
  ContinuousLinearMap.ext changeAtlas_refl_apply

@[simp]
theorem changeAtlas_changeAtlas {A'' : FiniteBundleAtlas E M F V} (h : TransfersTo A A' μ p k)
    (h' : TransfersTo A' A'' μ p k) (w : SobolevSection A μ p k) :
    changeAtlas h' (changeAtlas h w) = changeAtlas (h.trans h') w := by
  obtain ⟨s, hs⟩ := exists_ae_eq_coord w
  exact (changeAtlas_eq_of_ae_eq_coord h' (chartValueL_changeAtlas_ae h hs)
    (chartValueL_changeAtlas_ae (h.trans h') hs))

@[simp]
theorem changeAtlas_comp {A'' : FiniteBundleAtlas E M F V} (h : TransfersTo A A' μ p k)
    (h' : TransfersTo A' A'' μ p k) :
    (changeAtlas h').comp (changeAtlas h) = changeAtlas (h.trans h') :=
  ContinuousLinearMap.ext (changeAtlas_changeAtlas h h')

/-- The change of atlas is injective: two sections with the same readings almost everywhere in the
charts of `A'` have the same readings almost everywhere in the charts of `A`. -/
theorem changeAtlas_injective (h : TransfersTo A A' μ p k) :
    Function.Injective (changeAtlas h) := by
  intro w v hwv
  obtain ⟨s, hs⟩ := exists_ae_eq_coord w
  obtain ⟨t, ht⟩ := exists_ae_eq_coord v
  have hst := A'.coord_ae_eq_of_coord_ae_eq A fun i' ↦
    (chartValueL_changeAtlas_ae h hs i').symm.trans (hwv ▸ chartValueL_changeAtlas_ae h ht i')
  exact eq_of_ae_eq_coord hs fun i ↦ (ht i).trans (hst i).symm

/-- The change of atlas commutes with forgetting the highest derivative. -/
theorem lowerOrderL_changeAtlas (h : TransfersTo A A' μ p (k + 1)) (h₀ : TransfersTo A A' μ p k)
    (w : SobolevSection A μ p (k + 1)) :
    A'.sectionChartData.lowerOrderL μ p k (changeAtlas h w) =
      changeAtlas h₀ (A.sectionChartData.lowerOrderL μ p k w) := by
  obtain ⟨s, hs⟩ := exists_ae_eq_coord w
  refine eq_of_ae_eq_coord (s := s) (fun i' ↦ ?_) (chartValueL_changeAtlas_ae h₀ fun i ↦ ?_)
  · rw [SectionChartData.chartValueL_coe_lowerOrderL]
    exact chartValueL_changeAtlas_ae h hs i'
  · rw [SectionChartData.chartValueL_coe_lowerOrderL]
    exact hs i

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
      ‖changeAtlas h w‖ ≤ C * ‖w‖ ∧ ‖w‖ ≤ C * ‖changeAtlas h w‖ := by
  set T := changeAtlas h
  set S := changeAtlas h'
  refine ⟨max 1 (max ‖T‖ ‖S‖), lt_max_of_lt_left one_pos, fun w ↦ ⟨(T.le_opNorm w).trans
    (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) (norm_nonneg w)), ?_⟩⟩
  calc ‖w‖ = ‖S (T w)‖ := by rw [(changeAtlas_changeAtlas _ _ w).trans (changeAtlas_refl_apply w)]
    _ ≤ ‖S‖ * ‖T w‖ := S.le_opNorm _
    _ ≤ max 1 (max ‖T‖ ‖S‖) * ‖T w‖ :=
      mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) (norm_nonneg _)

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
    (A A' : FiniteBundleAtlas ℂ M F V) : TransfersTo A A' volume p k := fun w s hs ↦
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
