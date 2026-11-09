/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.SectionTopology
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Cone
import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney.Open

/-!
# The chart C∞ topology on metrics as a subspace of the section space

A native smooth metric `g` on a manifold `M` without boundary is a smooth section
`g.toSymmetricSection` of the bundle `Sym²(T*M)` of symmetric bilinear forms on the tangent
spaces. The sections carry the compact derivative topology `ContMDiffSection.frameTopology` of
any covering system of smooth frames, which does not depend on the cover. The metrics carry the
chart C∞ topology `Bundle.ContMDiffRiemannianMetric.chartCInftyTopology` of uniform convergence
on compact chart sets of all coordinate derivatives of the chart Gram matrices.

These agree: the chart C∞ topology is the subspace topology
`Bundle.ContMDiffRiemannianMetric.frameTopology` of the section space
(`Bundle.ContMDiffRiemannianMetric.chartCInftyTopology_eq_frameTopology`). In the
trivialization of `Sym²(T*M)` induced by the chart at `x₀`, the coordinates of
`g.toSymmetricSection` are the chart metric of `g` at `x₀` composed with that chart. Hence the
frame coordinates and the chart metric are obtained from each other by composing with the chart
`TauCeti.extChartAtDiffeomorph` or its inverse, and composition with a fixed smooth map is
continuous for the compact derivative topologies.

Consequently `toSymmetricSection` embeds the metrics into the section space, and on a compact
manifold its image, the metric cone, is open, so that the metrics form an open subspace of the
section space (`Bundle.ContMDiffRiemannianMetric.isOpenEmbedding_toSymmetricSection_chartCInfty`).
In particular every chart C∞ statement about metrics, such as the openness of positive scalar
curvature, is a statement about the subspace topology from the space of smooth sections of
`Sym²(T*M)`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.coe_trivializationAt_toSymmetricSection_snd`: the
  coordinates of the section of a metric in the trivialization at `x₀` are the coordinates of the
  metric in the tangent trivialization at `x₀`.
* `Bundle.ContMDiffRiemannianMetric.chartCInftyTopology_eq_frameTopology`: the chart C∞
  topology is induced by the frame topology of any covering frame system of `Sym²(T*M)`.
* `Bundle.ContMDiffRiemannianMetric.isEmbedding_toSymmetricSection_chartCInfty`: the section of a
  metric is an embedding for these topologies.
* `Bundle.ContMDiffRiemannianMetric.isOpenEmbedding_toSymmetricSection_chartCInfty`: on a compact
  manifold it is an open embedding.

## References

* R. Hamilton, *The inverse function theorem of Nash and Moser*, Bull. Amer. Math. Soc. 7 (1982),
  Part I, Example 1.1.5, for the space of metrics as an open subset of the Fréchet space of smooth
  symmetric sections.
* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, for compact derivative topologies.
-/

open Bundle Set Topology TopologicalSpace TauCeti TauCeti.Manifold
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

public section

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Cache the canonical operator-space instances: searching for the topology on iterated
-- multilinear maps into nested operator spaces otherwise exhausts instance-search heartbeats.
private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- In the trivialization of `Sym²(T*M)` at `x₀`, the section of a metric has the coordinates of
the metric in the tangent trivialization at `x₀`. -/
theorem coe_trivializationAt_toSymmetricSection_snd
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x₀ x : M}
    (hx : x ∈ (chartAt H x₀).source) :
    ((trivializationAt (symmetricBilinearMaps ℝ E ℝ)
        (fun x : M ↦ symmetricBilinearMaps ℝ (TangentSpace I x) ℝ) x₀
        ⟨x, g.toSymmetricSection x⟩).2 : E →L[ℝ] E →L[ℝ] ℝ) =
      g.toNondegenerateMetric.inCoordinates x₀ x := by
  have hx' : x ∈ (trivializationAt E (fun y : M ↦ TangentSpace I y) x₀).baseSet := by
    simpa using hx
  ext v w
  rw [g.toNondegenerateMetric.inCoordinates_apply x₀ hx' v w]
  simp [trivializationAt_symmetricBilinearMaps_apply, Trivialization.symmL_apply _ hx']

/-! ### The chart cover of `Sym²(T*M)` -/

/-- The trivialization of `Sym²(T*M)` at `x₀`. -/
private abbrev symTriv (x₀ : M) :
    Trivialization (symmetricBilinearMaps ℝ E ℝ)
      (π (symmetricBilinearMaps ℝ E ℝ)
        (fun x : M ↦ symmetricBilinearMaps ℝ (TangentSpace I x) ℝ)) :=
  trivializationAt (symmetricBilinearMaps ℝ E ℝ)
    (fun x : M ↦ symmetricBilinearMaps ℝ (TangentSpace I x) ℝ) x₀

private theorem chartSourceOpens_subset_baseSet (x₀ : M) :
    (chartSourceOpens H x₀ : Set M) ⊆ (symTriv (I := I) x₀).baseSet := by
  intro x hx
  simpa using hx

variable [I.Boundaryless]

/-- The chart target, as a subtype of the model space, is its own open-set form. -/
private def chartTargetHomeomorph (x₀ : M) :
    (extChartAt I x₀).target ≃ₜ extChartTargetOpens I x₀ where
  toFun z := ⟨z, z.2⟩
  invFun z := ⟨z, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

omit [IsManifold I ∞ M] in
private theorem coe_chartTargetHomeomorph_apply (x₀ : M) (z : (extChartAt I x₀).target) :
    (chartTargetHomeomorph x₀ z : E) = z :=
  (rfl)

/-- The frame coordinates of the section of a metric in the trivialization at `x₀`. -/
private def symFrameCoordinates
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x₀ : M) :
    C^∞⟮I, chartSourceOpens H x₀; 𝓘(ℝ, symmetricBilinearMaps ℝ E ℝ),
      symmetricBilinearMaps ℝ E ℝ⟯ :=
  (symTriv (I := I) x₀).frameCoordinates (chartSourceOpens_subset_baseSet x₀)
    g.toSymmetricSection

/-- The chart metric at `x₀`, as a smooth map on the chart target with symmetric values. -/
private def symChartMetric
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x₀ : M) :
    C^∞⟮𝓘(ℝ, E), extChartTargetOpens I x₀; 𝓘(ℝ, symmetricBilinearMaps ℝ E ℝ),
      symmetricBilinearMaps ℝ E ℝ⟯ :=
  (symFrameCoordinates g x₀).comp (extChartAtDiffeomorph (I := I) ∞ x₀).symm.toContMDiffMap

private theorem coe_symChartMetric_apply
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x₀ : M)
    (z : extChartTargetOpens I x₀) :
    (symChartMetric g x₀ z : E →L[ℝ] E →L[ℝ] ℝ) = g.toNondegenerateMetric.chartMetric x₀ z := by
  have hz : (extChartAt I x₀).symm z ∈ (chartAt H x₀).source := by
    simpa using (extChartAt I x₀).map_target z.2
  simp only [symChartMetric, symFrameCoordinates, ContMDiffMap.comp_apply,
    Trivialization.frameCoordinates_apply]
  rw [ContMDiffNondegenerateMetric.chartMetric_def, Diffeomorph.coe_coe,
    coe_extChartAtDiffeomorph_symm_apply]
  exact coe_trivializationAt_toSymmetricSection_snd g hz

private theorem symFrameCoordinates_eq_comp
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x₀ : M) :
    symFrameCoordinates g x₀ =
      (symChartMetric g x₀).comp (extChartAtDiffeomorph (I := I) ∞ x₀).toContMDiffMap := by
  refine ContMDiffMap.ext fun p ↦ ?_
  simp only [symChartMetric, ContMDiffMap.comp_apply, Diffeomorph.coe_coe,
    Diffeomorph.symm_apply_apply]

/-! ### Derivatives of the chart metric -/

/-- Inclusion of the multilinear maps with symmetric values into those with bilinear values. -/
private def symInclusion (m : ℕ) :
    C(E [×m]→L[ℝ] symmetricBilinearMaps ℝ E ℝ, E [×m]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) :=
  ⟨(symmetricBilinearMaps ℝ E ℝ).subtypeL.compContinuousMultilinearMap,
    (ContinuousMultilinearMap.isUniformInducing_postcomp _
      isUniformEmbedding_subtype_val.isUniformInducing).isInducing.continuous⟩

@[simp]
private theorem symInclusion_apply (m : ℕ) (q : E [×m]→L[ℝ] symmetricBilinearMaps ℝ E ℝ) :
    symInclusion m q = (symmetricBilinearMaps ℝ E ℝ).subtypeL.compContinuousMultilinearMap q :=
  (rfl)

private theorem isInducing_symInclusion (m : ℕ) : IsInducing (symInclusion (E := E) m) :=
  (ContinuousMultilinearMap.isUniformInducing_postcomp _
    isUniformEmbedding_subtype_val.isUniformInducing).isInducing

/-- The coordinate derivatives of the chart metric are those of its symmetric-valued form. -/
private theorem chartMetricDerivative_eq
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x₀ : M) (m : ℕ) :
    g.chartMetricDerivative x₀ m = ((symInclusion m).comp
      (ContMDiffMap.openIteratedFDerivContinuousMap (extChartTargetOpens I x₀)
        (symChartMetric g x₀) m (by exact_mod_cast le_top))).comp
      (chartTargetHomeomorph (I := I) x₀ :
        C((extChartAt I x₀).target, extChartTargetOpens I x₀)) := by
  ext1 z
  have hT : IsOpen ((extChartTargetOpens I x₀ : Set E)) := (extChartTargetOpens I x₀).isOpen
  have hz : (z : E) ∈ (extChartTargetOpens I x₀ : Set E) := z.2
  refine (chartMetricDerivative_apply g x₀ m z).trans ?_
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_ofClass, coe_chartTargetHomeomorph_apply,
    ContMDiffMap.openIteratedFDerivContinuousMap_apply, symInclusion_apply]
  rw [← ContinuousLinearMap.iteratedFDerivWithin_comp_left _
    ((ContMDiffMap.contDiffOn_extend _ _ _).contDiffWithinAt hz) hT.uniqueDiffOn hz
    (by exact_mod_cast le_top), ← iteratedFDerivWithin_of_isOpen m hT hz]
  refine iteratedFDerivWithin_congr (fun y hy ↦ ?_) hz m
  simp only [Function.comp_apply]
  rw [Subtype.val_injective.extend_apply (symChartMetric g x₀) (fun _ ↦ 0) ⟨y, hy⟩]
  exact (coe_symChartMetric_apply g x₀ ⟨y, hy⟩).symm

/-- The symmetric-valued chart metric at `x₀` depends continuously on the metric in the chart C∞
topology, for the weak Whitney topology on maps from the chart target. -/
private theorem continuous_symChartMetric (x₀ : M) :
    letI := chartCInftyTopology (I := I) (M := M)
    Continuous (fun g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      symChartMetric g x₀) := by
  let _ := chartCInftyTopology (I := I) (M := M)
  apply (ContMDiffMap.isInducing_openWeakWhitneyJet _).continuous_iff.mpr
  refine continuous_pi fun m ↦ ?_
  apply ((ContinuousMap.isInducing_postcomp _
    (isInducing_symInclusion (E := E) m)).continuous_iff).mpr
  refine ((ContinuousMap.continuous_precomp ((chartTargetHomeomorph (I := I) x₀).symm :
    C(extChartTargetOpens I x₀, (extChartAt I x₀).target))).comp
      (continuous_chartMetricDerivative ⊤ x₀ le_top)).congr fun g ↦ ?_
  -- The two descriptions of the chart target are identified by mutually inverse identity maps.
  ext1 z
  dsimp only [Function.comp_apply]
  rw [chartMetricDerivative_eq, ContMDiffMap.openWeakWhitneyJet_apply]
  rfl

/-! ### Comparison of the topologies -/

omit [I.Boundaryless] in
private theorem frameTopology_eq_induced {ι : Type*}
    (e : ι → Trivialization (symmetricBilinearMaps ℝ E ℝ)
      (π (symmetricBilinearMaps ℝ E ℝ)
        (fun x : M ↦ symmetricBilinearMaps ℝ (TangentSpace I x) ℝ)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet) :
    frameTopology I ∞ e U hU =
      .induced toSymmetricSection (ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := frameTopology I ∞ e U hU
  exact (isEmbedding_toSymmetricSection_frameTopology (IB := I) (n := ∞) e U hU).eq_induced

/-- The chart C∞ topology on smooth metrics is the subspace topology `frameTopology` from the
compact derivative topology on smooth sections of `Sym²(T*M)`, for any covering system of smooth
frames. -/
theorem chartCInftyTopology_eq_frameTopology [LocallyCompactSpace E]
    {ι : Type*}
    (e : ι → Trivialization (symmetricBilinearMaps ℝ E ℝ)
      (π (symmetricBilinearMaps ℝ E ℝ)
        (fun x : M ↦ symmetricBilinearMaps ℝ (TangentSpace I x) ℝ)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    chartCInftyTopology (I := I) (M := M) = frameTopology I ∞ e U hU := by
  rw [frameTopology_eq_induced, ContMDiffSection.frameTopology_eq_of_covers e U hU hcover
    (symTriv (I := I) (M := M)) (chartSourceOpens H) chartSourceOpens_subset_baseSet
    fun x ↦ ⟨x, mem_chart_source H x⟩]
  apply le_antisymm
  · -- In the chart C∞ topology, each frame coordinate is the chart metric composed with a chart.
    rw [← continuous_iff_le_induced]
    let _ := chartCInftyTopology (I := I) (M := M)
    let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) (symTriv (I := I) (M := M))
      (chartSourceOpens H) chartSourceOpens_subset_baseSet
    apply (ContMDiffSection.continuous_frameTopology_iff_frameCoordinates (I := I) (n := ∞)
      (symTriv (I := I) (M := M)) (chartSourceOpens H) chartSourceOpens_subset_baseSet).mpr
    intro x₀
    refine (ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
      ((continuous_symChartMetric x₀).prodMk
        (continuous_const (y := (extChartAtDiffeomorph (I := I) ∞ x₀).toContMDiffMap)))).congr
          fun g ↦ ?_
    exact (symFrameCoordinates_eq_comp g x₀).symm
  · -- Conversely, each chart metric is a frame coordinate composed with an inverse chart.
    rw [← continuous_id_iff_le]
    let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) (symTriv (I := I) (M := M))
      (chartSourceOpens H) chartSourceOpens_subset_baseSet
    let _ : TopologicalSpace (ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :=
      .induced toSymmetricSection inferInstance
    apply (continuous_chartCk_iff_continuous_chartMetricDerivative ⊤).mpr
    intro x₀ m _
    have hframe : Continuous (fun g : ContMDiffRiemannianMetric I ∞ E
        (fun x : M ↦ TangentSpace I x) ↦ symFrameCoordinates g x₀) :=
      (ContMDiffSection.continuous_frameCoordinates (I := I) (n := ∞)
        (symTriv (I := I) (M := M)) (chartSourceOpens H) chartSourceOpens_subset_baseSet x₀).comp
          continuous_induced_dom
    have hchart : Continuous (fun g : ContMDiffRiemannianMetric I ∞ E
        (fun x : M ↦ TangentSpace I x) ↦ symChartMetric g x₀) :=
      ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
        (hframe.prodMk
          (continuous_const (y := (extChartAtDiffeomorph (I := I) ∞ x₀).symm.toContMDiffMap)))
    have hjet : Continuous (fun g : ContMDiffRiemannianMetric I ∞ E
        (fun x : M ↦ TangentSpace I x) ↦
        ContMDiffMap.openIteratedFDerivContinuousMap (extChartTargetOpens I x₀)
          (symChartMetric g x₀) m (by exact_mod_cast le_top)) :=
      (continuous_apply (⟨m, by exact_mod_cast le_top⟩ : {m : ℕ // (m : ℕ∞ω) ≤ ∞})).comp
        ((ContMDiffMap.continuous_openWeakWhitneyJet _).comp hchart) |>.congr fun g ↦
          ContMDiffMap.openWeakWhitneyJet_apply _ _ _
    have hincl := (ContinuousMap.continuous_postcomp (symInclusion (E := E) m)).comp hjet
    refine ((ContinuousMap.continuous_precomp (chartTargetHomeomorph (I := I) x₀ :
      C((extChartAt I x₀).target, extChartTargetOpens I x₀))).comp hincl).congr fun g ↦ ?_
    exact (chartMetricDerivative_eq g x₀ m).symm

/-- The section of a metric embeds the smooth metrics with the chart C∞ topology into the smooth
sections of `Sym²(T*M)` with the compact derivative topology of any covering frame system. -/
theorem isEmbedding_toSymmetricSection_chartCInfty [LocallyCompactSpace E]
    {ι : Type*}
    (e : ι → Trivialization (symmetricBilinearMaps ℝ E ℝ)
      (π (symmetricBilinearMaps ℝ E ℝ)
        (fun x : M ↦ symmetricBilinearMaps ℝ (TangentSpace I x) ℝ)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := chartCInftyTopology (I := I) (M := M)
    letI := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
    IsEmbedding (toSymmetricSection (IB := I) (n := ∞) (F := E)
      (V := fun x : M ↦ TangentSpace I x)) := by
  let _ := chartCInftyTopology (I := I) (M := M)
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  exact ⟨⟨(chartCInftyTopology_eq_frameTopology e U hU hcover).trans
    (frameTopology_eq_induced e U hU)⟩, toSymmetricSection_injective⟩

/-- On a compact manifold the smooth metrics with the chart C∞ topology form an open subspace of
the smooth sections of `Sym²(T*M)`, with the compact derivative topology of any covering frame
system. -/
theorem isOpenEmbedding_toSymmetricSection_chartCInfty [FiniteDimensional ℝ E] [CompactSpace M]
    {ι : Type*}
    (e : ι → Trivialization (symmetricBilinearMaps ℝ E ℝ)
      (π (symmetricBilinearMaps ℝ E ℝ)
        (fun x : M ↦ symmetricBilinearMaps ℝ (TangentSpace I x) ℝ)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    letI := chartCInftyTopology (I := I) (M := M)
    letI := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
    IsOpenEmbedding (toSymmetricSection (IB := I) (n := ∞) (F := E)
      (V := fun x : M ↦ TangentSpace I x)) := by
  let _ := chartCInftyTopology (I := I) (M := M)
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  refine ⟨isEmbedding_toSymmetricSection_chartCInfty e U hU hcover, ?_⟩
  rw [range_toSymmetricSection]
  exact isOpen_positiveDefiniteSymmetricSections_frameTopology e U hU hcover

end Bundle.ContMDiffRiemannianMetric
