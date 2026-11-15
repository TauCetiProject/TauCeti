/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.FiniteOrderTopology
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Cone
import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney.Open

/-!
# Chart and section topologies on smooth metrics

A native smooth metric `g` on a manifold without boundary is a smooth section
`g.toSymmetricSection` of `Sym²(T*M)`. There are two descriptions of its Cᵏ topology:
compact convergence of chart Gram matrices and their derivatives through order `k`, and the
subspace topology obtained by regarding its symmetric tensor as a Cᵏ section with the compact
derivative topology of any covering system of smooth frames.

These agree for every finite `k`, and for `k = ∞`
(`Bundle.ContMDiffRiemannianMetric.chartCkTopology_eq_induced_ofLE`). In finite order this
identifies `chartCkTopology` with `frameCkTopology`. Thus, in particular, C² continuity and
openness statements about scalar curvature in chart coordinates apply to the finite-order
section topology on the same smooth-metric carrier. The comparison needs no compactness or
countability assumption on the manifold.

In the trivialization of `Sym²(T*M)` induced by a chart, the section coordinates are the
chart metric composed with that chart. Composition by the chart and its inverse is continuous
in each compact derivative topology, giving the comparison without choosing a basis.

In smooth regularity, `toSymmetricSection` embeds the metrics into smooth symmetric tensor
sections. On a compact manifold its image, the metric cone, is open, giving an open embedding.
In finite regularity the comparison is only with the subspace of smooth metrics inside Cᵏ
metrics; it does not assert that smooth sections are open among Cᵏ sections.

## Main results

* `Bundle.ContMDiffRiemannianMetric.chartCkTopology_eq_induced_ofLE`: the chart Cᵏ topology is
  induced from the section topology on Cᵏ metrics, for `k : ℕ∞`.
* `Bundle.ContMDiffRiemannianMetric.chartCkTopology_eq_frameCkTopology`: the finite-order chart
  and section topologies on the fixed smooth-metric carrier coincide.
* `Bundle.ContMDiffRiemannianMetric.chartC2Topology_eq_frameCkTopology`: the C² comparison
  directly in terms of the chart C² topology.
* `Bundle.ContMDiffRiemannianMetric.chartCInftyTopology_eq_frameTopology`: the smooth chart
  and section topologies coincide without forgetting regularity.
* `Bundle.ContMDiffRiemannianMetric.isEmbedding_toSymmetricSection_chartCInfty`: the smooth
  section map is an embedding.
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
  toFun z := ⟨z, mem_extChartTargetOpens.mpr z.2⟩
  invFun z := ⟨z, mem_extChartTargetOpens.mp z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

omit [IsManifold I ∞ M] in
private theorem coe_chartTargetHomeomorph_apply (x₀ : M) (z : (extChartAt I x₀).target) :
    (chartTargetHomeomorph x₀ z : E) = z :=
  (rfl)

/-- The frame coordinates of the section of a metric in the trivialization at `x₀`. -/
private def symFrameCoordinates (k : ℕ∞)
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x₀ : M) :
    C^((k : ℕ∞ω))⟮I, chartSourceOpens H x₀; 𝓘(ℝ, symmetricBilinearMaps ℝ E ℝ),
      symmetricBilinearMaps ℝ E ℝ⟯ :=
  (symTriv (I := I) x₀).frameCoordinates (chartSourceOpens_subset_baseSet x₀)
    (g.ofLE (m := (k : ℕ∞ω)) (by exact_mod_cast le_top)).toSymmetricSection

/-- The chart metric at `x₀`, as a Cᵏ map on the chart target with symmetric values. -/
private def symChartMetric (k : ℕ∞)
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x₀ : M) :
    C^((k : ℕ∞ω))⟮𝓘(ℝ, E), extChartTargetOpens I x₀; 𝓘(ℝ, symmetricBilinearMaps ℝ E ℝ),
      symmetricBilinearMaps ℝ E ℝ⟯ :=
  (symFrameCoordinates k g x₀).comp
    (extChartAtDiffeomorph (I := I) (k : ℕ∞ω) x₀).symm.toContMDiffMap

private theorem coe_symChartMetric_apply (k : ℕ∞)
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x₀ : M)
    (z : extChartTargetOpens I x₀) :
    (symChartMetric k g x₀ z : E →L[ℝ] E →L[ℝ] ℝ) = g.toNondegenerateMetric.chartMetric x₀ z := by
  have hz : (extChartAt I x₀).symm z ∈ (chartAt H x₀).source := by
    simpa using (extChartAt I x₀).map_target (mem_extChartTargetOpens.mp z.2)
  simp only [symChartMetric, symFrameCoordinates, ContMDiffMap.comp_apply,
    Trivialization.frameCoordinates_apply]
  rw [ContMDiffNondegenerateMetric.chartMetric_def, Diffeomorph.coe_coe,
    coe_extChartAtDiffeomorph_symm_apply]
  rw [toSymmetricSection_ofLE_apply]
  exact coe_trivializationAt_toSymmetricSection_snd g hz

private theorem symFrameCoordinates_eq_comp (k : ℕ∞)
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x₀ : M) :
    symFrameCoordinates k g x₀ =
      (symChartMetric k g x₀).comp
        (extChartAtDiffeomorph (I := I) (k : ℕ∞ω) x₀).toContMDiffMap := by
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
private theorem chartMetricDerivative_eq (k : ℕ∞)
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x₀ : M)
    (m : ℕ) (hm : (m : ℕ∞) ≤ k) :
    g.chartMetricDerivative x₀ m = ((symInclusion m).comp
      (ContMDiffMap.openIteratedFDerivContinuousMap (extChartTargetOpens I x₀)
        (symChartMetric k g x₀) m (by exact_mod_cast hm))).comp
      (chartTargetHomeomorph (I := I) x₀ :
        C((extChartAt I x₀).target, extChartTargetOpens I x₀)) := by
  ext1 z
  have hT : IsOpen ((extChartTargetOpens I x₀ : Set E)) := (extChartTargetOpens I x₀).isOpen
  have hz : (z : E) ∈ (extChartTargetOpens I x₀ : Set E) := mem_extChartTargetOpens.mpr z.2
  refine (chartMetricDerivative_apply g x₀ m z).trans ?_
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_ofClass, coe_chartTargetHomeomorph_apply,
    ContMDiffMap.openIteratedFDerivContinuousMap_apply, symInclusion_apply]
  rw [← ContinuousLinearMap.iteratedFDerivWithin_comp_left _
    ((ContMDiffMap.contMDiffOn_extend _ _ _).contDiffOn.contDiffWithinAt hz) hT.uniqueDiffOn hz
    (by exact_mod_cast hm), ← iteratedFDerivWithin_of_isOpen m hT hz]
  refine iteratedFDerivWithin_congr (fun y hy ↦ ?_) hz m
  simp only [Function.comp_apply]
  rw [Subtype.val_injective.extend_apply (symChartMetric k g x₀) (fun _ ↦ 0) ⟨y, hy⟩]
  exact (coe_symChartMetric_apply k g x₀ ⟨y, hy⟩).symm

/-- The symmetric-valued chart metric depends continuously on the metric in the chart Cᵏ
topology, for the Cᵏ weak Whitney topology on maps from the chart target. -/
private theorem continuous_symChartMetric (k : ℕ∞) (x₀ : M) :
    letI := chartCkTopology (I := I) (M := M) k
    Continuous (fun g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      symChartMetric k g x₀) := by
  let _ := chartCkTopology (I := I) (M := M) k
  apply (ContMDiffMap.isInducing_openWeakWhitneyJet _).continuous_iff.mpr
  refine continuous_pi fun m ↦ ?_
  apply ((ContinuousMap.isInducing_postcomp _
    (isInducing_symInclusion (E := E) m.1)).continuous_iff).mpr
  refine ((ContinuousMap.continuous_precomp ((chartTargetHomeomorph (I := I) x₀).symm :
    C(extChartTargetOpens I x₀, (extChartAt I x₀).target))).comp
      (continuous_chartMetricDerivative k x₀ (by exact_mod_cast m.2))).congr fun g ↦ ?_
  -- The two descriptions of the chart target are identified by mutually inverse identity maps.
  ext1 z
  dsimp only [Function.comp_apply]
  rw [chartMetricDerivative_eq k _ _ _ (by exact_mod_cast m.2),
    ContMDiffMap.openWeakWhitneyJet_apply]
  rfl

/-! ### Comparison of the topologies -/

omit [I.Boundaryless] in
private theorem frameTopology_eq_induced (n : ℕ∞) {ι : Type*}
    (e : ι → Trivialization (symmetricBilinearMaps ℝ E ℝ)
      (π (symmetricBilinearMaps ℝ E ℝ)
        (fun x : M ↦ symmetricBilinearMaps ℝ (TangentSpace I x) ℝ)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet) :
    frameTopology I n e U hU =
      .induced toSymmetricSection (ContMDiffSection.frameTopology (I := I) (n := n) e U hU) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := n) e U hU
  let _ := frameTopology I n e U hU
  exact (isEmbedding_toSymmetricSection_frameTopology (IB := I) (n := n) e U hU).eq_induced

/-- The chart Cᵏ topology on smooth metrics is induced by forgetting regularity and using the
section topology on Cᵏ metrics, for every finite order and for smooth regularity. -/
theorem chartCkTopology_eq_induced_ofLE [LocallyCompactSpace E] (k : ℕ∞)
    {ι : Type*}
    (e : ι → Trivialization (symmetricBilinearMaps ℝ E ℝ)
      (π (symmetricBilinearMaps ℝ E ℝ)
        (fun x : M ↦ symmetricBilinearMaps ℝ (TangentSpace I x) ℝ)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    chartCkTopology (I := I) (M := M) k =
      .induced (fun g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
        g.ofLE (m := (k : ℕ∞ω)) (by exact_mod_cast le_top)) (frameTopology I k e U hU) := by
  rw [frameTopology_eq_induced, induced_compose,
    ContMDiffSection.frameTopology_eq_of_covers e U hU hcover
    (symTriv (I := I) (M := M)) (chartSourceOpens H) chartSourceOpens_subset_baseSet
    fun x ↦ ⟨x, mem_chartSourceOpens.mpr (mem_chart_source H x)⟩]
  apply le_antisymm
  · -- Frame coordinates are chart metrics composed with charts; composition is Cᵏ-continuous.
    rw [← continuous_iff_le_induced]
    let _ := chartCkTopology (I := I) (M := M) k
    let _ := ContMDiffSection.frameTopology (I := I) (n := k) (symTriv (I := I) (M := M))
      (chartSourceOpens H) chartSourceOpens_subset_baseSet
    apply (ContMDiffSection.continuous_frameTopology_iff_frameCoordinates (I := I) (n := k)
      (symTriv (I := I) (M := M)) (chartSourceOpens H) chartSourceOpens_subset_baseSet).mpr
    intro x₀
    refine (ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
      ((continuous_symChartMetric k x₀).prodMk
        (continuous_const (y := (extChartAtDiffeomorph (I := I) k x₀).toContMDiffMap)))).congr
          fun g ↦ ?_
    exact (symFrameCoordinates_eq_comp k g x₀).symm
  · -- Conversely, each chart metric is a frame coordinate composed with an inverse chart.
    rw [← continuous_id_iff_le]
    let _ := ContMDiffSection.frameTopology (I := I) (n := k) (symTriv (I := I) (M := M))
      (chartSourceOpens H) chartSourceOpens_subset_baseSet
    let _ : TopologicalSpace (ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :=
      .induced (fun g ↦ (g.ofLE (m := (k : ℕ∞ω))
        (by exact_mod_cast le_top)).toSymmetricSection) inferInstance
    apply (continuous_chartCk_iff_continuous_chartMetricDerivative k).mpr
    intro x₀ m hm
    have hframe : Continuous (fun g : ContMDiffRiemannianMetric I ∞ E
        (fun x : M ↦ TangentSpace I x) ↦ symFrameCoordinates k g x₀) :=
      (ContMDiffSection.continuous_frameCoordinates (I := I) (n := k)
        (symTriv (I := I) (M := M)) (chartSourceOpens H) chartSourceOpens_subset_baseSet x₀).comp
          continuous_induced_dom
    have hchart : Continuous (fun g : ContMDiffRiemannianMetric I ∞ E
        (fun x : M ↦ TangentSpace I x) ↦ symChartMetric k g x₀) :=
      ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
        (hframe.prodMk
          (continuous_const (y := (extChartAtDiffeomorph (I := I) k x₀).symm.toContMDiffMap)))
    have hjet : Continuous (fun g : ContMDiffRiemannianMetric I ∞ E
        (fun x : M ↦ TangentSpace I x) ↦
        ContMDiffMap.openIteratedFDerivContinuousMap (extChartTargetOpens I x₀)
          (symChartMetric k g x₀) m (by exact_mod_cast hm)) :=
      (continuous_apply (⟨m, by exact_mod_cast hm⟩ : {m : ℕ // (m : ℕ∞ω) ≤ k})).comp
        ((ContMDiffMap.continuous_openWeakWhitneyJet _).comp hchart) |>.congr fun g ↦
          ContMDiffMap.openWeakWhitneyJet_apply _ _ _
    have hincl := (ContinuousMap.continuous_postcomp (symInclusion (E := E) m)).comp hjet
    refine ((ContinuousMap.continuous_precomp (chartTargetHomeomorph (I := I) x₀ :
      C((extChartAt I x₀).target, extChartTargetOpens I x₀))).comp hincl).congr fun g ↦ ?_
    exact (chartMetricDerivative_eq k g x₀ m hm).symm

/-- The chart and section definitions of the finite-order topology on smooth metrics agree.
In particular the chart C² topology is the topology induced from C² symmetric tensor sections. -/
theorem chartCkTopology_eq_frameCkTopology [LocallyCompactSpace E] (k : ℕ)
    {ι : Type*}
    (e : ι → Trivialization (symmetricBilinearMaps ℝ E ℝ)
      (π (symmetricBilinearMaps ℝ E ℝ)
        (fun x : M ↦ symmetricBilinearMaps ℝ (TangentSpace I x) ℝ)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    chartCkTopology (I := I) (M := M) k = frameCkTopology I e U hU k := by
  rw [frameCkTopology_def]
  exact chartCkTopology_eq_induced_ofLE k e U hU hcover

/-- The chart C² topology is the finite-order section topology of order two on smooth metrics. -/
theorem chartC2Topology_eq_frameCkTopology [LocallyCompactSpace E]
    {ι : Type*}
    (e : ι → Trivialization (symmetricBilinearMaps ℝ E ℝ)
      (π (symmetricBilinearMaps ℝ E ℝ)
        (fun x : M ↦ symmetricBilinearMaps ℝ (TangentSpace I x) ℝ)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    chartC2Topology (I := I) (M := M) = frameCkTopology I e U hU 2 := by
  simpa only [chartC2Topology, Nat.cast_ofNat] using
    chartCkTopology_eq_frameCkTopology (I := I) 2 e U hU hcover

/-- The chart C∞ topology agrees with the section topology on smooth metrics for any covering
system of smooth frames. No regularity-forgetting map is needed at smooth order. -/
theorem chartCInftyTopology_eq_frameTopology [LocallyCompactSpace E]
    {ι : Type*}
    (e : ι → Trivialization (symmetricBilinearMaps ℝ E ℝ)
      (π (symmetricBilinearMaps ℝ E ℝ)
        (fun x : M ↦ symmetricBilinearMaps ℝ (TangentSpace I x) ℝ)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    chartCInftyTopology (I := I) (M := M) = frameTopology I ∞ e U hU := by
  have hforget : (fun g : ContMDiffRiemannianMetric I ∞ E
      (fun x : M ↦ TangentSpace I x) ↦ g.ofLE (m := ∞) (by simp)) = id :=
    funext fun g ↦ ofLE_refl g _
  simpa only [hforget, induced_id] using
    chartCkTopology_eq_induced_ofLE (I := I) ⊤ e U hU hcover

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
    (frameTopology_eq_induced ⊤ e U hU)⟩, toSymmetricSection_injective⟩

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
