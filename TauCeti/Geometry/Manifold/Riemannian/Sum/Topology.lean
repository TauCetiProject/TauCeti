/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sum.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Disjoint unions of continuous families of metrics

The chart Cᵏ topology on smooth metrics respects disjoint unions: a family of disjoint-union
metrics is continuous exactly when both families on the summands are continuous. This holds
for every derivative order, including the chart C² and C∞ topologies, and requires no
compactness of either manifold or of the parameter space.

The coordinate metric in a chart centred in a summand is precisely the coordinate metric of
that summand. Its derivatives therefore agree with those of the summand, without a change of
coordinates or a derivative estimate. This is useful for assembling families on disconnected
manifolds, for example metrics on the boundary components of a bordism.

The topology and its family criterion are those of
`Bundle.ContMDiffRiemannianMetric.chartCkTopology` and `continuous_chartCk_iff`.
-/

public section

noncomputable section

open Bundle Set Filter Topology
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-- In a chart centred in the left summand, the disjoint-union metric has the same coordinate
bilinear form as the left metric. -/
theorem chartMetric_sumTangentSpace_inl
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ContMDiffRiemannianMetric I ∞ E (fun x : N ↦ TangentSpace I x))
    (x : M) {z : E} (hz : z ∈ (extChartAt I x).target) :
    (g.sumTangentSpace h).toNondegenerateMetric.chartMetric (Sum.inl x) z =
      g.toNondegenerateMetric.chartMetric x z := by
  have hz' : z ∈ (extChartAt I (Sum.inl x : M ⊕ N)).target := by
    simpa only [TauCeti.Manifold.extChartAt_target_sumInl] using hz
  have hy : (extChartAt I x).symm z ∈ (chartAt H x).source := by
    simpa using (extChartAt I x).map_target hz
  ext v w
  rw [(g.sumTangentSpace h).toNondegenerateMetric.chartMetric_apply hz',
    g.toNondegenerateMetric.chartMetric_apply hz, TauCeti.Manifold.extChartAt_symm_sumInl]
  simp only [toNondegenerateMetric_apply]
  have hbase : (extChartAt I x).symm z ∈
      (trivializationAt E (TangentSpace I : M → Type _) x).baseSet := by simpa using hy
  have hbase' : Sum.inl ((extChartAt I x).symm z) ∈
      (trivializationAt E (TangentSpace I : M ⊕ N → Type _) (Sum.inl x)).baseSet := by
    simpa [ChartedSpace.sum_chartAt_inl] using hy
  simp only [← Trivialization.symmL_apply (R := ℝ) _ hbase',
    ← Trivialization.symmL_apply (R := ℝ) _ hbase,
    TauCeti.Manifold.symmL_trivializationAt_sumInl hy]
  exact sumTangentSpace_inner_inl g h _ _ _

/-- In a chart centred in the right summand, the disjoint-union metric has the same coordinate
bilinear form as the right metric. -/
theorem chartMetric_sumTangentSpace_inr
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ContMDiffRiemannianMetric I ∞ E (fun x : N ↦ TangentSpace I x))
    (x : N) {z : E} (hz : z ∈ (extChartAt I x).target) :
    (g.sumTangentSpace h).toNondegenerateMetric.chartMetric (Sum.inr x) z =
      h.toNondegenerateMetric.chartMetric x z := by
  have hz' : z ∈ (extChartAt I (Sum.inr x : M ⊕ N)).target := by
    simpa only [TauCeti.Manifold.extChartAt_target_sumInr] using hz
  have hy : (extChartAt I x).symm z ∈ (chartAt H x).source := by
    simpa using (extChartAt I x).map_target hz
  ext v w
  rw [(g.sumTangentSpace h).toNondegenerateMetric.chartMetric_apply hz',
    h.toNondegenerateMetric.chartMetric_apply hz, TauCeti.Manifold.extChartAt_symm_sumInr]
  simp only [toNondegenerateMetric_apply]
  have hbase : (extChartAt I x).symm z ∈
      (trivializationAt E (TangentSpace I : N → Type _) x).baseSet := by simpa using hy
  have hbase' : Sum.inr ((extChartAt I x).symm z) ∈
      (trivializationAt E (TangentSpace I : M ⊕ N → Type _) (Sum.inr x)).baseSet := by
    simpa [ChartedSpace.sum_chartAt_inr] using hy
  simp only [← Trivialization.symmL_apply (R := ℝ) _ hbase',
    ← Trivialization.symmL_apply (R := ℝ) _ hbase,
    TauCeti.Manifold.symmL_trivializationAt_sumInr hy]
  exact sumTangentSpace_inner_inr g h _ _ _

variable [I.Boundaryless]

/-- Every coordinate derivative of a disjoint-union metric in a chart of the left summand is
the corresponding coordinate derivative of the left metric. -/
theorem iteratedFDeriv_chartMetric_sumTangentSpace_inl
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ContMDiffRiemannianMetric I ∞ E (fun x : N ↦ TangentSpace I x))
    (x : M) (m : ℕ) {z : E} (hz : z ∈ (extChartAt I x).target) :
    iteratedFDeriv ℝ m ((g.sumTangentSpace h).toNondegenerateMetric.chartMetric (Sum.inl x)) z =
      iteratedFDeriv ℝ m (g.toNondegenerateMetric.chartMetric x) z := by
  have heq : (g.sumTangentSpace h).toNondegenerateMetric.chartMetric (Sum.inl x) =ᶠ[𝓝 z]
      g.toNondegenerateMetric.chartMetric x := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with y hy
    exact chartMetric_sumTangentSpace_inl g h x hy
  exact (heq.iteratedFDeriv ℝ m).eq_of_nhds

/-- Every coordinate derivative of a disjoint-union metric in a chart of the right summand is
the corresponding coordinate derivative of the right metric. -/
theorem iteratedFDeriv_chartMetric_sumTangentSpace_inr
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ContMDiffRiemannianMetric I ∞ E (fun x : N ↦ TangentSpace I x))
    (x : N) (m : ℕ) {z : E} (hz : z ∈ (extChartAt I x).target) :
    iteratedFDeriv ℝ m ((g.sumTangentSpace h).toNondegenerateMetric.chartMetric (Sum.inr x)) z =
      iteratedFDeriv ℝ m (h.toNondegenerateMetric.chartMetric x) z := by
  have heq : (g.sumTangentSpace h).toNondegenerateMetric.chartMetric (Sum.inr x) =ᶠ[𝓝 z]
      h.toNondegenerateMetric.chartMetric x := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with y hy
    exact chartMetric_sumTangentSpace_inr g h x hy
  exact (heq.iteratedFDeriv ℝ m).eq_of_nhds

variable [LocallyCompactSpace E] (k : ℕ∞)

/-- Disjoint union preserves continuity of families for every chart Cᵏ topology. Both metrics
may vary, and the parameter space is arbitrary. -/
@[fun_prop]
theorem continuous_sumTangentSpace {P : Type*} [TopologicalSpace P]
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {h : P → ContMDiffRiemannianMetric I ∞ E (fun x : N ↦ TangentSpace I x)}
    (hg : @Continuous _ _ _ (chartCkTopology k) g)
    (hh : @Continuous _ _ _ (chartCkTopology k) h) :
    @Continuous _ _ _ (chartCkTopology k) (fun p ↦ (g p).sumTangentSpace (h p)) := by
  rw [continuous_chartCk_iff] at hg hh ⊢
  rintro (x | x) m hm
  · rw [TauCeti.Manifold.extChartAt_target_sumInl]
    exact (hg x m hm).congr fun q ↦
      (iteratedFDeriv_chartMetric_sumTangentSpace_inl (g q.1) (h q.1) x m q.2.property).symm
  · rw [TauCeti.Manifold.extChartAt_target_sumInr]
    exact (hh x m hm).congr fun q ↦
      (iteratedFDeriv_chartMetric_sumTangentSpace_inr (g q.1) (h q.1) x m q.2.property).symm

/-- A disjoint-union family is continuous in the chart Cᵏ topology if and only if both
summand families are continuous in that topology. In particular, no regularity can be lost by
assembling the summands. -/
theorem continuous_sumTangentSpace_iff {P : Type*} [TopologicalSpace P]
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {h : P → ContMDiffRiemannianMetric I ∞ E (fun x : N ↦ TangentSpace I x)} :
    @Continuous _ _ _ (chartCkTopology k) (fun p ↦ (g p).sumTangentSpace (h p)) ↔
      @Continuous _ _ _ (chartCkTopology k) g ∧
        @Continuous _ _ _ (chartCkTopology k) h := by
  refine ⟨fun hs ↦ ?_, fun ⟨hg, hh⟩ ↦ continuous_sumTangentSpace k hg hh⟩
  rw [continuous_chartCk_iff] at hs
  constructor
  · rw [continuous_chartCk_iff]
    intro x m hm
    have hc := hs (Sum.inl x) m hm
    rw [TauCeti.Manifold.extChartAt_target_sumInl] at hc
    exact hc.congr fun q ↦
      iteratedFDeriv_chartMetric_sumTangentSpace_inl (g q.1) (h q.1) x m q.2.property
  · rw [continuous_chartCk_iff]
    intro x m hm
    have hc := hs (Sum.inr x) m hm
    rw [TauCeti.Manifold.extChartAt_target_sumInr] at hc
    exact hc.congr fun q ↦
      iteratedFDeriv_chartMetric_sumTangentSpace_inr (g q.1) (h q.1) x m q.2.property

end Bundle.ContMDiffRiemannianMetric
