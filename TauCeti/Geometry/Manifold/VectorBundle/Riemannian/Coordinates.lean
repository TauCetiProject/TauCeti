/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Topology.VectorBundle.Bilinear

/-!
# Positivity of a Riemannian metric in chart coordinates

The native chart metric of a Riemannian metric is positive on the chart target.
-/

public section

open Bundle Set
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A Riemannian metric has a positive native chart metric at every point of the chart target. -/
theorem chartMetric_pos
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {x₀ : M} {z : E} (hz : z ∈ (extChartAt I x₀).target) {v : E} (hv : v ≠ 0) :
    0 < g.toNondegenerateMetric.chartMetric x₀ z v v := by
  have hbase := TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hz
  rw [TauCeti.Manifold.ContMDiffNondegenerateMetric.chartMetric_def,
    TauCeti.Manifold.ContMDiffNondegenerateMetric.inCoordinates_eq_tangentBilinFormInCoordinates,
    TauCeti.Manifold.tangentBilinFormInCoordinates_def]
  exact (TauCeti.forall_inCoordinates_bilinear_apply_self_pos_iff hbase _).mpr
    (fun v hv ↦ by simpa only [toNondegenerateMetric_apply] using g.pos _ v hv) v hv

end Bundle.ContMDiffRiemannianMetric
