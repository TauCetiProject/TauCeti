/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Invariance
public import TauCeti.Geometry.Manifold.Instances.HalfSpace
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# The boundary of a manifold modelled on the half-space in `E × ℝ`

Let `M` be a topological manifold modelled on the half-space `{q : E × ℝ | 0 ≤ q.2}` through
`TauCeti.modelWithCornersHalfSpace E`, with `E` finite dimensional. This file gives the boundary of
`M` the structure of a charted space modelled on `E`, one dimension lower.

Every chart, in the atlas or not, detects the boundary by the vanishing of the height coordinate
(`TauCeti.mem_boundary_modelWithCornersHalfSpace_iff`): this is the topological invariance of the
boundary, proved by invariance of domain in `TauCeti.Geometry.Manifold.Boundary.Invariance`, and
it needs no condition on the transition maps. Consequently each chart of `M` restricts to a chart
of the boundary that forgets the vanishing height, and these restricted charts form a charted-space
structure on the boundary (`TauCeti.halfSpaceBoundaryChartedSpace`). A transition map between two
boundary charts is the ambient transition map restricted to the hyperplane `E × {0}` and followed
by the projection to `E`, so the boundary inherits structures defined by the transition maps, for
instance PL ones (`TauCeti.Geometry.Manifold.PLGroupoid.Boundary`).

The construction parallels the boundary of a smooth manifold modelled on the Euclidean half-space,
`TauCeti.boundaryChartedSpace` in `TauCeti.Geometry.Manifold.Boundary.Charts`, where chart
independence of the boundary comes from the derivative instead.

## Main definitions

* `TauCeti.halfSpaceBoundaryChartedSpace`: the charted-space structure on the boundary, modelled
  on `E`.

## Main results

* `TauCeti.mem_boundary_modelWithCornersHalfSpace_iff`: a point lies on the boundary exactly when
  any chart around it reads it at height zero.
* `TauCeti.halfSpaceBoundaryChartedSpace_atlas` and the `halfSpaceBoundaryChartedSpace_chartAt_*`
  lemmas: the atlas of the boundary and the source, target, values and inverse of its charts.
-/

public section

open Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace {q : E × ℝ | 0 ≤ q.2} M]

/-- **Topological invariance of the boundary.** On a charted space modelled on the half-space in
`E × ℝ`, with `E` finite dimensional, a point lies on the boundary exactly when any chart around
it, in the atlas or not, reads it at height zero. -/
theorem mem_boundary_modelWithCornersHalfSpace_iff
    {e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}} {x : M} (hx : x ∈ e.source) :
    x ∈ (modelWithCornersHalfSpace E).boundary M ↔ (e x).val.2 = 0 := by
  rw [ModelWithCorners.boundary, mem_ofPred_eq,
    ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional hx,
    frontier_range_modelWithCornersHalfSpace, modelWithCornersHalfSpace_apply, mem_ofPred_eq]

variable {e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}}

/-- A point of `E × {0}` in the target of a chart of `M` is the reading of a boundary point. -/
private theorem symm_symm_mem_boundary_modelWithCornersHalfSpace {z : E}
    (hz : (modelWithCornersHalfSpace E).symm (z, 0) ∈ e.target) :
    e.symm ((modelWithCornersHalfSpace E).symm (z, 0)) ∈ (modelWithCornersHalfSpace E).boundary M :=
  (mem_boundary_modelWithCornersHalfSpace_iff (e.map_target hz)).2 <| by
    rw [e.right_inv hz]
    simp [modelWithCornersHalfSpace_symm_apply]

/-- A chart of `M` reads a boundary point in `E × {0}`. -/
private theorem symm_fst_apply_eq_apply_of_mem_boundary {x : M} (hx : x ∈ e.source)
    (hxb : x ∈ (modelWithCornersHalfSpace E).boundary M) :
    (modelWithCornersHalfSpace E).symm ((e x).val.1, 0) = e x :=
  Subtype.ext <| (coe_modelWithCornersHalfSpace_symm_apply E le_rfl).trans
    (Prod.ext rfl ((mem_boundary_modelWithCornersHalfSpace_iff hx).1 hxb).symm)

/-- The boundary chart attached to a chart `e` of `M`: read a boundary point through `e` and forget
its height, which vanishes. The base point `p` witnesses that the boundary is nonempty, which
`OpenPartialHomeomorph.subtypeCoord` needs to choose an irrelevant inverse value off the target. -/
private noncomputable def halfSpaceBoundaryChart (p : (modelWithCornersHalfSpace E).boundary M)
    (e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}) :
    OpenPartialHomeomorph ((modelWithCornersHalfSpace E).boundary M) E :=
  e.subtypeCoord _ ⟨p⟩ (fun z => (modelWithCornersHalfSpace E).symm (z, 0)) (fun q => q.val.1)
    symm_symm_mem_boundary_modelWithCornersHalfSpace symm_fst_apply_eq_apply_of_mem_boundary
    (fun z _ => by simp [modelWithCornersHalfSpace_symm_apply])
    ((modelWithCornersHalfSpace E).continuous_symm.comp (continuous_id.prodMk continuous_const))
    (continuous_fst.comp continuous_subtypeVal).continuousOn

variable {p : (modelWithCornersHalfSpace E).boundary M}

@[simp]
private theorem halfSpaceBoundaryChart_source :
    (halfSpaceBoundaryChart p e).source = Subtype.val ⁻¹' e.source := by
  unfold halfSpaceBoundaryChart
  apply OpenPartialHomeomorph.subtypeCoord_source

@[simp]
private theorem halfSpaceBoundaryChart_target :
    (halfSpaceBoundaryChart p e).target =
      {z | (modelWithCornersHalfSpace E).symm (z, 0) ∈ e.target} := by
  unfold halfSpaceBoundaryChart
  apply OpenPartialHomeomorph.subtypeCoord_target

@[simp]
private theorem halfSpaceBoundaryChart_apply (q : (modelWithCornersHalfSpace E).boundary M) :
    halfSpaceBoundaryChart p e q = (e q).val.1 := by
  unfold halfSpaceBoundaryChart
  apply OpenPartialHomeomorph.subtypeCoord_apply

private theorem coe_halfSpaceBoundaryChart_symm_apply {z : E}
    (hz : (modelWithCornersHalfSpace E).symm (z, 0) ∈ e.target) :
    ((halfSpaceBoundaryChart p e).symm z : M) =
      e.symm ((modelWithCornersHalfSpace E).symm (z, 0)) := by
  unfold halfSpaceBoundaryChart
  exact OpenPartialHomeomorph.coe_subtypeCoord_symm_apply _ _ _ _ _ _ _ _ _ _ hz

variable (E M) in
/-- The charted-space structure on the boundary of a manifold modelled on the half-space in
`E × ℝ`, with `E` finite dimensional. Its charts are the charts of `M` restricted to the boundary,
with the vanishing height forgotten. The implementation is opaque; use the characteristic lemmas
below to reason about its charts. -/
@[irreducible, instance] noncomputable def halfSpaceBoundaryChartedSpace :
    ChartedSpace E ((modelWithCornersHalfSpace E).boundary M) where
  atlas := range fun p => halfSpaceBoundaryChart p (chartAt _ p.val)
  chartAt p := halfSpaceBoundaryChart p (chartAt _ p.val)
  mem_chart_source p := by
    rw [halfSpaceBoundaryChart_source]
    exact mem_chart_source _ p.val
  chart_mem_atlas p := mem_range_self p

/-- The preferred boundary chart at `p` is the boundary chart induced by the preferred chart of `M`
at `p`. -/
private theorem halfSpaceBoundaryChartedSpace_chartAt
    (p : (modelWithCornersHalfSpace E).boundary M) :
    chartAt E p = halfSpaceBoundaryChart p (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)) := by
  unfold halfSpaceBoundaryChartedSpace
  rfl

variable (M) in
/-- The atlas of the boundary is the range of its preferred charts. -/
theorem halfSpaceBoundaryChartedSpace_atlas :
    atlas E ((modelWithCornersHalfSpace E).boundary M) =
      range fun p : (modelWithCornersHalfSpace E).boundary M => chartAt E p := by
  unfold atlas halfSpaceBoundaryChartedSpace chartAt
  rfl

/-- The source of the preferred boundary chart at `p` is the part of the boundary that the
preferred chart of `M` at `p` sees. -/
theorem halfSpaceBoundaryChartedSpace_chartAt_source
    (p : (modelWithCornersHalfSpace E).boundary M) :
    (chartAt E p).source = Subtype.val ⁻¹' (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).source := by
  rw [halfSpaceBoundaryChartedSpace_chartAt, halfSpaceBoundaryChart_source]

/-- The target of the preferred boundary chart at `p` is the target of the preferred chart of `M`
at `p`, pulled back to the hyperplane `E × {0}`. -/
theorem halfSpaceBoundaryChartedSpace_chartAt_target
    (p : (modelWithCornersHalfSpace E).boundary M) :
    (chartAt E p).target =
      {z | (modelWithCornersHalfSpace E).symm (z, 0) ∈
        (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).target} := by
  rw [halfSpaceBoundaryChartedSpace_chartAt, halfSpaceBoundaryChart_target]

/-- The preferred boundary chart at `p` reads a point through the preferred chart of `M` at `p` and
forgets its height. -/
theorem halfSpaceBoundaryChartedSpace_chartAt_apply
    (p q : (modelWithCornersHalfSpace E).boundary M) :
    chartAt E p q = (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M) q).val.1 := by
  rw [halfSpaceBoundaryChartedSpace_chartAt, halfSpaceBoundaryChart_apply]

/-- On its target, the inverse of the preferred boundary chart at `p` is the inverse of the
preferred chart of `M` at `p`, applied at height zero. -/
theorem coe_halfSpaceBoundaryChartedSpace_chartAt_symm_apply
    (p : (modelWithCornersHalfSpace E).boundary M) {z : E}
    (hz : (modelWithCornersHalfSpace E).symm (z, 0) ∈
      (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).target) :
    ((chartAt E p).symm z : M) =
      (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).symm ((modelWithCornersHalfSpace E).symm (z, 0)) := by
  rw [halfSpaceBoundaryChartedSpace_chartAt, coe_halfSpaceBoundaryChart_symm_apply hz]

end TauCeti
