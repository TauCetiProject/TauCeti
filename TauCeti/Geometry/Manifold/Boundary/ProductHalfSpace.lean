/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.OfHomeomorph
public import TauCeti.Geometry.Manifold.Instances.HalfSpace

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

The structure is the general construction `ModelWithCorners.boundaryChartedSpaceOfHomeomorph` for
forgetting the height, as is the boundary of a manifold modelled on the Euclidean half-space,
`TauCeti.boundaryChartedSpace` in `TauCeti.Geometry.Manifold.Boundary.Charts`, for deleting the
zeroth coordinate.

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
    x ∈ (modelWithCornersHalfSpace E).boundary M ↔ (e x).val.2 = 0 :=
  (ModelWithCorners.mem_boundary_iff_mem_frontier_range_of_finiteDimensional hx).trans
    (modelWithCornersHalfSpace_mem_frontier_range_iff _)

omit [FiniteDimensional ℝ E] in
variable (E) in
/-- Forgetting the vanishing height identifies the points that the half-space model sends to the
frontier of its range with `E`. -/
private noncomputable def halfSpaceFrontierHomeomorph :
    {q : {q : E × ℝ | 0 ≤ q.2} //
      modelWithCornersHalfSpace E q ∈ frontier (range (modelWithCornersHalfSpace E))} ≃ₜ E where
  toFun q := q.val.val.1
  invFun z := ⟨(modelWithCornersHalfSpace E).symm (z, 0),
    (modelWithCornersHalfSpace_mem_frontier_range_iff _).2 <| by
      rw [coe_modelWithCornersHalfSpace_symm_apply E le_rfl]⟩
  left_inv q := Subtype.ext <| Subtype.ext <|
    (coe_modelWithCornersHalfSpace_symm_apply E le_rfl).trans
      (Prod.ext rfl ((modelWithCornersHalfSpace_mem_frontier_range_iff _).1 q.property).symm)
  right_inv z := by simp [modelWithCornersHalfSpace_symm_apply]
  continuous_toFun := continuous_fst.comp (continuous_subtypeVal.comp continuous_subtypeVal)
  continuous_invFun := ((modelWithCornersHalfSpace E).continuous_symm.comp
    (continuous_id.prodMk continuous_const)).subtype_mk _

omit [FiniteDimensional ℝ E] in
private theorem halfSpaceFrontierHomeomorph_apply
    (q : {q : {q : E × ℝ | 0 ≤ q.2} //
      modelWithCornersHalfSpace E q ∈ frontier (range (modelWithCornersHalfSpace E))}) :
    halfSpaceFrontierHomeomorph E q = q.val.val.1 :=
  (rfl)

omit [FiniteDimensional ℝ E] in
private theorem coe_halfSpaceFrontierHomeomorph_symm_apply (z : E) :
    ((halfSpaceFrontierHomeomorph E).symm z : {q : E × ℝ | 0 ≤ q.2}) =
      (modelWithCornersHalfSpace E).symm (z, 0) :=
  (rfl)

variable (E M) in
/-- The charted-space structure on the boundary of a manifold modelled on the half-space in
`E × ℝ`, with `E` finite dimensional. Its charts are the charts of `M` restricted to the boundary,
with the vanishing height forgotten: the general construction
`ModelWithCorners.boundaryChartedSpaceOfHomeomorph` for forgetting the height. The implementation
is opaque; use the characteristic lemmas below to reason about its charts. -/
@[irreducible, instance] noncomputable def halfSpaceBoundaryChartedSpace :
    ChartedSpace E ((modelWithCornersHalfSpace E).boundary M) :=
  (modelWithCornersHalfSpace E).boundaryChartedSpaceOfHomeomorph M (halfSpaceFrontierHomeomorph E)
    (fun q ↦ q.val.1) fun q ↦ (halfSpaceFrontierHomeomorph_apply q).symm

variable (M) in
/-- The atlas of the boundary is the range of its preferred charts. -/
theorem halfSpaceBoundaryChartedSpace_atlas :
    atlas E ((modelWithCornersHalfSpace E).boundary M) =
      range fun p : (modelWithCornersHalfSpace E).boundary M => chartAt E p := by
  unfold halfSpaceBoundaryChartedSpace
  exact ModelWithCorners.boundaryChartedSpaceOfHomeomorph_atlas _ _ _ _ _

/-- The source of the preferred boundary chart at `p` is the part of the boundary that the
preferred chart of `M` at `p` sees. -/
theorem halfSpaceBoundaryChartedSpace_chartAt_source
    (p : (modelWithCornersHalfSpace E).boundary M) :
    (chartAt E p).source = Subtype.val ⁻¹' (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).source := by
  unfold halfSpaceBoundaryChartedSpace
  exact ModelWithCorners.boundaryChartedSpaceOfHomeomorph_chartAt_source p

/-- The target of the preferred boundary chart at `p` is the target of the preferred chart of `M`
at `p`, pulled back to the hyperplane `E × {0}`. -/
theorem halfSpaceBoundaryChartedSpace_chartAt_target
    (p : (modelWithCornersHalfSpace E).boundary M) :
    (chartAt E p).target =
      {z | (modelWithCornersHalfSpace E).symm (z, 0) ∈
        (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).target} := by
  unfold halfSpaceBoundaryChartedSpace
  simp_rw [ModelWithCorners.boundaryChartedSpaceOfHomeomorph_chartAt_target,
    coe_halfSpaceFrontierHomeomorph_symm_apply]

/-- The preferred boundary chart at `p` reads a point through the preferred chart of `M` at `p` and
forgets its height. -/
theorem halfSpaceBoundaryChartedSpace_chartAt_apply
    (p q : (modelWithCornersHalfSpace E).boundary M) :
    chartAt E p q = (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M) q).val.1 := by
  unfold halfSpaceBoundaryChartedSpace
  exact ModelWithCorners.boundaryChartedSpaceOfHomeomorph_chartAt_apply p q

/-- On its target, the inverse of the preferred boundary chart at `p` is the inverse of the
preferred chart of `M` at `p`, applied at height zero. -/
theorem coe_halfSpaceBoundaryChartedSpace_chartAt_symm_apply
    (p : (modelWithCornersHalfSpace E).boundary M) {z : E}
    (hz : (modelWithCornersHalfSpace E).symm (z, 0) ∈
      (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).target) :
    ((chartAt E p).symm z : M) =
      (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).symm ((modelWithCornersHalfSpace E).symm (z, 0)) := by
  unfold halfSpaceBoundaryChartedSpace
  rw [← coe_halfSpaceFrontierHomeomorph_symm_apply] at hz ⊢
  exact ModelWithCorners.coe_boundaryChartedSpaceOfHomeomorph_chartAt_symm_apply p hz

end TauCeti
