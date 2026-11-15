/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Invariance
public import TauCeti.Geometry.Manifold.Instances.HalfSpace
public import TauCeti.Geometry.Manifold.PLGroupoid.Inverse
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# The boundary of a PL manifold is a PL manifold

PL manifolds with boundary are modelled on the half-space `{q : E × ℝ | 0 ≤ q.2}` through
`TauCeti.modelWithCornersHalfSpace E`, as for the realizations of combinatorial manifolds. This file
gives the boundary of such a manifold the structure of a boundaryless PL manifold modelled on `E`,
one dimension lower, and shows that its inclusion is a PL map. This is the structure in which a
PL homeomorphism between boundaries, along which two PL manifolds are glued, is stated.

The tangential space `E` is finite dimensional. Then every chart, in the atlas or not, detects the
boundary by the vanishing of the height coordinate
(`TauCeti.mem_boundary_modelWithCornersHalfSpace_iff`): this is the topological invariance of the
boundary, proved by invariance of domain in `TauCeti.Geometry.Manifold.Boundary.Invariance`, and
it needs no condition on the transition maps. Consequently each chart of `M` restricts to a chart
of the boundary that forgets the vanishing height, and these restricted charts form a charted-space
structure on the boundary (`TauCeti.halfSpaceBoundaryChartedSpace`) for every topological manifold
`M` modelled on the half-space. A transition map between two boundary charts is the ambient
transition map restricted to the hyperplane `E × {0}` and followed by the projection to `E`, so it
is PL when the ambient one is (`TauCeti.hasGroupoid_boundary_PLGroupoid`).

The construction parallels the boundary of a smooth manifold modelled on the Euclidean half-space,
`TauCeti.boundaryChartedSpace` in `TauCeti.Geometry.Manifold.Boundary.Charts`, where chart
independence of the boundary comes from the derivative instead.

## Main definitions

* `TauCeti.halfSpaceBoundaryChartedSpace`: the charted-space structure on the boundary, modelled
  on `E`.

## Main results

* `TauCeti.mem_boundary_modelWithCornersHalfSpace_iff`: a point lies on the boundary exactly when
  any chart around it reads it at height zero.
* `TauCeti.hasGroupoid_boundary_PLGroupoid`: the boundary of a PL manifold is a PL manifold.
* `TauCeti.isPLMap_subtypeVal_boundary`: the inclusion of the boundary is a PL map.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1 (PL manifolds and their boundaries).
-/

public section

open Set

open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace {q : E × ℝ | 0 ≤ q.2} M]

/-- **Topological invariance of the boundary.** On a charted space modelled on the half-space in
`E × ℝ`, with `E` finite dimensional, a point lies on the boundary exactly when any chart around
it, in the atlas or not, reads it at height zero. -/
theorem mem_boundary_modelWithCornersHalfSpace_iff
    {e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}} {x : M} (hx : x ∈ e.source) :
    x ∈ (modelWithCornersHalfSpace E).boundary M ↔ (e x).1.2 = 0 := by
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
    (modelWithCornersHalfSpace E).symm ((e x).1.1, 0) = e x :=
  Subtype.ext <| (coe_modelWithCornersHalfSpace_symm_apply E le_rfl).trans
    (Prod.ext rfl ((mem_boundary_modelWithCornersHalfSpace_iff hx).1 hxb).symm)

/-- The boundary chart attached to a chart `e` of `M`: read a boundary point through `e` and forget
its height, which vanishes. The base point `p` witnesses that the boundary is nonempty, which
`OpenPartialHomeomorph.subtypeCoord` needs to choose an irrelevant inverse value off the target. -/
private noncomputable def halfSpaceBoundaryChart (p : (modelWithCornersHalfSpace E).boundary M)
    (e : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}) :
    OpenPartialHomeomorph ((modelWithCornersHalfSpace E).boundary M) E :=
  e.subtypeCoord _ ⟨p⟩ (fun z => (modelWithCornersHalfSpace E).symm (z, 0)) (fun q => q.1.1)
    symm_symm_mem_boundary_modelWithCornersHalfSpace symm_fst_apply_eq_apply_of_mem_boundary
    (fun z _ => by simp [modelWithCornersHalfSpace_symm_apply])
    ((modelWithCornersHalfSpace E).continuous_symm.comp (continuous_id.prodMk continuous_const))
    (continuous_fst.comp continuous_subtype_val).continuousOn

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
    halfSpaceBoundaryChart p e q = (e q).1.1 := by
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
  atlas := range fun p => halfSpaceBoundaryChart p (chartAt _ p.1)
  chartAt p := halfSpaceBoundaryChart p (chartAt _ p.1)
  mem_chart_source p := by
    rw [halfSpaceBoundaryChart_source]
    exact mem_chart_source _ p.1
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
@[simp]
theorem halfSpaceBoundaryChartedSpace_chartAt_source
    (p : (modelWithCornersHalfSpace E).boundary M) :
    (chartAt E p).source = Subtype.val ⁻¹' (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).source := by
  rw [halfSpaceBoundaryChartedSpace_chartAt, halfSpaceBoundaryChart_source]

/-- The target of the preferred boundary chart at `p` is the target of the preferred chart of `M`
at `p`, pulled back to the hyperplane `E × {0}`. -/
@[simp]
theorem halfSpaceBoundaryChartedSpace_chartAt_target
    (p : (modelWithCornersHalfSpace E).boundary M) :
    (chartAt E p).target =
      {z | (modelWithCornersHalfSpace E).symm (z, 0) ∈
        (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).target} := by
  rw [halfSpaceBoundaryChartedSpace_chartAt, halfSpaceBoundaryChart_target]

/-- The preferred boundary chart at `p` reads a point through the preferred chart of `M` at `p` and
forgets its height. -/
@[simp]
theorem halfSpaceBoundaryChartedSpace_chartAt_apply
    (p q : (modelWithCornersHalfSpace E).boundary M) :
    chartAt E p q = (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M) q).1.1 := by
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

/-- A transition map between two boundary charts is PL when the transition map between the
ambient charts is: it is the ambient transition map, read in `E × ℝ`, restricted to `E × {0}` and
followed by the projection to `E`. -/
private theorem halfSpaceBoundaryChart_symm_trans_mem_PLGroupoid
    (p q : (modelWithCornersHalfSpace E).boundary M)
    {e₁ e₂ : OpenPartialHomeomorph M {q : E × ℝ | 0 ≤ q.2}}
    (he : e₁.symm ≫ₕ e₂ ∈ PLGroupoid (modelWithCornersHalfSpace E)) :
    (halfSpaceBoundaryChart p e₁).symm ≫ₕ halfSpaceBoundaryChart q e₂ ∈ PLGroupoid 𝓘(ℝ, E) := by
  set I := modelWithCornersHalfSpace E
  set inl := (ContinuousLinearMap.inl ℝ E ℝ).toContinuousAffineMap
  set fst := (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  rw [mem_PLGroupoid_iff_isPLOn (ModelWithCorners.isConvexPolyhedron_range _)]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id,
    inter_univ, Function.id_comp, Function.comp_id]
  have hG := ((mem_PLGroupoid_iff I).1 he).1
  -- A point of the source of the boundary transition, placed at height zero, lies in the source
  -- of the ambient transition.
  have hsrc {z : E} (hz : z ∈ ((halfSpaceBoundaryChart p e₁).symm ≫ₕ
      halfSpaceBoundaryChart q e₂).source) : I.symm (z, 0) ∈ e₁.target ∧
        e₁.symm (I.symm (z, 0)) ∈ e₂.source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      halfSpaceBoundaryChart_target] at hz
    obtain ⟨hz₁, hz₂⟩ := hz
    rw [mem_preimage, halfSpaceBoundaryChart_source, mem_preimage,
      coe_halfSpaceBoundaryChart_symm_apply hz₁] at hz₂
    exact ⟨hz₁, hz₂⟩
  refine ((isPLOn_continuousAffineMap fst univ).comp (hG.comp (isPLOn_continuousAffineMap inl _)
    fun z hz => ⟨?_, ?_⟩) (subset_univ _)).congr fun z hz => ?_
  · simpa [inl] using hsrc hz
  · simp [inl, I]
  · have h := hsrc hz
    simp [inl, fst, I, coe_halfSpaceBoundaryChart_symm_apply h.1]

variable (M) in
/-- **The boundary of a PL manifold is a PL manifold.** If `M` is a PL manifold modelled on the
half-space in `E × ℝ`, with `E` finite dimensional, then the boundary charts form a PL atlas of
its boundary, which is therefore a boundaryless PL manifold modelled on `E`. -/
instance hasGroupoid_boundary_PLGroupoid
    [HasGroupoid M (PLGroupoid (modelWithCornersHalfSpace E))] :
    HasGroupoid ((modelWithCornersHalfSpace E).boundary M) (PLGroupoid 𝓘(ℝ, E)) where
  compatible := by
    rw [halfSpaceBoundaryChartedSpace_atlas]
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    dsimp only
    rw [halfSpaceBoundaryChartedSpace_chartAt, halfSpaceBoundaryChartedSpace_chartAt]
    exact halfSpaceBoundaryChart_symm_trans_mem_PLGroupoid p q
      (HasGroupoid.compatible (chart_mem_atlas _ _) (chart_mem_atlas _ _))

variable (M) in
/-- The inclusion of the boundary of a manifold modelled on the half-space in `E × ℝ`, with `E`
finite dimensional, is a PL map: in the boundary chart at a point and the chart of `M` there, it
reads as the affine inclusion `z ↦ (z, 0)` of `E` into `E × ℝ`. -/
theorem isPLMap_subtypeVal_boundary :
    IsPLMap 𝓘(ℝ, E) (modelWithCornersHalfSpace E)
      (Subtype.val : (modelWithCornersHalfSpace E).boundary M → M) := by
  refine isPLMap_iff_forall_isPLMapAt.2 fun p =>
    isPLMapAt_iff.2 ⟨continuous_subtype_val.continuousAt, ?_⟩
  set inl := (ContinuousLinearMap.inl ℝ E ℝ).toContinuousAffineMap
  have hp : chartAt E p p ∈ (chartAt E p).target := (chartAt E p).map_source (mem_chart_source E p)
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, id_eq,
    Function.comp_id]
  -- On the target of the boundary chart, the inclusion reads as `z ↦ (z, 0)`.
  have key {z : E} (hz : z ∈ (chartAt E p).target) :
      modelWithCornersHalfSpace E (chartAt _ (p : M) ((chartAt E p).symm z : M)) = inl z := by
    rw [halfSpaceBoundaryChartedSpace_chartAt_target] at hz
    rw [coe_halfSpaceBoundaryChartedSpace_chartAt_symm_apply p hz,
      OpenPartialHomeomorph.right_inv _ hz, modelWithCornersHalfSpace_apply,
      coe_modelWithCornersHalfSpace_symm_apply E le_rfl]
    simp [inl]
  rw [← isPLWithinAt_inter ((chartAt E p).open_target.mem_nhds hp)]
  exact (inl.isPLWithinAt _ _).congr (fun z hz => key hz.2) (key hp)

end TauCeti
