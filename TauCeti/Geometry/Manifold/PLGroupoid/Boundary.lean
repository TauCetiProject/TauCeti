/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.ProductHalfSpace
public import TauCeti.Geometry.Manifold.PLGroupoid.Inverse

/-!
# The boundary of a PL manifold is a PL manifold

PL manifolds with boundary are modelled on the half-space `{q : E × ℝ | 0 ≤ q.2}` through
`TauCeti.modelWithCornersHalfSpace E`, as for the realizations of combinatorial manifolds. With `E`
finite dimensional, the boundary of such a manifold carries the charted-space structure
`TauCeti.halfSpaceBoundaryChartedSpace` modelled on `E`, one dimension lower, whose charts are the
ambient charts restricted to the boundary with the vanishing height forgotten. This file shows that
it is a boundaryless PL manifold and that its inclusion is a PL map. This is the structure in which
a PL homeomorphism between boundaries, along which two PL manifolds are glued, is stated.

A transition map between two boundary charts is the ambient transition map restricted to the
hyperplane `E × {0}` and followed by the projection to `E`, so it is PL when the ambient one is
(`TauCeti.hasGroupoid_boundary_PLGroupoid`).

## Main results

* `TauCeti.hasGroupoid_boundary_PLGroupoid`: the boundary of a PL manifold is a PL manifold.
* `TauCeti.isPLMap_subtypeVal_boundary`: the inclusion of the boundary is a PL map.
* `TauCeti.isPLMap_iff_comp_subtypeVal_boundary`: a map into the boundary is PL exactly when it is
  PL as a map into `M`.

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

/-- A transition map between two preferred boundary charts is PL when the transition map between
the ambient charts is: it is the ambient transition map, read in `E × ℝ`, restricted to `E × {0}`
and followed by the projection to `E`. -/
private theorem halfSpaceBoundaryChartedSpace_chartAt_symm_trans_mem_PLGroupoid
    (p q : (modelWithCornersHalfSpace E).boundary M)
    (he : (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).symm ≫ₕ
      chartAt {q : E × ℝ | 0 ≤ q.2} (q : M) ∈ PLGroupoid (modelWithCornersHalfSpace E)) :
    (chartAt E p).symm ≫ₕ chartAt E q ∈ PLGroupoid 𝓘(ℝ, E) := by
  -- A point of the source of the boundary transition, placed at height zero, lies in the source
  -- of the ambient transition.
  have hsrc {z : E} (hz : z ∈ ((chartAt E p).symm ≫ₕ chartAt E q).source) :
      (modelWithCornersHalfSpace E).symm (z, 0) ∈ (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).target ∧
        (chartAt {q : E × ℝ | 0 ≤ q.2} (p : M)).symm ((modelWithCornersHalfSpace E).symm (z, 0)) ∈
          (chartAt {q : E × ℝ | 0 ≤ q.2} (q : M)).source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      halfSpaceBoundaryChartedSpace_chartAt_target] at hz
    obtain ⟨hz₁, hz₂⟩ := hz
    rw [mem_preimage, halfSpaceBoundaryChartedSpace_chartAt_source, mem_preimage,
      coe_halfSpaceBoundaryChartedSpace_chartAt_symm_apply p hz₁] at hz₂
    exact ⟨hz₁, hz₂⟩
  set inl := (ContinuousLinearMap.inl ℝ E ℝ).toContinuousAffineMap
  set fst := (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  rw [mem_PLGroupoid_iff_isPLOn (ModelWithCorners.isConvexPolyhedron_range _)]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id,
    inter_univ, Function.id_comp, Function.comp_id]
  have hG := ((mem_PLGroupoid_iff _).1 he).1
  refine ((isPLOn_continuousAffineMap fst univ).comp (hG.comp (isPLOn_continuousAffineMap inl _)
    fun z hz => ⟨?_, ?_⟩) (subset_univ _)).congr fun z hz => ?_
  · simpa [inl] using hsrc hz
  · simp [inl]
  · have h := hsrc hz
    simp [inl, fst, halfSpaceBoundaryChartedSpace_chartAt_apply,
      coe_halfSpaceBoundaryChartedSpace_chartAt_symm_apply p h.1]

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
    exact halfSpaceBoundaryChartedSpace_chartAt_symm_trans_mem_PLGroupoid p q
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

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- A map into the boundary of a manifold modelled on the half-space in `E × ℝ`, with `E` finite
dimensional, is PL at `x` exactly when it is PL at `x` as a map into `M`. -/
theorem isPLMapAt_iff_comp_subtypeVal_boundary
    {f : N → (modelWithCornersHalfSpace E).boundary M} {x : N} :
    IsPLMapAt I' 𝓘(ℝ, E) f x ↔ IsPLMapAt I' (modelWithCornersHalfSpace E) (Subtype.val ∘ f) x := by
  refine ⟨((isPLMap_subtypeVal_boundary M).isPLMapAt (f x)).comp, fun h => ?_⟩
  rw [isPLMapAt_iff] at h ⊢
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.2 h.1, ?_⟩
  -- The reading of `f` is the first component of the reading of `Subtype.val ∘ f`.
  set fst := (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  refine ((fst.isPLWithinAt univ _).comp h.2 (mapsTo_univ _ _)).congr (fun y _ => ?_) ?_ <;>
    simp [fst, halfSpaceBoundaryChartedSpace_chartAt_apply, modelWithCornersHalfSpace_apply]

/-- A map into the boundary of a manifold modelled on the half-space in `E × ℝ`, with `E` finite
dimensional, is PL exactly when it is PL as a map into `M`. -/
theorem isPLMap_iff_comp_subtypeVal_boundary {f : N → (modelWithCornersHalfSpace E).boundary M} :
    IsPLMap I' 𝓘(ℝ, E) f ↔ IsPLMap I' (modelWithCornersHalfSpace E) (Subtype.val ∘ f) := by
  simp only [isPLMap_iff_forall_isPLMapAt, isPLMapAt_iff_comp_subtypeVal_boundary]

end TauCeti
