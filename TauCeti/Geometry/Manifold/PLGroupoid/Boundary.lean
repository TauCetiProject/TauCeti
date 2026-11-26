/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Boundary.ProductHalfSpace
public import TauCeti.Geometry.Manifold.PLGroupoid.Inverse
public import TauCeti.Geometry.Manifold.PLGroupoid.Map

/-!
# The boundary of a PL manifold is a PL manifold

PL manifolds with boundary are modelled here on two half-spaces: the Euclidean half-space
`𝓡∂ (n + 1)`, the model of `TauCeti.boundaryChartedSpace`, and the product half-space
`{q : E × ℝ | 0 ≤ q.2}` through `TauCeti.modelWithCornersHalfSpace E`, the model of the
realizations of combinatorial manifolds. In both cases the boundary carries a charted-space
structure one dimension lower, whose charts read a boundary point through an ambient chart and
forget the vanishing coordinate. That this is well defined for a PL manifold, which need not carry
any smooth structure, is the topological invariance of the boundary
(`ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional`).

This file proves that the boundary is a boundaryless PL manifold of one dimension less, and that
its inclusion into `M` is a PL map. A boundary transition map is the ambient transition map
conjugated by the affine inclusion of the boundary hyperplane and the affine projection forgetting
the vanishing coordinate, and piecewise linearity is preserved by composition with affine maps.
This is the PL counterpart of `TauCeti.isManifold_boundary`. The structure on the boundary of a
product half-space model is the one in which a PL homeomorphism between boundaries, along which
two PL manifolds are glued, is stated.

## Main results

* `TauCeti.hasGroupoid_PLGroupoid_boundary`: the boundary of a PL manifold modelled on
  `𝓡∂ (n + 1)` is a PL manifold, modelled on `EuclideanSpace ℝ (Fin n)`.
* `TauCeti.isPLMap_subtypeVal_boundary`: its inclusion is a PL map.
* `TauCeti.hasGroupoid_PLGroupoid_halfSpaceBoundary`: the boundary of a PL manifold modelled on
  the half-space in `E × ℝ` is a PL manifold, modelled on `E`.
* `TauCeti.isPLMap_subtypeVal_halfSpaceBoundary`: its inclusion is a PL map.
* `TauCeti.isPLMap_iff_comp_subtypeVal_halfSpaceBoundary`: a map into that boundary is PL exactly
  when it is PL as a map into `M`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 1 and 2 (PL manifolds and their boundaries).
-/

public section

open Set Topology

open scoped Manifold

namespace TauCeti

section EuclideanHalfSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- The transition map between two preferred boundary charts is PL: read through the
parametrization of the coordinate hyperplane, it is the ambient transition map followed by the
deletion of the zeroth coordinate. -/
private theorem isPLOn_boundaryChart_symm_trans
    [HasGroupoid M (PLGroupoid (𝓡∂ (n + 1)))] (p q : ↥((𝓡∂ (n + 1)).boundary M)) :
    IsPLOn ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm ≫ₕ
        chartAt (EuclideanSpace ℝ (Fin n)) q)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm ≫ₕ
        chartAt (EuclideanSpace ℝ (Fin n)) q).source := by
  have hG := ((mem_PLGroupoid_iff _).1 (HasGroupoid.compatible (G := PLGroupoid (𝓡∂ (n + 1)))
    (chart_mem_atlas _ (p : M)) (chart_mem_atlas _ (q : M)))).1
  exact ((isPLOn_continuousAffineMap
      (euclideanHalfSpaceBoundaryProj n).toContinuousAffineMap univ).comp
    (hG.comp (isPLOn_continuousAffineMap
      (euclideanHalfSpaceBoundaryParam n).toContinuousAffineMap _)
      (mapsTo_boundaryParam_boundaryChartedSpace_chartAt_symm_trans M p q))
    (fun _ _ ↦ mem_univ _)).congr (eqOn_boundaryChartedSpace_chartAt_symm_trans M p q)

variable (M) in
/-- **The boundary of a PL manifold with boundary is a PL manifold** of dimension one less: the
transition maps between the boundary charts are PL. -/
instance hasGroupoid_PLGroupoid_boundary [HasGroupoid M (PLGroupoid (𝓡∂ (n + 1)))] :
    HasGroupoid ↥((𝓡∂ (n + 1)).boundary M) (PLGroupoid 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) where
  compatible := by
    rw [boundaryChartedSpace_atlas]
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    rw [mem_PLGroupoid_iff]
    constructor
    · simpa only [mfld_simps] using isPLOn_boundaryChart_symm_trans p q
    · simpa only [mfld_simps, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm] using isPLOn_boundaryChart_symm_trans q p

variable (M) in
/-- The inclusion of the boundary of a charted space modeled on a Euclidean half-space is a PL
map. In the preferred boundary and ambient charts it is the linear parametrization of the
coordinate hyperplane. -/
theorem isPLMap_subtypeVal_boundary :
    IsPLMap 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : ↥((𝓡∂ (n + 1)).boundary M) → M) := by
  refine isPLMap_iff_forall_isPLMapAt.2 fun p ↦ isPLMapAt_iff.2
    ⟨continuous_subtypeVal.continuousAt, ?_⟩
  set c := chartAt (EuclideanSpace ℝ (Fin n)) p
  -- On the target of the boundary chart, the reading of the inclusion is the parametrization.
  have heq : EqOn ((𝓡∂ (n + 1)) ∘ chartAt (EuclideanHalfSpace (n + 1)) (p : M) ∘ Subtype.val ∘
      c.symm ∘ 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).symm)
      (euclideanHalfSpaceBoundaryParam n) (range 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∩ c.target) := by
    rintro z ⟨-, hz⟩
    have hz' : EuclideanHalfSpace.boundaryParam n z ∈
        (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).target := by
      rwa [boundaryChartedSpace_chartAt_target M p] at hz
    simp only [Function.comp_apply, modelWithCornersSelf_coe_symm, id_eq]
    rw [boundaryChartedSpace_chartAt_symm_apply M p hz',
      (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).right_inv hz',
      modelWithCornersEuclideanHalfSpace_toFun, EuclideanHalfSpace.boundaryParam_coe]
  have hT : c.target ∈ 𝓝 (𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (c p)) :=
    c.open_target.mem_nhds (mem_chart_target _ p)
  refine (isPLWithinAt_inter hT).1
    (IsPLOn.isPLWithinAt ?_ ⟨mem_range_self _, mem_chart_target _ p⟩)
  exact (isPLOn_continuousAffineMap
    (euclideanHalfSpaceBoundaryParam n).toContinuousAffineMap _).congr heq

end EuclideanHalfSpace

section ProductHalfSpace

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
instance hasGroupoid_PLGroupoid_halfSpaceBoundary
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
theorem isPLMap_subtypeVal_halfSpaceBoundary :
    IsPLMap 𝓘(ℝ, E) (modelWithCornersHalfSpace E)
      (Subtype.val : (modelWithCornersHalfSpace E).boundary M → M) := by
  refine isPLMap_iff_forall_isPLMapAt.2 fun p =>
    isPLMapAt_iff.2 ⟨continuous_subtypeVal.continuousAt, ?_⟩
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
theorem isPLMapAt_iff_comp_subtypeVal_halfSpaceBoundary
    {f : N → (modelWithCornersHalfSpace E).boundary M} {x : N} :
    IsPLMapAt I' 𝓘(ℝ, E) f x ↔ IsPLMapAt I' (modelWithCornersHalfSpace E) (Subtype.val ∘ f) x := by
  refine ⟨((isPLMap_subtypeVal_halfSpaceBoundary M).isPLMapAt (f x)).comp, fun h => ?_⟩
  rw [isPLMapAt_iff] at h ⊢
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.2 h.1, ?_⟩
  -- The reading of `f` is the first component of the reading of `Subtype.val ∘ f`.
  set fst := (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  refine ((fst.isPLWithinAt univ _).comp h.2 (mapsTo_univ _ _)).congr (fun y _ => ?_) ?_ <;>
    simp [fst, halfSpaceBoundaryChartedSpace_chartAt_apply, modelWithCornersHalfSpace_apply]

/-- A map into the boundary of a manifold modelled on the half-space in `E × ℝ`, with `E` finite
dimensional, is PL exactly when it is PL as a map into `M`. -/
theorem isPLMap_iff_comp_subtypeVal_halfSpaceBoundary
    {f : N → (modelWithCornersHalfSpace E).boundary M} :
    IsPLMap I' 𝓘(ℝ, E) f ↔ IsPLMap I' (modelWithCornersHalfSpace E) (Subtype.val ∘ f) := by
  simp only [isPLMap_iff_forall_isPLMapAt, isPLMapAt_iff_comp_subtypeVal_halfSpaceBoundary]

end ProductHalfSpace

end TauCeti
