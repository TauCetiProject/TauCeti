/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.PLGroupoid.Map

/-!
# The boundary of a PL manifold is a PL manifold

Let `M` be a PL manifold with boundary modeled on the `(n + 1)`-dimensional Euclidean half-space:
a charted space over `EuclideanHalfSpace (n + 1)` whose transition maps lie in
`TauCeti.PLGroupoid (𝓡∂ (n + 1))`. Its boundary `(𝓡∂ (n + 1)).boundary M` carries the canonical
charted-space structure `TauCeti.boundaryChartedSpace`, modeled on `EuclideanSpace ℝ (Fin n)`: a
boundary chart reads a boundary point through an ambient chart and deletes the vanishing zeroth
coordinate. That this is well defined for a PL manifold, which need not carry any smooth
structure, is the topological invariance of the boundary
(`OpenPartialHomeomorph.isBoundaryPoint_iff_mem_frontier_range`).

This file proves that the boundary is a boundaryless PL manifold of one dimension less, and that
its inclusion into `M` is a PL map. A boundary transition map is the ambient transition map
conjugated by the linear parametrization of the coordinate hyperplane and the linear deletion of
the zeroth coordinate, and piecewise linearity is preserved by composition with linear maps. This
is the PL counterpart of `TauCeti.isManifold_boundary`.

## Main results

* `TauCeti.hasGroupoid_PLGroupoid_boundary`: the boundary of a PL manifold with boundary is a PL
  manifold, modeled on `EuclideanSpace ℝ (Fin n)`.
* `TauCeti.isPLMap_subtypeVal_boundary`: the inclusion of the boundary is a PL map.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (the boundary of a PL manifold).
-/

public section

open Set Topology

open scoped Manifold

namespace TauCeti

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
    ⟨continuous_subtype_val.continuousAt, ?_⟩
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

end TauCeti
