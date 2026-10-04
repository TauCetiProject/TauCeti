/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph

/-!
# Chart-independent detection of manifold boundary points

This file restates Mathlib's chart-independence results for interior and boundary points against
the range of a model with corners. This is the form used when computing the boundary of a concrete
model.

Mathlib states chart independence for charts of the atlas. The charts produced by local normal
forms, such as the charts of `Manifold.IsImmersionAt`, are only known to lie in the maximal atlas,
so the statements here are proved for every chart of `IsManifold.maximalAtlas`. Membership in the
maximal atlas makes a chart a local diffeomorphism, so Mathlib's
`IsLocalDiffeomorphAt.isInteriorPoint_iff` gives chart independence without a global `IsManifold`
assumption on the charted space.
-/

public section

open Set Topology

open scoped Manifold

namespace TauCeti.ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : WithTop ℕ∞}
  {e e' : OpenPartialHomeomorph M H} {x : M}

/-- An interior point of a charted space is detected by any maximal-atlas chart around it,
provided its differentiability exponent is nonzero. -/
theorem isInteriorPoint_iff_mem_interior_range (hk : k ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I k M) (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ I (e x) ∈ interior (range I) := by
  simpa only [ModelWithCorners.IsInteriorPoint, extChartAt_self_apply] using
    (e.isLocalDiffeomorphAt_of_mem_maximalAtlas he hx).isInteriorPoint_iff hk

/-- For two charts of the maximal atlas with nonzero differentiability exponent around a point
`x`, if the first reads `x` in the interior of its extended target, so does the second. -/
theorem mem_interior_extend_target_of_mem_maximalAtlas (hk : k ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I k M) (he' : e' ∈ IsManifold.maximalAtlas I k M)
    (hex : x ∈ e.source) (hex' : x ∈ e'.source)
    (hx : e.extend I x ∈ interior (e.extend I).target) :
    e'.extend I x ∈ interior (e'.extend I).target := by
  apply e'.mem_interior_extend_target (e'.map_source hex')
  exact (isInteriorPoint_iff_mem_interior_range hk he' hex').1 <|
    (isInteriorPoint_iff_mem_interior_range hk he hex).2
      (e.interior_extend_target_subset_interior_range hx)

/-- A boundary point of a charted space is detected by any maximal-atlas chart around it,
provided its differentiability exponent is nonzero. -/
theorem isBoundaryPoint_iff_mem_frontier_range (hk : k ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I k M) (hx : x ∈ e.source) :
    I.IsBoundaryPoint x ↔ I (e x) ∈ frontier (range I) := by
  rw [I.isBoundaryPoint_iff_not_isInteriorPoint,
    isInteriorPoint_iff_mem_interior_range hk he hx, I.isClosed_range.frontier_eq]
  simp

end TauCeti.ModelWithCorners
