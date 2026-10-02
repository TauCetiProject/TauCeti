/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Chart-independent detection of manifold boundary points

This file restates Mathlib's chart-independence results for interior and boundary points against
the range of a model with corners. This is the form used when computing the boundary of a concrete
model.

Mathlib states chart independence for charts of the atlas. The charts produced by local normal
forms, such as the charts of `Manifold.IsImmersionAt`, are only known to lie in the maximal atlas,
so the statements here are proved for every chart of `IsManifold.maximalAtlas`. The argument is
Mathlib's (`ModelWithCorners.mem_interior_range_of_mem_interior_range_of_mem_atlas`): a transition
map has invertible differential, and a differentiable map with surjective differential cannot send
a point to the frontier of a closed convex set with nonempty interior.
-/

public section

open Set Topology

open scoped Manifold

namespace TauCeti.ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : WithTop ℕ∞} [IsManifold I k M]
  {e e' : OpenPartialHomeomorph M H} {x : M}

/-- For two charts of the maximal atlas of a `C^k` manifold, `k ≠ 0`, around a point `x`, if the
first reads `x` in the interior of its extended target, so does the second. -/
theorem mem_interior_extend_target_of_mem_maximalAtlas (hk : k ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I k M) (he' : e' ∈ IsManifold.maximalAtlas I k M)
    (hex : x ∈ e.source) (hex' : x ∈ e'.source)
    (hx : e.extend I x ∈ interior (e.extend I).target) :
    e'.extend I x ∈ interior (e'.extend I).target := by
  let φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 k φ φ.source := I.contDiffOn_extendCoordChange he he'
  suffices h : Function.Surjective (fderivWithin 𝕜 φ φ.source (e.extend I x)) →
      e'.extend I x ∈ interior (range I) by
    refine e'.mem_interior_extend_target (by simp [hex']) <| h ?_
    exact (I.isInvertible_fderivWithin_extendCoordChange hk he he'
      (by simp [hex, hex'])).surjective
  intro hφx'
  -- Reduce to the real case, where the convexity argument applies.
  wlog _ : IsRCLikeNormedField 𝕜
  · simp [I.range_eq_univ_of_not_isRCLikeNormedField ‹_›]
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hφx : φ.source ∈ 𝓝 (e.extend I x) := by
    simp_rw [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_source,
      PartialEquiv.symm_source, Filter.inter_mem_iff, mem_interior_iff_mem_nhds.1 hx, true_and,
      e'.extend_source]
    exact e.extend_preimage_mem_nhds hex <| e'.open_source.mem_nhds hex'
  rw [← ContinuousLinearMap.coe_restrictScalars' (R := ℝ),
    (hφ.differentiableOn hk _ (by simp [φ, hex, hex'])).restrictScalars_fderivWithin (𝕜 := ℝ)
      (uniqueDiffWithinAt_of_mem_nhds hφx), fderivWithin_of_mem_nhds hφx] at hφx'
  -- The transition map `φ` sends the reading of `x` in `e` to its reading in `e'`.
  have hφe : φ (e.extend I x) = e'.extend I x := by
    simp only [φ, ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
      e.extend_left_inv hex]
  rw [← hφe]
  replace hφ := ((hφ.restrict_scalars ℝ).differentiableOn hk).differentiableAt hφx
  exact hφ.mem_interior_convex_of_surjective_fderiv hφx I.convex_range I.isClosed_range
    I.nonempty_interior (φ.mapsTo.mono_right <| by simp [φ, inter_assoc]) hφx'

/-- A point of a `C^k` manifold, `k ≠ 0`, is an interior point exactly when any chart of the
maximal atlas containing it in its source reads it inside the interior of the range of the
model. -/
theorem isInteriorPoint_iff_mem_interior_range (hk : k ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I k M) (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ I (e x) ∈ interior (range I) := by
  have hc := IsManifold.chart_mem_maximalAtlas (I := I) (n := k) x
  rw [I.isInteriorPoint_iff]
  refine ⟨fun h ↦ e.interior_extend_target_subset_interior_range
      (mem_interior_extend_target_of_mem_maximalAtlas hk hc he (mem_chart_source H x) hx h),
    fun h ↦ mem_interior_extend_target_of_mem_maximalAtlas hk he hc hx (mem_chart_source H x)
      (e.mem_interior_extend_target (e.map_source hx) h)⟩

/-- A point of a `C^k` manifold, `k ≠ 0`, is a boundary point exactly when any chart of the
maximal atlas containing it in its source reads it on the frontier of the range of the model. -/
theorem isBoundaryPoint_iff_mem_frontier_range (hk : k ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I k M) (hx : x ∈ e.source) :
    I.IsBoundaryPoint x ↔ I (e x) ∈ frontier (range I) := by
  rw [I.isBoundaryPoint_iff_not_isInteriorPoint,
    isInteriorPoint_iff_mem_interior_range hk he hx, I.isClosed_range.frontier_eq]
  simp

end TauCeti.ModelWithCorners
