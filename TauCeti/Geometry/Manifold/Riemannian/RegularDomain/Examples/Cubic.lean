/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.RegularDomain.Examples.GraphEpigraph

/-!
# The region above the cubic `y = x³` as a regular domain

The region `M = {y ≥ x³}` above the cubic in the Euclidean plane is the region above the graph of
`w(x) = x³` (`TauCeti.graphEpigraph`), a regular domain whose boundary is the cubic. Since
`w''(x) = 6x`:

* the boundary is convex at `q = (x, x³)` exactly when `x ≥ 0`
  (`TauCeti.isConvexAt_cubicEpigraph_iff`), and strictly convex exactly when `x > 0`
  (`TauCeti.isStrictlyConvexAt_cubicEpigraph_iff`);
* the set of points of the boundary at which it is convex is not open
  (`TauCeti.not_isOpen_setOf_isConvexAt_cubicEpigraph`): it contains the origin, but not the
  points `(-t, -t³)`, `t > 0`, which tend to it.

So convexity of the boundary, without strictness, is not an open condition.
-/

public section

open Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

/-- The Euclidean plane. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- **Convexity of the cubic `y = x³`.** The boundary of the region above the cubic is convex at
`q = (x, x³)` exactly when `x ≥ 0`. -/
theorem isConvexAt_cubicEpigraph_iff
    (q : letI := graphEpigraphChartedSpace (contDiff_fun_id.pow 3)
      (𝓡∂ (1 + 1)).boundary (graphEpigraph fun x : ℝ ↦ x ^ 3)) :
    letI := graphEpigraphChartedSpace (contDiff_fun_id.pow 3)
    haveI := isManifold_graphEpigraph (contDiff_fun_id.pow 3)
    letI := graphEpigraphRiemannianBundle (contDiff_fun_id.pow 3)
    haveI := isContMDiffRiemannianBundle_graphEpigraph (contDiff_fun_id.pow 3)
    IsConvexAt q ↔ 0 ≤ (q : ℝ²) 0 := by
  rw [isConvexAt_graphEpigraph_iff, iter_deriv_pow]
  norm_num [Finset.prod_range_succ]

/-- **Strict convexity of the cubic `y = x³`.** The boundary of the region above the cubic is
strictly convex at `q = (x, x³)` exactly when `x > 0`. -/
theorem isStrictlyConvexAt_cubicEpigraph_iff
    (q : letI := graphEpigraphChartedSpace (contDiff_fun_id.pow 3)
      (𝓡∂ (1 + 1)).boundary (graphEpigraph fun x : ℝ ↦ x ^ 3)) :
    letI := graphEpigraphChartedSpace (contDiff_fun_id.pow 3)
    haveI := isManifold_graphEpigraph (contDiff_fun_id.pow 3)
    letI := graphEpigraphRiemannianBundle (contDiff_fun_id.pow 3)
    haveI := isContMDiffRiemannianBundle_graphEpigraph (contDiff_fun_id.pow 3)
    IsStrictlyConvexAt q ↔ 0 < (q : ℝ²) 0 := by
  rw [isStrictlyConvexAt_graphEpigraph_iff, iter_deriv_pow]
  norm_num [Finset.prod_range_succ]

/-- **Convexity is not an open condition.** The set of points of the cubic `y = x³` at which the
boundary of the region above it is convex is `{x ≥ 0}`, which is not open in the boundary: the
points `(-t, -t³)`, `t > 0`, are not in it and tend to the origin, which is. -/
theorem not_isOpen_setOf_isConvexAt_cubicEpigraph :
    letI := graphEpigraphChartedSpace (contDiff_fun_id.pow 3)
    haveI := isManifold_graphEpigraph (contDiff_fun_id.pow 3)
    letI := graphEpigraphRiemannianBundle (contDiff_fun_id.pow 3)
    haveI := isContMDiffRiemannianBundle_graphEpigraph (contDiff_fun_id.pow 3)
    ¬IsOpen {q : (𝓡∂ (1 + 1)).boundary (graphEpigraph fun x : ℝ ↦ x ^ 3) | IsConvexAt q} := by
  let := graphEpigraphChartedSpace (contDiff_fun_id.pow 3)
  have := isManifold_graphEpigraph (contDiff_fun_id.pow 3)
  let := graphEpigraphRiemannianBundle (contDiff_fun_id.pow 3)
  have := isContMDiffRiemannianBundle_graphEpigraph (contDiff_fun_id.pow 3)
  have hmem : ∀ t : ℝ, (!₂[-t, -t ^ 3] : ℝ²) ∈ graphEpigraph fun x : ℝ ↦ x ^ 3 := fun t ↦ by
    simp only [mem_ofPred_eq]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      sub_neg_eq_add]
    exact le_of_eq (by ring)
  have hbd : ∀ t : ℝ, (⟨!₂[-t, -t ^ 3], hmem t⟩ : graphEpigraph fun x : ℝ ↦ x ^ 3) ∈
      (𝓡∂ (1 + 1)).boundary (graphEpigraph fun x : ℝ ↦ x ^ 3) := by
    intro t
    rw [boundary_graphEpigraph, mem_ofPred_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, sub_neg_eq_add]
    ring
  let γ : ℝ → (𝓡∂ (1 + 1)).boundary (graphEpigraph fun x : ℝ ↦ x ^ 3) :=
    fun t ↦ ⟨⟨!₂[-t, -t ^ 3], hmem t⟩, hbd t⟩
  have hγ : Continuous γ := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)
  intro hU
  have h0 : (0 : ℝ) ∈ γ ⁻¹' {q | IsConvexAt q} := by
    rw [Set.mem_preimage, Set.mem_ofPred_eq, isConvexAt_cubicEpigraph_iff]
    simp [γ]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hγ) 0 h0
  have ht : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have h := hball ht
  rw [Set.mem_preimage, Set.mem_ofPred_eq, isConvexAt_cubicEpigraph_iff] at h
  simp only [γ, Matrix.cons_val_zero, Left.nonneg_neg_iff] at h
  linarith

end TauCeti
