/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Combinatorial
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.ChartedSpace

/-!
# An atlas from spherical vertex links

If every vertex link of a simplicial complex is a combinatorial `n`-sphere, its weak
polyhedron is a charted space over Euclidean `(n + 1)`-space. The atlas consists of the
open vertex stars, each identified with the unit ball by radial coordinates. These stars
cover every point of the polyhedron, not just its vertices.

The chart at a vertex sends that vertex to the origin; the radius of any point in the
chart is one minus its coordinate at that vertex. The source, target, and atlas formulas
are exposed so that compatibility of these charts with a structure groupoid can be
checked separately. `AbstractSimplicialComplex.sphereLinkChartedSpace` assembles these charts
using `AbstractSimplicialComplex.starChartedSpace`. This gives a topological atlas, without
asserting smooth or piecewise-linear compatibility. It needs no finiteness or countability of the
ambient vertex type or complex. In particular, two-point links give one-dimensional
charts.

The local homeomorphisms come from
`IsCombinatorialSphere.exists_homeomorph_openStar_ball`. Their extension to charts uses
Mathlib's `OpenPartialHomeomorph.lift_openEmbedding` and the open inclusion of a ball.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 2–3 (vertex-star coordinates and combinatorial manifolds).
-/

public section

noncomputable section

open Set Metric

namespace AbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] (K : AbstractSimplicialComplex ι) (v : ι) {n : ℕ}

/-- A spherical vertex link gives a chart from its open star onto the Euclidean unit ball.
The choice of link homeomorphism is made once in this chart. -/
def sphereLinkChart
    (h : PreAbstractSimplicialComplex.IsCombinatorialSphere
      (PreAbstractSimplicialComplex.link K.toPreAbstractSimplicialComplex {v}) n) :
    OpenPartialHomeomorph (Realization K) (EuclideanSpace ℝ (Fin (n + 1))) := by
  letI : Nonempty (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨⟨0, by simp⟩⟩
  let e := h.exists_homeomorph_openStar_ball.choose
  let b := isOpen_ball.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    (Subtype.val : ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → _)
  exact (e.toOpenPartialHomeomorph.trans b).lift_openEmbedding
    (K.isOpen_openStarRealization v).isOpenEmbedding_subtypeVal

variable (h : PreAbstractSimplicialComplex.IsCombinatorialSphere
  (PreAbstractSimplicialComplex.link K.toPreAbstractSimplicialComplex {v}) n)

/-- The source is exactly the open vertex star. -/
@[simp]
theorem sphereLinkChart_source : (K.sphereLinkChart v h).source = K.openStarRealization v := by
  ext x
  simp [sphereLinkChart]

/-- The target is exactly the Euclidean unit ball. -/
@[simp]
theorem sphereLinkChart_target :
    (K.sphereLinkChart v h).target = ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  ext x
  simp [sphereLinkChart]

/-- On the open star, chart radius is one minus the apex coordinate. -/
theorem norm_sphereLinkChart (x : K.openStarRealization v) :
    ‖K.sphereLinkChart v h x.1‖ = 1 - x.1.1 v := by
  unfold sphereLinkChart
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  simpa only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    Homeomorph.toOpenPartialHomeomorph_apply,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply] using
    h.exists_homeomorph_openStar_ball.choose_spec x

/-- The vertex maps to the origin of its own chart. -/
@[simp]
theorem sphereLinkChart_vertex : K.sphereLinkChart v h (vertex K v) = 0 := by
  apply norm_eq_zero.mp
  simpa [vertex_val] using K.norm_sphereLinkChart v h
    ⟨vertex K v, by simp [vertex_val]⟩

/-- The inverse chart maps the origin back to the vertex. -/
@[simp]
theorem sphereLinkChart_symm_zero : (K.sphereLinkChart v h).symm 0 = vertex K v := by
  rw [← K.sphereLinkChart_vertex v h, OpenPartialHomeomorph.left_inv]
  simp [vertex_val]

/-- In the inverse chart, the apex coordinate is one minus the Euclidean radius. -/
@[simp]
theorem sphereLinkChart_symm_apply_apex {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hy : y ∈ ball 0 1) : ((K.sphereLinkChart v h).symm y).1 v = 1 - ‖y‖ := by
  have hyt : y ∈ (K.sphereLinkChart v h).target := by simpa using hy
  have hxs : (K.sphereLinkChart v h).symm y ∈ K.openStarRealization v := by
    simpa using (K.sphereLinkChart v h).map_target hyt
  have hr := K.norm_sphereLinkChart v h ⟨(K.sphereLinkChart v h).symm y, hxs⟩
  rw [(K.sphereLinkChart v h).right_inv hyt] at hr
  linarith

variable (hs : ∀ v, PreAbstractSimplicialComplex.IsCombinatorialSphere
  (PreAbstractSimplicialComplex.link K.toPreAbstractSimplicialComplex {v}) n)

/-- Spherical links at every vertex give a Euclidean charted space on the existing
weak realization topology, with the open vertex stars as chart sources. -/
@[instance_reducible]
def sphereLinkChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (Realization K) :=
  K.starChartedSpace (fun v ↦ K.sphereLinkChart v (hs v))
    (fun v ↦ K.sphereLinkChart_source v (hs v))

/-- The spherical-link atlas consists exactly of the vertex-star charts. -/
@[simp]
theorem sphereLinkChartedSpace_atlas :
    @atlas (EuclideanSpace ℝ (Fin (n + 1))) _ (Realization K) _
      (K.sphereLinkChartedSpace hs) = range (fun v ↦ K.sphereLinkChart v (hs v)) := by
  unfold sphereLinkChartedSpace
  exact K.starChartedSpace_atlas _ _

/-- At a vertex, the preferred spherical-link chart is that vertex's own chart. -/
@[simp]
theorem sphereLinkChartedSpace_chartAt_vertex :
    @chartAt (EuclideanSpace ℝ (Fin (n + 1))) _ (Realization K) _
      (K.sphereLinkChartedSpace hs) (vertex K v) = K.sphereLinkChart v (hs v) := by
  unfold sphereLinkChartedSpace
  exact K.starChartedSpace_chartAt_vertex _ _ v

end AbstractSimplicialComplex
