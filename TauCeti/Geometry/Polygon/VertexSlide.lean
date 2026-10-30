/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Polygon.DeltaMove
public import TauCeti.Geometry.Polygon.Subdivision
public import TauCeti.Topology.Homotopy.Isotopy.Basic

/-!
# Sliding a vertex across a triangle move

A Δ-move replaces one edge of a polygon by two sides of a triangle meeting the other
edges only at the old endpoints. Start by subdividing the edge at any interior point, then slide
the new vertex along
the segment to the apex of the triangle. Every intermediate polygon is simple. Its circle
parametrization varies continuously, giving an explicit isotopy.

This is the local motion underlying the geometric interpretation of polygonal moves. The
isotopy here is a motion of the polygon; extending it to an ambient isotopy requires an
additional extension theorem.

## References

* G. Burde, H. Zieschang, *Knots*, second edition, Chapter 1 §B, Definitions 1.6 and 1.7
  and Proposition 1.10, for triangle moves and their geometric interpretation.
-/

public section

open Set Function AffineMap Topology

namespace Polygon

variable {R V : Type*} {n : ℕ}

section Field

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V]
  {poly : Polygon V n} {i : Fin n} {c : V}

/-- During a triangle move, sliding the inserted vertex from an interior point of the old edge
to the apex preserves simplicity, including the initially collinear subdivision. -/
theorem IsDeltaMove.isSimple_insertVertex_lineMap (h : poly.IsDeltaMove R i c)
    (hp : poly.IsSimple R) {s t : R} (hs : s ∈ Ioo (0 : R) 1) (ht : t ∈ Icc (0 : R) 1) :
    (poly.insertVertex i (lineMap (poly.edgePath R i s) c t)).IsSimple R := by
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · subst t
    simpa only [lineMap_apply_zero] using hp.insertVertex_edgePath i hs
  have hd : poly.edgePath R i s ∈ affineSpan R {poly i, poly (finRotate n i)} :=
    AffineMap.lineMap_mem_affineSpan_pair s _ _
  have hc : c ∉ affineSpan R {poly i, poly (finRotate n i)} := by
    intro hc
    have hc' : c ∈ affineSpan R
        ((![poly i, poly (finRotate n i), c] : Fin 3 → V) '' {0, 1}) := by
      simpa using hc
    have := (h.affineIndependent.mem_affineSpan_iff 2 {0, 1}).mp hc'
    norm_num at this
  have hline : lineMap (poly.edgePath R i s) c t ∉
      affineSpan R {poly i, poly (finRotate n i)} := by
    intro hm
    apply hc
    have hv := (AffineSubspace.vsub_right_mem_direction_iff_mem hd _).mpr hm
    rw [lineMap_vsub_left, Submodule.smul_mem_iff _ ht0.ne'] at hv
    exact (AffineSubspace.vsub_right_mem_direction_iff_mem hd c).mp hv
  have hconv : Convex R h.triangle.closedInterior := by
    rw [← Affine.Simplex.convexHull_eq_closedInterior]
    exact convex_convexHull _ _
  have hcT : c ∈ h.triangle.closedInterior := by
    simpa using h.triangle.point_mem_closedInterior 2
  exact (h.of_mem_closedInterior
    (hconv.lineMap_mem (h.edgeSet_subset_closedInterior ⟨s, ⟨hs.1.le, hs.2.le⟩, rfl⟩)
      hcT ht) hline).isSimple_insertVertex hp

end Field

section Topology

variable [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [T2Space V] {poly : Polygon V n} {i : Fin n} {c : V}

/-- The explicit isotopy sliding a subdividing vertex along a Δ-move triangle to its apex.
The source circle has one unit of parameter time per edge of the subdivided polygon. -/
noncomputable def IsDeltaMove.vertexSlide (h : poly.IsDeltaMove ℝ i c)
    (hp : poly.IsSimple ℝ) (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
    TauCeti.Isotopy
      ⟨(poly.insertVertex i (poly.edgePath ℝ i s)).boundaryParamCircle,
        (poly.insertVertex i (poly.edgePath ℝ i s)).continuous_boundaryParamCircle⟩
      ⟨(poly.insertVertex i c).boundaryParamCircle,
        (poly.insertVertex i c).continuous_boundaryParamCircle⟩ where
  toFun p :=
    (poly.insertVertex i (lineMap (poly.edgePath ℝ i s) c (p.1 : ℝ))).boundaryParamCircle p.2
  continuous_toFun := by
    simp_rw [boundaryParamCircle_insertVertex_lineMap]
    exact ((poly.insertVertex i (poly.edgePath ℝ i s)).continuous_boundaryParamCircle.comp
      continuous_snd).lineMap
      ((poly.insertVertex i c).continuous_boundaryParamCircle.comp continuous_snd)
      (continuous_subtype_val.comp continuous_fst)
  map_zero_left := by intro z; simp
  map_one_left := by intro z; simp
  prop' t := IsClosedEmbedding.isEmbedding
    ((h.isSimple_insertVertex_lineMap hp hs t.property).isClosedEmbedding_boundaryParamCircle)

/-- At time `t` the vertex slide is the boundary parametrization of the polygon with the
inserted vertex at the corresponding point of the segment to the apex. -/
@[simp]
theorem IsDeltaMove.vertexSlide_apply (h : poly.IsDeltaMove ℝ i c)
    (hp : poly.IsSimple ℝ) (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1)
    (t : unitInterval) (z : AddCircle ((n + 1 : ℕ) : ℝ)) :
    h.vertexSlide hp s hs (t, z) =
      (poly.insertVertex i (lineMap (poly.edgePath ℝ i s) c (t : ℝ))).boundaryParamCircle z :=
  (rfl)

end Topology

end Polygon
