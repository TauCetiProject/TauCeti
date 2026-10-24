/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.LocallyFlat.Segment
public import TauCeti.Geometry.Polygon.Simple
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# Polygonal knots are locally flat

A simple closed polygon in a real Hausdorff locally convex affine space admits flattening charts:
around each of its points some chart of the ambient space identifies it with a coordinate line
in the chart target. This file proves that the realization `TauCeti.SimplePolygon.realize` of a
simple polygon is a locally flat embedding of the circle, `TauCeti.IsLocallyFlat`, so that polygonal
knots in `ℝ³`, the polygonal presentation of knots (Burde and Zieschang, Definition 1.3), are among
the locally flat embeddings to which the topological notions of concordance and sliceness apply.

The flattening chart at a point `z` of the polygon comes from its local structure,
`Polygon.IsSimple.exists_mem_nhds_inter_boundary_eq`: near `z` the polygon is two segments from
`z`, to points `a` and `b`, meeting only at `z`, and two such segments are flat at `z`
(`TauCeti.exists_isSliceChart_of_inter_eq_union_affineSegment`). The complementary model of the
local flatness is any topological real module `F'` with `V ≃L[ℝ] ℝ × F'`, where `V` is the space of
translations; for a knot in `ℝ³` it is `ℝ²`.

That a polygonal curve is locally flat is special to curves. A piecewise-linear embedding of a
manifold of dimension at least two need not be locally flat in codimension two: the cone on a
knotted circle in `S³` is a piecewise-linear disc in the four-ball which is not locally flat at the
cone point. For a curve the link of a vertex is a pair of points in a sphere, which is never
knotted. The same local model gives the local flatness of piecewise-linear curves in charts,
`TauCeti.IsLocallyFlat.of_isPLOn_chartAt`.

## Main results

* `Polygon.IsSimple.exists_isSliceChart`: every point of a simple polygon has a chart with values in
  `ℝ × F'` identifying the polygon in its source with `ℝ × {0}` in its target.
* `TauCeti.SimplePolygon.isLocallyFlat_realize`: the realization of a simple polygon is locally
  flat, with complementary model `F'`.
* `TauCeti.SimplePolygon.isLocallyFlat_realize_euclideanSpace`: a polygonal knot in `ℝᵐ⁺¹` is
  locally flat, with complementary model `ℝᵐ`.

## References

* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, Definition 1.3 (tame knots).
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1, for stars and links of points of polyhedra.
-/

public section

open Set Topology

variable {V P F' : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V] [T2Space V]
  [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P]
  [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']

namespace Polygon

open TauCeti

/-- **A simple polygon is flat at each of its points.** In a real Hausdorff locally convex affine
space modelled on `V ≃L[ℝ] ℝ × F'`, every point of a simple polygon lies in the source of a chart
with values in `ℝ × F'` identifying the polygon in its source with the line `ℝ × {0}` in its
target. -/
theorem IsSimple.exists_isSliceChart {n : ℕ} [NeZero n] {poly : Polygon P n}
    (h : poly.IsSimple ℝ) (e : V ≃L[ℝ] ℝ × F') {z : P} (hz : z ∈ poly.boundary ℝ) :
    ∃ φ : OpenPartialHomeomorph P (ℝ × F'), z ∈ φ.source ∧
      IsSliceChart φ ((univ : Set ℝ) ×ˢ ({0} : Set F')) (poly.boundary ℝ) := by
  obtain ⟨a, b, ha, hb, hab, U, hU, hUeq⟩ := h.exists_mem_nhds_inter_boundary_eq hz
  exact exists_isSliceChart_of_inter_eq_union_affineSegment e ha hb hab hU hUeq

end Polygon

namespace TauCeti.SimplePolygon

/-- **A polygonal knot is locally flat.** The realization of a simple polygon in a real Hausdorff
locally convex affine space modelled on `V ≃L[ℝ] ℝ × F'` is a locally flat embedding of the circle,
with complementary model `F'`. -/
theorem isLocallyFlat_realize (p : SimplePolygon ℝ P) (e : V ≃L[ℝ] ℝ × F') :
    IsLocallyFlat ℝ F' p.realize := by
  refine isLocallyFlat_iff_isSliceEmbedding.2 ⟨p.isClosedEmbedding_realize.isEmbedding, fun x => ?_⟩
  rw [p.range_realize]
  exact p.isSimple.exists_isSliceChart e (p.range_realize ▸ mem_range_self x)

/-- A polygonal knot in `ℝᵐ⁺¹` is locally flat, with complementary model `ℝᵐ`; for `m = 2` these
are the polygonal knots in `ℝ³`. -/
theorem isLocallyFlat_realize_euclideanSpace {m : ℕ}
    (p : SimplePolygon ℝ (EuclideanSpace ℝ (Fin (m + 1)))) :
    IsLocallyFlat ℝ (EuclideanSpace ℝ (Fin m)) p.realize :=
  p.isLocallyFlat_realize <| (EuclideanSpace.equiv (Fin (m + 1)) ℝ).trans <|
    (Fin.consEquivL ℝ fun _ => ℝ).symm.trans <|
      (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (EuclideanSpace.equiv (Fin m) ℝ).symm

end TauCeti.SimplePolygon
