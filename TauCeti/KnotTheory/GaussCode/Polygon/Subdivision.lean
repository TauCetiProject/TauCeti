/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Polygon.Subdivision
public import TauCeti.KnotTheory.GaussCode.Polygon.Basic

/-!
# Subdividing an edge does not change the Gauss code of a polygonal knot

Subdividing an edge of a polygonal knot `poly` at one of its points `c`,
`poly.insertVertex i c`, is the degenerate Δ-move
`TauCeti.SimplePolygon.IsElementaryMove.subdivide`. It does not move the knot, so it should not
change its diagram. This file proves that it does not change the based oriented Gauss code read
off from a regular projection (`Polygon.gaussCode`): when the projection along `d` is regular both
before and after subdividing, the two Gauss codes are equal
(`Polygon.gaussCode_insertVertex`). The projection after subdividing is regular exactly when it
is regular before and `c` is not a double point
(`Polygon.isRegularProjection_insertVertex_edgePath_iff`).

The number of crossings of `Polygon.gaussCode` is computed from the double points of the
polygon, so the two codes have equal but not definitionally equal numbers of crossings, and the
equality is stated for the codes paired with their numbers of crossings.

The proof compares the two traversals through the increasing change of time
`Polygon.exists_strictMono_boundaryParam_insertVertex_edgePath`. It carries the crossing times of
`poly` onto those of the subdivided polygon in increasing order, through the same points and along
edges with the same directions up to positive factors, so `Polygon.gaussCode_eq_of_strictMono`
applies.

## Main results

* `Polygon.gaussCode_insertVertex`: subdividing an edge of a polygonal knot does not change the
  Gauss code of a regular projection.

## References

* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, for Δ-moves and regular projections of polygonal knots.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1, for
  knot diagrams obtained from projections in general position.
-/

public section

open Set Function AffineMap Module TauCeti

namespace Polygon

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P] {n : ℕ} [NeZero n]
  {poly : Polygon P n} {p₀ : P} {d : V}

/-- **Subdividing an edge does not change the Gauss code.** Let `poly` be a simple polygon in a
three-dimensional real affine space, and `c` a point of its edge `i` such that the polygon
`poly.insertVertex i c`, with `c` inserted as a new vertex after vertex `i`, is still simple. If
the projection along `d` is regular for both polygons, then their Gauss codes are equal. The
numbers of crossings agree, and the codes are compared together with them. -/
theorem gaussCode_insertVertex (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {i : Fin n} {c : P}
    (hc : c ∈ poly.edgeSet ℝ i) (hs' : (poly.insertVertex i c).IsSimple ℝ)
    (hπ' : (poly.insertVertex i c).IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (b : Basis (Fin 3) ℝ V) :
    (⟨_, gaussCode hs' hπ' b⟩ : Σ m, BasedOrientedGaussCode m) = ⟨_, gaussCode hs hπ b⟩ := by
  rw [edgeSet_eq_image_edgePath] at hc
  obtain ⟨s, hs01, rfl⟩ := hc
  obtain ⟨φ, hφ, hφt⟩ := exists_strictMono_boundaryParam_insertVertex_edgePath poly i
    (mem_Ioo_of_hasNondegenerateEdges_insertVertex_edgePath poly i hs01 hs'.hasNondegenerateEdges)
  exact gaussCode_eq_of_strictMono b hs hπ hs' hπ'
    (doublePoints_insertVertex_edgePath poly i _ hs01) hφ fun t ht ↦
      hφt t (crossingTimes_subset_Ico ht)

end Polygon
