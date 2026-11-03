/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Polygon.Subdivision
public import TauCeti.KnotTheory.GaussCode.Polygon.Basic

/-!
# A Δ-move away from the crossings does not change the Gauss code

A Δ-move (`Polygon.IsDeltaMove`) replaces edge `i` of a polygonal knot `poly`, from vertex `i` to
the next vertex, by the two other sides of a triangle through a new vertex `c`: the polygon becomes
`poly.insertVertex i c`. In the argument that diagrams of combinatorially equivalent polygonal
knots are related by Reidemeister moves (Lickorish, Chapter 1; Burde–Zieschang, Chapter 1), the
Δ-moves are cut into small ones, and the effect of each on the diagram is read off from how the
projection of its triangle meets the rest of the diagram. When no side of the triangle passes over
or under another strand, the diagram only changes by a planar isotopy, and the Gauss code is
unchanged.

This file proves that case (`Polygon.gaussCode_insertVertex_of_disjoint`): if, for the projection
along `d`, edge `i` of `poly` contains no double point, and the two sides through `c` contain no
double point of `poly.insertVertex i c`, then the two Gauss codes are equal whenever the projection
is regular for both polygons. The Δ-move condition itself is not needed: the hypotheses only
concern the edges that change.

Under these hypotheses both polygons have the same double points
(`Polygon.doublePoints_insertVertex_of_disjoint`), lying on the edges they share, and away from
edge `i` the two traversals differ by an increasing change of time running along the same edges
(`Polygon.exists_strictMono_boundaryParam_insertVertex`). So the crossing times correspond in
order, at the same points and along edges with the same directions, and
`Polygon.gaussCode_eq_of_strictMono` applies.

## Main results

* `Polygon.gaussCode_insertVertex_of_disjoint`: a Δ-move whose moved edges carry no crossings does
  not change the Gauss code of a regular projection.

## References

* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, for Δ-moves and the Reidemeister moves they induce on regular projections.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1,
  pp. 2–4, for triangle moves and their effect on link diagrams.
-/

public section

open Set Module TauCeti

namespace Polygon

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P] {n : ℕ} [NeZero n]
  {poly : Polygon P n} {p₀ : P} {d : V}

/-- **A Δ-move away from the crossings does not change the Gauss code.** Let `poly` be a simple
polygon in a three-dimensional real affine space, and `poly.insertVertex i c` the simple polygon in
which edge `i` is replaced by the segments from vertex `i` to `c` and from `c` to the next vertex.
Suppose that the projection along `d` is regular for both polygons, that edge `i` of `poly`
contains no double point of `poly`, and that the two new segments contain no double point of
`poly.insertVertex i c`. Then the two polygons have the same Gauss code. The numbers of crossings
agree, and the codes are compared together with them. -/
theorem gaussCode_insertVertex_of_disjoint (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {i : Fin n} {c : P}
    (hs' : (poly.insertVertex i c).IsSimple ℝ)
    (hπ' : (poly.insertVertex i c).IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (hu : Disjoint (poly.edgeSet ℝ i) (poly.doublePoints ℝ (projAlong ℝ p₀ d)))
    (hvw : Disjoint (affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i)))
      ((poly.insertVertex i c).doublePoints ℝ (projAlong ℝ p₀ d)))
    (b : Basis (Fin 3) ℝ V) :
    (⟨_, gaussCode hs' hπ' b⟩ : Σ m, BasedOrientedGaussCode m) = ⟨_, gaussCode hs hπ b⟩ := by
  obtain ⟨φ, hφ, hφt⟩ := exists_strictMono_boundaryParam_insertVertex poly i c
  refine gaussCode_eq_of_strictMono b hs hπ hs' hπ' (doublePoints_insertVertex_of_disjoint hu hvw)
    hφ fun t ht ↦ ?_
  obtain ⟨ht₁, ht₂⟩ := mem_crossingTimes.1 ht
  -- A crossing time is not on edge `i`, which carries no double point.
  have hti : edgeIndexAt n t ≠ i := by
    intro hti
    refine disjoint_left.1 hu ?_ ht₂
    rw [boundaryParam_eq_edgePath_edgeIndexAt, hti]
    exact ⟨Int.fract t, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, rfl⟩
  obtain ⟨h₁, h₂, h₃⟩ := hφt t ht₁ hti
  exact ⟨h₁, h₂, 1, one_pos, by rw [h₃, one_smul]⟩

end Polygon
