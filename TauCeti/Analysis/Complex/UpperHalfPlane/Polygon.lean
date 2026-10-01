/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Triangle.Convex

import TauCeti.Data.Fin.Basic

/-!
# Convex hyperbolic polygons

A convex hyperbolic polygon with `n ≥ 3` vertices is given by its vertices `v₀, …, vₙ₋₁ ∈ ℍ`,
listed counterclockwise: every vertex other than the endpoints of an edge lies strictly to the
left of the geodesic through that edge (`ConvexPolygon`). Its carrier is the intersection of the
closed left half-planes of its edges (`ConvexPolygon.carrier`), its sides are the geodesic
segments between consecutive vertices (`ConvexPolygon.side`, via
`UpperHalfPlane.geodesicSegment`), and its interior angle at a vertex is the angle between the
two sides at that vertex (`ConvexPolygon.interiorAngle`).

## Main results

* `ConvexPolygon.vertex_injective`: the vertices are distinct.
* `ConvexPolygon.isClosed_carrier`, `ConvexPolygon.vertex_mem_carrier`,
  `ConvexPolygon.side_subset_carrier`, `ConvexPolygon.geodesicSegment_subset_carrier`: the
  carrier is closed and convex and contains the vertices and the sides.
* `ConvexPolygon.interiorAngle_pos`, `ConvexPolygon.interiorAngle_lt_pi`: the interior angles
  lie strictly between `0` and `π`.
* `ConvexPolygon.smul`, `ConvexPolygon.carrier_smul`, `ConvexPolygon.interiorAngle_smul`:
  everything transforms naturally under `PSL(2, ℝ)`.
* `ConvexPolygon.carrier_three`, `ConvexPolygon.sum_interiorAngle_three`: a polygon with three
  vertices is the triangle on them, with the same angles.

The counterclockwise orientation is a convention of this file: a clockwise list of vertices is
not a `ConvexPolygon`.

## Source

Walkden, *Hyperbolic geometry* (MATH32051 lecture notes, Manchester 2019), §7.1 (polygons with
given vertices) and §14.2 (a convex hyperbolic polygon is an intersection of finitely many
half-planes).
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups Pointwise Real

namespace TauCeti.UpperHalfPlane

/-- A convex hyperbolic polygon with `n` vertices `vertex 0, …, vertex (n - 1)`, listed
counterclockwise: every vertex other than `vertex i` and `vertex (i + 1)` lies strictly to the
left of the geodesic from `vertex i` to `vertex (i + 1)`. -/
@[ext]
structure ConvexPolygon (n : ℕ) [NeZero n] where
  /-- The vertices, in counterclockwise order; indices are taken cyclically. -/
  vertex : Fin n → ℍ
  /-- A polygon has at least three vertices. -/
  three_le : 3 ≤ n
  /-- Every vertex off an edge lies strictly to the left of it. -/
  vertex_mem_leftHalfPlane : ∀ i j : Fin n, j ≠ i → j ≠ i + 1 →
    vertex j ∈ leftHalfPlane (geodesicBetween (vertex i) (vertex (i + 1)))

namespace ConvexPolygon

variable {n : ℕ} [NeZero n] (P : ConvexPolygon n)

/-- The carrier of a convex polygon: the intersection of the closed left half-planes of its
edges. -/
def carrier : Set ℍ :=
  ⋂ i, closure (leftHalfPlane (geodesicBetween (P.vertex i) (P.vertex (i + 1))))

/-- The side of a convex polygon from `vertex i` to `vertex (i + 1)`. -/
def side (i : Fin n) : Set ℍ :=
  geodesicSegment (P.vertex i) (P.vertex (i + 1))

-- The body of `side` is not `@[expose]`d, so downstream modules rewrite with this.
/-- The side of a convex polygon, unfolded: the geodesic segment from `vertex i` to
`vertex (i + 1)`. -/
theorem side_def (i : Fin n) : P.side i = geodesicSegment (P.vertex i) (P.vertex (i + 1)) := by
  rfl

/-- The interior angle of a convex polygon at `vertex i`: the angle between the sides to
`vertex (i - 1)` and to `vertex (i + 1)`. -/
def interiorAngle (i : Fin n) : ℝ :=
  UpperHalfPlane.interiorAngle (P.vertex i) (P.vertex (i - 1)) (P.vertex (i + 1))

-- The body of `interiorAngle` is not `@[expose]`d, so downstream modules rewrite with this.
/-- The interior angle of a convex polygon, unfolded. -/
theorem interiorAngle_def (i : Fin n) :
    P.interiorAngle i =
      UpperHalfPlane.interiorAngle (P.vertex i) (P.vertex (i - 1)) (P.vertex (i + 1)) := by
  rfl

/-- Membership in the carrier. -/
theorem mem_carrier_iff (z : ℍ) :
    z ∈ P.carrier ↔
      ∀ i, z ∈ closure (leftHalfPlane (geodesicBetween (P.vertex i) (P.vertex (i + 1)))) :=
  Set.mem_iInter

/-- A vertex off an edge is not on the geodesic through that edge. -/
theorem vertex_notMem_range_geodesicLine {i j : Fin n} (hi : j ≠ i) (hi' : j ≠ i + 1) :
    P.vertex j ∉ Set.range (geodesicLine (geodesicBetween (P.vertex i) (P.vertex (i + 1)))) :=
  Set.disjoint_left.1 (disjoint_leftHalfPlane_range_geodesicLine _)
    (P.vertex_mem_leftHalfPlane i j hi hi')

/-- The vertices of a convex polygon are distinct. -/
theorem vertex_injective : Function.Injective P.vertex := by
  intro i j hij
  by_contra hne
  by_cases hj : j = i + 1
  · subst hj
    refine P.vertex_notMem_range_geodesicLine
      (add_one_ne_self (Nat.le_of_succ_le P.three_le) i).symm
      (add_one_add_one_ne_self P.three_le i).symm ?_
    rw [hij]
    exact mem_range_geodesicLine_geodesicBetween_left _ _
  · refine P.vertex_notMem_range_geodesicLine (Ne.symm hne) hj ?_
    rw [← hij]
    exact mem_range_geodesicLine_geodesicBetween_left _ _

/-- A vertex differs from the next one. -/
theorem vertex_ne_vertex_add_one (i : Fin n) : P.vertex i ≠ P.vertex (i + 1) :=
  P.vertex_injective.ne (add_one_ne_self (Nat.le_of_succ_le P.three_le) i).symm

/-- A vertex differs from the previous one. -/
theorem vertex_ne_vertex_sub_one (i : Fin n) : P.vertex i ≠ P.vertex (i - 1) :=
  P.vertex_injective.ne (sub_one_ne_self (Nat.le_of_succ_le P.three_le) i).symm

/-- The carrier is closed. -/
theorem isClosed_carrier : IsClosed P.carrier :=
  isClosed_iInter fun _ ↦ isClosed_closure

/-- The carrier is measurable. -/
theorem measurableSet_carrier : MeasurableSet P.carrier :=
  P.isClosed_carrier.measurableSet

/-- The vertices lie in the carrier. -/
theorem vertex_mem_carrier (i : Fin n) : P.vertex i ∈ P.carrier := by
  rw [mem_carrier_iff]
  intro j
  rw [closure_leftHalfPlane]
  by_cases hj : i = j
  · subst hj
    exact Or.inr (mem_range_geodesicLine_geodesicBetween_left _ _)
  by_cases hj' : i = j + 1
  · subst hj'
    exact Or.inr (mem_range_geodesicLine_geodesicBetween_right _ _)
  · exact Or.inl (P.vertex_mem_leftHalfPlane j i hj hj')

/-- Every vertex lies in the closed left half-plane of every edge. -/
theorem vertex_mem_closure_leftHalfPlane (i j : Fin n) :
    P.vertex j ∈ closure (leftHalfPlane (geodesicBetween (P.vertex i) (P.vertex (i + 1)))) :=
  (P.mem_carrier_iff _).1 (P.vertex_mem_carrier j) i

/-- The carrier is convex. -/
theorem geodesicSegment_subset_carrier {z w : ℍ} (hz : z ∈ P.carrier) (hw : w ∈ P.carrier) :
    geodesicSegment z w ⊆ P.carrier :=
  Set.subset_iInter fun i ↦ geodesicSegment_subset_closure_leftHalfPlane
    ((P.mem_carrier_iff z).1 hz i) ((P.mem_carrier_iff w).1 hw i)

/-- The sides lie in the carrier. -/
theorem side_subset_carrier (i : Fin n) : P.side i ⊆ P.carrier :=
  P.geodesicSegment_subset_carrier (P.vertex_mem_carrier i) (P.vertex_mem_carrier (i + 1))

/-- `vertex (i + 1)` is not on the geodesic through `vertex i` and `vertex (i - 1)`. -/
private theorem vertex_add_one_notMem_range_geodesicLine (i : Fin n) :
    P.vertex (i + 1) ∉
      Set.range (geodesicLine (geodesicBetween (P.vertex i) (P.vertex (i - 1)))) := by
  rw [range_geodesicLine_geodesicBetween_swap (P.vertex (i - 1)) (P.vertex i)]
  have h := P.vertex_notMem_range_geodesicLine (add_one_ne_sub_one P.three_le i)
    (by rw [sub_add_cancel]; exact add_one_ne_self (Nat.le_of_succ_le P.three_le) i)
  rwa [sub_add_cancel] at h

/-- The interior angles are positive. -/
theorem interiorAngle_pos (i : Fin n) : 0 < P.interiorAngle i :=
  TauCeti.UpperHalfPlane.interiorAngle_pos (P.vertex_add_one_notMem_range_geodesicLine i)

/-- The interior angles are less than `π`. -/
theorem interiorAngle_lt_pi (i : Fin n) : P.interiorAngle i < π :=
  TauCeti.UpperHalfPlane.interiorAngle_lt_pi (P.vertex_add_one_notMem_range_geodesicLine i)

/-- The translate of a convex polygon by an element of `PSL(2, ℝ)`. -/
def smul (h : PSL(2, ℝ)) : ConvexPolygon n where
  vertex := fun i ↦ h • P.vertex i
  three_le := P.three_le
  vertex_mem_leftHalfPlane i j hij hij' := by
    rw [geodesicBetween_smul h (P.vertex_ne_vertex_add_one i), ← smul_leftHalfPlane]
    exact Set.smul_mem_smul_set (P.vertex_mem_leftHalfPlane i j hij hij')

/-- The vertices of the translate. -/
@[simp]
theorem vertex_smul (h : PSL(2, ℝ)) (i : Fin n) : (P.smul h).vertex i = h • P.vertex i := by
  rfl

/-- The carrier of the translate is the translate of the carrier. -/
theorem carrier_smul (h : PSL(2, ℝ)) : (P.smul h).carrier = h • P.carrier := by
  rw [carrier, carrier, Set.smul_set_iInter]
  refine Set.iInter_congr fun i ↦ ?_
  rw [vertex_smul, vertex_smul, geodesicBetween_smul h (P.vertex_ne_vertex_add_one i),
    ← smul_leftHalfPlane, closure_smul]

/-- The interior angles are invariant under `PSL(2, ℝ)`. -/
@[simp]
theorem interiorAngle_smul (h : PSL(2, ℝ)) (i : Fin n) :
    (P.smul h).interiorAngle i = P.interiorAngle i :=
  TauCeti.UpperHalfPlane.interiorAngle_smul h (P.vertex_ne_vertex_sub_one i)
    (P.vertex_ne_vertex_add_one i)

/-! ### Polygons with three vertices -/

/-- The carrier of a polygon with three vertices is the triangle on them. -/
theorem carrier_three (P : ConvexPolygon 3) :
    P.carrier = triangle (P.vertex 0) (P.vertex 1) (P.vertex 2) := by
  have h0 : closedSide (P.vertex 0) (P.vertex 1) (P.vertex 2) =
      closure (leftHalfPlane (geodesicBetween (P.vertex 0) (P.vertex 1))) :=
    closedSide_eq_closure_leftHalfPlane_of_mem
      (P.vertex_mem_leftHalfPlane 0 2 (by decide) (by decide))
  have h1 : closedSide (P.vertex 1) (P.vertex 2) (P.vertex 0) =
      closure (leftHalfPlane (geodesicBetween (P.vertex 1) (P.vertex 2))) :=
    closedSide_eq_closure_leftHalfPlane_of_mem
      (P.vertex_mem_leftHalfPlane 1 0 (by decide) (by decide))
  have h2 : closedSide (P.vertex 2) (P.vertex 0) (P.vertex 1) =
      closure (leftHalfPlane (geodesicBetween (P.vertex 2) (P.vertex 0))) :=
    closedSide_eq_closure_leftHalfPlane_of_mem
      (P.vertex_mem_leftHalfPlane 2 1 (by decide) (by decide))
  ext z
  rw [triangle_def, h0, h1, h2, mem_carrier_iff, Set.mem_inter_iff, Set.mem_inter_iff]
  refine ⟨fun hz ↦ ⟨⟨hz 0, hz 1⟩, hz 2⟩, fun hz i ↦ ?_⟩
  fin_cases i
  exacts [hz.1.1, hz.1.2, hz.2]

/-- The interior angles of a polygon with three vertices are the angles of the triangle on them,
read counterclockwise from each vertex. -/
theorem interiorAngle_three (P : ConvexPolygon 3) (i : Fin 3) :
    P.interiorAngle i =
      UpperHalfPlane.interiorAngle (P.vertex i) (P.vertex (i + 1)) (P.vertex (i + 2)) := by
  have h : i - 1 = i + 2 := by revert i; decide
  rw [interiorAngle_def, h, interiorAngle_comm]

/-- The sum of the interior angles of a polygon with three vertices is the angle sum of the
triangle on them. -/
theorem sum_interiorAngle_three (P : ConvexPolygon 3) :
    ∑ i, P.interiorAngle i =
      UpperHalfPlane.interiorAngle (P.vertex 0) (P.vertex 1) (P.vertex 2) +
        UpperHalfPlane.interiorAngle (P.vertex 1) (P.vertex 2) (P.vertex 0) +
        UpperHalfPlane.interiorAngle (P.vertex 2) (P.vertex 0) (P.vertex 1) := by
  simp only [Fin.sum_univ_three, interiorAngle_three, Fin.isValue, Fin.reduceAdd]

end ConvexPolygon

end TauCeti.UpperHalfPlane
