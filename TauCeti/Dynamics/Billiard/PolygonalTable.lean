/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Polygon.Simple
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Topology.FilledHull
import Mathlib.Analysis.Convex.Between
import TauCeti.Analysis.Complex.PlaneSeparation.Inside
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.Normed.Module.FilledHull

/-!
# Polygonal billiard tables

A *polygonal billiard table* is a compact set `P ⊆ ℂ` with connected nonempty interior, equal to
the closure of its interior, whose frontier is the union of the boundaries of finitely many simple
polygons `P₀, …, P_h` with pairwise disjoint boundaries. One of these polygons is the outer
boundary and the others bound the `h` polygonal holes (Chernov and Markarian, Chapter 2;
Boldrighini, Keane and Marchetti, Section 2). The vertices of the table are the vertices of the
polygons, and its sides are their edges; a vertex may be flat (of angle `π`), since a simple polygon
may have consecutive collinear edges.

The sides are indexed by the finite type `TauCeti.PolygonalTable.Side`: a side is an edge `j` of
the boundary polygon `i`. Its relative interior is the open segment between its endpoints. The
relative interiors of distinct sides are disjoint, and every point of the frontier of the table
which is not a vertex lies in the relative interior of exactly one side: this is the point set on
which the reflection of the billiard flow in the side is defined.

## Main definitions

* `TauCeti.PolygonalTable`: a polygonal billiard table, possibly with polygonal holes.
* `TauCeti.PolygonalTable.vertexSet`: the set of vertices of the table.
* `TauCeti.PolygonalTable.Side`, `TauCeti.PolygonalTable.side`: the sides of the table.
* `TauCeti.PolygonalTable.sideInterior`: the relative interior of a side.
* `TauCeti.PolygonalTable.Side.direction`: the unit direction of a side.
* `TauCeti.PolygonalTable.ofSimplePolygon`: the table without holes bounded by a simple polygon.
* `TauCeti.PolygonalTable.ofSimplePolygonSideEquiv`: the sides of `ofSimplePolygon p` are indexed
  by the edges of `p`.

## Main results

* `TauCeti.PolygonalTable.frontier_eq_iUnion_side`: the frontier of the table is the union of its
  sides.
* `TauCeti.PolygonalTable.finite_vertexSet`: a table has finitely many vertices.
* `TauCeti.PolygonalTable.disjoint_sideInterior`, `TauCeti.PolygonalTable.eq_of_mem_sideInterior`:
  the relative interiors of distinct sides are disjoint.
* `TauCeti.PolygonalTable.sideInterior_eq_side_sdiff_vertexSet`: the relative interior of a side
  is the side minus the vertices.
* `TauCeti.PolygonalTable.existsUnique_mem_sideInterior_iff`: a point lies in the relative interior
  of exactly one side if and only if it lies in the frontier off the vertices.

## References

* N. Chernov, R. Markarian, *Chaotic Billiards*, Mathematical Surveys and Monographs 127, AMS
  (2006), Chapter 2.
* C. Boldrighini, M. Keane, F. Marchetti, *Billiards in polygons*, Ann. Probab. 6 (1978),
  532–540, Section 2.
-/

public section

open Set Topology

namespace TauCeti

/-- A **polygonal billiard table**, possibly with polygonal holes: a compact set `P ⊆ ℂ` with
connected nonempty interior and `P = closure (interior P)`, whose frontier is the union of the
boundaries of finitely many simple polygons `P₀, …, P_h` with pairwise disjoint boundaries. One of
the polygons is the outer boundary of the table and the other `h` bound its holes. -/
structure PolygonalTable where
  /-- The number `h` of holes; the frontier has `h + 1` components. -/
  numHoles : ℕ
  /-- The simple polygons bounding the table. -/
  component : Fin (numHoles + 1) → SimplePolygon ℝ ℂ
  /-- The boundaries of distinct polygons are disjoint. -/
  pairwise_disjoint_boundary :
    Pairwise fun i j => Disjoint ((component i).toPolygon.boundary ℝ)
      ((component j).toPolygon.boundary ℝ)
  /-- The table, as a set of points of the plane. -/
  carrier : Set ℂ
  /-- The table is compact. -/
  isCompact_carrier : IsCompact carrier
  /-- The interior of the table is connected and nonempty. -/
  isConnected_interior : IsConnected (interior carrier)
  /-- The table is the closure of its interior. -/
  closure_interior : closure (interior carrier) = carrier
  /-- The frontier of the table is the union of the boundaries of the polygons. -/
  frontier_carrier : frontier carrier = ⋃ i, (component i).toPolygon.boundary ℝ

namespace PolygonalTable

variable (T : PolygonalTable)

/-- The **vertices** of a polygonal table: the vertices of its boundary polygons. -/
def vertexSet : Set ℂ :=
  ⋃ i, range (T.component i).toPolygon.vertices

/-- The index type of the **sides** of a polygonal table: a side is an edge `j` of the boundary
polygon `i`. -/
abbrev Side : Type := Σ i : Fin (T.numHoles + 1), Fin (T.component i).numVertices

variable {T}

/-- The starting vertex of a side. -/
def Side.start (s : T.Side) : ℂ :=
  (T.component s.1).toPolygon s.2

/-- The end vertex of a side, the start of the next side of the same boundary polygon. -/
def Side.finish (s : T.Side) : ℂ :=
  (T.component s.1).toPolygon (finRotate _ s.2)

/-- The starting vertex of the side `⟨i, j⟩` is vertex `j` of the boundary polygon `i`. -/
@[simp]
theorem Side.start_mk (i : Fin (T.numHoles + 1)) (j : Fin (T.component i).numVertices) :
    Side.start (⟨i, j⟩ : T.Side) = (T.component i).toPolygon j :=
  (rfl)

/-- The end vertex of the side `⟨i, j⟩` is the vertex after `j` of the boundary polygon `i`. -/
@[simp]
theorem Side.finish_mk (i : Fin (T.numHoles + 1)) (j : Fin (T.component i).numVertices) :
    Side.finish (⟨i, j⟩ : T.Side) = (T.component i).toPolygon (finRotate _ j) :=
  (rfl)

variable (T)

/-- The **side** `s` of a polygonal table, as a set of points: the segment between its endpoints,
an edge of one of the boundary polygons. -/
noncomputable def side (s : T.Side) : Set ℂ :=
  (T.component s.1).toPolygon.edgeSet ℝ s.2

/-- The **relative interior** of the side `s`: the open segment between its endpoints. -/
noncomputable def sideInterior (s : T.Side) : Set ℂ :=
  openSegment ℝ s.start s.finish

/-- A side is the corresponding edge of its boundary polygon. -/
theorem side_def (s : T.Side) : T.side s = (T.component s.1).toPolygon.edgeSet ℝ s.2 :=
  (rfl)

/-- The relative interior of a side is the open segment between its endpoints. -/
theorem sideInterior_eq_openSegment (s : T.Side) :
    T.sideInterior s = openSegment ℝ s.start s.finish :=
  (rfl)

/-- A side is the segment between its endpoints. -/
theorem side_eq_segment (s : T.Side) : T.side s = segment ℝ s.start s.finish :=
  affineSegment_eq_segment ℝ _ _

/-- The relative interior of a side lies in the side. -/
theorem sideInterior_subset_side (s : T.Side) : T.sideInterior s ⊆ T.side s := by
  rw [side_eq_segment]
  exact openSegment_subset_segment ℝ _ _

/-- The endpoints of a side are distinct. -/
@[simp]
theorem Side.start_ne_finish (s : T.Side) : s.start ≠ s.finish :=
  (T.component s.1).isSimple.hasNondegenerateEdges s.2

variable {T}

/-- The start of a side lies in the side. -/
@[simp]
theorem Side.start_mem_side (s : T.Side) : s.start ∈ T.side s := by
  rw [side_eq_segment]
  exact left_mem_segment ℝ _ _

/-- The end of a side lies in the side. -/
@[simp]
theorem Side.finish_mem_side (s : T.Side) : s.finish ∈ T.side s := by
  rw [side_eq_segment]
  exact right_mem_segment ℝ _ _

/-- The start of a side does not lie in its relative interior. -/
@[simp]
theorem Side.start_notMem_sideInterior (s : T.Side) : s.start ∉ T.sideInterior s := by
  rw [sideInterior_eq_openSegment, left_mem_openSegment_iff]
  exact s.start_ne_finish

/-- The end of a side does not lie in its relative interior. -/
@[simp]
theorem Side.finish_notMem_sideInterior (s : T.Side) : s.finish ∉ T.sideInterior s := by
  rw [sideInterior_eq_openSegment, right_mem_openSegment_iff]
  exact s.start_ne_finish

/-- The unit direction `exp(i arg(b − a))` of a side from its start `a` to its finish `b`. -/
noncomputable def Side.direction (s : T.Side) : Circle :=
  Circle.exp (Complex.arg (s.finish - s.start))

theorem Side.direction_def (s : T.Side) :
    s.direction = Circle.exp (Complex.arg (s.finish - s.start)) :=
  (rfl)

/-- The unit direction of a side is the side vector `b − a` divided by its length. -/
theorem Side.coe_direction (s : T.Side) :
    (s.direction : ℂ) = (s.finish - s.start) / ‖s.finish - s.start‖ := by
  rw [direction_def, Circle.coe_exp, Complex.exp_arg_mul_I (sub_ne_zero.2 s.start_ne_finish.symm)]

variable (T)

/-- A table is closed. -/
theorem isClosed_carrier : IsClosed T.carrier :=
  T.isCompact_carrier.isClosed

/-- A table has nonempty interior. -/
theorem nonempty_interior : (interior T.carrier).Nonempty :=
  T.isConnected_interior.nonempty

/-- The interior of a table is the table minus the boundaries of its polygons. -/
theorem interior_carrier :
    interior T.carrier = T.carrier \ ⋃ i, (T.component i).toPolygon.boundary ℝ := by
  rw [← T.frontier_carrier, self_sdiff_frontier]

/-- **The frontier of a table is the union of its sides.** -/
theorem frontier_eq_iUnion_side : frontier T.carrier = ⋃ s, T.side s := by
  rw [T.frontier_carrier, iUnion_sigma]
  rfl

/-- Every side lies in the frontier of the table. -/
theorem side_subset_frontier (s : T.Side) : T.side s ⊆ frontier T.carrier :=
  T.frontier_eq_iUnion_side ▸ subset_iUnion T.side s

/-- Every side lies in the table. -/
theorem side_subset_carrier (s : T.Side) : T.side s ⊆ T.carrier :=
  (T.side_subset_frontier s).trans T.isClosed_carrier.frontier_subset

/-- The relative interior of a side lies in the frontier of the table. -/
theorem sideInterior_subset_frontier (s : T.Side) : T.sideInterior s ⊆ frontier T.carrier :=
  (T.sideInterior_subset_side s).trans (T.side_subset_frontier s)

/-- The relative interior of a side lies in the table. -/
theorem sideInterior_subset_carrier (s : T.Side) : T.sideInterior s ⊆ T.carrier :=
  (T.sideInterior_subset_side s).trans (T.side_subset_carrier s)

/-- The start of a side is a vertex. -/
@[simp]
theorem Side.start_mem_vertexSet (s : T.Side) : s.start ∈ T.vertexSet :=
  mem_iUnion.2 ⟨s.1, mem_range_self _⟩

/-- The end of a side is a vertex. -/
@[simp]
theorem Side.finish_mem_vertexSet (s : T.Side) : s.finish ∈ T.vertexSet :=
  mem_iUnion.2 ⟨s.1, mem_range_self _⟩

/-- The vertices of a table are the starts of its sides. -/
theorem mem_vertexSet_iff {x : ℂ} : x ∈ T.vertexSet ↔ ∃ s : T.Side, s.start = x := by
  refine ⟨fun hx => ?_, fun ⟨s, hs⟩ => hs ▸ s.start_mem_vertexSet⟩
  obtain ⟨i, j, rfl⟩ := mem_iUnion.1 hx
  exact ⟨⟨i, j⟩, rfl⟩

/-- Every vertex lies in the frontier of the table. -/
theorem vertexSet_subset_frontier : T.vertexSet ⊆ frontier T.carrier := by
  intro x hx
  obtain ⟨s, rfl⟩ := T.mem_vertexSet_iff.1 hx
  exact T.side_subset_frontier s (T.side_eq_segment s ▸ left_mem_segment ℝ _ _)

/-- A polygonal table has finitely many vertices. -/
theorem finite_vertexSet : T.vertexSet.Finite :=
  finite_iUnion fun _ => finite_range _

/-- **The relative interiors of distinct sides of a table are disjoint.** -/
theorem disjoint_sideInterior {s t : T.Side} (hst : s ≠ t) :
    Disjoint (T.sideInterior s) (T.sideInterior t) := by
  obtain ⟨i, j⟩ := s
  obtain ⟨i', j'⟩ := t
  rw [Set.disjoint_left]
  intro x hxs hxt
  have hs := T.sideInterior_subset_side _ hxs
  have ht := T.sideInterior_subset_side _ hxt
  rw [sideInterior_eq_openSegment] at hxs hxt
  by_cases hii : i = i'
  · subst hii
    have hjj : j ≠ j' := fun h => hst (h ▸ rfl)
    -- The common point is the common vertex, the end of one of the two sides, which does not
    -- lie in the relative interior of that side.
    rcases (T.component i).isSimple.eq_vertex_of_mem_edgeSet hjj hs ht with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Side.start_ne_finish (T := T) ⟨i, j⟩ (right_mem_openSegment_iff.1 hxs)
    · exact Side.start_ne_finish (T := T) ⟨i, j'⟩ (right_mem_openSegment_iff.1 hxt)
  · exact Set.disjoint_left.1 (T.pairwise_disjoint_boundary hii)
      (mem_iUnion.2 ⟨j, hs⟩) (mem_iUnion.2 ⟨j', ht⟩)

/-- A point lies in the relative interior of at most one side of a table. -/
theorem eq_of_mem_sideInterior {x : ℂ} {s t : T.Side} (hs : x ∈ T.sideInterior s)
    (ht : x ∈ T.sideInterior t) : s = t :=
  by_contra fun hst => Set.disjoint_left.1 (T.disjoint_sideInterior hst) hs ht

/-- The relative interior of a side contains no vertex of the table. -/
theorem disjoint_sideInterior_vertexSet (s : T.Side) : Disjoint (T.sideInterior s) T.vertexSet := by
  obtain ⟨i, j⟩ := s
  rw [Set.disjoint_right]
  intro x hx hxs
  obtain ⟨i', k, rfl⟩ := mem_iUnion.1 hx
  have hks := T.sideInterior_subset_side _ hxs
  by_cases hii : i' = i
  · subst hii
    -- A vertex on the side `⟨i', j⟩` of its own boundary polygon is one of its endpoints.
    by_cases hkj : k = j
    · subst hkj
      exact Side.start_notMem_sideInterior _ hxs
    by_cases hkj' : k = finRotate _ j
    · subst hkj'
      exact Side.finish_notMem_sideInterior (T := T) ⟨i', j⟩ hxs
    exact (T.component i').isSimple.apply_notMem_edgeSet hkj hkj' hks
  · exact Set.disjoint_left.1 (T.pairwise_disjoint_boundary hii)
      (mem_iUnion.2 ⟨k, (T.component i').toPolygon.apply_mem_edgeSet_self ℝ k⟩)
      (mem_iUnion.2 ⟨j, hks⟩)

/-- The relative interior of a side is the side minus the vertices of the table. -/
theorem sideInterior_eq_side_sdiff_vertexSet (s : T.Side) :
    T.sideInterior s = T.side s \ T.vertexSet := by
  refine Subset.antisymm (fun x hx => ⟨T.sideInterior_subset_side s hx,
    Set.disjoint_left.1 (T.disjoint_sideInterior_vertexSet s) hx⟩) ?_
  rintro x ⟨hx, hxv⟩
  rw [side_eq_segment] at hx
  exact mem_openSegment_of_ne_left_right (fun h => hxv (h ▸ s.start_mem_vertexSet))
    (fun h => hxv (h ▸ s.finish_mem_vertexSet)) hx

/-- The relative interiors of the sides cover the frontier of the table off its vertices. -/
theorem iUnion_sideInterior : ⋃ s, T.sideInterior s = frontier T.carrier \ T.vertexSet := by
  simp_rw [sideInterior_eq_side_sdiff_vertexSet, ← iUnion_sdiff, ← frontier_eq_iUnion_side]

/-- **Every point of the frontier of a table off its vertices lies in the relative interior of
exactly one side.** -/
theorem existsUnique_mem_sideInterior {x : ℂ} (hx : x ∈ frontier T.carrier)
    (hxv : x ∉ T.vertexSet) : ∃! s : T.Side, x ∈ T.sideInterior s := by
  have hx' : x ∈ ⋃ s, T.sideInterior s := T.iUnion_sideInterior ▸ ⟨hx, hxv⟩
  obtain ⟨s, hs⟩ := mem_iUnion.1 hx'
  exact ⟨s, hs, fun t ht => T.eq_of_mem_sideInterior ht hs⟩

/-- **A point lies in the relative interior of exactly one side of a table if and only if it lies
in the frontier of the table off its vertices.** -/
theorem existsUnique_mem_sideInterior_iff {x : ℂ} :
    (∃! s : T.Side, x ∈ T.sideInterior s) ↔ x ∈ frontier T.carrier \ T.vertexSet := by
  refine ⟨fun ⟨s, hs, _⟩ => ?_, fun hx => T.existsUnique_mem_sideInterior hx.1 hx.2⟩
  rw [← iUnion_sideInterior]
  exact mem_iUnion_of_mem s hs

/-- **A simple polygon bounds a table without holes**: the filled region of its boundary, which is a
Jordan curve. -/
noncomputable def ofSimplePolygon (p : SimplePolygon ℝ ℂ) : PolygonalTable where
  numHoles := 0
  component _ := p
  pairwise_disjoint_boundary i j hij := (hij (Subsingleton.elim (α := Fin 1) i j)).elim
  carrier := filledHull (p.toPolygon.boundary ℝ)
  isCompact_carrier := by
    have hC := p.isSimple.isJordanCurve_boundary
    exact (Metric.isCompact_iff_isClosed_bounded).2
      ⟨hC.isCompact.isClosed.isClosed_filledHull, isBounded_filledHull.2 hC.isCompact.isBounded⟩
  isConnected_interior := by
    have hC := p.isSimple.isJordanCurve_boundary
    rw [hC.interior_filledHull]
    exact hC.isConnected_filledHull_sdiff
  closure_interior := by
    have hC := p.isSimple.isJordanCurve_boundary
    rw [hC.interior_filledHull, hC.closure_filledHull_sdiff]
  frontier_carrier := by
    rw [p.isSimple.isJordanCurve_boundary.frontier_filledHull, iUnion_const]

/-- The table bounded by a simple polygon has no holes. -/
@[simp]
theorem ofSimplePolygon_numHoles (p : SimplePolygon ℝ ℂ) : (ofSimplePolygon p).numHoles = 0 :=
  (rfl)

/-- The boundary polygon of `ofSimplePolygon p` is `p`. -/
@[simp]
theorem ofSimplePolygon_component (p : SimplePolygon ℝ ℂ)
    (i : Fin ((ofSimplePolygon p).numHoles + 1)) :
    (ofSimplePolygon p).component i = p :=
  (rfl)

/-- The table bounded by a simple polygon is the filled hull of its boundary. -/
@[simp]
theorem ofSimplePolygon_carrier (p : SimplePolygon ℝ ℂ) :
    (ofSimplePolygon p).carrier = filledHull (p.toPolygon.boundary ℝ) :=
  (rfl)

/-- The frontier of the table bounded by a simple polygon is the boundary of the polygon. -/
theorem frontier_ofSimplePolygon_carrier (p : SimplePolygon ℝ ℂ) :
    frontier (ofSimplePolygon p).carrier = p.toPolygon.boundary ℝ :=
  p.isSimple.isJordanCurve_boundary.frontier_filledHull

/-- The interior of the table bounded by a simple polygon is the filled hull of the boundary of the
polygon minus that boundary. -/
theorem interior_ofSimplePolygon_carrier (p : SimplePolygon ℝ ℂ) :
    interior (ofSimplePolygon p).carrier =
      filledHull (p.toPolygon.boundary ℝ) \ p.toPolygon.boundary ℝ :=
  p.isSimple.isJordanCurve_boundary.interior_filledHull

/-- The sides of the table bounded by a simple polygon `p` are indexed by the edges of `p`. -/
noncomputable def ofSimplePolygonSideEquiv (p : SimplePolygon ℝ ℂ) :
    Fin p.numVertices ≃ (ofSimplePolygon p).Side where
  toFun j := ⟨0, j⟩
  invFun s := s.2
  left_inv _ := rfl
  right_inv := fun ⟨i, _⟩ => by
    obtain rfl := Subsingleton.elim (α := Fin 1) i 0
    rfl

/-- The side of `ofSimplePolygon p` indexed by the edge `j` of `p` starts at vertex `j` of `p`. -/
@[simp]
theorem Side.start_ofSimplePolygonSideEquiv (p : SimplePolygon ℝ ℂ) (j : Fin p.numVertices) :
    (ofSimplePolygonSideEquiv p j).start = p.toPolygon j :=
  (rfl)

/-- The side of `ofSimplePolygon p` indexed by the edge `j` of `p` ends at the vertex after `j`. -/
@[simp]
theorem Side.finish_ofSimplePolygonSideEquiv (p : SimplePolygon ℝ ℂ) (j : Fin p.numVertices) :
    (ofSimplePolygonSideEquiv p j).finish = p.toPolygon (finRotate _ j) :=
  (rfl)

/-- The side of `ofSimplePolygon p` indexed by the edge `j` of `p` is that edge. -/
@[simp]
theorem side_ofSimplePolygonSideEquiv (p : SimplePolygon ℝ ℂ) (j : Fin p.numVertices) :
    (ofSimplePolygon p).side (ofSimplePolygonSideEquiv p j) = p.toPolygon.edgeSet ℝ j :=
  (rfl)

/-- The relative interior of the side of `ofSimplePolygon p` indexed by the edge `j` of `p` is the
open segment between the endpoints of that edge. -/
@[simp]
theorem sideInterior_ofSimplePolygonSideEquiv (p : SimplePolygon ℝ ℂ) (j : Fin p.numVertices) :
    (ofSimplePolygon p).sideInterior (ofSimplePolygonSideEquiv p j) =
      openSegment ℝ (p.toPolygon j) (p.toPolygon (finRotate _ j)) :=
  (rfl)

/-- The vertices of `ofSimplePolygon p` are the vertices of `p`. -/
@[simp]
theorem vertexSet_ofSimplePolygon (p : SimplePolygon ℝ ℂ) :
    (ofSimplePolygon p).vertexSet = range p.toPolygon.vertices := by
  ext x
  rw [vertexSet, mem_iUnion]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩

/-- A triangle in the plane is a polygonal table, so the type of tables is inhabited. -/
noncomputable instance instInhabited : Inhabited PolygonalTable :=
  ⟨ofSimplePolygon (Affine.Triangle.toSimplePolygon
    ⟨![0, 1, Complex.I], by
      rw [affineIndependent_iff_not_collinear_set, collinear_iff_of_mem (mem_insert 0 _)]
      rintro ⟨v, hv⟩
      obtain ⟨r, hr⟩ := hv 1 (by simp)
      obtain ⟨r', hr'⟩ := hv Complex.I (by simp)
      simp only [vadd_eq_add, add_zero, Complex.real_smul] at hr hr'
      have h : (r : ℂ) * Complex.I = r' := by
        rw [hr', mul_left_comm, ← hr, mul_one]
      have hr0 : r = 0 := by simpa using congrArg Complex.im h
      simp [hr0] at hr⟩)⟩

end PolygonalTable

end TauCeti
