/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Polygon.Simple
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledHull
import Mathlib.Analysis.Convex.Between
import TauCeti.Analysis.Complex.PlaneSeparation.Inside
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
* `TauCeti.PolygonalTable.ofSimplePolygon`: the table without holes bounded by a simple polygon.

## Main results

* `TauCeti.PolygonalTable.frontier_eq_iUnion_side`: the frontier of the table is the union of its
  sides.
* `TauCeti.PolygonalTable.finite_vertexSet`: a table has finitely many vertices.
* `TauCeti.PolygonalTable.disjoint_sideInterior`: the relative interiors of distinct sides are
  disjoint.
* `TauCeti.PolygonalTable.existsUnique_mem_sideInterior`: every point of the frontier off the
  vertices lies in the relative interior of exactly one side.

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
theorem Side.start_ne_finish (s : T.Side) : s.start ≠ s.finish :=
  (T.component s.1).isSimple.hasNondegenerateEdges s.2

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

/-- The start of a side is a vertex. -/
theorem Side.start_mem_vertexSet (s : T.Side) : s.start ∈ T.vertexSet :=
  mem_iUnion.2 ⟨s.1, mem_range_self _⟩

/-- The end of a side is a vertex. -/
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

/-- **Every point of the frontier of a table off its vertices lies in the relative interior of
exactly one side.** -/
theorem existsUnique_mem_sideInterior {x : ℂ} (hx : x ∈ frontier T.carrier)
    (hxv : x ∉ T.vertexSet) : ∃! s : T.Side, x ∈ T.sideInterior s := by
  rw [frontier_eq_iUnion_side, mem_iUnion] at hx
  obtain ⟨s, hs⟩ := hx
  rw [side_eq_segment] at hs
  refine ⟨s, mem_openSegment_of_ne_left_right (fun h => hxv (h ▸ s.start_mem_vertexSet))
    (fun h => hxv (h ▸ s.finish_mem_vertexSet)) hs, fun t ht => ?_⟩
  by_contra hts
  exact Set.disjoint_left.1 (T.disjoint_sideInterior hts) ht
    (mem_openSegment_of_ne_left_right (fun h => hxv (h ▸ s.start_mem_vertexSet))
      (fun h => hxv (h ▸ s.finish_mem_vertexSet)) hs)

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
