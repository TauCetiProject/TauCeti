/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Polygon.Basic
public import TauCeti.Data.Fin.Basic

/-!
# Relabelling and inserting vertices of polygons

Two operations on Mathlib's `Polygon P n`, a cyclic list of vertices. The cyclic relabelling
`Polygon.rotate` moves the base point of the vertex list one step along the polygon; it has the
same edges in the same cyclic order, so it presents the same oriented polygon. Inserting a vertex,
`Polygon.insertVertex poly i c`, puts the new vertex `c` between vertex `i` and the next one, which
replaces edge `i` by the two segments through `c`.

## Main definitions

* `Polygon.rotate`: the cyclic relabelling of the vertices of a polygon.
* `Polygon.insertVertex`: the polygon with a new vertex inserted after vertex `i`.

The file also records the elementary description of the boundary of a polygon as the union of
the paths of its edges, and the fact that the vertices lie on the boundary.

## Main results

* `Polygon.mem_boundary_iff`: a point lies on the boundary exactly when it lies on some edge.
* `Polygon.apply_mem_boundary`: every vertex lies on the boundary.
* `Polygon.boundary_rotate`: the cyclic relabelling has the same boundary.
* `Polygon.boundary_insertVertex`: inserting a vertex `c` after vertex `i` replaces edge `i` by the
  segments from vertex `i` to `c` and from `c` to the next vertex.
-/

public section

open Set Function

namespace Polygon

variable {R V P : Type*} {n : ℕ}

/-! ### Relabelling and inserting vertices -/

/-- The cyclic relabelling of a polygon: vertex `i` of `poly.rotate` is vertex `i + 1` of `poly`.
It has the same edges in the same cyclic order (`Polygon.edgeSet_rotate`), so it presents the same
oriented polygon. -/
def rotate (poly : Polygon P n) : Polygon P n :=
  ⟨poly.vertices ∘ finRotate n⟩

@[simp]
theorem rotate_apply (poly : Polygon P n) (i : Fin n) : poly.rotate i = poly (finRotate n i) :=
  (rfl)

/-- The polygon with the new vertex `c` inserted after vertex `i`, at position `i + 1`. Its edges
are those of `poly`, except that the edge from vertex `i` to the next vertex is replaced by the
edges from vertex `i` to `c` and from `c` to the next vertex (`Polygon.boundary_insertVertex`). -/
def insertVertex (poly : Polygon P n) (i : Fin n) (c : P) : Polygon P (n + 1) :=
  ⟨Fin.insertNth i.succ c poly.vertices⟩

variable (poly : Polygon P n) (i : Fin n) (c : P)

/-- The vertices of `poly.insertVertex i c` are those of `poly` with `c` inserted at `i + 1`. -/
theorem insertVertex_vertices :
    (poly.insertVertex i c).vertices = Fin.insertNth i.succ c poly.vertices :=
  (rfl)

@[simp]
theorem insertVertex_apply_succ_self : poly.insertVertex i c i.succ = c :=
  Fin.insertNth_apply_same (α := fun _ ↦ P) _ _ _

@[simp]
theorem insertVertex_apply_succAbove (k : Fin n) :
    poly.insertVertex i c (i.succ.succAbove k) = poly k :=
  Fin.insertNth_apply_succAbove (α := fun _ ↦ P) _ _ _ _

@[simp]
theorem insertVertex_apply_castSucc_self : poly.insertVertex i c i.castSucc = poly i := by
  rw [← Fin.succAbove_succ_self, insertVertex_apply_succAbove]

/-- The vertex after the new vertex `c` is the vertex after `i` in `poly`. -/
theorem insertVertex_apply_finRotate_succ_self :
    poly.insertVertex i c (finRotate (n + 1) i.succ) = poly (finRotate n i) := by
  rw [Fin.finRotate_succ_eq_succ_succAbove, insertVertex_apply_succAbove]

/-! ### Points of the boundary -/

section Boundary

variable [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]
  {poly : Polygon P n} {x : P}

/-- A point lies on the boundary of a polygon exactly when it lies on the path of some edge, at
a parameter in `[0, 1]`. -/
theorem mem_boundary_iff :
    x ∈ poly.boundary R ↔ ∃ i, ∃ t ∈ Icc (0 : R) 1, poly.edgePath R i t = x := by
  simp only [boundary, mem_iUnion, edgeSet_eq_image_edgePath, mem_image]

variable [IsOrderedRing R] (poly : Polygon P n) (i : Fin n)

variable (R) in
/-- Vertex `i` is the starting point of edge `i`. -/
theorem apply_mem_edgeSet_self : poly i ∈ poly.edgeSet R i :=
  left_mem_affineSegment R _ _

variable (R) in
/-- The vertex after vertex `i` is the end point of edge `i`. -/
theorem apply_finRotate_mem_edgeSet : poly (finRotate n i) ∈ poly.edgeSet R i :=
  right_mem_affineSegment R _ _

variable (R) in
/-- Every vertex of a polygon lies on its boundary. -/
theorem apply_mem_boundary : poly i ∈ poly.boundary R :=
  mem_iUnion.2 ⟨i, poly.apply_mem_edgeSet_self R i⟩

end Boundary

/-! ### Edges after relabelling and inserting vertices -/

section Edges

variable [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]

@[simp]
theorem edgeSet_rotate (j : Fin n) : poly.rotate.edgeSet R j = poly.edgeSet R (finRotate n j) := by
  rw [edgeSet, edgeSet, rotate_apply, rotate_apply]

/-- Cyclically relabelling the vertices does not change the boundary: the edges of
`poly.rotate` are those of `poly`, reindexed by `finRotate n`. -/
@[simp]
theorem boundary_rotate : poly.rotate.boundary R = poly.boundary R := by
  simp only [boundary, edgeSet_rotate]
  exact (finRotate n).surjective.iUnion_comp (poly.edgeSet R)

/-- The first new edge runs from vertex `i` to the new vertex `c`. -/
@[simp]
theorem edgeSet_insertVertex_castSucc_self :
    (poly.insertVertex i c).edgeSet R i.castSucc = affineSegment R (poly i) c := by
  rw [edgeSet, finRotate_apply, Fin.coeSucc_eq_succ, insertVertex_apply_castSucc_self,
    insertVertex_apply_succ_self]

/-- The second new edge runs from the new vertex `c` to the vertex after `i`. -/
@[simp]
theorem edgeSet_insertVertex_succ_self :
    (poly.insertVertex i c).edgeSet R i.succ = affineSegment R c (poly (finRotate n i)) := by
  rw [edgeSet, insertVertex_apply_succ_self, insertVertex_apply_finRotate_succ_self]

/-- Every edge of `poly` other than edge `i` is an edge of `poly.insertVertex i c`. -/
theorem edgeSet_insertVertex_succAbove {k : Fin n} (hk : k ≠ i) :
    (poly.insertVertex i c).edgeSet R (i.succ.succAbove k) = poly.edgeSet R k := by
  rw [edgeSet, Fin.finRotate_succ_succAbove_of_ne hk, insertVertex_apply_succAbove,
    insertVertex_apply_succAbove, edgeSet]

/-- Inserting the vertex `c` after vertex `i` replaces edge `i` by the segments from vertex `i` to
`c` and from `c` to the next vertex. -/
theorem boundary_insertVertex :
    (poly.insertVertex i c).boundary R = (⋃ (k : Fin n) (_ : k ≠ i), poly.edgeSet R k) ∪
      (affineSegment R (poly i) c ∪ affineSegment R c (poly (finRotate n i))) := by
  ext x
  simp only [boundary, mem_iUnion, mem_union]
  constructor
  · rintro ⟨j, hj⟩
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i.succ j
    · exact .inr (.inr (by rwa [edgeSet_insertVertex_succ_self] at hj))
    · by_cases hk : k = i
      · subst hk
        rw [Fin.succAbove_succ_self, edgeSet_insertVertex_castSucc_self] at hj
        exact .inr (.inl hj)
      · exact .inl ⟨k, hk, by rwa [edgeSet_insertVertex_succAbove _ _ _ hk] at hj⟩
  · rintro (⟨k, hk, hx⟩ | hx | hx)
    · exact ⟨i.succ.succAbove k, by rwa [edgeSet_insertVertex_succAbove _ _ _ hk]⟩
    · exact ⟨i.castSucc, by rwa [edgeSet_insertVertex_castSucc_self]⟩
    · exact ⟨i.succ, by rwa [edgeSet_insertVertex_succ_self]⟩

end Edges

end Polygon
