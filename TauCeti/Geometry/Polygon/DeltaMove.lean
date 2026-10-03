/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Relation
public import TauCeti.Analysis.Convex.Between
public import TauCeti.Geometry.Polygon.Simple

/-!
# Δ-moves and combinatorial equivalence of polygons

A *Δ-move* (Burde–Zieschang, Definition 1.6; Lickorish, Chapter 1) changes a closed polygon `k`
across a triangle `D` one of whose sides is an edge `u` of `k`: if `D ∩ k = u`, then `u` is
replaced by the other two sides of `D`. The inverse operation `Δ⁻¹` removes a vertex in the same
way. Two polygonal knots are *combinatorially equivalent* (Burde–Zieschang, Definition 1.7) when
a finite sequence of Δ- and Δ⁻¹-moves transforms one into the other; for knots in `ℝ³` or `S³`
this is the same as being ambient isotopic (Burde–Zieschang, Proposition 1.10, not formalized
here).

Polygons are Mathlib's `Polygon P n`, cyclic lists of vertices. The Δ-move across edge `i` with new
vertex `c` is `Polygon.insertVertex`, which puts `c` between vertex `i` and the next one; it
replaces edge `i` by the two segments through `c` (`Polygon.boundary_insertVertex`). Its condition,
`Polygon.IsDeltaMove`, asks that the edge's endpoints and `c` be affinely independent, so that they
span a genuine triangle `D`, and that every other edge meet `D` only at the endpoints of edge `i`.
This form is symmetric between the two polygons. For a simple polygon it is exactly
the textbook condition `D ∩ k = u` (`Polygon.isDeltaMove_iff_of_isSimple`), and for a simple
polygon after the move it is exactly the condition `D ∩ k' = v ∪ w` of the inverse move
(`Polygon.isDeltaMove_iff_of_isSimple_insertVertex`). A Δ-move keeps a polygon simple, and so does
its inverse (`Polygon.IsDeltaMove.isSimple_insertVertex_iff`).

Δ-moves across a degenerate triangle `D` are also admitted. For a Δ-move between simple polygons
such a triangle is the edge `u` itself, and the move subdivides `u` at a point `c` of it; this is
the elementary move `TauCeti.SimplePolygon.IsElementaryMove.subdivide`.

The vertex labels of `Polygon P n` carry a base point that the polygonal knot does not have.
Relabelling the vertices cyclically, `Polygon.rotate`, gives the same oriented polygon, and it is
the last kind of elementary move on `TauCeti.SimplePolygon`. The equivalence relation generated
by the three, `TauCeti.SimplePolygon.CombinatoriallyEquivalent`, is combinatorial equivalence of
oriented polygonal knots when the ambient space is `ℝ³`. For example, a triangle becomes the
parallelogram it spans by a Δ-move (`Affine.Triangle.isDeltaMove_parallelogram`).

## Main definitions

* `Polygon.IsDeltaMove`: the condition for inserting a vertex to be a Δ-move.
* `TauCeti.SimplePolygon.deltaMove`: the simple polygon obtained by a Δ-move.
* `TauCeti.SimplePolygon.IsElementaryMove`: a cyclic relabelling, a Δ-move, or a subdivision of an
  edge of a simple polygon.
* `TauCeti.SimplePolygon.CombinatoriallyEquivalent`: the equivalence relation they generate.

## Main results

* `Polygon.IsDeltaMove.closedInterior_inter_boundary` and
  `Polygon.IsDeltaMove.closedInterior_inter_boundary_insertVertex`: the triangle meets the polygon
  before the move in `u`, and after the move in `v ∪ w`.
* `Polygon.isDeltaMove_iff_of_isSimple` and `Polygon.isDeltaMove_iff_of_isSimple_insertVertex`:
  the converses, for simple polygons.
* `Polygon.IsDeltaMove.isSimple_insertVertex_iff`: a Δ-move keeps a polygon simple, and so does
  its inverse.
* `Affine.Triangle.isDeltaMove_parallelogram`: a triangle `abd` becomes the parallelogram `abcd` by
  a Δ-move across its edge `bd`.

## References

* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1 §B, Definitions 1.6 and 1.7 and Proposition 1.10.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1.
-/

public section

open Set Function

namespace Polygon

variable {R V P : Type*} {n : ℕ}

/-! ### The Δ-move condition -/

section Condition

variable [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]
  (poly : Polygon P n) (i : Fin n) (c : P)

variable (R) in
/-- Inserting the vertex `c` after vertex `i` is a **Δ-move**: the endpoints `a`, `b` of edge `i`
and `c` are affinely independent, so they span a triangle `D` (`Polygon.IsDeltaMove.triangle`), and
every other edge meets `D` only at `a` or `b`. Then edge `i` is replaced by the other two sides of
`D`.

This condition is symmetric between the polygon before and after the move. For a simple polygon
it is the textbook condition that `D` meets the polygon exactly in edge `i`
(`Polygon.isDeltaMove_iff_of_isSimple`), and for a simple polygon after the move it is the
condition of the inverse move (`Polygon.isDeltaMove_iff_of_isSimple_insertVertex`). -/
structure IsDeltaMove : Prop where
  /-- The endpoints of edge `i` and the new vertex are affinely independent. -/
  affineIndependent : AffineIndependent R ![poly i, poly (finRotate n i), c]
  /-- Every edge other than edge `i` meets the triangle only at the endpoints of edge `i`. -/
  edgeSet_inter_subset : ∀ ⦃k : Fin n⦄, k ≠ i →
    poly.edgeSet R k ∩ (⟨_, affineIndependent⟩ : Affine.Triangle R P).closedInterior ⊆
      {poly i, poly (finRotate n i)}

variable {poly i c}

/-- The triangle of a Δ-move, spanned by the endpoints of the edge and the new vertex. -/
def IsDeltaMove.triangle (h : poly.IsDeltaMove R i c) : Affine.Triangle R P :=
  ⟨_, h.affineIndependent⟩

@[simp]
theorem IsDeltaMove.triangle_points (h : poly.IsDeltaMove R i c) :
    h.triangle.points = ![poly i, poly (finRotate n i), c] :=
  (rfl)

/-- Every edge other than edge `i` meets the triangle of a Δ-move only at the endpoints of edge
`i`. -/
theorem IsDeltaMove.edgeSet_inter_closedInterior_subset (h : poly.IsDeltaMove R i c) {k : Fin n}
    (hk : k ≠ i) :
    poly.edgeSet R k ∩ h.triangle.closedInterior ⊆ {poly i, poly (finRotate n i)} :=
  h.edgeSet_inter_subset hk

end Condition

section IsSimple

variable [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]
  {poly : Polygon P n} {i : Fin n} (c : P)

/-- In a simple polygon with a vertex `c` inserted after vertex `i`, a point of an old edge `k`
lying on the first new edge is vertex `i`, and edge `k` is the edge before vertex `i`. -/
private theorem eq_and_finRotate_eq_of_isSimple_insertVertex
    (hq : (poly.insertVertex i c).IsSimple R) {k : Fin n} (hk : k ≠ i) {x : P}
    (hxk : x ∈ poly.edgeSet R k) (hx : x ∈ affineSegment R (poly i) c) :
    x = poly i ∧ finRotate n k = i := by
  have hne : i.succ.succAbove k ≠ i.castSucc := by
    rw [← Fin.succAbove_succ_self]
    exact Fin.succAbove_right_injective.ne hk
  rw [← poly.edgeSet_insertVertex_succAbove i c hk] at hxk
  rw [← poly.edgeSet_insertVertex_castSucc_self i c] at hx
  rcases hq.eq_vertex_of_mem_edgeSet hne hxk hx with ⟨h₁, h₂⟩ | ⟨h₁, -⟩
  · rw [Fin.finRotate_succ_succAbove_of_ne hk, ← Fin.succAbove_succ_self] at h₁
    exact ⟨by rwa [insertVertex_apply_castSucc_self] at h₂,
      (Fin.succAbove_right_injective h₁).symm⟩
  · rw [finRotate_apply, Fin.coeSucc_eq_succ] at h₁
    exact absurd h₁ (Fin.succAbove_ne _ _)

/-- In a simple polygon with a vertex `c` inserted after vertex `i`, a point of an old edge `k`
lying on the second new edge is the vertex after `i`, and edge `k` is the edge after it. -/
private theorem eq_and_eq_finRotate_of_isSimple_insertVertex
    (hq : (poly.insertVertex i c).IsSimple R) {k : Fin n} (hk : k ≠ i) {x : P}
    (hxk : x ∈ poly.edgeSet R k) (hx : x ∈ affineSegment R c (poly (finRotate n i))) :
    x = poly (finRotate n i) ∧ k = finRotate n i := by
  have hne : i.succ.succAbove k ≠ i.succ := Fin.succAbove_ne _ _
  rw [← poly.edgeSet_insertVertex_succAbove i c hk] at hxk
  rw [← poly.edgeSet_insertVertex_succ_self i c] at hx
  rcases hq.eq_vertex_of_mem_edgeSet hne hxk hx with ⟨h₁, -⟩ | ⟨h₁, h₂⟩
  · rw [Fin.finRotate_succ_succAbove_of_ne hk] at h₁
    exact absurd h₁.symm (Fin.succAbove_ne _ _)
  · rw [Fin.finRotate_succ_eq_succ_succAbove] at h₁
    have hk' := Fin.succAbove_right_injective h₁
    subst hk'
    exact ⟨by rwa [insertVertex_apply_succAbove] at h₂, rfl⟩

end IsSimple

/-! ### Δ-moves -/

section DeltaMove

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [Nontrivial R] [AddCommGroup V] [Module R V]
  [AddTorsor V P] {poly : Polygon P n} {i : Fin n} {c : P}

namespace IsDeltaMove

variable (h : poly.IsDeltaMove R i c)
include h

omit [IsOrderedRing R] in
/-- The two endpoints of the edge replaced by a Δ-move are distinct. -/
theorem left_ne_right : poly i ≠ poly (finRotate n i) := by
  simpa using h.affineIndependent.injective.ne (a₁ := 0) (a₂ := 1) (by decide)

omit [IsOrderedRing R] in
/-- The new vertex of a Δ-move differs from the start of the replaced edge. -/
theorem left_ne_apex : poly i ≠ c := by
  simpa using h.affineIndependent.injective.ne (a₁ := 0) (a₂ := 2) (by decide)

omit [IsOrderedRing R] in
/-- The new vertex of a Δ-move differs from the end of the replaced edge. -/
theorem apex_ne_right : c ≠ poly (finRotate n i) := by
  simpa using h.affineIndependent.injective.ne (a₁ := 2) (a₂ := 1) (by decide)

omit [Nontrivial R] in
/-- The two new edges meet only at the new vertex. -/
theorem affineSegment_inter_affineSegment :
    affineSegment R (poly i) c ∩ affineSegment R c (poly (finRotate n i)) = {c} :=
  h.affineIndependent.comm_right.affineSegment_inter_eq_endpoint

/-- The end of the replaced edge is not on the first new edge. -/
theorem right_notMem_affineSegment : poly (finRotate n i) ∉ affineSegment R (poly i) c := by
  intro hB
  have := h.affineSegment_inter_affineSegment.subset ⟨hB, right_mem_affineSegment _ _ _⟩
  exact h.apex_ne_right (this : _ = c).symm

/-- The start of the replaced edge is not on the second new edge. -/
theorem left_notMem_affineSegment : poly i ∉ affineSegment R c (poly (finRotate n i)) := by
  intro hA
  have := h.affineSegment_inter_affineSegment.subset ⟨left_mem_affineSegment _ _ _, hA⟩
  exact h.left_ne_apex (this : _ = c)

omit [Nontrivial R] in
/-- The replaced edge is a side of the triangle of a Δ-move. -/
theorem edgeSet_subset_closedInterior : poly.edgeSet R i ⊆ h.triangle.closedInterior :=
  (h.triangle.closedInterior_face_eq_affineSegment (i := 0) (j := 1)
    (by decide)).symm.subset.trans (h.triangle.closedInterior_face_subset_closedInterior _)

omit [Nontrivial R] in
/-- The first new edge is a side of the triangle of a Δ-move. -/
theorem affineSegment_left_subset_closedInterior :
    affineSegment R (poly i) c ⊆ h.triangle.closedInterior :=
  (h.triangle.closedInterior_face_eq_affineSegment (i := 0) (j := 2)
    (by decide)).symm.subset.trans (h.triangle.closedInterior_face_subset_closedInterior _)

omit [Nontrivial R] in
/-- The second new edge is a side of the triangle of a Δ-move. -/
theorem affineSegment_right_subset_closedInterior :
    affineSegment R c (poly (finRotate n i)) ⊆ h.triangle.closedInterior :=
  (h.triangle.closedInterior_face_eq_affineSegment (i := 2) (j := 1)
    (by decide)).symm.subset.trans (h.triangle.closedInterior_face_subset_closedInterior _)

omit [Nontrivial R] in
/-- Before a Δ-move, the triangle meets the polygon exactly in the edge it replaces: `D ∩ k = u`
in Burde–Zieschang, Definition 1.6. -/
theorem closedInterior_inter_boundary :
    h.triangle.closedInterior ∩ poly.boundary R = poly.edgeSet R i := by
  refine Subset.antisymm (fun x ⟨hxT, hx⟩ => ?_) fun x hx =>
    ⟨h.edgeSet_subset_closedInterior hx, mem_iUnion.2 ⟨i, hx⟩⟩
  obtain ⟨k, hk⟩ := mem_iUnion.1 hx
  by_cases hki : k = i
  · exact hki ▸ hk
  · rcases h.edgeSet_inter_closedInterior_subset hki ⟨hk, hxT⟩ with rfl | rfl
    exacts [left_mem_affineSegment _ _ _, right_mem_affineSegment _ _ _]

omit [Nontrivial R] in
/-- After a Δ-move, the triangle meets the polygon exactly in the two new edges: `D ∩ k' = v ∪ w`,
the condition for the inverse move. -/
theorem closedInterior_inter_boundary_insertVertex :
    h.triangle.closedInterior ∩ (poly.insertVertex i c).boundary R =
      affineSegment R (poly i) c ∪ affineSegment R c (poly (finRotate n i)) := by
  rw [boundary_insertVertex]
  refine Subset.antisymm (fun x ⟨hxT, hx⟩ => ?_) fun x hx => ⟨?_, .inr hx⟩
  · rcases hx with hx | hx
    · obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx
      rcases h.edgeSet_inter_closedInterior_subset hk ⟨hxk, hxT⟩ with rfl | rfl
      exacts [.inl (left_mem_affineSegment _ _ _), .inr (right_mem_affineSegment _ _ _)]
    · exact hx
  · rcases hx with hx | hx
    exacts [h.affineSegment_left_subset_closedInterior hx,
      h.affineSegment_right_subset_closedInterior hx]

end IsDeltaMove

omit [Nontrivial R] in
/-- **The textbook form of a Δ-move.** For a simple polygon, inserting `c` after vertex `i` is a
Δ-move exactly when the edge's endpoints and `c` span a triangle meeting the polygon exactly in
edge `i` (Burde–Zieschang, Definition 1.6). -/
theorem isDeltaMove_iff_of_isSimple (hp : poly.IsSimple R) :
    poly.IsDeltaMove R i c ↔ ∃ h : AffineIndependent R ![poly i, poly (finRotate n i), c],
      (⟨_, h⟩ : Affine.Triangle R P).closedInterior ∩ poly.boundary R = poly.edgeSet R i := by
  refine ⟨fun h => ⟨h.affineIndependent, h.closedInterior_inter_boundary⟩,
    fun ⟨hind, heq⟩ => ⟨hind, fun k hk x ⟨hxk, hxT⟩ => ?_⟩⟩
  have hxi : x ∈ poly.edgeSet R i := heq ▸ ⟨hxT, mem_iUnion.2 ⟨k, hxk⟩⟩
  rcases hp.eq_vertex_of_mem_edgeSet hk hxk hxi with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
  exacts [.inl rfl, .inr rfl]

omit [Nontrivial R] in
/-- **The textbook form of an inverse Δ-move.** For a polygon that is simple after `c` is inserted
after vertex `i`, the insertion is a Δ-move exactly when the endpoints of edge `i` and `c` span a
triangle meeting the new polygon exactly in the two new edges, which is the condition for removing
`c` again by a `Δ⁻¹`-move. -/
theorem isDeltaMove_iff_of_isSimple_insertVertex (hq : (poly.insertVertex i c).IsSimple R) :
    poly.IsDeltaMove R i c ↔ ∃ h : AffineIndependent R ![poly i, poly (finRotate n i), c],
      (⟨_, h⟩ : Affine.Triangle R P).closedInterior ∩ (poly.insertVertex i c).boundary R =
        affineSegment R (poly i) c ∪ affineSegment R c (poly (finRotate n i)) := by
  refine ⟨fun h => ⟨h.affineIndependent, h.closedInterior_inter_boundary_insertVertex⟩,
    fun ⟨hind, heq⟩ => ⟨hind, fun k hk x ⟨hxk, hxT⟩ => ?_⟩⟩
  have hx : x ∈ affineSegment R (poly i) c ∪ affineSegment R c (poly (finRotate n i)) :=
    heq ▸ ⟨hxT, by rw [boundary_insertVertex]; exact .inl (mem_iUnion₂.2 ⟨k, hk, hxk⟩)⟩
  rcases hx with hx | hx
  · exact .inl (eq_and_finRotate_eq_of_isSimple_insertVertex c hq hk hxk hx).1
  · exact .inr (eq_and_eq_finRotate_of_isSimple_insertVertex c hq hk hxk hx).1

/-- **The inverse of a Δ-move keeps a polygon simple.** If the polygon is simple after a Δ-move, it
was simple before. -/
theorem IsDeltaMove.isSimple_of_isSimple_insertVertex (h : poly.IsDeltaMove R i c)
    (hq : (poly.insertVertex i c).IsSimple R) : poly.IsSimple R := by
  refine ⟨fun k => ?_, fun k₁ k₂ x hne hx₁ hx₂ => ?_⟩
  · by_cases hk : k = i
    · exact hk ▸ h.left_ne_right
    · have := hq.hasNondegenerateEdges (i.succ.succAbove k)
      rwa [Fin.finRotate_succ_succAbove_of_ne hk, insertVertex_apply_succAbove,
        insertVertex_apply_succAbove] at this
  -- A point shared by an old edge `k` and edge `i` is an endpoint of edge `i`, and the new edge
  -- through that endpoint locates edge `k` next to edge `i`.
  have key {k : Fin n} (hk : k ≠ i) (hxk : x ∈ poly.edgeSet R k) (hxi : x ∈ poly.edgeSet R i) :
      (i = finRotate n k ∧ x = poly i) ∨ (k = finRotate n i ∧ x = poly k) := by
    rcases h.edgeSet_inter_closedInterior_subset hk
        ⟨hxk, h.edgeSet_subset_closedInterior hxi⟩ with rfl | rfl
    · exact .inl ⟨(eq_and_finRotate_eq_of_isSimple_insertVertex c hq hk hxk
        (left_mem_affineSegment _ _ _)).2.symm, rfl⟩
    · obtain ⟨-, rfl⟩ := eq_and_eq_finRotate_of_isSimple_insertVertex c hq hk hxk
        (right_mem_affineSegment _ _ _)
      exact .inr ⟨rfl, rfl⟩
  by_cases h₁ : k₁ = i
  · subst h₁
    exact (key (Ne.symm hne) hx₂ hx₁).symm
  by_cases h₂ : k₂ = i
  · subst h₂
    exact key h₁ hx₁ hx₂
  -- Two old edges meet in the new polygon as they did in the old one.
  rw [← poly.edgeSet_insertVertex_succAbove i c h₁] at hx₁
  rw [← poly.edgeSet_insertVertex_succAbove i c h₂] at hx₂
  rcases hq.eq_vertex_of_mem_edgeSet (Fin.succAbove_right_injective.ne hne) hx₁ hx₂ with
    ⟨e, rfl⟩ | ⟨e, rfl⟩
  · rw [Fin.finRotate_succ_succAbove_of_ne h₁] at e
    exact .inl ⟨Fin.succAbove_right_injective e, insertVertex_apply_succAbove _ _ _ _⟩
  · rw [Fin.finRotate_succ_succAbove_of_ne h₂] at e
    exact .inr ⟨Fin.succAbove_right_injective e, insertVertex_apply_succAbove _ _ _ _⟩

/-- After a Δ-move on a simple polygon, an old edge `k` meets the first new edge only at vertex
`i`, which it reaches as the edge before vertex `i`. This is the condition of
`Polygon.IsSimple.eq_vertex_of_mem_edgeSet` for these two edges. -/
private theorem IsDeltaMove.eq_vertex_of_mem_affineSegment_left (h : poly.IsDeltaMove R i c)
    (hp : poly.IsSimple R) {k : Fin n} (hk : k ≠ i) {x : P} (hxk : x ∈ poly.edgeSet R k)
    (hx : x ∈ affineSegment R (poly i) c) :
    (i.castSucc = finRotate (n + 1) (i.succ.succAbove k) ∧
        x = poly.insertVertex i c i.castSucc) ∨
      (i.succ.succAbove k = finRotate (n + 1) i.castSucc ∧
        x = poly.insertVertex i c (i.succ.succAbove k)) := by
  rcases h.edgeSet_inter_closedInterior_subset hk
      ⟨hxk, h.affineSegment_left_subset_closedInterior hx⟩ with rfl | rfl
  · rcases hp.eq_vertex_of_mem_edgeSet hk hxk (left_mem_affineSegment _ _ _) with
      ⟨e, -⟩ | ⟨e₁, e₂⟩
    · refine .inl ⟨?_, (insertVertex_apply_castSucc_self _ _ _).symm⟩
      rw [Fin.finRotate_succ_succAbove_of_ne hk, ← e, Fin.succAbove_succ_self]
    · subst e₁
      exact absurd e₂ h.left_ne_right
  · exact absurd hx h.right_notMem_affineSegment

/-- After a Δ-move on a simple polygon, an old edge `k` meets the second new edge only at the
vertex after `i`, which it reaches as the edge after that vertex. This is the condition of
`Polygon.IsSimple.eq_vertex_of_mem_edgeSet` for these two edges. -/
private theorem IsDeltaMove.eq_vertex_of_mem_affineSegment_right (h : poly.IsDeltaMove R i c)
    (hp : poly.IsSimple R) {k : Fin n} (hk : k ≠ i) {x : P} (hxk : x ∈ poly.edgeSet R k)
    (hx : x ∈ affineSegment R c (poly (finRotate n i))) :
    (i.succ = finRotate (n + 1) (i.succ.succAbove k) ∧ x = poly.insertVertex i c i.succ) ∨
      (i.succ.succAbove k = finRotate (n + 1) i.succ ∧
        x = poly.insertVertex i c (i.succ.succAbove k)) := by
  rcases h.edgeSet_inter_closedInterior_subset hk
      ⟨hxk, h.affineSegment_right_subset_closedInterior hx⟩ with rfl | rfl
  · exact absurd hx h.left_notMem_affineSegment
  · rcases hp.eq_vertex_of_mem_edgeSet hk hxk (right_mem_affineSegment _ _ _) with
      ⟨-, e⟩ | ⟨e, -⟩
    · exact absurd e.symm h.left_ne_right
    · subst e
      exact .inr ⟨(Fin.finRotate_succ_eq_succ_succAbove i).symm,
        (insertVertex_apply_succAbove _ _ _ _).symm⟩

/-- **A Δ-move keeps a polygon simple.** -/
theorem IsDeltaMove.isSimple_insertVertex (h : poly.IsDeltaMove R i c) (hp : poly.IsSimple R) :
    (poly.insertVertex i c).IsSimple R := by
  refine ⟨fun j => ?_, fun j₁ j₂ x hne hx₁ hx₂ => ?_⟩
  · obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i.succ j
    · rw [insertVertex_apply_succ_self, insertVertex_apply_finRotate_succ_self]
      exact h.apex_ne_right
    · by_cases hk : k = i
      · subst hk
        rw [Fin.succAbove_succ_self, finRotate_apply, Fin.coeSucc_eq_succ,
          insertVertex_apply_castSucc_self, insertVertex_apply_succ_self]
        exact h.left_ne_apex
      · rw [Fin.finRotate_succ_succAbove_of_ne hk, insertVertex_apply_succAbove,
          insertVertex_apply_succAbove]
        exact hp.hasNondegenerateEdges k
  -- The two new edges meet only at the new vertex.
  have new (hx₁ : x ∈ affineSegment R (poly i) c)
      (hx₂ : x ∈ affineSegment R c (poly (finRotate n i))) :
      i.succ = finRotate (n + 1) i.castSucc ∧ x = poly.insertVertex i c i.succ := by
    rw [insertVertex_apply_succ_self]
    exact ⟨by rw [finRotate_apply, Fin.coeSucc_eq_succ],
      h.affineSegment_inter_affineSegment.subset ⟨hx₁, hx₂⟩⟩
  -- An index of the new polygon is the second new edge `i.succ`, the first new edge
  -- `i.succ.succAbove i`, or an old edge `i.succ.succAbove k` with `k ≠ i`.
  obtain rfl | ⟨k₁, rfl⟩ := Fin.eq_self_or_eq_succAbove i.succ j₁ <;>
    obtain rfl | ⟨k₂, rfl⟩ := Fin.eq_self_or_eq_succAbove i.succ j₂
  · exact absurd rfl hne
  · rw [edgeSet_insertVertex_succ_self] at hx₁
    by_cases hk₂ : k₂ = i
    · subst hk₂
      rw [Fin.succAbove_succ_self, edgeSet_insertVertex_castSucc_self] at hx₂
      rw [Fin.succAbove_succ_self]
      exact .inr (new hx₂ hx₁)
    · rw [edgeSet_insertVertex_succAbove _ _ _ hk₂] at hx₂
      exact (h.eq_vertex_of_mem_affineSegment_right hp hk₂ hx₂ hx₁).symm
  · rw [edgeSet_insertVertex_succ_self] at hx₂
    by_cases hk₁ : k₁ = i
    · subst hk₁
      rw [Fin.succAbove_succ_self, edgeSet_insertVertex_castSucc_self] at hx₁
      rw [Fin.succAbove_succ_self]
      exact .inl (new hx₁ hx₂)
    · rw [edgeSet_insertVertex_succAbove _ _ _ hk₁] at hx₁
      exact h.eq_vertex_of_mem_affineSegment_right hp hk₁ hx₁ hx₂
  · have hk : k₁ ≠ k₂ := fun e => hne (e ▸ rfl)
    by_cases hk₁ : k₁ = i
    · subst hk₁
      rw [Fin.succAbove_succ_self, edgeSet_insertVertex_castSucc_self] at hx₁
      rw [edgeSet_insertVertex_succAbove _ _ _ hk.symm] at hx₂
      rw [Fin.succAbove_succ_self]
      exact (h.eq_vertex_of_mem_affineSegment_left hp hk.symm hx₂ hx₁).symm
    by_cases hk₂ : k₂ = i
    · subst hk₂
      rw [Fin.succAbove_succ_self, edgeSet_insertVertex_castSucc_self] at hx₂
      rw [edgeSet_insertVertex_succAbove _ _ _ hk₁] at hx₁
      rw [Fin.succAbove_succ_self]
      exact h.eq_vertex_of_mem_affineSegment_left hp hk₁ hx₁ hx₂
    -- Two old edges meet in the new polygon as they did in the old one.
    rw [edgeSet_insertVertex_succAbove _ _ _ hk₁] at hx₁
    rw [edgeSet_insertVertex_succAbove _ _ _ hk₂] at hx₂
    rcases hp.eq_vertex_of_mem_edgeSet hk hx₁ hx₂ with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · exact .inl ⟨by rw [Fin.finRotate_succ_succAbove_of_ne hk₁, e],
        (insertVertex_apply_succAbove _ _ _ _).symm⟩
    · exact .inr ⟨by rw [Fin.finRotate_succ_succAbove_of_ne hk₂, e],
        (insertVertex_apply_succAbove _ _ _ _).symm⟩

/-- **A Δ-move keeps a polygon simple, and so does its inverse.** -/
theorem IsDeltaMove.isSimple_insertVertex_iff (h : poly.IsDeltaMove R i c) :
    (poly.insertVertex i c).IsSimple R ↔ poly.IsSimple R :=
  ⟨h.isSimple_of_isSimple_insertVertex, h.isSimple_insertVertex⟩

end DeltaMove

end Polygon

namespace Affine.Triangle

variable {R V P : Type*} [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- Inserting a vertex `c` after vertex `1` of a triangle `abd` gives the quadrilateral `abcd`. -/
theorem toPolygon_insertVertex_one (t : Affine.Triangle R P) (c : P) :
    t.toPolygon.insertVertex 1 c = ⟨![t.points 0, t.points 1, c, t.points 2]⟩ :=
  congrArg Polygon.mk <| (Polygon.insertVertex_vertices _ _ _).trans <| funext fun j => by
    fin_cases j <;> rfl

variable [PartialOrder R] [IsOrderedRing R]

/-- **A triangle becomes a parallelogram by a Δ-move.** For a triangle with vertices `a`, `b`, `d`,
inserting the fourth vertex `c = b + (d - a)` of the parallelogram after `b` is a Δ-move across the
edge `bd`, turning the triangle `abd` into the parallelogram `abcd`
(`Affine.Triangle.toPolygon_insertVertex_one`). -/
theorem isDeltaMove_parallelogram (t : Affine.Triangle R P) :
    t.toPolygon.IsDeltaMove R 1 ((t.points 2 -ᵥ t.points 0) +ᵥ t.points 1) := by
  set a := t.points 0 with ha
  set b := t.points 1 with hb
  set d := t.points 2 with hd
  set c := (d -ᵥ a) +ᵥ b
  -- Measured from `a`, the sides `u = b - a` and `v = d - a` are linearly independent, and the
  -- fourth vertex is `c - a = u + v`.
  have hli : LinearIndependent R ![b -ᵥ a, d -ᵥ a] := by
    convert ((affineIndependent_iff_linearIndependent_vsub R _ 0).1 t.independent).comp
      ![⟨1, by decide⟩, ⟨2, by decide⟩] (by decide) using 1
    ext j
    fin_cases j <;> rfl
  have hc : c -ᵥ a = (b -ᵥ a) + (d -ᵥ a) := by
    rw [vadd_vsub_assoc, add_comm]
  -- Measured from `b`, the sides `d - b = v - u` and `c - b = v` of the triangle `bdc` are
  -- linearly independent.
  have hind : AffineIndependent R ![b, d, c] := by
    rw [affineIndependent_iff_linearIndependent_vsub R _ 0,
      ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))]
    have hdb : d -ᵥ b = (d -ᵥ a) - (b -ᵥ a) := (vsub_sub_vsub_cancel_right d b a).symm
    have hcb : c -ᵥ b = d -ᵥ a := vadd_vsub _ _
    have hli' : LinearIndependent R ![(d -ᵥ a) - (b -ᵥ a), d -ᵥ a] :=
      LinearIndependent.pair_iff.2 fun r s hrs => by
        obtain ⟨h₁, h₂⟩ := LinearIndependent.pair_iff.1 hli (-r) (r + s) (by
          rw [← hrs, smul_sub, add_smul, neg_smul]
          abel)
        rw [neg_eq_zero] at h₁
        rw [h₁, zero_add] at h₂
        exact ⟨h₁, h₂⟩
    convert hli' using 1
    ext j
    fin_cases j
    · exact hdb
    · exact hcb
  -- A point of the triangle `bdc` is `a + (w₀ + w₂) • u + (w₁ + w₂) • v`.
  have hT {x : P} (hx : x ∈ (⟨_, hind⟩ : Affine.Triangle R P).closedInterior) :
      ∃ w : Fin 3 → R, (∀ j, 0 ≤ w j) ∧ w 0 + w 1 + w 2 = 1 ∧
        x -ᵥ a = (w 0 + w 2) • (b -ᵥ a) + (w 1 + w 2) • (d -ᵥ a) := by
    obtain ⟨w, hw, hw01, rfl⟩ := hx
    refine ⟨w, fun j => (hw01 j).1, by rwa [Fin.sum_univ_three] at hw, ?_⟩
    rw [Finset.univ.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w _ hw a,
      vadd_vsub, Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    rw [hc, smul_add, add_smul, add_smul]
    abel
  have hpoints : t.toPolygon.vertices = t.points := rfl
  have h01 : finRotate 3 0 = 1 := by decide
  have h12 : finRotate 3 1 = 2 := by decide
  have h20 : finRotate 3 2 = 0 := by decide
  refine ⟨by rwa [hpoints, h12], fun k hk x ⟨hxk, hxT⟩ => ?_⟩
  obtain ⟨w, hw0, hw1, hx⟩ := hT hxT
  rw [Polygon.edgeSet, hpoints] at hxk
  rw [hpoints, h12]
  have hk' : k = 0 ∨ k = 2 := by
    revert hk
    fin_cases k <;> decide
  rcases hk' with rfl | rfl
  · -- The edge `ab`: a point `a + s • u` of it in the triangle has `w₁ = w₂ = 0`, so it is `b`.
    rw [h01, ← ha, ← hb] at hxk
    obtain ⟨s, -, rfl⟩ := hxk
    rw [AffineMap.lineMap_vsub_left] at hx
    obtain ⟨-, h⟩ := LinearIndependent.pair_iff.1 hli (w 0 + w 2 - s) (w 1 + w 2) (by
      rw [sub_smul, hx]
      abel)
    obtain ⟨h₁, h₂⟩ := (add_eq_zero_iff_of_nonneg (hw0 1) (hw0 2)).1 h
    rw [h₁, h₂, add_zero, add_zero] at hw1
    left
    rw [← vsub_left_cancel_iff (p := a), AffineMap.lineMap_vsub_left, hx, h₁, h₂, hw1]
    simp only [add_zero, zero_smul, one_smul]
    rfl
  · -- The edge `da`: a point `a + s • v` of it in the triangle has `w₀ = w₂ = 0`, so it is `d`.
    rw [h20, ← ha, ← hd] at hxk
    obtain ⟨s, -, rfl⟩ := hxk
    rw [AffineMap.lineMap_vsub_right] at hx
    obtain ⟨h, -⟩ := LinearIndependent.pair_iff.1 hli (w 0 + w 2) (w 1 + w 2 - (1 - s)) (by
      rw [sub_smul, hx]
      abel)
    obtain ⟨h₀, h₂⟩ := (add_eq_zero_iff_of_nonneg (hw0 0) (hw0 2)).1 h
    rw [h₀, h₂, add_zero, zero_add] at hw1
    right
    rw [mem_singleton_iff, ← vsub_left_cancel_iff (p := a), AffineMap.lineMap_vsub_right, hx, h₀,
      h₂, hw1]
    simp only [add_zero, zero_smul, one_smul, zero_add]
    rfl

end Affine.Triangle

namespace TauCeti

namespace SimplePolygon

variable {R V P : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [Nontrivial R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- The simple polygon obtained from `p` by the Δ-move inserting `c` after vertex `i`. -/
@[expose] def deltaMove (p : SimplePolygon R P) (i : Fin p.numVertices) (c : P)
    (h : p.toPolygon.IsDeltaMove R i c) : SimplePolygon R P where
  numVertices := p.numVertices + 1
  toPolygon := p.toPolygon.insertVertex i c
  isSimple := h.isSimple_insertVertex p.isSimple

@[simp]
theorem deltaMove_numVertices (p : SimplePolygon R P) (i : Fin p.numVertices) (c : P)
    (h : p.toPolygon.IsDeltaMove R i c) : (p.deltaMove i c h).numVertices = p.numVertices + 1 :=
  rfl

@[simp]
theorem deltaMove_toPolygon (p : SimplePolygon R P) (i : Fin p.numVertices) (c : P)
    (h : p.toPolygon.IsDeltaMove R i c) :
    (p.deltaMove i c h).toPolygon = p.toPolygon.insertVertex i c :=
  rfl

/-- The **elementary moves** on simple polygons: a cyclic relabelling of the vertices, which keeps
the oriented polygon, a Δ-move, and a degenerate Δ-move, which subdivides an edge. The inverse
moves are not listed separately; the equivalence relation
`TauCeti.SimplePolygon.CombinatoriallyEquivalent` they generate is symmetric.

A degenerate Δ-move is one whose triangle `D` collapses to a segment. If the result is to be a
simple polygon again, the new vertex `c` lies on the edge `u` it replaces, so `D = u` and
`D ∩ k = u` holds automatically; the move subdivides `u` at `c`, and its inverse removes a vertex
at which the polygon does not turn. -/
inductive IsElementaryMove : SimplePolygon R P → SimplePolygon R P → Prop
  /-- Relabel the vertices cyclically. -/
  | rotate (p : SimplePolygon R P) : IsElementaryMove p p.rotate
  /-- Replace an edge by the other two sides of a triangle meeting the polygon only in that edge. -/
  | deltaMove (p : SimplePolygon R P) (i : Fin p.numVertices) (c : P)
      (h : p.toPolygon.IsDeltaMove R i c) : IsElementaryMove p (p.deltaMove i c h)
  /-- Subdivide an edge at one of its points, a degenerate Δ-move. -/
  | subdivide (p : SimplePolygon R P) (i : Fin p.numVertices) (c : P)
      (hc : c ∈ p.toPolygon.edgeSet R i) (hq : (p.toPolygon.insertVertex i c).IsSimple R) :
      IsElementaryMove p (p.insertVertex i c hq)

/-- **Combinatorial equivalence** of simple polygons (Burde–Zieschang, Definition 1.7): the
equivalence relation generated by Δ-moves, including the degenerate ones that subdivide an edge,
and cyclic relabellings. For simple polygons in `ℝ³`,
the polygonal presentations of oriented knots, it coincides with ambient isotopy of oriented knots
(Burde–Zieschang, Proposition 1.10, not formalized here). -/
def CombinatoriallyEquivalent : SimplePolygon R P → SimplePolygon R P → Prop :=
  Relation.EqvGen IsElementaryMove

namespace CombinatoriallyEquivalent

/-- Combinatorial equivalence is an equivalence relation. -/
theorem equivalence : Equivalence (CombinatoriallyEquivalent (R := R) (P := P)) :=
  Relation.EqvGen.is_equivalence _

@[refl]
theorem refl (p : SimplePolygon R P) : CombinatoriallyEquivalent p p :=
  Relation.EqvGen.refl p

@[symm]
theorem symm {p q : SimplePolygon R P} (h : CombinatoriallyEquivalent p q) :
    CombinatoriallyEquivalent q p :=
  Relation.EqvGen.symm _ _ h

@[trans]
theorem trans {p q r : SimplePolygon R P} (h : CombinatoriallyEquivalent p q)
    (h' : CombinatoriallyEquivalent q r) : CombinatoriallyEquivalent p r :=
  Relation.EqvGen.trans _ _ _ h h'

/-- The induction principle for combinatorial equivalence: a relation that holds for every
elementary move and is reflexive, symmetric and transitive along combinatorial equivalence holds
for every combinatorially equivalent pair. -/
theorem induction {motive : SimplePolygon R P → SimplePolygon R P → Prop}
    (move : ∀ {p q : SimplePolygon R P}, IsElementaryMove p q → motive p q)
    (refl : ∀ p : SimplePolygon R P, motive p p)
    (symm : ∀ {p q : SimplePolygon R P}, CombinatoriallyEquivalent p q → motive p q → motive q p)
    (trans : ∀ {p q r : SimplePolygon R P}, CombinatoriallyEquivalent p q →
      CombinatoriallyEquivalent q r → motive p q → motive q r → motive p r)
    {p q : SimplePolygon R P} (h : CombinatoriallyEquivalent p q) : motive p q :=
  Relation.EqvGen.rec (motive := fun p q _ => motive p q) (fun _ _ => move) refl (fun _ _ => symm)
    (fun _ _ _ => trans) h

end CombinatoriallyEquivalent

/-- An elementary move is a combinatorial equivalence. -/
theorem IsElementaryMove.combinatoriallyEquivalent {p q : SimplePolygon R P}
    (h : IsElementaryMove p q) : CombinatoriallyEquivalent p q :=
  Relation.EqvGen.rel _ _ h

/-- A simple polygon is combinatorially equivalent to its cyclic relabelling. -/
theorem combinatoriallyEquivalent_rotate (p : SimplePolygon R P) :
    CombinatoriallyEquivalent p p.rotate :=
  (IsElementaryMove.rotate p).combinatoriallyEquivalent

/-- A simple polygon is combinatorially equivalent to the result of a Δ-move on it. -/
theorem combinatoriallyEquivalent_deltaMove (p : SimplePolygon R P) (i : Fin p.numVertices)
    (c : P) (h : p.toPolygon.IsDeltaMove R i c) :
    CombinatoriallyEquivalent p (p.deltaMove i c h) :=
  (IsElementaryMove.deltaMove p i c h).combinatoriallyEquivalent

/-- A simple polygon is combinatorially equivalent to the result of subdividing one of its edges. -/
theorem combinatoriallyEquivalent_subdivide (p : SimplePolygon R P) (i : Fin p.numVertices)
    (c : P) (hc : c ∈ p.toPolygon.edgeSet R i) (hq : (p.toPolygon.insertVertex i c).IsSimple R) :
    CombinatoriallyEquivalent p (p.insertVertex i c hq) :=
  (IsElementaryMove.subdivide p i c hc hq).combinatoriallyEquivalent

end SimplePolygon

end TauCeti
