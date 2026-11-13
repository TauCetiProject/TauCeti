/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.BarycentricSubdivision
public import TauCeti.Combinatorics.Graph.Serre.Card
public import TauCeti.Combinatorics.PolygonalComplex.Examples
public import Mathlib.Basic.Finite.Sum
import Mathlib.Tactic.FinCases

/-!
# Triangulated polygonal complexes and barycentric subdivision

A polygonal complex is *triangulated* (`PolygonalComplex.IsTriangulated`) when it is the
incidence structure of a simplicial complex of dimension at most two. These are the conditions
(C1)–(C3) of Gallier and Xu under which a cell complex is a triangulated complex: every face is a
triangle, a dart is determined by its two endpoints, so that there are no loops and no parallel
edges, and distinct faces have distinct sets of vertices.

The *barycentric subdivision* `C.barycentricSubdivision` of a polygonal complex `C` has as its
vertices the vertices of `C`, the midpoints of the geometric edges of `C` and the centres of the
faces of `C`. Its edges are the two halves of every edge of `C`, as in the barycentric subdivision
`SerreGraph.barycentricSubdivision` of the one-skeleton, and, for every corner `c` of a face `f`,
an edge from the centre of `f` to the vertex of `c` and an edge from the centre of `f` to the
midpoint of the side of `f` starting at `c`. The side starting at `c` carries two triangles: the
centre, the vertex of `c` and the midpoint; and the centre, the midpoint and the vertex at the end
of the side. These are the first two steps of the proof of Gallier and Xu that every cell complex
can be refined to a triangulated complex: every edge is subdivided, and every face is coned off
from a central vertex.

A single subdivision is not triangulated in general: the centre of the torus face `a b a⁻¹ b⁻¹` is
joined to its single vertex by four parallel edges, one for each corner. What one subdivision
achieves is *regularity* (`PolygonalComplex.IsRegular`, as for regular CW complexes): no edge is a
loop and every face is an embedded polygon, with its corners at distinct vertices and its sides on
distinct geometric edges. Every barycentric subdivision is regular, and the barycentric subdivision
of a complex is triangulated exactly when the complex is regular. Hence the second barycentric
subdivision of every polygonal complex is triangulated, as for the Δ-complexes of Hatcher's
exercise. Barycentric subdivision keeps the Euler characteristic.

## Implementation notes

Gallier and Xu complete their proof by splitting every triangle of the first subdivision into four
triangles. That need not give a triangulated complex: for the sphere digon `a a⁻¹`, two triangles
of the first subdivision share two edges, and their corner triangles at the common vertex get two
parallel inner edges. The second barycentric subdivision avoids this.

## Main definitions

* `TauCeti.PolygonalComplex.IsTriangulated`: the complex is a simplicial complex of dimension at
  most two.
* `TauCeti.PolygonalComplex.IsRegular`: no edge is a loop and every face is an embedded polygon.
* `TauCeti.PolygonalComplex.barycentricSubdivision`: the barycentric subdivision, with its
  one-skeleton `TauCeti.PolygonalComplex.barycentricGraph` and its triangles
  `TauCeti.PolygonalComplex.barycentricSide`.

## Main results

* `TauCeti.PolygonalComplex.IsTriangulated.isRegular`: a triangulated complex is regular.
* `TauCeti.PolygonalComplex.isRegular_barycentricSubdivision`: every barycentric subdivision is
  regular.
* `TauCeti.PolygonalComplex.isTriangulated_barycentricSubdivision_iff`: the barycentric subdivision
  is triangulated exactly when the complex is regular.
* `TauCeti.PolygonalComplex.isTriangulated_barycentricSubdivision_barycentricSubdivision`: the
  second barycentric subdivision is triangulated.
* `TauCeti.PolygonalComplex.eulerChar_barycentricSubdivision`: the Euler characteristic is
  unchanged.
* `TauCeti.SurfaceModel.isTriangulated_torus_barycentricSubdivision_barycentricSubdivision`,
  `TauCeti.SurfaceModel.not_isTriangulated_torus_barycentricSubdivision`,
  `TauCeti.SurfaceModel.not_isTriangulated_sphere_barycentricSubdivision`: the torus needs two
  subdivisions, and the sphere digon `a a⁻¹` is not regular.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6, conditions (C1)–(C3), p. 84, and Proposition 6.1, pp. 86–87.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §2.1, Exercise 23.
-/

public section

universe u v w

namespace TauCeti

namespace PolygonalComplex

variable (C : PolygonalComplex.{u, v, w})

/-! ### Triangulated and regular complexes -/

/-- The vertices of a face: the vertices at its corners, where its sides start. -/
def faceVertices (f : C.Face) : Set C.graph.V := Set.range fun i => C.graph.src (C.side f i)

theorem faceVertices_def (f : C.Face) :
    C.faceVertices f = Set.range fun i => C.graph.src (C.side f i) := (rfl)

variable {C} in
@[simp] theorem mem_faceVertices_iff {f : C.Face} {x : C.graph.V} :
    x ∈ C.faceVertices f ↔ ∃ i, C.graph.src (C.side f i) = x :=
  Iff.rfl

/-- A polygonal complex is triangulated when it is the incidence structure of a simplicial complex
of dimension at most two: every face is a triangle, a dart is determined by its endpoints, and
distinct faces have distinct sets of vertices. These are the conditions (C1)–(C3) of Gallier and
Xu, with faces compared by their vertex sets as simplices are. -/
structure IsTriangulated : Prop where
  /-- Every face is a triangle. -/
  sides_eq_three (f : C.Face) : C.sides f = 3
  /-- A dart is determined by its two endpoints: there are no loops and no parallel edges. -/
  eq_of_src_eq_of_tgt_eq ⦃e e' : C.graph.E⦄ :
    C.graph.src e = C.graph.src e' → C.graph.tgt e = C.graph.tgt e' → e = e'
  /-- Distinct faces have distinct sets of vertices. -/
  faceVertices_injective : Function.Injective C.faceVertices

/-- A polygonal complex is regular, as a regular CW complex, when no edge is a loop and every face
is an embedded polygon: its corners sit at distinct vertices and its sides lie on distinct
geometric edges. The condition on the sides matters only for faces with two sides. -/
structure IsRegular : Prop where
  /-- No edge is a loop. -/
  src_ne_tgt (e : C.graph.E) : C.graph.src e ≠ C.graph.tgt e
  /-- The corners of a face sit at distinct vertices: its sides start at distinct vertices. -/
  src_side_injective (f : C.Face) :
    Function.Injective fun i : Fin (C.sides f) => C.graph.src (C.side f i)
  /-- The sides of a face lie on distinct geometric edges. -/
  toGeomEdge_side_injective (f : C.Face) :
    Function.Injective fun i : Fin (C.sides f) => C.graph.toGeomEdge (C.side f i)

variable {C}

/-- In a regular complex, two corners of the same face at the same vertex coincide. -/
theorem IsRegular.eq_of_fst_eq_of_cornerVertex_eq (h : C.IsRegular) {c c' : C.Corner}
    (hf : c.1 = c'.1) (hv : C.cornerVertex c = C.cornerVertex c') : c = c' := by
  obtain ⟨f, i⟩ := c
  obtain ⟨f', i'⟩ := c'
  obtain rfl : f = f' := hf
  rw [← src_outgoing, ← src_outgoing, outgoing_def, outgoing_def] at hv
  exact congrArg (Sigma.mk f) (h.src_side_injective f hv)

/-- In a regular complex, two sides of the same face on the same geometric edge coincide. -/
theorem IsRegular.eq_of_fst_eq_of_toGeomEdge_outgoing_eq (h : C.IsRegular) {c c' : C.Corner}
    (hf : c.1 = c'.1)
    (he : C.graph.toGeomEdge (C.outgoing c) = C.graph.toGeomEdge (C.outgoing c')) : c = c' := by
  obtain ⟨f, i⟩ := c
  obtain ⟨f', i'⟩ := c'
  obtain rfl : f = f' := hf
  rw [outgoing_def, outgoing_def] at he
  exact congrArg (Sigma.mk f) (h.toGeomEdge_side_injective f he)

/-- In a regular complex, a dart is determined by its source and its geometric edge. -/
theorem IsRegular.eq_of_src_eq_of_toGeomEdge_eq (h : C.IsRegular) {e e' : C.graph.E}
    (hs : C.graph.src e = C.graph.src e') (he : C.graph.toGeomEdge e = C.graph.toGeomEdge e') :
    e = e' := by
  obtain rfl | rfl := C.graph.toGeomEdge_eq_toGeomEdge_iff.1 he
  · rfl
  · exact absurd (hs.trans (C.graph.src_rev e)) (h.src_ne_tgt e)

/-- A triangulated complex has no loops. -/
theorem IsTriangulated.src_ne_tgt (h : C.IsTriangulated) (e : C.graph.E) :
    C.graph.src e ≠ C.graph.tgt e := fun he =>
  C.graph.rev_ne e (h.eq_of_src_eq_of_tgt_eq (by rw [SerreGraph.src_rev, he])
    (by rw [SerreGraph.tgt_rev, he]))

/-- A triangulated complex is regular. -/
theorem IsTriangulated.isRegular (h : C.IsTriangulated) : C.IsRegular := by
  -- On a triangle two distinct positions are cyclically adjacent, and rotating twice does not
  -- return to the start.
  have adj : ∀ {n : ℕ}, n = 3 → ∀ i j : Fin n, i ≠ j → finRotate n i = j ∨ finRotate n j = i := by
    rintro _ rfl
    decide
  have rot : ∀ {n : ℕ}, n = 3 → ∀ i : Fin n, finRotate n (finRotate n i) ≠ i := by
    rintro _ rfl
    decide
  have hv (f : C.Face) :
      Function.Injective fun i : Fin (C.sides f) => C.graph.src (C.side f i) := by
    intro i j hij
    dsimp only at hij
    by_contra hne
    rcases adj (h.sides_eq_three f) i j hne with hj | hi
    · exact h.src_ne_tgt (C.side f i) (by rw [C.tgt_side, hj, hij])
    · exact h.src_ne_tgt (C.side f j) (by rw [C.tgt_side, hi, hij])
  refine ⟨h.src_ne_tgt, hv, fun f i j hij => ?_⟩
  rcases C.graph.toGeomEdge_eq_toGeomEdge_iff.1 hij with he | he
  · exact hv f (by simp only [he])
  · -- The side `j` runs backwards along the side `i`: then `j` follows `i` and `i` follows `j`,
    -- which is impossible on a triangle.
    have h₁ : finRotate _ i = j := hv f (by
      simp only [he, SerreGraph.src_rev, ← C.tgt_side])
    have h₂ : finRotate _ j = i := hv f (by
      simp only [← C.tgt_side, he, SerreGraph.tgt_rev])
    exact absurd (by rw [h₁, h₂]) (rot (h.sides_eq_three f) i)

variable (C)

/-! ### The barycentric subdivision -/

/-- The one-skeleton of the barycentric subdivision. Its vertices are the vertices and the edge
midpoints of `C` (the vertices of `C.graph.barycentricSubdivision`) and the face centres of `C`.
Its darts are the halves `(.inl e, b)` of the darts `e` of `C`, the edges `(.inr (.inl c), b)` from
the centre of the face of the corner `c` to the vertex of `c`, and the edges `(.inr (.inr c), b)`
from that centre to the midpoint of the side starting at `c`; for the last two, `b = true` is the
direction leaving the centre. It is reducible, so that its vertices and darts are seen to be these
sums. -/
abbrev barycentricGraph : SerreGraph.{max u v w, max v w} where
  V := C.graph.barycentricSubdivision.V ⊕ C.Face
  E := (C.graph.E ⊕ C.Corner ⊕ C.Corner) × Bool
  src x := match x with
    | (.inl e, b) => .inl (C.graph.barycentricSubdivision.src (C.graph.barycentricDart e b))
    | (.inr (.inl c), true) => .inr c.1
    | (.inr (.inl c), false) => .inl (C.graph.barycentricVertex (C.cornerVertex c))
    | (.inr (.inr c), true) => .inr c.1
    | (.inr (.inr c), false) =>
      .inl (C.graph.barycentricMidpoint (C.graph.toGeomEdge (C.outgoing c)))
  rev x := (x.1, !x.2)
  rev_rev x := by simp
  rev_ne x := by simp [Prod.ext_iff]

/-- A dart of the barycentric subdivision ends where its reverse starts. -/
@[simp] theorem barycentricGraph_tgt (x : C.graph.E ⊕ C.Corner ⊕ C.Corner) (b : Bool) :
    C.barycentricGraph.tgt (x, b) = C.barycentricGraph.src (x, !b) := (rfl)

/-- The sides of the two triangles of the barycentric subdivision on the side starting at the
corner `c`: the triangle `(c, false)` runs from the centre to the vertex of `c`, along the first
half of the side to its midpoint, and back to the centre; the triangle `(c, true)` runs from the
centre to the midpoint, along the second half of the side to the vertex of the next corner, and
back to the centre. -/
def barycentricSide : C.Corner × Bool → Fin 3 → C.barycentricGraph.E
  | (c, false) => ![(.inr (.inl c), true), (.inl (C.outgoing c), true), (.inr (.inr c), false)]
  | (c, true) => ![(.inr (.inr c), true), (.inl (C.graph.rev (C.outgoing c)), false),
      (.inr (.inl (C.nextCorner c)), false)]

/-- The sides of the triangle `(c, false)` of the barycentric subdivision. -/
@[simp] theorem barycentricSide_false (c : C.Corner) :
    C.barycentricSide (c, false) =
      ![(.inr (.inl c), true), (.inl (C.outgoing c), true), (.inr (.inr c), false)] := (rfl)

/-- The sides of the triangle `(c, true)` of the barycentric subdivision. -/
@[simp] theorem barycentricSide_true (c : C.Corner) :
    C.barycentricSide (c, true) = ![(.inr (.inr c), true),
      (.inl (C.graph.rev (C.outgoing c)), false), (.inr (.inl (C.nextCorner c)), false)] := (rfl)

/-- The sides of each triangle of the barycentric subdivision form a closed dart sequence. -/
theorem tgt_barycentricSide (f : C.Corner × Bool) (i : Fin 3) :
    C.barycentricGraph.tgt (C.barycentricSide f i) =
      C.barycentricGraph.src (C.barycentricSide f (finRotate 3 i)) := by
  obtain ⟨c, _ | _⟩ := f <;> fin_cases i <;> simp

/-- The barycentric subdivision of a polygonal complex: its one-skeleton is `C.barycentricGraph`,
and it has two triangles `(c, false)` and `(c, true)` on the side starting at each corner `c`. It
is reducible, so that its one-skeleton and faces are seen to be `C.barycentricGraph` and
`C.Corner × Bool`. -/
abbrev barycentricSubdivision : PolygonalComplex.{max u v w, max v w, w} where
  graph := C.barycentricGraph
  Face := C.Corner × Bool
  sides _ := 3
  sides_pos _ := Nat.succ_pos 2
  side := C.barycentricSide
  tgt_side := C.tgt_barycentricSide

/-- The vertices of a triangle of the barycentric subdivision: the centre of its face, the
midpoint of its side, and the vertex at the start of that side (for `b = false`) or at its end
(for `b = true`). -/
@[simp] theorem faceVertices_barycentricSubdivision (c : C.Corner) (b : Bool) :
    C.barycentricSubdivision.faceVertices (c, b) =
      {.inr c.1, .inl (C.graph.barycentricMidpoint (C.graph.toGeomEdge (C.outgoing c))),
        .inl (C.graph.barycentricVertex (C.cornerVertex (if b then C.nextCorner c else c)))} := by
  ext x
  rw [mem_faceVertices_iff]
  cases b <;> simp [Fin.exists_fin_succ, eq_comm, or_comm]

/-- The barycentric subdivision of a polygonal complex is regular. -/
@[simp] theorem isRegular_barycentricSubdivision : C.barycentricSubdivision.IsRegular where
  src_ne_tgt := by
    rintro ⟨e | c | c, _ | _⟩ <;> simp
  src_side_injective := by
    rintro ⟨c, _ | _⟩ i j hij <;> fin_cases i <;> fin_cases j <;> simp_all
  toGeomEdge_side_injective := by
    rintro ⟨c, _ | _⟩ i j hij <;>
      rcases C.barycentricGraph.toGeomEdge_eq_toGeomEdge_iff.1 hij with hij | hij <;>
      fin_cases i <;> fin_cases j <;> simp_all

variable {C}

/-- In a regular complex, the corner at the start of a side and the corner at its end sit at
distinct vertices. -/
theorem IsRegular.cornerVertex_ne_cornerVertex_nextCorner (h : C.IsRegular) (c : C.Corner) :
    C.cornerVertex c ≠ C.cornerVertex (C.nextCorner c) := by
  rw [← tgt_outgoing, ← src_outgoing]
  exact h.src_ne_tgt _

/-- In the barycentric subdivision of a regular complex, a dart is determined by its endpoints. -/
private theorem IsRegular.eq_of_src_eq_of_tgt_eq_barycentricSubdivision (h : C.IsRegular)
    {x y : C.barycentricGraph.E} (hs : C.barycentricGraph.src x = C.barycentricGraph.src y)
    (ht : C.barycentricGraph.tgt x = C.barycentricGraph.tgt y) : x = y := by
  -- Two darts of different kinds have endpoints of different kinds; two darts of the same kind
  -- with the same endpoints come from the same dart or corner of `C`, by regularity.
  rcases x with ⟨e | c | c, _ | _⟩ <;> rcases y with ⟨e' | c' | c', _ | _⟩ <;>
    simp only [barycentricGraph_tgt, Bool.not_true, Bool.not_false, Prod.mk.injEq,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, SerreGraph.barycentricSubdivision_src_true,
      SerreGraph.barycentricSubdivision_src_false, SerreGraph.barycentricVertex_inj,
      SerreGraph.barycentricMidpoint_inj, SerreGraph.barycentricVertex_ne_barycentricMidpoint,
      SerreGraph.barycentricMidpoint_ne_barycentricVertex, and_true] at hs ht ⊢ <;>
    first
      | exact h.eq_of_src_eq_of_toGeomEdge_eq hs ht
      | exact h.eq_of_src_eq_of_toGeomEdge_eq ht hs
      | exact h.eq_of_fst_eq_of_cornerVertex_eq hs ht
      | exact h.eq_of_fst_eq_of_cornerVertex_eq ht hs
      | exact h.eq_of_fst_eq_of_toGeomEdge_outgoing_eq hs ht
      | exact h.eq_of_fst_eq_of_toGeomEdge_outgoing_eq ht hs

/-- In the barycentric subdivision of a regular complex, a triangle is determined by its vertices:
the centre gives the face, the midpoint gives the side, and the vertex gives the half of the
side. -/
private theorem IsRegular.faceVertices_barycentricSubdivision_injective (h : C.IsRegular) :
    Function.Injective C.barycentricSubdivision.faceVertices := by
  rintro ⟨c, b⟩ ⟨c', b'⟩ hcc'
  have hmem := Set.ext_iff.1 hcc'
  simp only [faceVertices_barycentricSubdivision, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hmem
  have h₁ := (hmem (.inr c.1)).1 (.inl rfl)
  have h₂ := (hmem (.inl (C.graph.barycentricMidpoint (C.graph.toGeomEdge (C.outgoing c))))).1
    (.inr (.inl rfl))
  simp only [Sum.inr.injEq, reduceCtorEq, Sum.inl.injEq, SerreGraph.barycentricMidpoint_inj,
    SerreGraph.barycentricMidpoint_ne_barycentricVertex, or_false, false_or] at h₁ h₂
  obtain rfl := h.eq_of_fst_eq_of_toGeomEdge_outgoing_eq h₁ h₂
  have h₃ := (hmem (.inl (C.graph.barycentricVertex
    (C.cornerVertex (if b then C.nextCorner c else c))))).1 (.inr (.inr rfl))
  simp only [reduceCtorEq, Sum.inl.injEq, SerreGraph.barycentricVertex_ne_barycentricMidpoint,
    SerreGraph.barycentricVertex_inj, false_or] at h₃
  cases b <;> cases b'
  · rfl
  · exact absurd h₃ (h.cornerVertex_ne_cornerVertex_nextCorner c)
  · exact absurd h₃.symm (h.cornerVertex_ne_cornerVertex_nextCorner c)
  · rfl

/-- The barycentric subdivision of a regular polygonal complex is triangulated. -/
theorem IsRegular.isTriangulated_barycentricSubdivision (h : C.IsRegular) :
    C.barycentricSubdivision.IsTriangulated where
  sides_eq_three _ := rfl
  eq_of_src_eq_of_tgt_eq _ _ := h.eq_of_src_eq_of_tgt_eq_barycentricSubdivision
  faceVertices_injective := h.faceVertices_barycentricSubdivision_injective

/-- A polygonal complex whose barycentric subdivision is triangulated is regular. -/
theorem isRegular_of_isTriangulated_barycentricSubdivision
    (h : C.barycentricSubdivision.IsTriangulated) : C.IsRegular where
  src_ne_tgt e he := by
    have := h.eq_of_src_eq_of_tgt_eq (e := (.inl e, true)) (e' := (.inl (C.graph.rev e), true))
      (by simp [he]) (by simp)
    simp only [Prod.mk.injEq, Sum.inl.injEq, and_true] at this
    exact C.graph.rev_ne e this.symm
  src_side_injective f i j hij := by
    have := h.eq_of_src_eq_of_tgt_eq (e := (.inr (.inl ⟨f, i⟩), true))
      (e' := (.inr (.inl ⟨f, j⟩), true)) rfl (by simpa [← src_outgoing, outgoing_def] using hij)
    simpa using this
  toGeomEdge_side_injective f i j hij := by
    have := h.eq_of_src_eq_of_tgt_eq (e := (.inr (.inr ⟨f, i⟩), true))
      (e' := (.inr (.inr ⟨f, j⟩), true)) rfl (by simpa [outgoing_def] using hij)
    simpa using this

variable (C)

/-- The barycentric subdivision of a polygonal complex is triangulated exactly when the complex
is regular. -/
@[simp] theorem isTriangulated_barycentricSubdivision_iff :
    C.barycentricSubdivision.IsTriangulated ↔ C.IsRegular :=
  ⟨isRegular_of_isTriangulated_barycentricSubdivision,
    IsRegular.isTriangulated_barycentricSubdivision⟩

/-- The second barycentric subdivision of a polygonal complex is triangulated. -/
theorem isTriangulated_barycentricSubdivision_barycentricSubdivision :
    C.barycentricSubdivision.barycentricSubdivision.IsTriangulated :=
  C.isRegular_barycentricSubdivision.isTriangulated_barycentricSubdivision

variable {C} in
/-- The barycentric subdivision of a triangulated complex is triangulated. -/
theorem IsTriangulated.barycentricSubdivision (h : C.IsTriangulated) :
    C.barycentricSubdivision.IsTriangulated :=
  h.isRegular.isTriangulated_barycentricSubdivision

/-- The barycentric subdivision does not change the Euler characteristic. -/
@[simp] theorem eulerChar_barycentricSubdivision [Finite C.graph.V] [Finite C.graph.E]
    [Finite C.Face] : C.barycentricSubdivision.eulerChar = C.eulerChar := by
  have h₁ := C.barycentricGraph.card_E_eq_two_mul_card_geomEdge
  have h₂ := C.graph.card_E_eq_two_mul_card_geomEdge
  simp [eulerChar_def] at h₁ ⊢
  omega

/-- A one-vertex polygon is not regular: its edges are loops. -/
theorem not_isRegular_polygon {α : Type*} (w : List (α × Bool)) (hw : w ≠ []) :
    ¬(polygon w hw).IsRegular := fun h =>
  h.src_ne_tgt (w.head hw) (Subsingleton.elim _ _)

end PolygonalComplex

namespace SurfaceModel

open PolygonalComplex

/-- The torus polygon `a b a⁻¹ b⁻¹` is not regular: its edges are loops. -/
theorem not_isRegular_torus : ¬torus.IsRegular := by
  rw [torus_toPolygonalComplex]
  exact not_isRegular_polygon _ _

/-- The barycentric subdivision of the torus is not triangulated: the centre of its face is joined
to its single vertex by four parallel edges, one for each corner. -/
theorem not_isTriangulated_torus_barycentricSubdivision :
    ¬torus.barycentricSubdivision.IsTriangulated :=
  (isTriangulated_barycentricSubdivision_iff _).not.2 not_isRegular_torus

/-- The second barycentric subdivision of the torus is triangulated. -/
theorem isTriangulated_torus_barycentricSubdivision_barycentricSubdivision :
    torus.barycentricSubdivision.barycentricSubdivision.IsTriangulated :=
  isTriangulated_barycentricSubdivision_barycentricSubdivision _

/-- The second barycentric subdivision of the torus has Euler characteristic `0`. -/
theorem eulerChar_torus_barycentricSubdivision_barycentricSubdivision :
    torus.barycentricSubdivision.barycentricSubdivision.eulerChar = 0 := by
  rw [eulerChar_barycentricSubdivision, eulerChar_barycentricSubdivision]
  exact eulerChar_torus

/-- The sphere digon `a a⁻¹` is not regular: its two sides lie on the same edge, although its two
corners sit at distinct vertices and its edge is not a loop. -/
theorem not_isRegular_sphere : ¬sphere.IsRegular := by
  rw [sphere_toPolygonalComplex]
  intro h
  have := h.toGeomEdge_side_injective () (a₁ := ⟨0, by decide⟩) (a₂ := ⟨1, by decide⟩)
    (SerreGraph.segment.toGeomEdge_rev false).symm
  exact absurd this (by decide)

/-- The barycentric subdivision of the sphere digon is not triangulated: the centre of its face is
joined to the midpoint of its edge by two parallel edges, one for each side. -/
theorem not_isTriangulated_sphere_barycentricSubdivision :
    ¬sphere.barycentricSubdivision.IsTriangulated :=
  (isTriangulated_barycentricSubdivision_iff _).not.2 not_isRegular_sphere

end SurfaceModel

end TauCeti
