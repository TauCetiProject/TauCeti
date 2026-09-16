/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Polygon.Basic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Boundary
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity

/-!
# The combinatorial polygon of Schwarz--Christoffel boundary values

A finite indexed family of Schwarz--Christoffel prevertices supplies a list of complex boundary
values.  This file appends the common boundary value at infinity and packages the resulting cyclic
list as Mathlib's `Polygon`.  The indexing here is purely combinatorial: no ordering or distinctness
assumption is imposed on the prevertices.

When the indices list distinct prevertices in increasing order and the relevant integrability and
decay hypotheses hold, the extra vertex at infinity records the subdivision of the closing boundary
side into the two unbounded real intervals.  For the classical exponent sum `-2` it need not be a
geometric corner: the two adjacent polygon edges may be collinear.

The edge formulas below separate the three positions in the index list.  There is one edge between
each pair of index-successive finite vertices, one edge from the last-indexed finite vertex to
infinity, and one from infinity to the first-indexed finite vertex.  Their union is the polygon
boundary.  Under the ordering and analytic hypotheses above, these are the three kinds of boundary
interval.  The formulas are the finite combinatorial interface used to identify the range of the
compactified Schwarz--Christoffel boundary with a polygonal boundary.

## Main definitions

* `TauCeti.schwarzChristoffelPolygon` -- the polygon whose vertices are the finite
  Schwarz--Christoffel vertices followed by the vertex at infinity.

## Main results

* `TauCeti.schwarzChristoffelPolygon_edgeSet_castSucc_castSucc` -- the bounded edges join
  consecutive finite vertices.
* `TauCeti.schwarzChristoffelPolygon_edgeSet_last_prevertex` -- the penultimate edge joins the
  last finite vertex to the vertex at infinity.
* `TauCeti.schwarzChristoffelPolygon_edgeSet_last` -- the final edge joins the vertex at infinity
  back to the first finite vertex.
* `TauCeti.schwarzChristoffelPolygon_boundary` -- the polygon boundary is the union of those
  three kinds of edge.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {n : ℕ}

/-- The polygon formed by the Schwarz--Christoffel boundary values at a nonempty, finitely indexed
family of prevertices, with the common boundary value at infinity appended as the final vertex.

The prevertices are indexed by `Fin (n + 1)`, so there is always a first and a last finite vertex.
The resulting polygon has `n + 2` vertices.  As with the underlying total definitions, its finite
vertices and its vertex at infinity represent actual limits under the corresponding integrability
and decay hypotheses. -/
def schwarzChristoffelPolygon (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) :
    Polygon ℂ (n + 2) where
  vertices := Fin.lastCases (schwarzChristoffelVertexAtInfinity a e z₀)
    (schwarzChristoffelVertex a e z₀)

/-- A finite vertex of the Schwarz--Christoffel polygon is the boundary value at the
corresponding prevertex. -/
@[simp]
theorem schwarzChristoffelPolygon_apply_castSucc (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (i : Fin (n + 1)) :
    schwarzChristoffelPolygon a e z₀ i.castSucc =
      schwarzChristoffelVertex a e z₀ i := by
  rw [schwarzChristoffelPolygon]
  -- Reduce the structure projection explicitly so that `Fin.lastCases_castSucc` applies without
  -- unfolding either of the opaque analytic vertex definitions.
  change @Fin.lastCases (n + 1) (fun _ => ℂ)
    (schwarzChristoffelVertexAtInfinity a e z₀)
    (schwarzChristoffelVertex a e z₀) i.castSucc = _
  exact Fin.lastCases_castSucc i

/-- The final vertex of the Schwarz--Christoffel polygon is its common boundary value at
infinity. -/
@[simp]
theorem schwarzChristoffelPolygon_apply_last (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) :
    schwarzChristoffelPolygon a e z₀ (Fin.last (n + 1)) =
      schwarzChristoffelVertexAtInfinity a e z₀ := by
  rw [schwarzChristoffelPolygon]
  -- Reduce the structure projection explicitly while leaving the analytic vertex opaque.
  change @Fin.lastCases (n + 1) (fun _ => ℂ)
    (schwarzChristoffelVertexAtInfinity a e z₀)
    (schwarzChristoffelVertex a e z₀) (Fin.last (n + 1)) = _
  exact Fin.lastCases_last

/-- When a finite prevertex has integrable total exponent, the corresponding polygon vertex is
the canonical boundary value of the Schwarz--Christoffel map there. -/
theorem schwarzChristoffelPolygon_apply_castSucc_eq_boundary (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (i : Fin (n + 1))
    (hi : -1 < ∑ j with a j = a i, e j) :
    schwarzChristoffelPolygon a e z₀ i.castSucc =
      schwarzChristoffelBoundary a e z₀ (a i) := by
  rw [schwarzChristoffelPolygon_apply_castSucc,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ i hi]

/-! ### The three kinds of edge -/

/-- A bounded edge of the Schwarz--Christoffel polygon joins the vertices at two consecutive
indices. -/
@[simp]
theorem schwarzChristoffelPolygon_edgeSet_castSucc_castSucc (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (i : Fin n) :
    (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc =
      segment ℝ (schwarzChristoffelVertex a e z₀ i.castSucc)
        (schwarzChristoffelVertex a e z₀ i.succ) := by
  rw [Polygon.edgeSet, affineSegment_eq_segment]
  have hrotate : finRotate (n + 2) i.castSucc.castSucc = i.succ.castSucc := by
    apply Fin.ext
    simp
  rw [schwarzChristoffelPolygon_apply_castSucc, hrotate,
    schwarzChristoffelPolygon_apply_castSucc]

/-- The edge after the last finite prevertex joins its boundary value to the common value at
infinity. -/
@[simp]
theorem schwarzChristoffelPolygon_edgeSet_last_prevertex (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) :
    (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last n).castSucc =
      segment ℝ (schwarzChristoffelVertex a e z₀ (Fin.last n))
        (schwarzChristoffelVertexAtInfinity a e z₀) := by
  rw [Polygon.edgeSet, affineSegment_eq_segment]
  have hrotate : finRotate (n + 2) (Fin.last n).castSucc = Fin.last (n + 1) := by
    apply Fin.ext
    simp
  rw [schwarzChristoffelPolygon_apply_castSucc, hrotate,
    schwarzChristoffelPolygon_apply_last]

/-- The final edge of the Schwarz--Christoffel polygon joins the common value at infinity back to
the first finite boundary value. -/
@[simp]
theorem schwarzChristoffelPolygon_edgeSet_last (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) :
    (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 1)) =
      segment ℝ (schwarzChristoffelVertexAtInfinity a e z₀)
        (schwarzChristoffelVertex a e z₀ 0) := by
  rw [Polygon.edgeSet, affineSegment_eq_segment]
  rw [finRotate_last, schwarzChristoffelPolygon_apply_last]
  -- Present `0` through the finite-vertex embedding so the corresponding simp theorem applies.
  change segment ℝ (schwarzChristoffelVertexAtInfinity a e z₀)
    (schwarzChristoffelPolygon a e z₀ (0 : Fin (n + 1)).castSucc) = _
  rw [schwarzChristoffelPolygon_apply_castSucc]

/-! ### The complete polygon boundary -/

/-- The boundary of the Schwarz--Christoffel polygon is the union of the bounded edges between
successive finite vertices and the two edges incident to the vertex at infinity. -/
theorem schwarzChristoffelPolygon_boundary (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) :
    (schwarzChristoffelPolygon a e z₀).boundary ℝ =
      (⋃ i : Fin n, segment ℝ (schwarzChristoffelVertex a e z₀ i.castSucc)
        (schwarzChristoffelVertex a e z₀ i.succ)) ∪
      segment ℝ (schwarzChristoffelVertex a e z₀ (Fin.last n))
        (schwarzChristoffelVertexAtInfinity a e z₀) ∪
      segment ℝ (schwarzChristoffelVertexAtInfinity a e z₀)
        (schwarzChristoffelVertex a e z₀ 0) := by
  ext z
  simp only [Polygon.boundary, mem_iUnion, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    refine Fin.lastCases (motive := fun i =>
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i →
        ((∃ i : Fin n, z ∈ segment ℝ (schwarzChristoffelVertex a e z₀ i.castSucc)
          (schwarzChristoffelVertex a e z₀ i.succ)) ∨
        z ∈ segment ℝ (schwarzChristoffelVertex a e z₀ (Fin.last n))
          (schwarzChristoffelVertexAtInfinity a e z₀)) ∨
        z ∈ segment ℝ (schwarzChristoffelVertexAtInfinity a e z₀)
          (schwarzChristoffelVertex a e z₀ 0)) ?_ ?_ i hi
    · intro h
      exact Or.inr (by simpa using h)
    · intro j h
      refine Fin.lastCases (motive := fun j =>
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc →
          ((∃ i : Fin n, z ∈ segment ℝ
            (schwarzChristoffelVertex a e z₀ i.castSucc)
            (schwarzChristoffelVertex a e z₀ i.succ)) ∨
          z ∈ segment ℝ (schwarzChristoffelVertex a e z₀ (Fin.last n))
            (schwarzChristoffelVertexAtInfinity a e z₀)) ∨
          z ∈ segment ℝ (schwarzChristoffelVertexAtInfinity a e z₀)
            (schwarzChristoffelVertex a e z₀ 0)) ?_ ?_ j h
      · intro h
        exact Or.inl (Or.inr (by simpa using h))
      · intro k h
        exact Or.inl (Or.inl ⟨k, by simpa using h⟩)
  · rintro ((⟨i, hi⟩ | hi) | hi)
    · exact ⟨i.castSucc.castSucc, by simpa using hi⟩
    · exact ⟨(Fin.last n).castSucc, by simpa using hi⟩
    · exact ⟨Fin.last (n + 1), by simpa using hi⟩

end TauCeti
