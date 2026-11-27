/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Region.Basic

/-!
# Regression examples: regions of the triangular lattice

* **A single face.** For `R = {W(0)}`, no edge is interior, the three edges of `W(0)` are the
  boundary edges, `∂R = {(0,0), (1,0), (1,1)}`, and the edge count reads `3 = 2·0 + 3`.
* **The unit hexagon.** For the six faces `R₆` at the origin, the six edges at `0` are interior,
  the six outer edges are boundary edges, `∂R₆` is the set of the six neighbours of `0`,
  `V(R₆) ∖ ∂R₆ = {0}`, and the edge count reads `18 = 2·6 + 6`.
* **Regions spanned by vertex sets.** `Faces({(0,0), (1,0), (1,1), (0,1)}) = {W(0), B(0)}`,
  while `Faces({(0,0), (1,0)}) = ∅` although these two vertices are the endpoints of the edge
  `⟨(0, 0), 0⟩` (from `(0,0)` in direction `e₁`): tilings live on sets of faces, and a vertex
  set is used only through `Faces`.
-/

public section

namespace TauCeti.Examples.LozengeRegion

open TauCeti

/-! ### A single face -/

/-- The white face `W(0)`. -/
abbrev white₀ : TriFace := ⟨(0, 0), true⟩

/-- The black face `B(0)`. -/
abbrev black₀ : TriFace := ⟨(0, 0), false⟩

/-- A single face has no interior edge. -/
theorem interiorEdges_white₀ : interiorEdges {white₀} = ∅ := by
  ext ⟨⟨a, b⟩, k⟩
  fin_cases k <;> simp [mem_interiorEdges_iff]

/-- The boundary edges of a single face are its three edges. -/
theorem boundaryEdges_white₀ : boundaryEdges {white₀} = ↑white₀.edges := by
  ext ⟨⟨a, b⟩, k⟩
  fin_cases k <;> simp [mem_boundaryEdges_iff, Prod.ext_iff]
  omega

/-- A single face has three boundary edges. -/
theorem ncard_boundaryEdges_white₀ : (boundaryEdges {white₀}).ncard = 3 := by
  rw [boundaryEdges_white₀, Set.ncard_coe_finset, TriFace.card_edges]

/-- The boundary vertices of `W(0)` are its three vertices `(0,0)`, `(1,0)`, `(1,1)`. -/
theorem boundaryVertices_white₀ : boundaryVertices {white₀} = {(0, 0), (1, 0), (1, 1)} := by
  ext ⟨x, y⟩
  simp [mem_boundaryVertices, boundaryEdges_white₀, TriEdge.endpoints_def, Prod.ext_iff]
  omega

/-- The edge count `3 |R| = 2 |E°(R)| + |E∂(R)|` for `R = {W(0)}` reads `3 = 2·0 + 3`. -/
example : 3 * ({white₀} : Finset TriFace).card =
    2 * (interiorEdges {white₀}).ncard + (boundaryEdges {white₀}).ncard ∧
    (interiorEdges {white₀}).ncard = 0 ∧ (boundaryEdges {white₀}).ncard = 3 := by
  have h := three_mul_card_eq_two_mul_ncard_interiorEdges_add_ncard_boundaryEdges {white₀}
  simp only [Finset.coe_singleton] at h
  exact ⟨h, by simp [interiorEdges_white₀], ncard_boundaryEdges_white₀⟩

/-! ### The unit hexagon -/

/-- The unit hexagon `R₆`: the six faces at the origin. -/
abbrev hexagon : Finset TriFace := vertexFaces (0, 0)

/-- The six edges at the origin. -/
def edgesAtZero : Finset TriEdge :=
  {⟨(0, 0), 0⟩, ⟨(0, 0), 1⟩, ⟨(0, 0), 2⟩, ⟨(-1, 0), 0⟩, ⟨(0, -1), 1⟩, ⟨(-1, -1), 2⟩}

/-- The six outer edges of the unit hexagon, joining consecutive neighbours of the origin. -/
def outerEdges : Finset TriEdge :=
  {⟨(1, 0), 1⟩, ⟨(0, 1), 0⟩, ⟨(-1, 0), 2⟩, ⟨(-1, -1), 1⟩, ⟨(-1, -1), 0⟩, ⟨(0, -1), 2⟩}

/-- The six neighbours of the origin. -/
def neighborsOfZero : Set (ℤ × ℤ) := {(1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1)}

/-- The interior edges of the unit hexagon are the six edges at the origin. -/
theorem interiorEdges_hexagon : interiorEdges ↑hexagon = ↑edgesAtZero := by
  ext ⟨⟨a, b⟩, k⟩
  fin_cases k <;> simp [mem_interiorEdges_iff, vertexFaces_def, edgesAtZero, Prod.ext_iff] <;>
    omega

/-- The boundary edges of the unit hexagon are its six outer edges. -/
theorem boundaryEdges_hexagon : boundaryEdges ↑hexagon = ↑outerEdges := by
  ext ⟨⟨a, b⟩, k⟩
  fin_cases k <;> simp [mem_boundaryEdges_iff, vertexFaces_def, outerEdges, Prod.ext_iff] <;>
    omega

/-- The unit hexagon has six interior edges. -/
theorem ncard_interiorEdges_hexagon : (interiorEdges ↑hexagon).ncard = 6 := by
  rw [interiorEdges_hexagon, Set.ncard_coe_finset]
  simp [edgesAtZero]

/-- The unit hexagon has six boundary edges. -/
theorem ncard_boundaryEdges_hexagon : (boundaryEdges ↑hexagon).ncard = 6 := by
  rw [boundaryEdges_hexagon, Set.ncard_coe_finset]
  simp [outerEdges]

/-- The boundary vertices of the unit hexagon are the six neighbours of the origin. -/
theorem boundaryVertices_hexagon : boundaryVertices ↑hexagon = neighborsOfZero := by
  ext ⟨x, y⟩
  simp [mem_boundaryVertices, boundaryEdges_hexagon, outerEdges, TriEdge.endpoints_def,
    neighborsOfZero, Prod.ext_iff]
  omega

/-- The vertices of the unit hexagon are the origin and its six neighbours. -/
theorem regionVertices_hexagon : regionVertices ↑hexagon = insert (0, 0) neighborsOfZero := by
  ext ⟨x, y⟩
  simp [vertexFaces_def, neighborsOfZero, Prod.ext_iff]
  omega

/-- The only vertex of the unit hexagon that is not a boundary vertex is the origin. -/
theorem regionVertices_diff_boundaryVertices_hexagon :
    regionVertices ↑hexagon \ boundaryVertices ↑hexagon = {(0, 0)} := by
  rw [regionVertices_hexagon, boundaryVertices_hexagon, Set.insert_sdiff_of_notMem _
    (by simp [neighborsOfZero]), Set.sdiff_self, insert_empty_eq]

/-- The edge count `3 |R| = 2 |E°(R)| + |E∂(R)|` for the unit hexagon reads `18 = 2·6 + 6`. -/
example : 3 * hexagon.card = 2 * (interiorEdges ↑hexagon).ncard + (boundaryEdges ↑hexagon).ncard ∧
    3 * hexagon.card = 18 ∧ 2 * (interiorEdges ↑hexagon).ncard = 12 ∧
    (boundaryEdges ↑hexagon).ncard = 6 := by
  refine ⟨three_mul_card_eq_two_mul_ncard_interiorEdges_add_ncard_boundaryEdges _, by simp,
    by rw [ncard_interiorEdges_hexagon], ncard_boundaryEdges_hexagon⟩

/-! ### Regions spanned by vertex sets -/

/-- The faces spanned by the four vertices of the unit square are `W(0)` and `B(0)`. -/
theorem facesOf_square :
    facesOf {(0, 0), (1, 0), (1, 1), (0, 1)} = {white₀, black₀} := by
  ext ⟨⟨a, b⟩, c⟩
  cases c <;> simp [mem_facesOf, or_imp, forall_and, Prod.ext_iff] <;> omega

/-- The vertices `(0,0)` and `(1,0)` span no face, although they are the endpoints of the edge
`⟨(0, 0), 0⟩` from `(0,0)` in direction `e₁`. -/
theorem facesOf_pair : facesOf {(0, 0), (1, 0)} = ∅ ∧
    (⟨(0, 0), 0⟩ : TriEdge).endpoints = s((0, 0), (1, 0)) := by
  refine ⟨?_, by simp [TriEdge.endpoints_def]⟩
  ext ⟨⟨a, b⟩, c⟩
  cases c <;> simp [mem_facesOf, or_imp, forall_and, Prod.ext_iff] <;> omega

end TauCeti.Examples.LozengeRegion
