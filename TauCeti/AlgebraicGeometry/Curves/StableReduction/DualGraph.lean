/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Relation

/-!
# Dual graphs of geometric nodal curves

This file defines `TauCeti.DualGraph`, a finite nonempty connected graph with natural number
vertex weights, together with its half-edge incidence and valence. No curve appears in this
file: the structure is the combinatorial shape that the dual graph of a proper geometric nodal
curve has, with vertices standing for irreducible components, edges for nodes and weights for
component genera, and the comparison with an actual curve is not defined or proved here.

The graph invariants that only make sense against a curve, the first Betti number and the
arithmetic genus, are deliberately not defined here. They belong with the node-splitting and
normalization stages that construct a curve's dual graph, which are not yet on `main`.

Edges carry two half-edges even when both endpoints agree, so a loop contributes two to the
valence of its vertex. `valence` counts half-edges at a vertex, which is the form in which the
stability condition of a stable curve is stated.

## Main definitions

* `TauCeti.DualGraph`: finite nonempty connected weighted graph.
* `TauCeti.DualGraph.HalfEdge`: an edge together with an endpoint index.
* `TauCeti.DualGraph.incident`: the half-edges meeting a given vertex.
* `TauCeti.DualGraph.valence`: the number of half-edges at a vertex, counting loops twice.

## References

* [Busonero, Melo, Stoppino, *On the complexity group of stable curves*](https://arxiv.org/abs/0808.1529),
  Section 1: the dual graph of a nodal curve, its first Betti number `b₁ = δ - γ + c`, the
  valence conditions defining stability, and the arithmetic genus as the sum of component
  genera plus `b₁`.
* [Liu, *Algebraic Geometry and Arithmetic Curves*](https://global.oup.com/academic/product/algebraic-geometry-and-arithmetic-curves-9780199202492),
  Chapter 10.3: dual graphs of semistable curves, valence counted with loops twice, and the
  genus formula for a connected nodal curve.
-/

public section

namespace TauCeti

universe u

/-- Minimal compiled shape of the dual graph of a geometric nodal curve.

An edge has two half-edges even when both endpoints agree, so loops contribute two to valence. -/
structure DualGraph where
  /-- The vertices, indexing the irreducible components of the curve. -/
  Vertex : Type u
  /-- There are finitely many components. -/
  [vertexFintype : Fintype Vertex]
  /-- A curve has at least one component. -/
  [vertexNonempty : Nonempty Vertex]
  /-- The edges, indexing the nodes of the curve. -/
  Edge : Type u
  /-- There are finitely many nodes. -/
  [edgeFintype : Fintype Edge]
  /-- The two branches of a node, as an edge together with a half-edge index. Both values may
  agree, which is how a node joining a component to itself becomes a loop. -/
  endpoint : Edge → Fin 2 → Vertex
  /-- The geometric genus of each component, the vertex weight. -/
  genus : Vertex → ℕ
  /-- The curve is connected: any two components are joined by a chain of nodes. -/
  connected : ∀ v w, Relation.ReflTransGen
    (fun v w ↦ ∃ e, (endpoint e 0 = v ∧ endpoint e 1 = w) ∨
      (endpoint e 0 = w ∧ endpoint e 1 = v)) v w

namespace DualGraph

variable (G : DualGraph)

instance : Fintype G.Vertex := G.vertexFintype
instance : Nonempty G.Vertex := G.vertexNonempty
instance : Fintype G.Edge := G.edgeFintype
instance : Fintype (G.Edge × Fin 2) := instFintypeProd _ _

/-- Half-edges make the loop-counting convention explicit in the data. -/
abbrev HalfEdge := G.Edge × Fin 2

/-- The vertex incident to a half-edge. -/
def HalfEdge.vertex (h : G.HalfEdge) : G.Vertex := G.endpoint h.1 h.2

-- `by rfl`, not `rfl`: `HalfEdge.vertex` is not `@[expose]`, so a theorem exported from this
-- module cannot unfold it in term mode.
@[simp]
theorem HalfEdge.vertex_mk (e : G.Edge) (i : Fin 2) :
    HalfEdge.vertex G (e, i) = G.endpoint e i := by rfl

section Valence

variable [DecidableEq G.Vertex]

/-- The half-edges meeting a vertex. A node joining a component to itself contributes both of
its half-edges, so it is counted twice. -/
def incident (v : G.Vertex) : Finset G.HalfEdge :=
  {h ∈ Finset.univ | HalfEdge.vertex G h = v}

/-- The valence of a vertex: the number of half-edges meeting it, counting loops twice. The
stability condition of a stable curve is a lower bound on this quantity. -/
def valence (v : G.Vertex) : ℕ := (G.incident v).card

@[simp]
theorem mem_incident {v : G.Vertex} {h : G.HalfEdge} :
    h ∈ G.incident v ↔ HalfEdge.vertex G h = v := by
  simp [incident]

-- `by rfl`, not `rfl`: `valence` is not `@[expose]`, so a theorem exported from this module
-- cannot unfold it in term mode.
@[simp]
theorem valence_def (v : G.Vertex) : G.valence v = (G.incident v).card := by rfl

/-- Every half-edge meets exactly one vertex, so the valences sum to the number of half-edges,
which is twice the number of edges. Stated after unfolding `valence` (see `valence_def`), as
the simp normal form. -/
@[simp]
theorem sum_valence : ∑ v, (G.incident v).card = 2 * Fintype.card G.Edge := by
  classical
  have : ∑ v, (G.incident v).card = Finset.univ.card (α := G.HalfEdge) := by
    simp only [incident]
    rw [← Finset.card_biUnion]
    · congr 1
      ext h
      simp
    · intro x _ y _ hxy
      simp only [Finset.disjoint_left, Finset.mem_filter]
      rintro a ⟨-, rfl⟩ ⟨-, h⟩
      exact hxy h
  rw [this, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]

end Valence

end DualGraph

end TauCeti
