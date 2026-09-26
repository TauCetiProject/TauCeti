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

The **dual graph** of a proper geometric nodal curve is the finite connected weighted graph whose
vertices are the irreducible components, whose edges are the nodes (with two half-edges even when
both endpoints agree, so loops contribute two to valence), and whose vertex weights are the genera
of the components.

The arithmetic genus of the curve is recovered from this combinatorial data alone: it is the sum
of the component genera plus the first Betti number of the underlying graph, the latter measuring
how many independent cycles the nodes create.

## Main definitions

* `TauCeti.DualGraph`: finite nonempty connected weighted dual graph.
* `TauCeti.DualGraph.HalfEdge`: an edge together with an endpoint index.
* `TauCeti.DualGraph.firstBetti`: first Betti number by Euler characteristic.
* `TauCeti.DualGraph.arithmeticGenus`: arithmetic genus `∑ genus + firstBetti`.

## References

* [Caporaso, *On the complexity group of stable curves*](https://arxiv.org/abs/0808.1529),
  Section 1: the dual graph of a nodal curve, its first Betti number `b₁ = δ - γ + c`, and the
  arithmetic genus as the sum of component genera plus `b₁`.
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

/-- Half-edges make the loop-counting convention explicit in the data. -/
abbrev HalfEdge := G.Edge × Fin 2

/-- The vertex incident to a half-edge. -/
def HalfEdge.vertex (h : G.HalfEdge) : G.Vertex := G.endpoint h.1 h.2

-- `by rfl`, not `rfl`: `HalfEdge.vertex` is not `@[expose]`, so a theorem exported from this
-- module cannot unfold it in term mode.
@[simp]
theorem HalfEdge.vertex_mk (e : G.Edge) (i : Fin 2) :
    HalfEdge.vertex G (e, i) = G.endpoint e i := by rfl

/-- The first Betti number of the connected dual graph, by Euler characteristic. -/
def firstBetti : ℕ := Fintype.card G.Edge + 1 - Fintype.card G.Vertex

-- `by rfl`, not `rfl`: `firstBetti` is not `@[expose]`, so a theorem exported from this module
-- cannot unfold it in term mode.
@[simp]
theorem firstBetti_eq : G.firstBetti = Fintype.card G.Edge + 1 - Fintype.card G.Vertex := by rfl

/-- The arithmetic genus encoded by a connected weighted dual graph. -/
def arithmeticGenus : ℕ := (∑ v, G.genus v) + G.firstBetti

-- `by rfl`, not `rfl`: `arithmeticGenus` is not `@[expose]`, so a theorem exported from this
-- module cannot unfold it in term mode.
@[simp]
theorem arithmeticGenus_eq : G.arithmeticGenus = (∑ v, G.genus v) + G.firstBetti := by rfl

end DualGraph

end TauCeti
