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
of the components. This is the combinatorial carrier that Layer 1 of the Stable Reduction roadmap
pins before numerical types and decorated graphs.

The signatures match `StableReduction/Suggested.lean`.

## Main definitions

* `TauCeti.DualGraph`: finite nonempty connected weighted dual graph.
* `TauCeti.DualGraph.HalfEdge`: an edge together with an endpoint index.
* `TauCeti.DualGraph.firstBetti`: first Betti number by Euler characteristic.
* `TauCeti.DualGraph.arithmeticGenus`: arithmetic genus `∑ genus + firstBetti`.

## References

* [Stacks, Tag 0C6P](https://stacks.math.columbia.edu/tag/0C6P) (dual graph of a nodal curve).
-/

public section

namespace TauCeti

universe u

/-- Minimal compiled shape of the dual graph of a geometric nodal curve.

An edge has two half-edges even when both endpoints agree, so loops contribute two to valence. -/
structure DualGraph where
  Vertex : Type u
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  [vertexNonempty : Nonempty Vertex]
  Edge : Type u
  [edgeFintype : Fintype Edge]
  [edgeDecidableEq : DecidableEq Edge]
  endpoint : Edge → Fin 2 → Vertex
  genus : Vertex → ℕ
  connected : ∀ v w, Relation.ReflTransGen
    (fun v w ↦ ∃ e, (endpoint e 0 = v ∧ endpoint e 1 = w) ∨
      (endpoint e 0 = w ∧ endpoint e 1 = v)) v w

namespace DualGraph

variable (G : DualGraph)

instance : Fintype G.Vertex := G.vertexFintype
instance : DecidableEq G.Vertex := G.vertexDecidableEq
instance : Nonempty G.Vertex := G.vertexNonempty
instance : Fintype G.Edge := G.edgeFintype
instance : DecidableEq G.Edge := G.edgeDecidableEq

/-- Half-edges make the loop-counting convention explicit in the data. -/
abbrev HalfEdge := G.Edge × Fin 2

/-- The vertex incident to a half-edge. -/
def HalfEdge.vertex (h : G.HalfEdge) : G.Vertex := G.endpoint h.1 h.2

/-- The first Betti number of the connected dual graph, by Euler characteristic. -/
def firstBetti : ℕ := Fintype.card G.Edge + 1 - Fintype.card G.Vertex

/-- The arithmetic genus encoded by a connected weighted dual graph. -/
def arithmeticGenus : ℕ := ∑ v, G.genus v + G.firstBetti

end DualGraph

end TauCeti
