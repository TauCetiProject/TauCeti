/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# The affine simply-laced diagram of type `A`

For `2 ≤ n`, the affine diagram `Ãₙ` is the cycle on `n + 1` vertices. This file records its
simple-graph model, its marked affine vertex, and the basic graph invariants used when comparing
affine diagrams with quiver constructions.

## References

* V. Kac, *Infinite-dimensional Lie algebras*, Chapter 4.
-/

public section

namespace TauCeti

/-- The underlying simple graph of the affine Dynkin diagram `Ãₙ`, for `n ≥ 2`.

The restriction `2 ≤ n` is needed because `Ã₁` has two edges between its vertices and is not a
simple graph. -/
def affineADiagram (n : ℕ) (hn : 2 ≤ n) : SimpleGraph (Fin (n + 1)) := by
  by_cases h : 2 ≤ n
  · exact SimpleGraph.cycleGraph (n + 1)
  · exact False.elim (h hn)

namespace affineADiagram

/-- Vertex `0` is the marked affine vertex of `Ãₙ`. -/
def affineVertex (n : ℕ) (_hn : 2 ≤ n) : Fin (n + 1) := 0

/-- The marked affine vertex is the zero vertex of the cycle model. -/
@[simp]
theorem affineVertex_eq_zero (n : ℕ) (hn : 2 ≤ n) : affineVertex n hn = 0 := (rfl)

/-- The affine `A` diagram is the cycle graph, for ranks at least two. -/
@[simp]
theorem affineADiagram_eq_cycleGraph (n : ℕ) (hn : 2 ≤ n) :
    affineADiagram n hn = SimpleGraph.cycleGraph (n + 1) := by
  simp [affineADiagram, hn]

/-- The graph underlying `Ãₙ` is connected. -/
theorem connected (n : ℕ) (hn : 2 ≤ n) : (affineADiagram n hn).Connected := by
  rw [affineADiagram_eq_cycleGraph n hn]
  exact SimpleGraph.connected_cycleGraph_add_one (n := n)

/-- Adjacency in the affine `A` diagram is characterized by neighboring vertices. -/
theorem adj_iff (n : ℕ) (hn : 2 ≤ n) (i j : Fin (n + 1)) :
    (affineADiagram n hn).Adj i j ↔
      (i - j).val = 1 ∨ (j - i).val = 1 :=
  by
    rw [affineADiagram_eq_cycleGraph n hn]
    exact SimpleGraph.cycleGraph_adj'

end affineADiagram
end TauCeti
