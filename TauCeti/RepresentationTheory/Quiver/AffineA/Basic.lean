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
def affineADiagram (n : ℕ) (_hn : 2 ≤ n) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.cycleGraph (n + 1)

namespace affineADiagram

/-- Vertex `0` is the marked affine vertex of `Ãₙ`. -/
def affineVertex (n : ℕ) (_hn : 2 ≤ n) : Fin (n + 1) := 0

/-- The marked affine vertex is the zero vertex of the cycle model. -/
@[simp]
theorem affineVertex_eq_zero (n : ℕ) (hn : 2 ≤ n) : affineVertex n hn = 0 := (rfl)

/-- The affine `A` diagram is the cycle graph on `n + 1` vertices. -/
@[simp]
theorem eq_cycleGraph (n : ℕ) (hn : 2 ≤ n) :
    affineADiagram n hn = SimpleGraph.cycleGraph (n + 1) := (rfl)

/-- The graph underlying `Ãₙ` is connected. -/
theorem connected (n : ℕ) (hn : 2 ≤ n) : (affineADiagram n hn).Connected := by
  rw [eq_cycleGraph]
  exact SimpleGraph.connected_cycleGraph_add_one

/-- Two vertices of the affine `A` diagram are adjacent exactly when they differ by `1` in
`Fin (n + 1)`, in either order. -/
theorem adj_iff (n : ℕ) (hn : 2 ≤ n) (i j : Fin (n + 1)) :
    (affineADiagram n hn).Adj i j ↔ (i - j).val = 1 ∨ (j - i).val = 1 := by
  rw [eq_cycleGraph]
  exact SimpleGraph.cycleGraph_adj'

end affineADiagram
end TauCeti
