/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.GodsilMcKay

/-!
# A Godsil–McKay switching of the tree `T(2, 2, 2)`

On `Fin 7`, the tree `T(2, 2, 2)` with edges `04, 05, 06, 14, 25, 36` carries a Godsil–McKay
partition with the single cell `X = {0, 1, 2, 3}`, which is independent, and `Y = {4, 5, 6}`:
each vertex of `Y` has exactly two neighbours in `X`. Switching complements all adjacencies
between `Y` and `X` and gives the graph with edges `15, 16, 24, 26, 34, 35`, a hexagon together
with the isolated vertex `0`. The two graphs are cospectral, with cospectral complements.
-/

@[expose] public section

open SimpleGraph

namespace TauCeti.GodsilMcKayExample

/-- The tree `T(2, 2, 2)` on `Fin 7`, with centre `0`. -/
def tree222 : SimpleGraph (Fin 7) :=
  fromRel fun i j ↦ (i, j) ∈ [(0, 4), (0, 5), (0, 6), (1, 4), (2, 5), (3, 6)]

/-- Adjacency in `T(2, 2, 2)` is decidable. -/
instance : DecidableRel tree222.Adj := fun i j ↦ by unfold tree222; infer_instance

/-- The Godsil–McKay partition of `T(2, 2, 2)` with the cell `{0, 1, 2, 3}`. -/
def tree222Partition : tree222.GodsilMcKayPartition Unit where
  cell x := if x.val < 4 then some () else none
  nonempty _ := ⟨0, rfl⟩
  equitable := by decide
  outside := by decide

-- Switching `T(2, 2, 2)` gives the hexagon `1 - 5 - 3 - 4 - 2 - 6 - 1` and the isolated vertex `0`.
example : tree222Partition.switch =
    fromRel fun i j ↦ (i, j) ∈ [(1, 5), (1, 6), (2, 4), (2, 6), (3, 4), (3, 5)] := by
  ext i j
  revert i j
  decide

-- The switched graph is cospectral with `T(2, 2, 2)`, and so are the complements.
example :
    (tree222Partition.switch.adjMatrix ℤ).charpoly = (tree222.adjMatrix ℤ).charpoly ∧
      (tree222Partition.switchᶜ.adjMatrix ℤ).charpoly = (tree222ᶜ.adjMatrix ℤ).charpoly :=
  ⟨tree222Partition.charpoly_adjMatrix_switch ℤ, tree222Partition.charpoly_adjMatrix_compl_switch ℤ⟩

end TauCeti.GodsilMcKayExample
