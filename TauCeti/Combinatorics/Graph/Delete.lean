/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Edge deletion in standard multigraphs

This file computes edge deletion `Graph.deleteEdges` in two families of multigraphs: graphs
`Graph.ofSimpleGraph H` built from simple graphs, where deletion corresponds to
`SimpleGraph.deleteEdges`, and the graphs `Graph.banana u w F` on two vertices, where deletion
removes edges from `F`. These identities let deletion-based connectivity predicates be compared
with their simple-graph versions and evaluated on explicit examples.
-/

public section

open Set

namespace Graph

variable {α β : Type*}

/-- Deleting edges commutes with regarding a simple graph as a multigraph. -/
@[simp]
theorem ofSimpleGraph_deleteEdges (H : SimpleGraph α) (F : Set (Sym2 α)) :
    (Graph.ofSimpleGraph H).deleteEdges F = Graph.ofSimpleGraph (H.deleteEdges F) :=
  Graph.ext (by simp) fun e x y ↦ by simp [and_assoc]

/-- Deleting edges from a graph on two vertices removes them from its edge set. -/
@[simp]
theorem banana_deleteEdges (u w : α) (F D : Set β) :
    (banana u w F).deleteEdges D = banana u w (F \ D) :=
  Graph.ext (by simp) fun e x y ↦ by simp [and_assoc, and_comm (a := e ∉ D)]

end Graph
