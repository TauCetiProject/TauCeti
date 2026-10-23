/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Roots and paths to them in the connected components of a graph

Every connected component of a simple graph has a representative vertex, and every vertex of the
graph is joined to the representative of its component by a walk. Choosing these once for all, as
the representatives themselves are not canonical, gives a **root** for every vertex together with a
**root path** from that root to the vertex. Two adjacent vertices lie in the same connected
component, so they have the same root.

These choices are the scaffolding for the statements which integrate a quantity along a path from a
root in every connected component: the product of the values of a `1`-cochain along the root path
of a vertex, or the product of transition factors along it.

## Main definitions

* `SimpleGraph.componentRoot`: the chosen representative of the connected component of a vertex.
* `SimpleGraph.componentPath`: a chosen walk from that representative to the vertex.

## Main results

* `SimpleGraph.reachable_componentRoot`: the root of a vertex reaches it.
* `SimpleGraph.isPath_componentPath`: the chosen walk is a path.
* `SimpleGraph.componentRoot_eq_of_adj`: adjacent vertices have the same root.
-/

public section

namespace SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V)

/-- The chosen root of the connected component of a vertex. -/
noncomputable def componentRoot (v : V) : V :=
  (G.connectedComponentMk v).nonempty_supp.some

/-- The root of the connected component of a vertex reaches it. -/
theorem reachable_componentRoot (v : V) : G.Reachable (componentRoot G v) v :=
  SimpleGraph.ConnectedComponent.exact
    ((G.connectedComponentMk v).nonempty_supp.some_mem)

/-- A chosen walk from the root of the connected component of a vertex to that vertex. -/
noncomputable def componentPath (v : V) : G.Walk (componentRoot G v) v :=
  (reachable_componentRoot G v).exists_path_of_dist.choose

/-- The chosen walk from the root of a connected component to a vertex is a path. -/
theorem isPath_componentPath (v : V) : (componentPath G v).IsPath :=
  (reachable_componentRoot G v).exists_path_of_dist.choose_spec.1

/-- The roots of adjacent vertices are the same. -/
theorem componentRoot_eq_of_adj {v w : V} (h : G.Adj v w) :
    componentRoot G w = componentRoot G v :=
  congrArg (fun C : G.ConnectedComponent => C.nonempty_supp.some)
    (SimpleGraph.ConnectedComponent.sound h.symm.reachable)

end SimpleGraph
