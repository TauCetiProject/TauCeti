/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Roots and paths to them in the connected components of a graph

Every connected component of a simple graph has a representative vertex, and every vertex of the
graph is joined to the representative of its component by a walk. Choosing these once for all, as
the representatives themselves are not canonical, gives a **root** for every vertex together with a
**root path** from that root to the vertex. Two vertices have the same root exactly when they lie
in the same connected component.

These choices are the scaffolding for the statements which integrate a quantity along a path from a
root in every connected component: the product of the values of a `1`-cochain along the root path
of a vertex, or the product of transition factors along it.

## Main definitions

* `SimpleGraph.componentRoot`: the chosen representative of the connected component of a vertex.
* `SimpleGraph.componentPath`: a chosen walk from that representative to the vertex.

## Main results

* `SimpleGraph.reachable_componentRoot`: the root of a vertex reaches it.
* `SimpleGraph.isPath_componentPath`: the chosen walk is a path.
* `SimpleGraph.componentRoot_eq_componentRoot_iff`: two vertices have the same root if and only if
  they are reachable from each other.
-/

public section

namespace SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V)

/-- The chosen root of the connected component of a vertex. -/
noncomputable def componentRoot (v : V) : V :=
  (G.connectedComponentMk v).out

/-- The root of the connected component of a vertex reaches it. -/
theorem reachable_componentRoot (v : V) : G.Reachable (componentRoot G v) v :=
  ConnectedComponent.exact (G.connectedComponentMk v).out_eq

/-- A chosen walk from the root of the connected component of a vertex to that vertex. -/
noncomputable def componentPath (v : V) : G.Walk (componentRoot G v) v :=
  (reachable_componentRoot G v).exists_isPath.choose

/-- The chosen walk from the root of a connected component to a vertex is a path. -/
theorem isPath_componentPath (v : V) : (componentPath G v).IsPath :=
  (reachable_componentRoot G v).exists_isPath.choose_spec

/-- Two vertices have the same root if and only if they lie in the same connected component. -/
@[simp]
theorem componentRoot_eq_componentRoot_iff {v w : V} :
    componentRoot G v = componentRoot G w ↔ G.Reachable v w :=
  ⟨fun h => (reachable_componentRoot G v).symm.trans (h ▸ reachable_componentRoot G w),
    fun h => congrArg Quot.out (ConnectedComponent.sound h)⟩

end SimpleGraph
