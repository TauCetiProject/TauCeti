/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Simple
public import TauCeti.Combinatorics.Graph.Orientation.Basic
public import TauCeti.Combinatorics.Quiver.UnderlyingGraph

/-!
# The underlying graph of an orientation

An orientation of a multigraph gives an explicit arrow family on its actual vertices. Forgetting
the directions and multiplicities of these arrows and discarding loops recovers the multigraph's
underlying simple graph.

## Main results

* `Graph.Orientation.underlyingGraph_hom`: the simple graph underlying an orientation's arrow
  family is the underlying simple graph of the original multigraph.
-/

public section

open TauCeti

universe u v

namespace Graph.Orientation

variable {V : Type u} {E : Type v} {G : Graph V E} (o : G.Orientation)

/-- Forgetting the directions and multiplicities of an orientation's arrows and discarding loops
recovers the underlying simple graph of the original multigraph. -/
@[simp]
theorem underlyingGraph_hom :
    @TauCeti.Quiver.underlyingGraph G.vertexSet ⟨o.Hom⟩ = G.toSimpleGraph := by
  ext x y
  rw [@TauCeti.Quiver.underlyingGraph_adj G.vertexSet ⟨o.Hom⟩ x y,
    Graph.toSimpleGraph_adj]
  exact and_congr Iff.rfl (o.nonempty_hom_or_nonempty_hom_iff_adj x y)

end Graph.Orientation
