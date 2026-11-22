/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Simple
public import TauCeti.Combinatorics.Graph.Orientation.Basic
public import TauCeti.Combinatorics.Quiver.Reachable

/-!
# The underlying graph of an orientation

An orientation of a multigraph gives an explicit arrow family on its actual vertices. Forgetting
the directions and multiplicities of these arrows recovers the multigraph's underlying simple
graph. Thus weak connectivity of the orientation is precisely preconnectivity in that simple graph.

## Main results

* `Graph.Orientation.underlyingGraph_hom`: the simple graph underlying an orientation's arrow
  family is the underlying simple graph of the original multigraph.
* `Graph.Orientation.isStronglyConnected_symmetrify_hom_iff`: the symmetrized arrow family is
  strongly connected exactly when the underlying simple graph is preconnected.
-/

public section

open TauCeti

universe u v

namespace Graph.Orientation

variable {V : Type u} {E : Type v} {G : Graph V E} (o : G.Orientation)

private theorem nonempty_hom_or_nonempty_hom_iff_adj (x y : G.vertexSet) :
    Nonempty (o.Hom x y) ∨ Nonempty (o.Hom y x) ↔ G.Adj x y := by
  constructor
  · rintro (ha | ha)
    · exact ha.elim fun a ↦ a.isLink.adj
    · exact ha.elim fun a ↦ a.isLink.symm.adj
  · rintro ⟨e, he⟩
    let e' : G.edgeSet := ⟨e, he.edge_mem⟩
    rcases (o.isLink e').eq_and_eq_or_eq_and_eq he with h | h
    · exact .inl ⟨⟨e', Subtype.ext h.1, Subtype.ext h.2⟩⟩
    · exact .inr ⟨⟨e', Subtype.ext h.1, Subtype.ext h.2⟩⟩

/-- Forgetting the directions and multiplicities of an orientation's arrows recovers the
underlying simple graph of the original multigraph. -/
@[simp]
theorem underlyingGraph_hom :
    @TauCeti.Quiver.underlyingGraph G.vertexSet ⟨o.Hom⟩ = G.toSimpleGraph := by
  ext x y
  rw [@TauCeti.Quiver.underlyingGraph_adj G.vertexSet ⟨o.Hom⟩ x y,
    Graph.toSimpleGraph_adj]
  exact and_congr Iff.rfl (o.nonempty_hom_or_nonempty_hom_iff_adj x y)

/-- Weak connectivity of an orientation's arrow family is preconnectivity of the original
multigraph's underlying simple graph. -/
theorem isStronglyConnected_symmetrify_hom_iff :
    @Quiver.IsStronglyConnected (Quiver.Symmetrify G.vertexSet)
        (@Quiver.symmetrifyQuiver G.vertexSet ⟨o.Hom⟩) ↔
      G.toSimpleGraph.Preconnected := by
  rw [@TauCeti.Quiver.isStronglyConnected_symmetrify_iff_preconnected G.vertexSet ⟨o.Hom⟩,
    o.underlyingGraph_hom]

end Graph.Orientation
