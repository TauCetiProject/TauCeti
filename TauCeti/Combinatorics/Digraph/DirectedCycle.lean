/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Digraph.ArrowWalk
public import TauCeti.Combinatorics.Network.DirectedCycle

/-!
# Directed cycles and connectivity in digraphs

This file specializes the directed-cycle criterion for explicit arrow families to `Digraph`.
For an adjacency `s → t`, lying on a directed cycle is equivalent to reachability from `t`
back to `s`. Consequently, a digraph is strongly connected exactly when its underlying undirected
simple graph is preconnected and every adjacency can be completed to a directed cycle.

The preconnected form also covers the empty digraph and so matches the convention for
`Quiver.IsStronglyConnected`.

The characterization follows J. Bang-Jensen and G. Gutin, *Digraphs: Theory, Algorithms and
Applications*, 2nd ed., Springer, 2009, Section 5.3.
-/

public section

open Relation TauCeti

universe u

namespace Digraph

variable {V : Type u} {D : Digraph V} {s t : V}

/-- An adjacency arrow of a digraph lies on a directed cycle exactly when its target can reach
its source in the digraph. -/
theorem liesOnCycle_adjHom_iff (h : D.Adj s t) :
    ArrowWalk.LiesOnCycle (Q := D.AdjHom) (PLift.up h) ↔ ReflTransGen D.Adj t s := by
  rw [ArrowWalk.liesOnCycle_iff_nonempty, nonempty_arrowWalk_iff_reflTransGen]

/-- A digraph is strongly connected exactly when its underlying undirected simple graph is
preconnected and each of its adjacency arrows lies on a directed cycle. -/
theorem isStronglyConnected_iff_preconnected_and_forall_liesOnCycle :
    @Quiver.IsStronglyConnected V ⟨D.AdjHom⟩ ↔
      D.toSimpleGraphInclusive.Preconnected ∧
        ∀ ⦃v w⦄ (h : D.Adj v w),
          ArrowWalk.LiesOnCycle (Q := D.AdjHom) (PLift.up h) := by
  rw [TauCeti.isStronglyConnected_iff_isWeaklyConnected_and_forall_liesOnCycle,
    isStronglyConnected_symmetrify_adjHom_iff]
  refine and_congr Iff.rfl ⟨fun h v w hv ↦ h ⟨hv⟩, fun h v w e ↦ ?_⟩
  simpa only [Subsingleton.elim e ⟨e.down⟩] using h e.down

/-- **Directed-cycle characterization of strong connectivity for digraphs.** Every vertex can
reach every other vertex exactly when the underlying undirected simple graph is preconnected and
every adjacency `v → w` can be completed by a directed walk from `w` back to `v`. -/
theorem isStronglyConnected_iff_preconnected_and_forall_adj_reflTransGen :
    @Quiver.IsStronglyConnected V ⟨D.AdjHom⟩ ↔
      D.toSimpleGraphInclusive.Preconnected ∧
        ∀ ⦃v w⦄, D.Adj v w → ReflTransGen D.Adj w v := by
  rw [isStronglyConnected_iff_preconnected_and_forall_liesOnCycle]
  refine and_congr Iff.rfl ⟨fun h v w hv ↦ ?_, fun h v w e ↦ ?_⟩
  · exact (liesOnCycle_adjHom_iff hv).1 (h hv)
  · exact (liesOnCycle_adjHom_iff e).2 (h e)

end Digraph
