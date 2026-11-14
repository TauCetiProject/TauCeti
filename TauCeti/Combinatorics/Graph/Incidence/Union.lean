/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Incidence.Basic
public import TauCeti.Combinatorics.Graph.Union

/-!
# Incidence counts in compatible unions

In a compatible union, the incident edges, loops, and nonloop incident edges at a vertex are the
unions of the corresponding sets in the two graphs. When the graphs have disjoint edge sets,
the finite counts add, even at a vertex common to both graphs. In particular, these formulas
apply to disjoint unions. Parallel edge identities remain distinct and a loop counts once.

The set identities in `TauCeti.Combinatorics.Graph.Union` need no finiteness. The counting
identities here require only finiteness of the sets counted at the chosen vertex, not of all
edges or vertices. This distinction matters for `Set.ncard`, which returns zero on infinite sets.
-/

public section

open Set

universe u v

namespace Graph.Compatible

variable {α : Type u} {β : Type v} {G H : Graph α β}

/-- Counts of incident edges add in an edge-disjoint union, including at shared vertices.
Only the two incidence sets at this vertex need be finite. -/
theorem incidenceCount_union (h : G.Compatible H) (hE : Disjoint E(G) E(H)) (x : α)
    (hG : (G.incidenceSet x).Finite) (hH : (H.incidenceSet x).Finite) :
    h.union.incidenceCount x = G.incidenceCount x + H.incidenceCount x := by
  simp only [incidenceCount_def, h.incidenceSet_union]
  exact ncard_union_eq
    (hE.mono (G.incidenceSet_subset_edgeSet x) (H.incidenceSet_subset_edgeSet x)) hG hH

/-- Counts of loops add in an edge-disjoint union, counting every loop identity once. -/
theorem ncard_loopSet_union (h : G.Compatible H) (hE : Disjoint E(G) E(H)) (x : α)
    (hG : (G.loopSet x).Finite) (hH : (H.loopSet x).Finite) :
    (h.union.loopSet x).ncard = (G.loopSet x).ncard + (H.loopSet x).ncard := by
  rw [h.loopSet_union]
  exact ncard_union_eq
    (hE.mono ((G.loopSet_subset_incidenceSet x).trans (G.incidenceSet_subset_edgeSet x))
      ((H.loopSet_subset_incidenceSet x).trans (H.incidenceSet_subset_edgeSet x))) hG hH

/-- Counts of nonloop incident edges add in an edge-disjoint union. Finiteness of the nonloop
incidence sets suffices, even if either input has infinitely many loops. -/
theorem nonloopIncidenceCount_union (h : G.Compatible H) (hE : Disjoint E(G) E(H)) (x : α)
    (hG : (G.incidenceSet x \ G.loopSet x).Finite)
    (hH : (H.incidenceSet x \ H.loopSet x).Finite) :
    h.union.nonloopIncidenceCount x = G.nonloopIncidenceCount x + H.nonloopIncidenceCount x := by
  simp only [nonloopIncidenceCount_def, h.incidenceSet_sdiff_loopSet_union]
  exact ncard_union_eq
    (hE.mono (sdiff_subset.trans (G.incidenceSet_subset_edgeSet x))
      (sdiff_subset.trans (H.incidenceSet_subset_edgeSet x))) hG hH

end Graph.Compatible
