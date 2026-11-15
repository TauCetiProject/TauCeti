/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Isomorphism
public import TauCeti.Combinatorics.Graph.Serre.Multigraph
public import TauCeti.Combinatorics.Graph.Serre.OfGraph.Basic

/-!
# Forgetting the darts of a multigraph recovers the multigraph

The Serre graph `G.toSerreGraph` of a multigraph `G` attaches two darts to every actual edge of
`G`, ordering the two ends of the edge arbitrarily. Passing back to the underlying multigraph
identifies each dart with its reverse. This file shows that nothing is lost on the way: the two
darts over an edge form exactly one reversal orbit, and the resulting multigraph
`G.toSerreGraph.toGraph` is isomorphic to `G` by an isomorphism which is the identity on the
actual vertices and sends the orbit of a dart to the edge it lies over. In particular the result
does not depend on how the ends of the edges were ordered, a loop of `G` is again a single loop,
and parallel edges stay distinct.

## Main declarations

* `Graph.toSerreGraph_edge_eq_iff`: two darts of `G.toSerreGraph` are equal up to reversal exactly
  when they lie over the same edge of `G`.
* `Graph.toSerreGraphEdgeEquiv`: the actual edges of `G` are the reversal orbits of darts of
  `G.toSerreGraph`.
* `Graph.toSerreGraph_toGraph_isLink`: the incidence of `G.toSerreGraph.toGraph` is that of `G`.
* `Graph.toSerreGraphToGraphIso`: the isomorphism from `G.toSerreGraph.toGraph` to `G`.
* `Graph.connected_toGraph_toSerreGraph_iff`: `G.toSerreGraph.toGraph` is connected exactly when
  `G` is.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1.
-/

public section

open TauCeti

namespace Graph

variable {V E : Type*} (G : Graph V E)

/-- Two darts of the Serre graph of a multigraph agree up to reversal exactly when they lie over
the same edge. -/
theorem toSerreGraph_edge_eq_iff (d d' : G.toSerreGraph.E) :
    G.toSerreGraph.edge d = G.toSerreGraph.edge d' ↔ d.1 = d'.1 := by
  rw [SerreGraph.edge_eq_iff]
  refine ⟨fun h => h.elim (congrArg Prod.fst) (congrArg Prod.fst), ?_⟩
  obtain ⟨e, b⟩ := d
  obtain ⟨e', b'⟩ := d'
  rintro rfl
  cases b <;> cases b' <;> first | exact .inl rfl | exact .inr rfl

/-- The two darts over an edge of a multigraph have the same reversal orbit. -/
@[simp] theorem toSerreGraph_edge_false (e : G.edgeSet) :
    G.toSerreGraph.edge (e, false) = G.toSerreGraph.edge (e, true) :=
  (G.toSerreGraph_edge_eq_iff _ _).2 rfl

/-- The actual edges of a multigraph are the reversal orbits of the darts of its Serre graph:
an edge corresponds to the orbit formed by its two darts. -/
noncomputable def toSerreGraphEdgeEquiv : G.edgeSet ≃ G.toSerreGraph.Edge :=
  Equiv.ofBijective (fun e => G.toSerreGraph.edge (e, true))
    ⟨fun _ _ h => (G.toSerreGraph_edge_eq_iff _ _).1 h, fun q => by
      obtain ⟨⟨e, b⟩, rfl⟩ := G.toSerreGraph.edge_surjective q
      exact ⟨e, (G.toSerreGraph_edge_eq_iff _ _).2 rfl⟩⟩

@[simp] theorem toSerreGraphEdgeEquiv_apply (e : G.edgeSet) :
    G.toSerreGraphEdgeEquiv e = G.toSerreGraph.edge (e, true) := (rfl)

/-- The reversal orbit of a dart corresponds to the edge the dart lies over. -/
@[simp] theorem toSerreGraphEdgeEquiv_symm_edge (d : G.toSerreGraph.E) :
    G.toSerreGraphEdgeEquiv.symm (G.toSerreGraph.edge d) = d.1 := by
  rw [Equiv.symm_apply_eq, toSerreGraphEdgeEquiv_apply, toSerreGraph_edge_eq_iff]

/-- The ends of the reversal orbit of a dart are the ends of the edge the dart lies over. -/
theorem toSerreGraph_edgeEnds_edge (d : G.toSerreGraph.E) :
    G.toSerreGraph.edgeEnds (G.toSerreGraph.edge d) = G.edgeEnds d.1 := by
  rw [SerreGraph.edgeEnds_edge, toSerreGraph_edgeEnds]

/-- The reversal orbit of a dart links two vertices in the multigraph underlying the Serre graph
exactly when the edge the dart lies over links them in the original multigraph. -/
theorem toSerreGraph_toGraph_isLink_edge (d : G.toSerreGraph.E) (x y : G.vertexSet) :
    G.toSerreGraph.toGraph.IsLink (G.toSerreGraph.edge d) x y ↔ G.IsLink d.1.1 x.1 y.1 := by
  rw [SerreGraph.toGraph_isLink, toSerreGraph_edgeEnds_edge, edgeEnds_eq_iff_isLink]

/-- The multigraph underlying the Serre graph of a multigraph has the incidence of the original
multigraph, under the identification of reversal orbits with edges. -/
theorem toSerreGraph_toGraph_isLink (q : G.toSerreGraph.Edge) (x y : G.vertexSet) :
    G.toSerreGraph.toGraph.IsLink q x y ↔ G.IsLink (G.toSerreGraphEdgeEquiv.symm q).1 x.1 y.1 := by
  induction q using SerreGraph.Edge.ind with
  | h d => rw [toSerreGraph_toGraph_isLink_edge, toSerreGraphEdgeEquiv_symm_edge]

/-- Forgetting the darts of the Serre graph of a multigraph recovers the multigraph: the
isomorphism is the identity on actual vertices and sends the reversal orbit of a dart to the edge
the dart lies over. -/
noncomputable def toSerreGraphToGraphIso : G.toSerreGraph.toGraph.Iso G where
  vertexEquiv :=
    (Set.equivOfEq G.toSerreGraph.vertexSet_toGraph).trans (Equiv.Set.univ G.vertexSet)
  edgeEquiv :=
    ((Set.equivOfEq G.toSerreGraph.edgeSet_toGraph).trans
      (Equiv.Set.univ G.toSerreGraph.Edge)).trans G.toSerreGraphEdgeEquiv.symm
  map_isLink_iff q x y := (G.toSerreGraph_toGraph_isLink q.1 x.1 y.1).symm

@[simp] theorem toSerreGraphToGraphIso_vertexEquiv_apply (x : G.toSerreGraph.toGraph.vertexSet) :
    G.toSerreGraphToGraphIso.vertexEquiv x = x.1 := (rfl)

@[simp] theorem toSerreGraphToGraphIso_edgeEquiv_apply (q : G.toSerreGraph.toGraph.edgeSet) :
    G.toSerreGraphToGraphIso.edgeEquiv q = G.toSerreGraphEdgeEquiv.symm q.1 := (rfl)

@[simp] theorem coe_toSerreGraphToGraphIso_vertexEquiv_symm_apply (x : G.vertexSet) :
    (G.toSerreGraphToGraphIso.vertexEquiv.symm x).1 = x := (rfl)

@[simp] theorem coe_toSerreGraphToGraphIso_edgeEquiv_symm_apply (e : G.edgeSet) :
    (G.toSerreGraphToGraphIso.edgeEquiv.symm e).1 = G.toSerreGraph.edge (e, true) := (rfl)

/-- A loop of a multigraph is a single loop of the multigraph underlying its Serre graph, although
it carries two darts. -/
theorem toSerreGraph_toGraph_isLoopAt_iff (e : G.edgeSet) (x : G.vertexSet) :
    G.toSerreGraph.toGraph.IsLoopAt (G.toSerreGraphEdgeEquiv e) x ↔ G.IsLoopAt e.1 x.1 :=
  G.toSerreGraph_toGraph_isLink_edge (e, true) x x

/-- Reachability in the multigraph underlying the Serre graph of a multigraph is reachability in
the original multigraph. -/
theorem reachable_toGraph_toSerreGraph_iff (x y : G.vertexSet) :
    G.toSerreGraph.toGraph.Reachable x y ↔ G.Reachable x.1 y.1 := by
  rw [SerreGraph.reachable_toGraph_iff, nonempty_serrePath_iff_reachable]

/-- The multigraph underlying the Serre graph of a multigraph is connected exactly when the
original multigraph is. -/
theorem connected_toGraph_toSerreGraph_iff : G.toSerreGraph.toGraph.Connected ↔ G.Connected := by
  rw [SerreGraph.connected_toGraph_iff, connected_iff_nonempty_serrePath,
    SerreGraph.connected_iff, SerreGraph.preconnected_iff]

end Graph
