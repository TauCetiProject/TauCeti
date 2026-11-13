/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Basic
public import TauCeti.Combinatorics.Graph.OfSimpleGraph
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Ear.Basic

import TauCeti.Combinatorics.Graph.Connectivity.Walk.OfSimpleGraph
import TauCeti.Combinatorics.Graph.Connectivity.Walk.Trace

/-!
# Ear decompositions of simple graphs as multigraph ear decompositions

A simple graph `G` has two ear-decomposition interfaces: `SimpleGraph.EarDecomposition`, whose
stages are subgraphs `H : G.Subgraph`, and `Graph.EarDecomposition` for the multigraph
`Graph.ofSimpleGraph G`, whose stages are multigraph subgraphs. This file identifies them.

Through `SimpleGraph.Subgraph.toGraph`, ears, initial vertices or cycles, and decompositions of a
subgraph `H` correspond to those of `H.toGraph` in `Graph.ofSimpleGraph G`. The correspondence
transports underlying walks with `SimpleGraph.Walk.toGraph` and `Graph.Walk.toSimpleGraph`, so it
preserves the number of ears, the kind and walk of every ear, the stage after every prefix,
prefix decompositions, openness, and starting from a single vertex. In particular, results proved
for multigraph ear decompositions apply to simple graphs, and conversely.

## Main definitions

* `SimpleGraph.Ear.toGraph`, `Graph.Ear.toSimpleGraph`: transport of single ears.
* `SimpleGraph.EarDecomposition.toGraph`, `Graph.EarDecomposition.toSimpleGraph`: transport of
  ear decompositions.
* `SimpleGraph.Subgraph.earDecompositionEquivOfSimpleGraph`: the two transports are mutually
  inverse.

## Implementation notes

The decomposition transports are reducible and exposed, so that the length of a transported
decomposition unfolds to the original length even at reducible transparency. Statements can then
use `Fin` indices over either length interchangeably, and `rw` and `simp` can use them.
-/

public section

open scoped Graph Sym2

universe u

variable {α : Type u} {G : SimpleGraph α}

namespace SimpleGraph

namespace Ear

variable {H : G.Subgraph}

/-- An ear over `H` in a simple graph `G`, as an ear over `H.toGraph` in `Graph.ofSimpleGraph G`
with the corresponding edge-labelled walk. -/
def toGraph : G.Ear H → (Graph.ofSimpleGraph G).Ear H.toGraph
  | .«open» p hp hu hv huv hint hedge =>
      .open H.toGraph_le p.toGraph (p.isPath_toGraph_iff.mpr hp) (by simpa using hu)
        (by simpa using hv) huv (by simpa using hint) (by simpa using hedge)
  | .closed c hc hu hint =>
      .closed H.toGraph_le c.toGraph (c.isCycle_toGraph_iff.mpr hc) (by simpa using hu)
        (by simpa using hint) fun _ he ↦ by
          simpa using closed_edges_notMem_edgeSet hint (by simpa using he)

@[simp]
theorem toWalk_toGraph (e : G.Ear H) :
    e.toGraph.toWalk = ⟨e.toWalk.1, e.toWalk.2.1, (e.toWalk.2.2 : G.Walk _ _).toGraph⟩ := by
  cases e with
  | «open» => rw [toGraph, Graph.Ear.toWalk_open, toWalk_open]
  | closed => rw [toGraph, Graph.Ear.toWalk_closed, toWalk_closed]

@[simp]
theorem kind_toGraph_eq_open_iff (e : G.Ear H) :
    e.toGraph.kind = .open ↔ e.kind = .«open» := by
  cases e <;> simp [toGraph]

/-- The graph traced by a transported ear is the multigraph of the subgraph traced by the ear. -/
@[simp]
theorem toGraph_toGraph (e : G.Ear H) : e.toGraph.toGraph = e.toSubgraph.toGraph := by
  cases e <;> simp [toGraph]

/-- Adjoining a transported ear gives the multigraph of the subgraph obtained by adjoining the
ear. -/
@[simp]
theorem add_toGraph (e : G.Ear H) : e.toGraph.add = e.adjoin.toGraph := by
  refine le_antisymm ?_ ?_
  · rw [Graph.Ear.add_le_iff, toGraph_toGraph, Subgraph.toGraph_le_toGraph_iff,
      Subgraph.toGraph_le_toGraph_iff]
    exact ⟨e.le_adjoin, e.toSubgraph_le_adjoin⟩
  · rw [adjoin_def, Subgraph.toGraph_sup, Graph.Compatible.union_le_iff, ← toGraph_toGraph]
    exact ⟨e.toGraph.base_le_add, e.toGraph.toGraph_le_add⟩

end Ear

namespace EarStart

variable {H : G.Subgraph}

/-- An initial vertex or cycle of a simple graph, as an initial vertex or cycle of
`Graph.ofSimpleGraph G`. -/
def toGraph : {H : G.Subgraph} → G.EarStart H → (Graph.ofSimpleGraph G).EarStart H.toGraph
  | _, .vertex v =>
      cast (congrArg _ (Subgraph.toGraph_singletonSubgraph v).symm) (.vertex ⟨v, Set.mem_univ v⟩)
  | _, .cycle c hc =>
      cast (congrArg _ c.walkGraph_toGraph) (.cycle c.toGraph (c.isCycle_toGraph_iff.mpr hc))

@[simp]
theorem isCycle_toGraph (s : G.EarStart H) : s.toGraph.IsCycle ↔ s.IsCycle := by
  cases s with
  | vertex v =>
      exact (Graph.EarStart.isCycle_iff_of_heq (Subgraph.toGraph_singletonSubgraph v)
        (cast_heq (congrArg _ (Subgraph.toGraph_singletonSubgraph v).symm)
          ((.vertex ⟨v, Set.mem_univ v⟩) :
            (Graph.ofSimpleGraph G).EarStart (Graph.noEdge {v} (Sym2 α))))).trans
        ((Graph.EarStart.isCycle_vertex _).trans
          (SimpleGraph.EarStart.isCycle_vertex _).symm)
  | cycle c hc =>
      exact (Graph.EarStart.isCycle_iff_of_heq c.walkGraph_toGraph.symm
        (cast_heq (congrArg _ c.walkGraph_toGraph) (.cycle c.toGraph _))).trans
        ((Graph.EarStart.isCycle_cycle _ _).trans
          (SimpleGraph.EarStart.isCycle_cycle _ _).symm)

end EarStart

end SimpleGraph

namespace Graph

namespace Ear

variable {K : Graph α (Sym2 α)} {H : G.Subgraph}

/-- An ear over `K` in `Graph.ofSimpleGraph G`, as an ear of `G` over a subgraph `H` whose
multigraph is `K`, with the corresponding vertex-based walk. -/
def toSimpleGraph : (ofSimpleGraph G).Ear K → H.toGraph = K → G.Ear H
  | .open _ p hp hs ht hst hint hedge, h =>
      .«open» p.toSimpleGraph (p.isPath_toSimpleGraph_iff.mpr hp) (by simpa [← h] using hs)
        (by simpa [← h] using ht) hst (by simpa [← h] using hint) (by simpa [← h] using hedge)
  | .closed _ c hc hs hint _, h =>
      .closed c.toSimpleGraph (c.isCycle_toSimpleGraph_iff.mpr hc) (by simpa [← h] using hs)
        (by simpa [← h] using hint)

@[simp]
theorem toWalk_toSimpleGraph (e : (ofSimpleGraph G).Ear K) (h : H.toGraph = K) :
    (e.toSimpleGraph h).toWalk =
      ⟨e.toWalk.1, e.toWalk.2.1, (e.toWalk.2.2 : (ofSimpleGraph G).Walk _ _).toSimpleGraph⟩ := by
  cases e with
  | «open» => rw [toSimpleGraph, SimpleGraph.Ear.toWalk_open, toWalk_open]
  | closed => rw [toSimpleGraph, SimpleGraph.Ear.toWalk_closed, toWalk_closed]

@[simp]
theorem kind_toSimpleGraph_eq_open_iff (e : (ofSimpleGraph G).Ear K) (h : H.toGraph = K) :
    (e.toSimpleGraph h).kind = .«open» ↔ e.kind = .open := by
  cases e <;> simp [toSimpleGraph]

@[simp]
theorem _root_.SimpleGraph.Ear.toSimpleGraph_toGraph (e : G.Ear H) :
    e.toGraph.toSimpleGraph rfl = e :=
  SimpleGraph.Ear.ext <| by
    rw [toWalk_toSimpleGraph, SimpleGraph.Ear.toWalk_toGraph,
      SimpleGraph.Walk.toSimpleGraph_toGraph]

@[simp]
theorem toGraph_toSimpleGraph (e : (ofSimpleGraph G).Ear H.toGraph) :
    (e.toSimpleGraph rfl).toGraph = e :=
  Ear.ext _ _ (by cases e <;> simp [toSimpleGraph, SimpleGraph.Ear.toGraph]) <| by
    rw [SimpleGraph.Ear.toWalk_toGraph, toWalk_toSimpleGraph, Walk.toGraph_toSimpleGraph]

private theorem toGraph_toSimpleGraph_heq (e : (ofSimpleGraph G).Ear K) (h : H.toGraph = K) :
    (e.toSimpleGraph h).toGraph ≍ e := by
  subst h
  exact heq_of_eq (toGraph_toSimpleGraph e)

/-- Transporting an ear to a simple graph and adjoining it recovers the multigraph obtained by
adjoining the original ear. -/
@[simp]
theorem toGraph_adjoin_toSimpleGraph (e : (ofSimpleGraph G).Ear K) (h : H.toGraph = K) :
    (e.toSimpleGraph h).adjoin.toGraph = e.add := by
  subst h
  rw [← SimpleGraph.Ear.add_toGraph, toGraph_toSimpleGraph]

end Ear

namespace EarStart

variable {K : Graph α (Sym2 α)} {H : G.Subgraph}

private theorem eq_singletonSubgraph {v : α} (h : H.toGraph = noEdge {v} (Sym2 α)) :
    H = G.singletonSubgraph v :=
  SimpleGraph.Subgraph.toGraph_injective <| by
    rw [h, SimpleGraph.Subgraph.toGraph_singletonSubgraph]

private theorem eq_toSubgraph {s : α} {c : (ofSimpleGraph G).Walk s s}
    (h : H.toGraph = (ofSimpleGraph G).walkGraph c) : H = c.toSimpleGraph.toSubgraph :=
  SimpleGraph.Subgraph.toGraph_injective <| by
    rw [h, ← SimpleGraph.Walk.walkGraph_toGraph, Walk.toGraph_toSimpleGraph]

/-- An initial vertex or cycle of `Graph.ofSimpleGraph G` with initial graph `K`, as an initial
vertex or cycle of `G` with an initial subgraph whose multigraph is `K`. -/
def toSimpleGraph : {K : Graph α (Sym2 α)} → (ofSimpleGraph G).EarStart K → H.toGraph = K →
    G.EarStart H
  | _, .vertex v, h => cast (congrArg _ (eq_singletonSubgraph h).symm) (.vertex v.1)
  | _, .cycle c hc, h =>
      cast (congrArg _ (eq_toSubgraph h).symm)
        (.cycle c.toSimpleGraph (c.isCycle_toSimpleGraph_iff.mpr hc))

private theorem isCycle_cast {K L : G.Subgraph} (h : K = L) (s : G.EarStart K) :
    (cast (congrArg _ h) s).IsCycle ↔ s.IsCycle := by
  subst h
  rfl

@[simp]
theorem isCycle_toSimpleGraph (s : (ofSimpleGraph G).EarStart K) (h : H.toGraph = K) :
    (s.toSimpleGraph h).IsCycle ↔ s.IsCycle := by
  cases s with
  | vertex => rw [toSimpleGraph, isCycle_cast (eq_singletonSubgraph h).symm]; simp
  | cycle => rw [toSimpleGraph, isCycle_cast (eq_toSubgraph h).symm]; simp

private theorem toSimpleGraph_cast {K L : Graph α (Sym2 α)} (e : K = L)
    (s : (ofSimpleGraph G).EarStart K) (h : H.toGraph = L) :
    (cast (congrArg _ e) s).toSimpleGraph h ≍ s.toSimpleGraph (h.trans e.symm) := by
  subst e
  rfl

private theorem toGraph_cast {H₁ H₂ : G.Subgraph} (e : H₁ = H₂) (s : G.EarStart H₁) :
    (cast (congrArg _ e) s).toGraph ≍ s.toGraph := by
  subst e
  rfl

private theorem toSimpleGraph_toGraph_heq {H₁ H₂ : G.Subgraph} (s : G.EarStart H₁)
    (h : H₂.toGraph = H₁.toGraph) : s.toGraph.toSimpleGraph h ≍ s := by
  cases s with
  | vertex v =>
    rw [SimpleGraph.EarStart.toGraph]
    refine (toSimpleGraph_cast (SimpleGraph.Subgraph.toGraph_singletonSubgraph v).symm _ _).trans ?_
    rw [toSimpleGraph]
    exact cast_heq _ _
  | @cycle u c hc =>
    rw [SimpleGraph.EarStart.toGraph]
    refine (toSimpleGraph_cast c.walkGraph_toGraph _ _).trans ?_
    rw [toSimpleGraph]
    refine (cast_heq _ _).trans ?_
    suffices ∀ c' : G.Walk u u, c' = c → ∀ hc', SimpleGraph.EarStart.cycle c' hc' ≍
        SimpleGraph.EarStart.cycle c hc from this _ c.toSimpleGraph_toGraph _
    rintro _ rfl _
    rfl

private theorem toGraph_toSimpleGraph_heq (s : (ofSimpleGraph G).EarStart K)
    (h : H.toGraph = K) : (s.toSimpleGraph h).toGraph ≍ s := by
  cases s with
  | vertex v =>
    rw [toSimpleGraph]
    refine (toGraph_cast (eq_singletonSubgraph h).symm _).trans ?_
    rw [SimpleGraph.EarStart.toGraph]
    exact cast_heq _ _
  | @cycle u c hc =>
    rw [toSimpleGraph]
    refine (toGraph_cast (eq_toSubgraph h).symm _).trans ?_
    rw [SimpleGraph.EarStart.toGraph]
    refine (cast_heq _ _).trans ?_
    suffices ∀ c' : (ofSimpleGraph G).Walk u u, c' = c → ∀ hc', cycle c' hc' ≍ cycle c hc from
      this _ c.toGraph_toSimpleGraph _
    rintro _ rfl _
    rfl

private theorem toSimpleGraph_heq_of_heq {K₁ K₂ : Graph α (Sym2 α)} {H₁ H₂ : G.Subgraph}
    {s₁ : (ofSimpleGraph G).EarStart K₁} {s₂ : (ofSimpleGraph G).EarStart K₂} (hK : K₁ = K₂)
    (hs : s₁ ≍ s₂) (h₁ : H₁.toGraph = K₁) (h₂ : H₂.toGraph = K₂) :
    s₁.toSimpleGraph h₁ ≍ s₂.toSimpleGraph h₂ := by
  subst hK
  cases eq_of_heq hs
  obtain rfl : H₁ = H₂ := SimpleGraph.Subgraph.toGraph_injective (h₁.trans h₂.symm)
  rfl

@[simp]
theorem _root_.SimpleGraph.EarStart.toSimpleGraph_toGraph (s : G.EarStart H) :
    s.toGraph.toSimpleGraph rfl = s :=
  eq_of_heq (toSimpleGraph_toGraph_heq s rfl)

@[simp]
theorem toGraph_toSimpleGraph (s : (ofSimpleGraph G).EarStart H.toGraph) :
    (s.toSimpleGraph rfl).toGraph = s :=
  eq_of_heq (toGraph_toSimpleGraph_heq s rfl)

end EarStart

end Graph

namespace SimpleGraph.EarDecomposition

variable {H : G.Subgraph}

/-- An ear decomposition of a subgraph `H` of a simple graph `G`, as an ear decomposition of
`H.toGraph` in `Graph.ofSimpleGraph G` with the multigraphs of the same stages and the transported
ears. -/
@[expose, reducible]
def toGraph (d : G.EarDecomposition H) : (Graph.ofSimpleGraph G).EarDecomposition H.toGraph where
  length := d.length
  graphAfter i := (d.subgraphAfter i).toGraph
  start := d.start.toGraph
  earAt i := ⟨_, (d.earAt i).toGraph⟩
  earAt_fst _ := rfl
  graphAfter_succ i := by rw [d.subgraphAfter_succ, Ear.add_toGraph]
  graphAfter_last := by rw [d.subgraphAfter_last]

@[simp]
theorem length_toGraph (d : G.EarDecomposition H) : d.toGraph.length = d.length := rfl

@[simp]
theorem graphAfter_toGraph (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    d.toGraph.graphAfter i = (d.subgraphAfter i).toGraph := rfl

theorem initial_toGraph (d : G.EarDecomposition H) : d.toGraph.initial = d.initial.toGraph := by
  rw [Graph.EarDecomposition.initial_eq_graphAfter, ← subgraphAfter_zero]

theorem walkAt_toGraph (d : G.EarDecomposition H) (i : Fin d.length) :
    d.toGraph.walkAt i =
      ⟨(d.walkAt i).1, (d.walkAt i).2.1, ((d.walkAt i).2.2 : G.Walk _ _).toGraph⟩ := by
  rw [walkAt_def]
  exact (Graph.EarDecomposition.walkAt_eq _ _).trans (d.earAt i).toWalk_toGraph

theorem kindAt_toGraph_eq_open_iff (d : G.EarDecomposition H) (i : Fin d.length) :
    d.toGraph.kindAt i = .open ↔ d.kindAt i = .«open» := by
  rw [kindAt_def, ← (d.earAt i).kind_toGraph_eq_open_iff]
  exact Iff.of_eq (congrArg (· = .open) (Graph.EarDecomposition.kindAt_eq d.toGraph i))

@[simp]
theorem isOpen_toGraph (d : G.EarDecomposition H) : d.toGraph.IsOpen ↔ d.IsOpen := by
  rw [Graph.EarDecomposition.isOpen_iff, isOpen_iff]
  exact and_congr d.start.isCycle_toGraph (forall_congr' d.kindAt_toGraph_eq_open_iff)

/-- A transported decomposition starts from a single vertex exactly when the original one does. -/
@[simp]
theorem isVertexStart_toGraph (d : G.EarDecomposition H) :
    d.toGraph.IsVertexStart ↔ ∃ v, d.initial = G.singletonSubgraph v := by
  rw [Graph.EarDecomposition.isVertexStart_iff, initial_toGraph]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, Subgraph.toGraph_injective (by rw [hv, Subgraph.toGraph_singletonSubgraph])⟩
  · rintro ⟨v, hv⟩
    exact ⟨⟨v, Set.mem_univ v⟩, by rw [hv, Subgraph.toGraph_singletonSubgraph]⟩

end SimpleGraph.EarDecomposition

namespace Graph.EarDecomposition

variable {K : Graph α (Sym2 α)} {H : G.Subgraph}

/-- An ear decomposition of `K` in `Graph.ofSimpleGraph G`, as an ear decomposition in `G` of a
subgraph `H` whose multigraph is `K`, with the subgraphs of the same stages and the transported
ears. -/
@[expose, reducible]
def toSimpleGraph (d : (ofSimpleGraph G).EarDecomposition K) (h : H.toGraph = K) :
    G.EarDecomposition H where
  length := d.length
  subgraphAfter i :=
    SimpleGraph.Subgraph.toGraphOrderIso.symm ⟨d.graphAfter i, d.graphAfter_le i⟩
  start := d.start.toSimpleGraph (SimpleGraph.Subgraph.toGraph_toGraphOrderIso_symm_apply _)
  earAt i := (d.earAt i).2.toSimpleGraph
    ((SimpleGraph.Subgraph.toGraph_toGraphOrderIso_symm_apply _).trans (d.earAt_fst i).symm)
  subgraphAfter_succ i := SimpleGraph.Subgraph.toGraph_injective <| by
    rw [SimpleGraph.Subgraph.toGraph_toGraphOrderIso_symm_apply, Ear.toGraph_adjoin_toSimpleGraph]
    exact d.graphAfter_succ i
  subgraphAfter_last := SimpleGraph.Subgraph.toGraph_injective <| by
    rw [SimpleGraph.Subgraph.toGraph_toGraphOrderIso_symm_apply, h]
    exact d.graphAfter_last

@[simp]
theorem length_toSimpleGraph (d : (ofSimpleGraph G).EarDecomposition K) (h : H.toGraph = K) :
    (d.toSimpleGraph h).length = d.length := rfl

theorem toGraph_subgraphAfter_toSimpleGraph (d : (ofSimpleGraph G).EarDecomposition K)
    (h : H.toGraph = K) (i : Fin (d.length + 1)) :
    ((d.toSimpleGraph h).subgraphAfter i).toGraph = d.graphAfter i :=
  SimpleGraph.Subgraph.toGraph_toGraphOrderIso_symm_apply _

@[simp]
theorem toGraph_initial_toSimpleGraph (d : (ofSimpleGraph G).EarDecomposition K)
    (h : H.toGraph = K) : (d.toSimpleGraph h).initial.toGraph = d.initial := by
  rw [← SimpleGraph.EarDecomposition.subgraphAfter_zero, initial_eq_graphAfter]
  exact d.toGraph_subgraphAfter_toSimpleGraph h 0

@[simp]
theorem walkAt_toSimpleGraph (d : (ofSimpleGraph G).EarDecomposition K) (h : H.toGraph = K)
    (i : Fin d.length) :
    (d.toSimpleGraph h).walkAt i =
      ⟨(d.walkAt i).1, (d.walkAt i).2.1,
        ((d.walkAt i).2.2 : (ofSimpleGraph G).Walk _ _).toSimpleGraph⟩ := by
  rw [walkAt_eq]
  exact (SimpleGraph.EarDecomposition.walkAt_def _ _).trans (Ear.toWalk_toSimpleGraph _ _)

@[simp]
theorem kindAt_toSimpleGraph_eq_open_iff (d : (ofSimpleGraph G).EarDecomposition K)
    (h : H.toGraph = K) (i : Fin d.length) :
    (d.toSimpleGraph h).kindAt i = .«open» ↔ d.kindAt i = .open := by
  rw [kindAt_eq]
  exact (Iff.of_eq (congrArg (fun k : SimpleGraph.EarKind ↦ k = .«open»)
    (SimpleGraph.EarDecomposition.kindAt_def (d.toSimpleGraph h) i))).trans
      (Ear.kind_toSimpleGraph_eq_open_iff _ _)

@[simp]
theorem isOpen_toSimpleGraph (d : (ofSimpleGraph G).EarDecomposition K) (h : H.toGraph = K) :
    (d.toSimpleGraph h).IsOpen ↔ d.IsOpen := by
  rw [SimpleGraph.EarDecomposition.isOpen_iff, isOpen_iff]
  exact and_congr (d.start.isCycle_toSimpleGraph _)
    (forall_congr' (d.kindAt_toSimpleGraph_eq_open_iff h))

@[simp]
theorem _root_.SimpleGraph.EarDecomposition.toSimpleGraph_toGraph
    (d : G.EarDecomposition H) : d.toGraph.toSimpleGraph rfl = d := by
  refine SimpleGraph.EarDecomposition.ext rfl ?_ ?_ fun i ↦ ?_
  · apply SimpleGraph.Subgraph.toGraph_injective
    rw [toGraph_initial_toSimpleGraph, SimpleGraph.EarDecomposition.initial_toGraph]
  · exact EarStart.toSimpleGraph_toGraph_heq d.start _
  · rw [walkAt_toSimpleGraph, SimpleGraph.EarDecomposition.walkAt_toGraph,
      SimpleGraph.Walk.toSimpleGraph_toGraph]
    congr 1

@[simp]
theorem toGraph_toSimpleGraph (d : (ofSimpleGraph G).EarDecomposition H.toGraph) :
    (d.toSimpleGraph rfl).toGraph = d := by
  refine EarDecomposition.ext _ _ rfl (heq_of_eq (funext fun i ↦ ?_))
    (EarStart.toGraph_toSimpleGraph_heq d.start _) (heq_of_eq (funext fun i ↦ ?_))
  · exact d.toGraph_subgraphAfter_toSimpleGraph rfl i
  · exact Sigma.ext ((d.toGraph_subgraphAfter_toSimpleGraph rfl _).trans (d.earAt_fst i).symm)
      (Ear.toGraph_toSimpleGraph_heq _ _)

/-- Transporting a prefix of a multigraph ear decomposition gives the corresponding prefix of the
transported decomposition. -/
theorem toSimpleGraph_prefix (d : (ofSimpleGraph G).EarDecomposition K) (h : H.toGraph = K)
    (k : Fin (d.length + 1)) :
    (d.prefix k).toSimpleGraph (d.toGraph_subgraphAfter_toSimpleGraph h k) =
      (d.toSimpleGraph h).prefix k := by
  refine SimpleGraph.EarDecomposition.ext (d.length_prefix k) ?_ ?_ fun i ↦ ?_
  · apply SimpleGraph.Subgraph.toGraph_injective
    rw [toGraph_initial_toSimpleGraph, SimpleGraph.EarDecomposition.initial_prefix,
      toGraph_initial_toSimpleGraph, initial_prefix]
  · have hzero : (d.prefix k).graphAfter 0 = d.graphAfter 0 := by
      simpa only [initial_eq_graphAfter] using d.initial_prefix k
    exact EarStart.toSimpleGraph_heq_of_heq hzero (d.heq_start_prefix k) _ _
  · refine (walkAt_toSimpleGraph _ _ i).trans (Eq.trans ?_
      ((SimpleGraph.EarDecomposition.walkAt_prefix _ k _).trans (walkAt_toSimpleGraph d h _)).symm)
    have hi := d.walkAt_prefix k (i.cast (d.length_prefix k))
    rw [Fin.cast_cast, Fin.cast_eq_self] at hi
    rw [hi]
    rfl

end Graph.EarDecomposition

namespace SimpleGraph

/-- Transporting a prefix of an ear decomposition gives the corresponding prefix of the
transported decomposition. -/
theorem EarDecomposition.toGraph_prefix {H : G.Subgraph} (d : G.EarDecomposition H)
    (k : Fin (d.length + 1)) : (d.prefix k).toGraph = d.toGraph.prefix k := by
  have hleft : (d.prefix k).toGraph.length = k :=
    (EarDecomposition.length_toGraph (d.prefix k)).trans (d.length_prefix k)
  have hright : (d.toGraph.prefix k).length = k := d.toGraph.length_prefix k
  have hlen : (d.prefix k).toGraph.length = (d.toGraph.prefix k).length :=
    hleft.trans hright.symm
  refine Graph.EarDecomposition.ext _ _ hlen ?_ ?_ ?_
  · refine (Fin.heq_fun_iff (congrArg (· + 1) hlen)).mpr fun i ↦ ?_
    let j : Fin (k + 1) := Fin.cast (congrArg (· + 1) hleft) i
    have hi : i = Fin.cast (congrArg (· + 1) hleft).symm j := Fin.ext rfl
    have hj : (⟨i, congrArg (· + 1) hlen ▸ i.2⟩ :
        Fin ((d.toGraph.prefix k).length + 1)) =
        Fin.cast (congrArg (· + 1) hright).symm j := Fin.ext rfl
    rw [hj, hi, EarDecomposition.graphAfter_toGraph,
      show Fin.cast (congrArg (· + 1) hleft).symm j = j from Fin.ext rfl,
      Graph.EarDecomposition.graphAfter_prefix,
      EarDecomposition.graphAfter_toGraph,
      SimpleGraph.EarDecomposition.subgraphAfter_prefix]
  · exact (d.toGraph.heq_start_prefix k).symm
  · refine (Fin.heq_fun_iff hlen).mpr fun i ↦ ?_
    let j : Fin k := Fin.cast hleft i
    have hi : i = Fin.cast hleft.symm j := Fin.ext rfl
    have hj : (⟨i, hlen ▸ i.2⟩ : Fin (d.toGraph.prefix k).length) =
        Fin.cast hright.symm j := Fin.ext rfl
    rw [hj, hi, Graph.EarDecomposition.earAt_prefix]
    change (⟨_, ((d.prefix k).earAt (Fin.cast hleft.symm j)).toGraph⟩ :
        Σ K : Graph α (Sym2 α), (Graph.ofSimpleGraph G).Ear K) = _
    rw [show Fin.cast hleft.symm j = j from Fin.ext rfl,
      SimpleGraph.EarDecomposition.earAt_prefix]
    rfl

/-- Ear decompositions of a subgraph `H` of a simple graph `G` correspond to ear decompositions of
`H.toGraph` in `Graph.ofSimpleGraph G`. -/
def Subgraph.earDecompositionEquivOfSimpleGraph (H : G.Subgraph) :
    G.EarDecomposition H ≃ (Graph.ofSimpleGraph G).EarDecomposition H.toGraph where
  toFun d := d.toGraph
  invFun d := d.toSimpleGraph rfl
  left_inv := EarDecomposition.toSimpleGraph_toGraph
  right_inv := Graph.EarDecomposition.toGraph_toSimpleGraph

@[simp]
theorem Subgraph.earDecompositionEquivOfSimpleGraph_apply {H : G.Subgraph}
    (d : G.EarDecomposition H) : H.earDecompositionEquivOfSimpleGraph d = d.toGraph := (rfl)

@[simp]
theorem Subgraph.earDecompositionEquivOfSimpleGraph_symm_apply {H : G.Subgraph}
    (d : (Graph.ofSimpleGraph G).EarDecomposition H.toGraph) :
    H.earDecompositionEquivOfSimpleGraph.symm d = d.toSimpleGraph rfl := (rfl)

end SimpleGraph
