/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.EdgeConnectivity
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Bidirected
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.OfSimpleGraph
public import TauCeti.Combinatorics.Network.Acyclic
public import TauCeti.Combinatorics.Network.ShortestAugmentation

/-!
# Menger's theorem for edge-disjoint paths in multigraphs

Let `G : Graph α β` be a multigraph and let `s ≠ t`. Two walks of `G` are *edge-disjoint* when no
edge identity is traversed by both; distinct parallel edges are different edges, while a single
edge cannot be shared even if the two walks traverse it in opposite directions. A set `F` of edges
*separates* `s` from `t` when `s` and `t` are not reachable in `G.deleteEdges F`.

This file proves the local edge form of Menger's theorem for multigraphs with finitely many actual
vertices and edges: the largest number of pairwise edge-disjoint `s`–`t` paths equals the least
number of edges separating `s` from `t`. Weak duality, that every family of pairwise edge-disjoint
`s`–`t` walks has at most as many members as every separating set of edges, needs no finiteness:
each member traverses an edge of the separating set, and different members traverse different
edges. The predicate form identifies `k`-edge-reachability (`Graph.IsEdgeReachable`) with the
existence of `k` pairwise edge-disjoint `s`–`t` paths. Through `Graph.ofSimpleGraph`, the same
statements hold for simple graphs, with Mathlib's `SimpleGraph.IsEdgeReachable`.

## Main results

* `Graph.card_le_encard_of_not_reachable_deleteEdges`: **weak duality**, a family of pairwise
  edge-disjoint `s`–`t` walks has at most as many members as any set of edges separating `s` from
  `t`.
* `Graph.exists_paths_edgeSeparator_card_eq`: **Menger's theorem** for edge-disjoint paths in a
  multigraph, in witness form: there are a family of pairwise edge-disjoint `s`–`t` paths and a set
  of actual edges separating `s` from `t` of the same size.
* `Graph.isEdgeReachable_iff_exists_paths`: the predicate form, `s` and `t` are `k`-edge-reachable
  exactly when there are `k` pairwise edge-disjoint `s`–`t` paths.
* `SimpleGraph.card_le_encard_of_not_reachable_deleteEdges`,
  `SimpleGraph.exists_paths_edgeSeparator_card_eq`, `SimpleGraph.isEdgeReachable_iff_exists_paths`:
  the same statements for simple graphs.

## Implementation notes

Attainment runs the max-flow/min-cut theorem over `ℤ` (`TauCeti.Flow.exists_val_eq_arrowSum`) on
the bidirected arrow family `Graph.BidirectedHom G`, with capacity one on every arrow. A maximum
flow has the value of a cut `S`, which is the number of arrows leaving `S`. Each edge crossing `S`
gives exactly one arrow leaving `S`, so these arrows come from as many distinct edges, and deleting
those edges separates `s` from `t`. Directed paths carrying a unit flow may still use the two
opposite arrows of a single edge, so the flow is first replaced by an acyclic flow of the same
value (`TauCeti.Flow.exists_isAcyclic`), which is positive on at most one of any two opposite
arrows. Its decomposition into unit paths then gives arrow-disjoint directed paths no two of which
use the same edge, and these are edge-disjoint paths of `G`.

## References

* K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927).
* L. R. Ford, D. R. Fulkerson, *Maximal flow through a network*, Canad. J. Math. 8 (1956).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Sections 9.1 and 9.2.
-/

public section

open Finset TauCeti

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {s t : α}

/-- **Weak duality for edge-disjoint walks.** A family of `s`–`t` walks, from an actual vertex `s`,
of which no two traverse a common edge has at most as many members as any set of edges whose
deletion leaves `s` and `t` unreachable. -/
theorem card_le_encard_of_not_reachable_deleteEdges {ι : Type*} {P : ι → G.Walk s t}
    (hP : Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges) (hs : s ∈ V(G)) {F : Set β}
    (hF : ¬(G.deleteEdges F).Reachable s t) : ENat.card ι ≤ F.encard := by
  -- Each member traverses an edge of `F`, and different members traverse different edges.
  have h (i : ι) : ∃ e ∈ (P i).edges, e ∈ F := by
    by_contra! h
    exact hF (reachable_deleteEdges_iff_exists_walk.2 ⟨hs, P i, h⟩)
  choose g hg hgF using h
  have hinj : Function.Injective g := fun i j hij ↦ by
    by_contra hne
    exact hP hne (hg i) (hij ▸ hg j)
  rw [← hinj.encard_range]
  exact Set.encard_le_encard (Set.range_subset_iff.2 hgF)

/-- An acyclic integer flow on the bidirected arrow family of a multigraph, between distinct
vertices and carrying at most one unit on every arrow, carries as many paths of the multigraph as
its value, no two of which traverse a common edge. -/
private theorem exists_paths_card_eq_val_of_isAcyclic [Fintype V(G)]
    [∀ x y, Fintype (G.BidirectedHom x y)] {cap : Assignment G.BidirectedHom ℤ} {s t : V(G)}
    (hst : s ≠ t) (f : Flow cap s t) (hf : f.toFun.IsAcyclic)
    (hf₁ : ∀ ⦃x y : V(G)⦄ (e : G.BidirectedHom x y), f.toFun e ≤ 1) :
    ∃ (k : ℕ) (P : Fin k → G.Walk s t), (k : ℤ) = f.val ∧ (∀ i, (P i).IsPath) ∧
      Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges := by
  obtain ⟨k, P, hk, hP, hone, hdisj⟩ := f.exists_paths_card_eq_val hst hf₁
  refine ⟨k, fun i ↦ (P i).toGraphWalk, hk, fun i ↦ (ArrowWalk.isPath_toGraphWalk_iff _).2 (hP i),
    fun i j hij e hei hej ↦ ?_⟩
  -- Two paths sharing an edge traverse it either along the same arrow, which arrow-disjointness
  -- excludes, or along opposite arrows, both carrying flow, which acyclicity excludes.
  simp only [ArrowWalk.edges_toGraphWalk, List.mem_map] at hei hej
  obtain ⟨⟨x, y, e, hxy⟩, hai, rfl⟩ := hei
  obtain ⟨⟨x', y', e', hxy'⟩, haj, rfl : e' = e⟩ := hej
  rcases hxy.eq_and_eq_or_eq_and_eq hxy' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · obtain rfl : x = x' := Subtype.ext h₁
    obtain rfl : y = y' := Subtype.ext h₂
    exact hdisj hij hai haj
  · obtain rfl : x = y' := Subtype.ext h₁
    obtain rfl : y = x' := Subtype.ext h₂
    exact hf.not_pos_and_pos (⟨_, hxy⟩ : G.BidirectedHom x y) ⟨_, hxy'⟩
      ⟨(hone i _ hai).symm ▸ one_pos, (hone j _ haj).symm ▸ one_pos⟩

/-- **Menger's theorem for edge-disjoint paths in a multigraph.** For distinct points `s` and `t`
of a multigraph with finitely many actual vertices and edges, some family of `s`–`t` paths, no two
of which traverse a common edge, has as many members as some set of actual edges whose deletion
leaves `s` and `t` unreachable. By `Graph.card_le_encard_of_not_reachable_deleteEdges`, the family
is then largest and the set of edges smallest. -/
theorem exists_paths_edgeSeparator_card_eq [Finite V(G)] [Finite E(G)] (hst : s ≠ t) :
    ∃ (k : ℕ) (P : Fin k → G.Walk s t) (F : Finset β), (∀ i, (P i).IsPath) ∧
      (Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges) ∧ (F : Set β) ⊆ E(G) ∧
      ¬(G.deleteEdges F).Reachable s t ∧ #F = k := by
  classical
  -- Unless both points are actual vertices, they are not even reachable.
  by_cases hst' : s ∈ V(G) ∧ t ∈ V(G)
  swap
  · refine ⟨0, Fin.elim0, ∅, fun i ↦ i.elim0, fun i ↦ i.elim0, by simp, fun h ↦ hst' ?_, rfl⟩
    exact ⟨by simpa using h.left_mem, by simpa using h.right_mem⟩
  obtain ⟨hs, ht⟩ := hst'
  have := Fintype.ofFinite V(G)
  have (x y : V(G)) : Fintype (G.BidirectedHom x y) := Fintype.ofFinite _
  have hne : (⟨s, hs⟩ : V(G)) ≠ ⟨t, ht⟩ := fun h ↦ hst (congrArg Subtype.val h)
  -- A maximum flow for unit capacities on the bidirected arrow family has the value of a cut `S`,
  -- the number of arrows leaving `S`. An acyclic flow of the same value carries as many
  -- edge-disjoint paths; the edges of the arrows leaving `S` separate `s` from `t`.
  obtain ⟨f, S, hsS, htS, hval⟩ := Flow.exists_val_eq_arrowSum hne
    (cap := (1 : Assignment G.BidirectedHom ℤ)) fun _ _ _ ↦ zero_le_one
  obtain ⟨g, hg, hgval, -⟩ := f.exists_isAcyclic
  obtain ⟨k, P, hk, hP, hdisj⟩ :=
    exists_paths_card_eq_val_of_isAcyclic hne g hg fun _ _ e ↦ g.le_upper e
  let A : Finset (Σ x y, G.BidirectedHom x y) := {a | a.1 ∈ S ∧ a.2.1 ∈ Sᶜ}
  refine ⟨k, P, A.image fun a ↦ a.2.2.1, hP, hdisj, fun e he ↦ ?_, fun h ↦ ?_, ?_⟩
  · obtain ⟨a, -, rfl⟩ := mem_image.1 he
    exact a.2.2.2.edge_mem
  · -- A walk avoiding the deleted edges is a directed walk avoiding the arrows leaving `S`, so it
    -- cannot leave `S`.
    obtain ⟨-, p, hp⟩ := reachable_deleteEdges_iff_exists_walk.1 h
    have hA : ReachableWithout (A : Set (Σ x y, G.BidirectedHom x y)) (⟨s, hs⟩ : V(G)) ⟨t, ht⟩ :=
      reachableWithout_def.2 ⟨p.toBidirected hs, fun a ha haA ↦ hp a.2.2.1
        (p.edges_toBidirected hs ▸ List.mem_map_of_mem ha) (mem_coe.2 (mem_image_of_mem _ haA))⟩
    refine htS (hA.mem_of_mem (C := (S : Set V(G))) hsS fun v w e hv he ↦ ?_)
    by_contra hw
    exact he (by simpa [A] using ⟨hv, hw⟩)
  · -- Different arrows leaving `S` come from different edges.
    rw [card_image_of_injOn, ← Nat.cast_inj (R := ℤ), hk, hgval, hval, arrowSum_one]
    rintro ⟨x, y, e, hxy⟩ ha ⟨x', y', e', hxy'⟩ ha' (rfl : e = e')
    simp only [A, coe_filter, mem_univ, true_and, mem_compl, Set.mem_ofPred_eq] at ha ha'
    rcases hxy.eq_and_eq_or_eq_and_eq hxy' with ⟨h₁, h₂⟩ | ⟨h₁, -⟩
    · obtain rfl : x = x' := Subtype.ext h₁
      obtain rfl : y = y' := Subtype.ext h₂
      rfl
    · obtain rfl : x = y' := Subtype.ext h₁
      exact absurd ha.1 ha'.2

/-- **Menger's theorem for edge-disjoint paths in a multigraph, predicate form.** For an actual
vertex `s` of a multigraph with finitely many actual vertices and edges, `s` and `t` stay reachable
after deleting any fewer than `k` edges exactly when there are `k` `s`–`t` paths, no two of which
traverse a common edge. -/
theorem isEdgeReachable_iff_exists_paths [Finite V(G)] [Finite E(G)] (hs : s ∈ V(G)) (k : ℕ) :
    G.IsEdgeReachable k s t ↔ ∃ P : Fin k → G.Walk s t, (∀ i, (P i).IsPath) ∧
      Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges := by
  refine ⟨fun h ↦ ?_, fun ⟨P, _, hP⟩ ↦ isEdgeReachable_def.2 fun F hF ↦ ?_⟩
  · -- Between equal endpoints, the trivial path may be repeated.
    obtain rfl | hst := eq_or_ne s t
    · exact ⟨fun _ ↦ .nil, fun _ ↦ Walk.isPath_nil, fun _ _ _ ↦ by simp⟩
    obtain ⟨m, P, F, hP, hdisj, -, hF, hFm⟩ := exists_paths_edgeSeparator_card_eq (G := G) hst
    have hkm : k ≤ m := hFm ▸ not_lt.1 fun hlt ↦ hF (isEdgeReachable_def.1 h (by simpa using hlt))
    exact ⟨fun i ↦ P (Fin.castLE hkm i), fun i ↦ hP _,
      fun i j hij ↦ hdisj fun h ↦ hij (Fin.castLE_injective hkm h)⟩
  · by_contra h
    exact hF.not_ge (by simpa using card_le_encard_of_not_reachable_deleteEdges hP hs h)

end Graph

/-! ### Simple graphs -/

namespace SimpleGraph

variable {α : Type u} {G : SimpleGraph α} {s t : α}

/-- **Weak duality for edge-disjoint walks in a simple graph.** A family of `s`–`t` walks of which
no two traverse a common edge has at most as many members as any set of edges whose deletion leaves
`s` and `t` unreachable. -/
theorem card_le_encard_of_not_reachable_deleteEdges {ι : Type*} {P : ι → G.Walk s t}
    (hP : Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges) {F : Set (Sym2 α)}
    (hF : ¬(G.deleteEdges F).Reachable s t) : ENat.card ι ≤ F.encard :=
  Graph.card_le_encard_of_not_reachable_deleteEdges (P := fun i ↦ (P i).toGraph)
    (by simpa only [Walk.edges_toGraph] using hP) (Set.mem_univ s)
    (by rwa [Graph.ofSimpleGraph_deleteEdges, reachable_ofSimpleGraph_iff])

/-- **Menger's theorem for edge-disjoint paths in a simple graph.** For distinct vertices `s` and
`t` of a finite simple graph, some family of `s`–`t` paths, no two of which traverse a common edge,
has as many members as some set of edges of `G` whose deletion leaves `s` and `t` unreachable. By
`SimpleGraph.card_le_encard_of_not_reachable_deleteEdges`, the family is then largest and the set
of edges smallest. -/
theorem exists_paths_edgeSeparator_card_eq [Finite α] (hst : s ≠ t) :
    ∃ (k : ℕ) (P : Fin k → G.Walk s t) (F : Finset (Sym2 α)), (∀ i, (P i).IsPath) ∧
      (Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges) ∧ (F : Set (Sym2 α)) ⊆ G.edgeSet ∧
      ¬(G.deleteEdges F).Reachable s t ∧ #F = k := by
  have : Finite (Graph.ofSimpleGraph G).vertexSet := Subtype.finite
  have : Finite (Graph.ofSimpleGraph G).edgeSet := Subtype.finite
  obtain ⟨k, P, F, hP, hdisj, hFE, hF, hk⟩ :=
    Graph.exists_paths_edgeSeparator_card_eq (G := Graph.ofSimpleGraph G) hst
  refine ⟨k, fun i ↦ (P i).toSimpleGraph, F,
    fun i ↦ (Graph.Walk.isPath_toSimpleGraph_iff _).2 (hP i),
    by simpa only [Graph.Walk.edges_toSimpleGraph] using hdisj, by simpa using hFE, ?_, hk⟩
  rwa [Graph.ofSimpleGraph_deleteEdges, reachable_ofSimpleGraph_iff] at hF

/-- **Menger's theorem for edge-disjoint paths in a simple graph, predicate form.** In a finite
simple graph, `s` and `t` stay reachable after deleting any fewer than `k` edges exactly when there
are `k` `s`–`t` paths, no two of which traverse a common edge. -/
theorem isEdgeReachable_iff_exists_paths [Finite α] (k : ℕ) :
    G.IsEdgeReachable k s t ↔ ∃ P : Fin k → G.Walk s t, (∀ i, (P i).IsPath) ∧
      Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges := by
  have : Finite (Graph.ofSimpleGraph G).vertexSet := Subtype.finite
  have : Finite (Graph.ofSimpleGraph G).edgeSet := Subtype.finite
  rw [← Graph.isEdgeReachable_ofSimpleGraph_iff,
    Graph.isEdgeReachable_iff_exists_paths (Set.mem_univ s)]
  refine ⟨fun ⟨P, hP, hdisj⟩ ↦ ⟨fun i ↦ (P i).toSimpleGraph, fun i ↦ ?_, ?_⟩,
    fun ⟨P, hP, hdisj⟩ ↦ ⟨fun i ↦ (P i).toGraph, fun i ↦ ?_, ?_⟩⟩
  · exact (Graph.Walk.isPath_toSimpleGraph_iff _).2 (hP i)
  · simpa only [Graph.Walk.edges_toSimpleGraph] using hdisj
  · exact (Walk.isPath_toGraph_iff _).2 (hP i)
  · simpa only [Walk.edges_toGraph] using hdisj

end SimpleGraph
