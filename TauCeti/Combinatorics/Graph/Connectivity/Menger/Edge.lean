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
public import TauCeti.Combinatorics.Network.Menger.Edge

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

The set-to-set form allows disjoint terminal sets `A` and `B`. Its paths may share endpoints, but
their internal vertices avoid both terminal sets. The largest number of pairwise edge-disjoint
`A`–`B` paths equals the least number of edges whose deletion separates every vertex of `B` from
every vertex of `A`. Set-to-set weak duality also needs no finiteness. Empty terminal sets are
allowed.

## Main results

* `Graph.card_le_encard_of_not_reachable_deleteEdges`: **weak duality**, a family of pairwise
  edge-disjoint `s`–`t` walks has at most as many members as any set of edges separating `s` from
  `t`.
* `Graph.exists_paths_edgeSeparator_card_eq`: **Menger's theorem** for edge-disjoint paths in a
  multigraph, in witness form: there are a family of pairwise edge-disjoint `s`–`t` paths and a set
  of actual edges separating `s` from `t` of the same size.
* `Graph.isEdgeReachable_iff_exists_paths`: the predicate form, `s` and `t` are `k`-edge-reachable
  exactly when there are `k` pairwise edge-disjoint `s`–`t` paths.
* `Graph.card_le_encard_of_forall_not_reachable_deleteEdges`: set-to-set weak duality.
* `Graph.exists_paths_setEdgeSeparator_card_eq`: the corresponding witness theorem between
  disjoint vertex sets.
* `Graph.forall_exists_reachable_deleteEdges_iff_exists_paths`: its predicate form.
* `SimpleGraph.card_le_encard_of_not_reachable_deleteEdges`,
  `SimpleGraph.exists_paths_edgeSeparator_card_eq`, `SimpleGraph.isEdgeReachable_iff_exists_paths`:
  the same statements for simple graphs.
* `SimpleGraph.card_le_encard_of_forall_not_reachable_deleteEdges`,
  `SimpleGraph.exists_paths_setEdgeSeparator_card_eq`,
  `SimpleGraph.forall_exists_reachable_deleteEdges_iff_exists_paths`: the set-to-set theorems for
  simple graphs.

## Implementation notes

Attainment starts from `TauCeti.SetFlow.exists_val_eq_arrowSum` over `ℤ` on the bidirected arrow
family `Graph.BidirectedHom G`, with capacity one on every arrow. A maximum set-to-set flow has the
value of a cut `S`, the number of arrows leaving `S`. It is replaced by an acyclic flow of the same
value using `TauCeti.SetFlow.exists_isAcyclic`, decomposed into arrow-disjoint unit paths, and
trimmed so the path interiors avoid `A ∪ B`. Acyclicity prevents two paths from using opposite
orientations of one edge. Each cut edge supplies exactly one arrow leaving `S`, so the cut arrows
have distinct underlying edges; deleting those edges separates `B` from `A`. The local theorem is
the singleton-terminal corollary.

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

/-! ### Edge-disjoint paths between vertex sets -/

/-- **Weak duality for edge-disjoint set-to-set walks.** A family of walks, each from a vertex of
`A` to a vertex of `B`, of which no two traverse a common edge has at most as many members as any
set of edges whose deletion leaves no vertex of `B` reachable from a vertex of `A`. No finiteness
assumption is needed, but every walk must start at an actual vertex. -/
theorem card_le_encard_of_forall_not_reachable_deleteEdges {A B : Set α} {ι : Type*}
    {a b : ι → α} {P : ∀ i, G.Walk (a i) (b i)} (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ B)
    (hstart : ∀ i, a i ∈ V(G))
    (hP : Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges) {F : Set β}
    (hF : ∀ a ∈ A, ∀ b ∈ B, ¬(G.deleteEdges F).Reachable a b) : ENat.card ι ≤ F.encard := by
  have h (i : ι) : ∃ e ∈ (P i).edges, e ∈ F := by
    by_contra! h
    exact hF _ (ha i) _ (hb i) (reachable_deleteEdges_iff_exists_walk.2 ⟨hstart i, P i, h⟩)
  choose g hg hgF using h
  have hinj : Function.Injective g := fun i j hij ↦ by
    by_contra hne
    exact hP hne (hg i) (hij ▸ hg j)
  rw [← hinj.encard_range]
  exact Set.encard_le_encard (Set.range_subset_iff.2 hgF)

/-- Arrow-disjoint walks supported positively by an acyclic assignment become edge-disjoint
walks of the underlying multigraph. -/
private theorem pairwise_disjoint_edges_toGraphWalk {ι : Type*} {a b : ι → V(G)}
    {P : ∀ i, ArrowWalk G.BidirectedHom (a i) (b i)} {f : Assignment G.BidirectedHom ℤ}
    (hf : f.IsAcyclic)
    (hone : ∀ i (e : Σ x y, G.BidirectedHom x y), e ∈ (P i).arrows → f e.2.2 = 1)
    (hdisj : Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows) :
    Pairwise fun i j ↦ (P i).toGraphWalk.edges.Disjoint (P j).toGraphWalk.edges := by
  intro i j hij e hei hej
  simp only [ArrowWalk.edges_toGraphWalk, List.mem_map] at hei hej
  obtain ⟨⟨x, y, d, hxy⟩, hai, rfl⟩ := hei
  obtain ⟨⟨x', y', d', hxy'⟩, haj, rfl : d' = d⟩ := hej
  rcases hxy.eq_and_eq_or_eq_and_eq hxy' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · obtain rfl : x = x' := Subtype.ext h₁
    obtain rfl : y = y' := Subtype.ext h₂
    exact hdisj hij hai haj
  · obtain rfl : x = y' := Subtype.ext h₁
    obtain rfl : y = x' := Subtype.ext h₂
    exact hf.not_pos_and_pos (⟨_, hxy⟩ : G.BidirectedHom x y) ⟨_, hxy'⟩
      ⟨(hone i _ hai).symm ▸ one_pos, (hone j _ haj).symm ▸ one_pos⟩

/-- **Menger's theorem for edge-disjoint paths between vertex sets in a multigraph.** Let `A` and
`B` be disjoint finite vertex sets of a multigraph with finitely many actual vertices and edges.
Some family of pairwise edge-disjoint paths from `A` to `B`, with no internal vertex in
either terminal set, has as many members as some set of actual edges whose deletion separates
`B` from `A`. Shared endpoints are allowed. -/
theorem exists_paths_setEdgeSeparator_card_eq [Finite V(G)] [Finite E(G)] {A B : Finset α}
    (hAB : Disjoint A B) :
    ∃ (k : ℕ) (a b : Fin k → α) (P : ∀ i, G.Walk (a i) (b i)) (F : Finset β),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).support, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
      (Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges) ∧ (F : Set β) ⊆ E(G) ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬(G.deleteEdges F).Reachable a b) ∧ #F = k := by
  classical
  let _ : Fintype V(G) := Fintype.ofFinite _
  let _ : Fintype E(G) := Fintype.ofFinite _
  let _ (x y : V(G)) : Fintype (G.BidirectedHom x y) := Fintype.ofFinite _
  let A' : Finset V(G) := {v | v.1 ∈ A}
  let B' : Finset V(G) := {v | v.1 ∈ B}
  have hAB' : Disjoint A' B' := by
    rw [disjoint_left]
    intro v hvA hvB
    exact disjoint_left.1 hAB (by simpa [A'] using hvA) (by simpa [B'] using hvB)
  obtain ⟨f, S, hS, hval⟩ := SetFlow.exists_val_eq_arrowSum (Q := G.BidirectedHom)
    (cap := (1 : Assignment G.BidirectedHom ℤ)) hAB' fun _ _ _ ↦ zero_le_one
  -- Cancel cycles without changing the flow value, then decompose into arrow-disjoint unit paths.
  obtain ⟨g, hg, hgval, -⟩ := f.exists_isAcyclic
  obtain ⟨k, a, b, P, hk, ha, hb, hP, hint, hone, hdisj⟩ :=
    g.exists_paths_card_eq_val fun _ _ e ↦ g.le_cap e
  -- The acyclic assignment cannot support opposite orientations of one edge, so the trimmed
  -- arrow-disjoint paths are also edge-disjoint in the multigraph.
  have hPdisj : Pairwise fun i j ↦ (P i).toGraphWalk.edges.Disjoint (P j).toGraphWalk.edges :=
    pairwise_disjoint_edges_toGraphWalk hg hone hdisj
  -- The edges underlying the cut arrows separate the terminal sets.
  let C : Finset (Σ x y, G.BidirectedHom x y) := {e | e.1 ∈ S ∧ e.2.1 ∈ Sᶜ}
  refine ⟨k, fun i ↦ a i, fun i ↦ b i, fun i ↦ (P i).toGraphWalk,
    C.image fun e ↦ e.2.2.1, fun i ↦ by simpa [A'] using ha i,
    fun i ↦ by simpa [B'] using hb i,
    fun i ↦ (ArrowWalk.isPath_toGraphWalk_iff _).2 (hP i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i v hv hva hvb
    obtain ⟨hvG, hvQ⟩ := (ArrowWalk.mem_support_toGraphWalk_iff _).1 hv
    have hvint := hint i ⟨v, hvG⟩ hvQ
      (fun h ↦ hva (congrArg Subtype.val h)) (fun h ↦ hvb (congrArg Subtype.val h))
    simpa [A', B'] using hvint
  · exact hPdisj
  · rintro e he
    obtain ⟨a, -, rfl⟩ := mem_image.1 he
    exact a.2.2.2.edge_mem
  · intro x hx y hy hxy
    have hxG : x ∈ V(G) := by simpa using hxy.left_mem
    have hyG : y ∈ V(G) := by simpa using hxy.right_mem
    obtain ⟨-, p, hp⟩ := reachable_deleteEdges_iff_exists_walk.1 hxy
    have hC : ReachableWithout (C : Set (Σ x y, G.BidirectedHom x y))
        (⟨x, hxG⟩ : V(G)) ⟨y, hyG⟩ := reachableWithout_def.2
      ⟨p.toBidirected hxG, fun e he heC ↦ hp e.2.2.1
        (p.edges_toBidirected hxG ▸ List.mem_map_of_mem he)
        (mem_coe.2 (mem_image_of_mem _ heC))⟩
    exact hS.not_reachableWithout_of_cut_subset
      (by intro v w e hv hw; simpa [C] using ⟨hv, hw⟩)
      ⟨x, hxG⟩ (by simpa [A'] using hx) ⟨y, hyG⟩ (by simpa [B'] using hy) hC
  · -- Cut arrows have distinct underlying edges, giving the cardinality equality.
    rw [card_image_of_injOn, ← Nat.cast_inj (R := ℤ), hk, hgval, hval, arrowSum_one]
    rintro e he e' he' h
    simp only [C, coe_filter, mem_univ, true_and, mem_compl, Set.mem_ofPred_eq] at he he'
    exact bidirectedHom_edge_injOn_cut (G := G) (S : Set V(G)) he he' h

/-! ### Edge-disjoint paths between two vertices -/

/-- **Weak duality for edge-disjoint walks.** A family of `s`–`t` walks, from an actual vertex `s`,
of which no two traverse a common edge has at most as many members as any set of edges whose
deletion leaves `s` and `t` unreachable. -/
theorem card_le_encard_of_not_reachable_deleteEdges {ι : Type*} {P : ι → G.Walk s t}
    (hP : Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges) (hs : s ∈ V(G)) {F : Set β}
    (hF : ¬(G.deleteEdges F).Reachable s t) : ENat.card ι ≤ F.encard :=
  card_le_encard_of_forall_not_reachable_deleteEdges (G := G) (A := {s}) (B := {t})
    (a := fun _ ↦ s) (b := fun _ ↦ t) (P := P) (by simp) (by simp) (fun _ ↦ hs) hP (by simpa)

/-- **Menger's theorem for edge-disjoint paths in a multigraph.** For distinct points `s` and `t`
of a multigraph with finitely many actual vertices and edges, some family of `s`–`t` paths, no two
of which traverse a common edge, has as many members as some set of actual edges whose deletion
leaves `s` and `t` unreachable. By `Graph.card_le_encard_of_not_reachable_deleteEdges`, the family
is then largest and the set of edges smallest. -/
theorem exists_paths_edgeSeparator_card_eq [Finite V(G)] [Finite E(G)] (hst : s ≠ t) :
    ∃ (k : ℕ) (P : Fin k → G.Walk s t) (F : Finset β), (∀ i, (P i).IsPath) ∧
      (Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges) ∧ (F : Set β) ⊆ E(G) ∧
      ¬(G.deleteEdges F).Reachable s t ∧ #F = k := by
  have hdisj : Disjoint ({s} : Finset α) {t} := by simpa using hst
  obtain ⟨k, a, b, P, F, ha, hb, hP, -, hdisjP, hFE, hF, hk⟩ :=
    exists_paths_setEdgeSeparator_card_eq (G := G) hdisj
  have ha' : a = fun _ ↦ s := funext fun i ↦ by simpa using ha i
  have hb' : b = fun _ ↦ t := funext fun i ↦ by simpa using hb i
  subst a
  subst b
  exact ⟨k, P, F, hP, hdisjP, hFE, hF s (by simp) t (by simp), hk⟩

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
    · exact ⟨fun _ ↦ .nil, fun _ ↦ by simp, fun _ _ _ ↦ by simp⟩
    obtain ⟨m, P, F, hP, hdisj, -, hF, hFm⟩ := exists_paths_edgeSeparator_card_eq (G := G) hst
    have hkm : k ≤ m := hFm ▸ not_lt.1 fun hlt ↦ hF (isEdgeReachable_def.1 h (by simpa using hlt))
    exact ⟨fun i ↦ P (Fin.castLE hkm i), fun i ↦ hP _,
      hdisj.comp_of_injective (Fin.castLE_injective hkm)⟩
  · by_contra h
    exact hF.not_ge (by simpa using card_le_encard_of_not_reachable_deleteEdges hP hs h)

/-- **Menger's theorem for edge-disjoint paths between vertex sets in a multigraph, predicate
form.** For disjoint finite sets `A` and `B` in a finite multigraph, deleting fewer than `k` edges
always leaves some vertex of `B` reachable from some vertex of `A` exactly when there are `k`
pairwise edge-disjoint `A`–`B` paths with no internal terminal vertex. -/
theorem forall_exists_reachable_deleteEdges_iff_exists_paths [Finite V(G)] [Finite E(G)]
    {A B : Finset α} (hAB : Disjoint A B) (k : ℕ) :
    (∀ F : Finset β, #F < k → ∃ a ∈ A, ∃ b ∈ B, (G.deleteEdges F).Reachable a b) ↔
      ∃ (a b : Fin k → α) (P : ∀ i, G.Walk (a i) (b i)), (∀ i, a i ∈ A) ∧
        (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
        (∀ i, ∀ v ∈ (P i).support, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
        Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges := by
  refine ⟨fun h ↦ ?_, fun ⟨a, b, P, ha, hb, _hPath, _hint, hP⟩ F hF ↦ ?_⟩
  · obtain ⟨m, a, b, P, F, ha, hb, hP, hint, hdisj, -, hsep, hFm⟩ :=
      exists_paths_setEdgeSeparator_card_eq (G := G) hAB
    have hkm : k ≤ m := hFm ▸ not_lt.1 fun hlt ↦
      let ⟨a, ha, b, hb, hab⟩ := h F hlt
      hsep a ha b hb hab
    exact ⟨fun i ↦ a (Fin.castLE hkm i), fun i ↦ b (Fin.castLE hkm i),
      fun i ↦ P (Fin.castLE hkm i), fun i ↦ ha _, fun i ↦ hb _, fun i ↦ hP _,
      fun i ↦ hint _, hdisj.comp_of_injective (Fin.castLE_injective hkm)⟩
  · by_contra h
    push Not at h
    have hstart (i : Fin k) : a i ∈ V(G) := by
      have hab : a i ≠ b i := fun hab ↦ disjoint_left.1 hAB (ha i) (hab ▸ hb i)
      have hpos : 0 < (P i).length := Nat.pos_of_ne_zero fun hzero ↦
        hab ((P i).eq_of_length_eq_zero hzero)
      exact (P i).support_subset_vertexSet_of_pos hpos _ (P i).start_mem_support
    have hle := card_le_encard_of_forall_not_reachable_deleteEdges (G := G)
      (A := (A : Set α)) (B := (B : Set α)) ha hb hstart hP (F := (F : Set β)) h
    exact hF.not_ge (by simpa using hle)

end Graph

/-! ### Simple graphs -/

namespace SimpleGraph

variable {α : Type u} {G : SimpleGraph α} {s t : α}

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

/-! ### Edge-disjoint paths between vertex sets -/

/-- **Weak duality for edge-disjoint set-to-set walks in a simple graph.** A family of walks from
`A` to `B`, of which no two traverse a common edge, has at most as many members as any set of edges
whose deletion leaves no vertex of `B` reachable from a vertex of `A`. -/
theorem card_le_encard_of_forall_not_reachable_deleteEdges {A B : Set α} {ι : Type*}
    {a b : ι → α} {P : ∀ i, G.Walk (a i) (b i)} (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ B)
    (hP : Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges) {F : Set (Sym2 α)}
    (hF : ∀ a ∈ A, ∀ b ∈ B, ¬(G.deleteEdges F).Reachable a b) : ENat.card ι ≤ F.encard :=
  Graph.card_le_encard_of_forall_not_reachable_deleteEdges (G := Graph.ofSimpleGraph G)
    (P := fun i ↦ (P i).toGraph) ha hb (fun _ ↦ Set.mem_univ _) (by simpa using hP)
    (by simpa only [Graph.ofSimpleGraph_deleteEdges, reachable_ofSimpleGraph_iff] using hF)

/-- **Weak duality for edge-disjoint walks in a simple graph.** A family of `s`–`t` walks of which
no two traverse a common edge has at most as many members as any set of edges whose deletion leaves
`s` and `t` unreachable. -/
theorem card_le_encard_of_not_reachable_deleteEdges {ι : Type*} {P : ι → G.Walk s t}
    (hP : Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges) {F : Set (Sym2 α)}
    (hF : ¬(G.deleteEdges F).Reachable s t) : ENat.card ι ≤ F.encard :=
  card_le_encard_of_forall_not_reachable_deleteEdges (G := G) (A := {s}) (B := {t})
    (a := fun _ ↦ s) (b := fun _ ↦ t) (P := P) (by simp) (by simp) hP (by simpa)

/-- **Menger's theorem for edge-disjoint paths between vertex sets in a simple graph.** For
disjoint finite vertex sets `A` and `B` in a finite simple graph, some family of pairwise
edge-disjoint `A`–`B` paths with no internal terminal vertex and some separating edge set have the
same cardinality. Shared endpoints are allowed. -/
theorem exists_paths_setEdgeSeparator_card_eq [Finite α] {A B : Finset α}
    (hAB : Disjoint A B) :
    ∃ (k : ℕ) (a b : Fin k → α) (P : ∀ i, G.Walk (a i) (b i)) (F : Finset (Sym2 α)),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).support, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
      (Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges) ∧ (F : Set (Sym2 α)) ⊆ G.edgeSet ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬(G.deleteEdges F).Reachable a b) ∧ #F = k := by
  have : Finite (Graph.ofSimpleGraph G).vertexSet := Subtype.finite
  have : Finite (Graph.ofSimpleGraph G).edgeSet := Subtype.finite
  obtain ⟨k, a, b, P, F, ha, hb, hP, hint, hdisj, hFE, hF, hk⟩ :=
    Graph.exists_paths_setEdgeSeparator_card_eq (G := Graph.ofSimpleGraph G) hAB
  refine ⟨k, a, b, fun i ↦ (P i).toSimpleGraph, F, ha, hb,
    fun i ↦ (Graph.Walk.isPath_toSimpleGraph_iff _).2 (hP i), ?_,
    by simpa only [Graph.Walk.edges_toSimpleGraph] using hdisj, by simpa using hFE, ?_, hk⟩
  · simpa only [Graph.Walk.support_toSimpleGraph] using hint
  · simpa only [Graph.ofSimpleGraph_deleteEdges, reachable_ofSimpleGraph_iff] using hF

/-- **Menger's theorem for edge-disjoint paths between vertex sets in a simple graph, predicate
form.** For disjoint finite vertex sets `A` and `B` in a finite simple graph, deleting fewer than
`k` edges always leaves an `A`–`B` connection exactly when there are `k` pairwise edge-disjoint
`A`–`B` paths with no internal terminal vertex. -/
theorem forall_exists_reachable_deleteEdges_iff_exists_paths [Finite α] {A B : Finset α}
    (hAB : Disjoint A B) (k : ℕ) :
    (∀ F : Finset (Sym2 α), #F < k → ∃ a ∈ A, ∃ b ∈ B, (G.deleteEdges F).Reachable a b) ↔
      ∃ (a b : Fin k → α) (P : ∀ i, G.Walk (a i) (b i)), (∀ i, a i ∈ A) ∧
        (∀ i, b i ∈ B) ∧ (∀ i, (P i).IsPath) ∧
        (∀ i, ∀ v ∈ (P i).support, v ≠ a i → v ≠ b i → v ∉ A ∧ v ∉ B) ∧
        Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges := by
  have : Finite (Graph.ofSimpleGraph G).vertexSet := Subtype.finite
  have : Finite (Graph.ofSimpleGraph G).edgeSet := Subtype.finite
  have hgraph := Graph.forall_exists_reachable_deleteEdges_iff_exists_paths
    (G := Graph.ofSimpleGraph G) hAB k
  simp only [Graph.ofSimpleGraph_deleteEdges, reachable_ofSimpleGraph_iff] at hgraph
  rw [hgraph]
  refine ⟨fun ⟨a, b, P, ha, hb, hP, hint, hdisj⟩ ↦
    ⟨a, b, fun i ↦ (P i).toSimpleGraph, ha, hb, fun i ↦ ?_, ?_, ?_⟩,
    fun ⟨a, b, P, ha, hb, hP, hint, hdisj⟩ ↦
    ⟨a, b, fun i ↦ (P i).toGraph, ha, hb, fun i ↦ ?_, ?_, ?_⟩⟩
  · exact (Graph.Walk.isPath_toSimpleGraph_iff _).2 (hP i)
  · simpa only [Graph.Walk.support_toSimpleGraph] using hint
  · simpa only [Graph.Walk.edges_toSimpleGraph] using hdisj
  · exact (Walk.isPath_toGraph_iff _).2 (hP i)
  · simpa only [Walk.support_toGraph] using hint
  · simpa only [Walk.edges_toGraph] using hdisj

end SimpleGraph
