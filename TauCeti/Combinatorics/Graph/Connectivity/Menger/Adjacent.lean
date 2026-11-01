/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Menger.Vertex
import TauCeti.Combinatorics.Graph.Connectivity.Walk.Decomposition
import TauCeti.Combinatorics.Network.Menger.Adjacent

/-!
# Menger's theorem for adjacent vertices in multigraphs

Let `G : Graph α β` be a multigraph and let `s ≠ t` be actual vertices.  The local vertex form
of Menger's theorem does not apply directly when an edge joins `s` and `t`, because deleting
vertices other than the terminals cannot destroy that one-edge path.  This file counts those
direct edge identities separately.

If `D = {e | G.IsLink e s t}` is finite, then after deleting `D` some set `X` of `k` actual
vertices separates `s` from `t`, while the original graph has `k + |D|` distinct internally
vertex-disjoint paths.  The family contains the one-edge path of every `e ∈ D`; parallel edges
therefore contribute separately.  Weak duality bounds every internally disjoint path family by
`|X| + |D|` for every such separator.

The attainment theorem is transported from the directed adjacent-terminal theorem for the
bidirected arrow family.  A directed arrow from `s` to `t` is exactly an edge identity in `D`, and
the walk equivalence preserves paths and internal disjointness.

## Main results

* `Graph.card_le_card_add_card_of_not_reachable_deleteEdges_deleteVerts`: weak duality.
* `Graph.exists_paths_vertexSeparator_card_add_card_eq`: adjacent-terminal Menger in witness form.
* `Graph.forall_reachable_deleteEdges_deleteVerts_iff_exists_paths`: the predicate form.

## References

* K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Section 9.1.
-/

public section

open Finset TauCeti

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {s t : α}

private theorem not_reachable_deleteEdges_deleteVerts_of_isMixedSeparator
    [Fintype {e : β // G.IsLink e s t}] (hs : s ∈ V(G)) (ht : t ∈ V(G))
    {X : Finset V(G)}
    (hX : IsMixedSeparator X (arrowFinset G.BidirectedHom ⟨s, hs⟩ ⟨t, ht⟩) ⟨s, hs⟩
      ⟨t, ht⟩) :
    ¬((G.deleteEdges {e | G.IsLink e s t}).deleteVerts
      (X.map (Function.Embedding.subtype _) : Set α)).Reachable s t := by
  intro h
  obtain ⟨q, -, hqX⟩ := reachable_deleteVerts_iff_exists_walk.1 h
  let p : G.Walk s t := q.mapLe G.deleteEdges_le
  rcases hX.exists_mem (p.toBidirected hs) with ⟨x, hx, hxX⟩ | ⟨a, ha, haD⟩
  · have hxp : x.1 ∈ p.support := by
      rw [← Walk.vertices_toBidirected p hs]
      exact List.mem_unattach.2 ⟨x.2, hx⟩
    have hxq : x.1 ∈ q.support := by simpa [p] using hxp
    exact hqX x.1 hxq (by simpa using hxX)
  · have hea : a.2.2.1 ∈ p.edges := by
      rw [← Walk.edges_toBidirected p hs]
      exact List.mem_map_of_mem ha
    have heq : a.2.2.1 ∈ q.edges := by simpa [p] using hea
    have heG := q.edges_subset_edgeSet heq
    rw [edgeSet_deleteEdges] at heG
    exact heG.2 (by
      obtain ⟨hsource, htarget⟩ := mem_arrowFinset.1 haD
      simpa [hsource, htarget] using a.2.2.2)

/-! ### Weak duality -/

/-- **Weak duality for internally vertex-disjoint paths between possibly adjacent vertices.**
Let `X` be a finite set of points avoiding `s` and `t`.  If deleting `X` and every edge
joining `s` to `t` separates the terminals, then a finite family of distinct internally disjoint
`s`–`t` paths has at most `#X` plus the number of direct edge identities members. -/
theorem card_le_card_add_card_of_not_reachable_deleteEdges_deleteVerts
    [Fintype {e : β // G.IsLink e s t}] {I : Type*} [Fintype I] {P : I → G.Walk s t}
    (hinj : Function.Injective P) (hP : ∀ i, (P i).IsPath)
    (hdisj : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) (hs : s ∈ V(G))
    {X : Finset α} (hsX : s ∉ X) (htX : t ∉ X)
    (hX : ¬((G.deleteEdges {e | G.IsLink e s t}).deleteVerts
      (X : Set α)).Reachable s t) :
    Fintype.card I ≤ #X + Fintype.card {e : β // G.IsLink e s t} := by
  classical
  let avoidsDirect (i : I) : Prop := ∀ e ∈ (P i).edges, ¬G.IsLink e s t
  have havoid : Fintype.card {i // avoidsDirect i} ≤ #X := by
    let Q (i : {i // avoidsDirect i}) : (G.deleteEdges {e | G.IsLink e s t}).Walk s t :=
      (P i.1).transfer G.deleteEdges_le fun e he ↦ by
        rw [edgeSet_deleteEdges]
        exact ⟨(P i.1).edges_subset_edgeSet he, i.2 e he⟩
    have hle := card_le_encard_of_not_reachable_deleteVerts
      (G := G.deleteEdges {e | G.IsLink e s t}) (P := Q)
      (fun i j hij ↦ by
        simpa [Q, Walk.internallyDisjoint_def] using
          hdisj (fun h ↦ hij (Subtype.ext h)))
      (by simpa using hs) hsX htX hX
    rw [ENat.card_eq_coe_fintype_card, Set.encard_coe_eq_coe_finsetCard, Nat.cast_le] at hle
    exact hle
  have hdirect : Fintype.card {i // ¬avoidsDirect i} ≤
      Fintype.card {e : β // G.IsLink e s t} := by
    have hex (i : {i // ¬avoidsDirect i}) :
        ∃ e, e ∈ (P i.1).edges ∧ G.IsLink e s t := by
      simpa [avoidsDirect] using i.2
    choose e he hlink using hex
    let f (i : {i // ¬avoidsDirect i}) : {e : β // G.IsLink e s t} := ⟨e i, hlink i⟩
    refine Fintype.card_le_of_injective f fun i j hij ↦ ?_
    have hwalk : (hlink i).toWalk = (hlink j).toWalk :=
      congrArg (fun z : {e : β // G.IsLink e s t} ↦ z.2.toWalk) hij
    apply Subtype.ext
    apply hinj
    exact ((hP i).eq_toWalk_of_isLink_mem_edges (hlink i) (he i)).trans
      (hwalk.trans ((hP j).eq_toWalk_of_isLink_mem_edges (hlink j) (he j)).symm)
  rw [Fintype.card_congr (Equiv.sumCompl avoidsDirect).symm, Fintype.card_sum]
  omega

/-! ### Attainment -/

/-- **Menger's theorem for internally vertex-disjoint paths between possibly adjacent vertices.**
Let `s ≠ t` be actual vertices of a multigraph with finitely many actual vertices and finitely
many edges joining the terminals.  For some `k`, there are distinct internally disjoint paths
indexed by `Fin k ⊕ {e // G.IsLink e s t}`.  The path indexed by a direct edge is that one-edge
path.  There is also a set `X` of `k` actual vertices such that deleting `X` and all direct edges
separates `s` from `t`. -/
theorem exists_paths_vertexSeparator_card_add_card_eq [Finite V(G)]
    [Finite {e : β // G.IsLink e s t}] (hst : s ≠ t) (hs : s ∈ V(G)) (ht : t ∈ V(G)) :
    ∃ (k : ℕ) (P : Fin k ⊕ {e : β // G.IsLink e s t} → G.Walk s t) (X : Finset α),
      Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
      (Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) ∧
      (∀ e, P (.inr e) = e.2.toWalk) ∧ (X : Set α) ⊆ V(G) ∧ s ∉ X ∧ t ∉ X ∧
      ¬((G.deleteEdges {e | G.IsLink e s t}).deleteVerts
        (X : Set α)).Reachable s t ∧ #X = k := by
  let _ := Fintype.ofFinite {e : β // G.IsLink e s t}
  obtain ⟨k, P, X, hinj, hP, hdisj, hdirect, hX, hk⟩ :=
    TauCeti.exists_paths_isMixedSeparator_card_eq
      (Q := G.BidirectedHom) (s := ⟨s, hs⟩) (t := ⟨t, ht⟩)
      (fun h ↦ hst (congrArg Subtype.val h))
  refine ⟨k, fun i ↦ (P i).toGraphWalk, X.map (Function.Embedding.subtype _),
    ArrowWalk.toGraphWalk_injective.comp hinj,
    fun i ↦ (P i).isPath_toGraphWalk_iff.2 (hP i),
    fun i j hij ↦ by simpa using hdisj hij, ?_, map_subtype_subset X,
    (by
      intro hsmem
      obtain ⟨x, hx, hxs⟩ := mem_map.1 hsmem
      change x.1 = s at hxs
      have hxsub : x = ⟨s, hs⟩ := Subtype.ext hxs
      exact hX.source_notMem (hxsub ▸ hx)), (by
      intro htmem
      obtain ⟨x, hx, hxt⟩ := mem_map.1 htmem
      change x.1 = t at hxt
      have hxsub : x = ⟨t, ht⟩ := Subtype.ext hxt
      exact hX.target_notMem (hxsub ▸ hx)),
    not_reachable_deleteEdges_deleteVerts_of_isMixedSeparator hs ht hX, by simpa using hk⟩
  intro e
  have he := congrArg ArrowWalk.toGraphWalk (hdirect e)
  simpa using he

/-- **Menger's theorem for adjacent vertices, predicate form.** For distinct actual vertices,
after deleting every direct edge, every set of fewer than `k` nonterminal points leaves
the terminals reachable exactly when there are distinct internally disjoint paths indexed by
`Fin k ⊕ {e // G.IsLink e s t}`. -/
theorem forall_reachable_deleteEdges_deleteVerts_iff_exists_paths [Finite V(G)]
    [Finite {e : β // G.IsLink e s t}] (hst : s ≠ t) (hs : s ∈ V(G)) (ht : t ∈ V(G))
    (k : ℕ) :
    (∀ X : Finset α, s ∉ X → t ∉ X → #X < k →
      ((G.deleteEdges {e | G.IsLink e s t}).deleteVerts
        (X : Set α)).Reachable s t) ↔
      ∃ P : Fin k ⊕ {e : β // G.IsLink e s t} → G.Walk s t, Function.Injective P ∧
        (∀ i, (P i).IsPath) ∧ Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) := by
  let _ := Fintype.ofFinite {e : β // G.IsLink e s t}
  refine ⟨fun h ↦ ?_, fun ⟨P, hinj, hP, hdisj⟩ X hsX htX hX ↦ ?_⟩
  · obtain ⟨m, P, X, hinj, hP, hdisj, -, -, hsX, htX, hX, rfl⟩ :=
      exists_paths_vertexSeparator_card_add_card_eq hst hs ht
    have hkm : k ≤ #X := not_lt.1 fun hlt ↦ hX (h X hsX htX hlt)
    have hf : Function.Injective
        (Sum.map (Fin.castLE hkm) (id : {e : β // G.IsLink e s t} → _)) :=
      Sum.map_injective.2 ⟨Fin.castLE_injective hkm, Function.injective_id⟩
    exact ⟨P ∘ Sum.map (Fin.castLE hkm) id, hinj.comp hf, fun i ↦ hP _,
      hdisj.comp_of_injective hf⟩
  · by_contra hreach
    have hle := card_le_card_add_card_of_not_reachable_deleteEdges_deleteVerts
      hinj hP hdisj hs hsX htX hreach
    simp only [Fintype.card_sum, Fintype.card_fin] at hle
    omega

end Graph
