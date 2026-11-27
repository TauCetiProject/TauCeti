/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Cliques: vertices lying in them, enumerated cliques and edges

Facts about cliques missing from Mathlib's clique API.

A vertex lies in a triangle exactly when it has two adjacent neighbours, and a copy of a graph
(an injective homomorphism, such as an isomorphism) maps `n`-cliques to `n`-cliques, so that
lying in an `n`-clique is an isomorphism invariant of a vertex. Such invariants let an isomorphism
of graphs be recognised to respect a distinguished set of vertices, for instance the vertices of
gadgets attached to a graph.

The range of an injective family of vertices is a clique exactly when the family is pairwise
adjacent, which turns a statement about a clique enumerated by an index type into one about its
members. On a finite vertex type, the `2`-cliques are the edges: there are as many of them as
edges. Both are used to count the principal minors of an adjacency matrix.

## Main results

* `SimpleGraph.isClique_range_iff_pairwise`: the range of an injective family is a clique exactly
  when its members are pairwise adjacent.
* `SimpleGraph.card_cliqueFinset_two`: a finite graph has as many `2`-cliques as edges.
* `SimpleGraph.exists_isNClique_three_mem_iff`: a vertex lies in a triangle exactly when it has
  two adjacent neighbours.
* `SimpleGraph.IsNClique.map_copy`: a copy of a graph, for instance a graph isomorphism, maps
  `n`-cliques to `n`-cliques.
* `SimpleGraph.Iso.exists_isNClique_mem_iff`: a graph isomorphism maps the vertices lying in an
  `n`-clique to the vertices lying in an `n`-clique.
-/

public section

namespace SimpleGraph

open scoped Finset

variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

/-- A vertex lies in a triangle exactly when it has two adjacent neighbours. -/
theorem exists_isNClique_three_mem_iff {v : V} :
    (∃ s, G.IsNClique 3 s ∧ v ∈ s) ↔ ∃ a b, G.Adj v a ∧ G.Adj v b ∧ G.Adj a b := by
  classical
  constructor
  · rintro ⟨s, hs, hv⟩
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.1 hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨b, c, hab, hac, hbc⟩
    · exact ⟨a, c, hab.symm, hbc, hac⟩
    · exact ⟨a, b, hac.symm, hbc.symm, hab⟩
  · rintro ⟨a, b, ha, hb, hab⟩
    exact ⟨{v, a, b}, is3Clique_triple_iff.2 ⟨ha, hb, hab⟩, Finset.mem_insert_self _ _⟩

/-- A copy of `G` in `G'`, that is an injective graph homomorphism, maps `n`-cliques to
`n`-cliques. -/
theorem IsNClique.map_copy {n : ℕ} {s : Finset V} (hs : G.IsNClique n s) (f : Copy G G') :
    G'.IsNClique n (s.map f.toEmbedding) := by
  refine ⟨?_, by simp [hs.card_eq]⟩
  rw [Finset.coe_map]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
  exact f.toHom.map_adj (hs.isClique ha hb (ne_of_apply_ne _ hab))

/-- A graph isomorphism maps the vertices lying in an `n`-clique to the vertices lying in an
`n`-clique. -/
theorem Iso.exists_isNClique_mem_iff (ψ : G ≃g G') {n : ℕ} {v : V} :
    (∃ s, G'.IsNClique n s ∧ ψ v ∈ s) ↔ ∃ s, G.IsNClique n s ∧ v ∈ s :=
  ⟨fun ⟨_, hs, hv⟩ ↦
      ⟨_, hs.map_copy ψ.symm.toCopy, Finset.mem_map.2 ⟨_, hv, ψ.symm_apply_apply v⟩⟩,
    fun ⟨_, hs, hv⟩ ↦ ⟨_, hs.map_copy ψ.toCopy, Finset.mem_map_of_mem _ hv⟩⟩

/-- The range of an injective family of vertices is a clique exactly when the members of the
family are pairwise adjacent. -/
theorem isClique_range_iff_pairwise {ι : Type*} {f : ι → V} (hf : Function.Injective f) :
    G.IsClique (Set.range f) ↔ Pairwise fun i j ↦ G.Adj (f i) (f j) := by
  rw [← Set.image_univ, isClique_iff, hf.injOn.pairwise_image, Set.pairwise_univ]

/-- A finite graph has as many `2`-cliques as edges: an edge `s(a, b)` corresponds to the
`2`-clique `{a, b}`. -/
theorem card_cliqueFinset_two [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    #(G.cliqueFinset 2) = #G.edgeFinset := by
  symm
  refine Finset.card_bij (fun e _ ↦ e.toFinset) (fun e he ↦ ?_)
    (fun e₁ _ e₂ _ h ↦ Sym2.ext fun a ↦ by rw [← Sym2.mem_toFinset, h, Sym2.mem_toFinset])
    (fun s hs ↦ ?_)
  · induction e using Sym2.ind with | h x y =>
    rw [mem_edgeFinset, mem_edgeSet] at he
    rw [Sym2.toFinset_mk_eq, mem_cliqueFinset_iff, isNClique_iff, Finset.coe_pair, isClique_pair,
      Finset.card_pair he.ne]
    exact ⟨fun _ ↦ he, rfl⟩
  · rw [mem_cliqueFinset_iff, isNClique_iff] at hs
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hs.2
    rw [Finset.coe_pair, isClique_pair] at hs
    exact ⟨s(a, b), by simpa using hs.1 hab, Sym2.toFinset_mk_eq⟩

end SimpleGraph
