/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Vertices lying in cliques

Two facts about the vertices of a graph that lie in a clique, missing from Mathlib's clique API.
A vertex lies in a triangle exactly when it has two adjacent neighbours, and a copy of a graph
(an injective homomorphism, such as an isomorphism) maps `n`-cliques to `n`-cliques, so that
lying in an `n`-clique is an isomorphism invariant of a vertex. Such invariants let an isomorphism
of graphs be recognised to respect a distinguished set of vertices, for instance the vertices of
gadgets attached to a graph.

## Main results

* `SimpleGraph.exists_isNClique_three_mem_iff`: a vertex lies in a triangle exactly when it has
  two adjacent neighbours.
* `SimpleGraph.IsNClique.map_copy`: a copy of a graph, for instance a graph isomorphism, maps
  `n`-cliques to `n`-cliques.
* `SimpleGraph.Iso.exists_isNClique_mem_iff`: a graph isomorphism maps the vertices lying in an
  `n`-clique to the vertices lying in an `n`-clique.
-/

public section

namespace SimpleGraph

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

end SimpleGraph
