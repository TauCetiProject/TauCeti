/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import TauCeti.Combinatorics.SimpleGraph.Finite
import TauCeti.Order.Hom.PowersetCard

/-!
# Triples spanning an odd number of edges

For a graph `G` on a finite vertex type, `G.oddTripleFinset` is the set of three-element
vertex sets spanning an odd number of edges of `G`. Reading `G` as a binary one-cochain on the
full simplex on its vertices, these are the two-dimensional faces of the simplex on which the
coboundary is nonzero, so its cardinality is the size of the coboundary of `G`. They need not
be triangles of `G` in the sense of `G.cliqueFinset 3`: a triple spanning a single edge is odd.

## Main definitions and results

* `SimpleGraph.oddTripleFinset`, `SimpleGraph.oddTripleFinset_def`: the `3`-element vertex subsets
  spanning an odd number of edges of `G`.
* `SimpleGraph.mem_oddTripleFinset`, `SimpleGraph.triple_mem_oddTripleFinset_iff`,
  `SimpleGraph.mem_oddTripleFinset_iff_induce`: membership characterizations.
* `SimpleGraph.oddTripleFinset_bot`: the empty graph has no odd triples.
* `SimpleGraph.Iso.map_oddTripleFinset`, `SimpleGraph.Iso.card_oddTripleFinset_eq`:
  invariance under graph isomorphism.
* `SimpleGraph.mem_oddTripleFinset_iff_of_cliqueFree`: in a `3`-clique-free graph, an odd triple
  is a `3`-element vertex set spanning a single edge.
* `SimpleGraph.card_oddTripleFinset_eq_card_filter_lt`, `SimpleGraph.card_oddTripleFinset_eq_sum`:
  over a linear order, odd triples are counted by strictly increasing triples `u < v < w`.
-/

public section

open Finset

namespace SimpleGraph

variable {V W : Type*}

section Basic

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The three-element vertex sets spanning an odd number of edges of `G`. -/
def oddTripleFinset : Finset (Finset V) :=
  {t ∈ univ.powersetCard 3 | Odd #(G.edgeFinset ∩ t.sym2)}

/-- Characterization of `G.oddTripleFinset` as the `3`-element subsets of `univ` spanning an odd
number of edges of `G`. -/
theorem oddTripleFinset_def :
    G.oddTripleFinset = {t ∈ (univ : Finset V).powersetCard 3 | Odd #(G.edgeFinset ∩ t.sym2)} :=
  (rfl)

variable {G}

/-- A set of vertices is an odd triple when it has three elements spanning an odd number of
edges. -/
@[simp, grind =]
theorem mem_oddTripleFinset {t : Finset V} :
    t ∈ G.oddTripleFinset ↔ #t = 3 ∧ Odd #(G.edgeFinset ∩ t.sym2) := by
  simp [oddTripleFinset]

/-- Three vertices span an odd number of edges exactly when an odd number of the three pairs
are adjacent. If two of the vertices coincide, both sides are false. -/
@[simp 1100, grind =]
theorem triple_mem_oddTripleFinset_iff {a b c : V} :
    {a, b, c} ∈ G.oddTripleFinset ↔ Xor (G.Adj a b) (Xor (G.Adj a c) (G.Adj b c)) := by
  by_cases h : a ≠ b ∧ a ≠ c ∧ b ≠ c
  · obtain ⟨hab, hac, hbc⟩ := h
    rw [mem_oddTripleFinset, card_edgeFinset_inter_sym2_triple hab hac hbc]
    have h3 : #({a, b, c} : Finset V) = 3 := card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
    by_cases h₁ : G.Adj a b <;> by_cases h₂ : G.Adj a c <;> by_cases h₃ : G.Adj b c <;>
      simp [h₁, h₂, h₃, h3, xor_def, Nat.odd_iff]
  · simp only [not_and_or, not_not] at h
    have hlt : #({a, b, c} : Finset V) < 3 := by
      rcases h with rfl | rfl | rfl
      · rw [card_insert_of_mem (by simp)]
        exact card_le_two.trans_lt (by omega)
      · rw [card_insert_of_mem (by simp)]
        exact card_le_two.trans_lt (by omega)
      · rw [insert_eq_of_mem (mem_singleton_self b)]
        exact card_le_two.trans_lt (by omega)
    rw [mem_oddTripleFinset, iff_false_intro fun h3 : _ ∧ _ ↦ hlt.ne h3.1]
    rcases h with rfl | rfl | rfl <;> simp [G.adj_comm, xor_def]

/-- Membership in `G.oddTripleFinset` in terms of the induced subgraph on `s`. -/
theorem mem_oddTripleFinset_iff_induce {s : Finset V} :
    s ∈ G.oddTripleFinset ↔ #s = 3 ∧ Odd #(G.induce (s : Set V)).edgeFinset := by
  rw [mem_oddTripleFinset, ← filter_edgeFinset_toFinset_subset,
    card_filter_edgeFinset_toFinset_subset]

/-- The empty graph has no odd triples. -/
@[simp]
theorem oddTripleFinset_bot : (⊥ : SimpleGraph V).oddTripleFinset = ∅ := by
  ext s
  simp only [mem_oddTripleFinset, notMem_empty, iff_false, not_and, Nat.not_odd_iff_even]
  intro _
  rw [card_eq_zero.mpr (by ext; simp)]
  simp

/-- In a `3`-clique-free graph, a vertex subset belongs to `G.oddTripleFinset` iff it has
`3` vertices and spans a single edge of `G`. -/
theorem mem_oddTripleFinset_iff_of_cliqueFree (hG : G.CliqueFree 3) {s : Finset V} :
    s ∈ G.oddTripleFinset ↔ #s = 3 ∧ #(G.edgeFinset ∩ s.sym2) = 1 := by
  rw [mem_oddTripleFinset]
  refine and_congr_right fun hs3 ↦ ⟨fun hodd ↦ ?_, fun h1 ↦ h1 ▸ odd_one⟩
  obtain ⟨a, b, c, -, -, -, rfl⟩ := card_eq_three.mp hs3
  have hsub := G.edgeFinset_inter_sym2_triple_subset a b c
  have hcard_pairs : #({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 V)) ≤ 3 :=
    (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))
  have hle3 : #(G.edgeFinset ∩ ({a, b, c} : Finset V).sym2) ≤ 3 :=
    (card_le_card hsub).trans hcard_pairs
  obtain ⟨k, hk⟩ := hodd
  have hk1 : k ≤ 1 := by omega
  rcases Nat.eq_or_lt_of_le hk1 with rfl | hk0
  · exfalso
    have heq := eq_of_subset_of_card_le hsub (hk ▸ hcard_pairs)
    have mem_of (e : Sym2 V) (he : e ∈ ({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 V))) :
        e ∈ G.edgeSet := by
      rw [← mem_edgeFinset]
      exact (mem_inter.mp (heq ▸ he)).1
    exact hG {a, b, c} (is3Clique_triple_iff.mpr
      ⟨mem_of s(a, b) (by simp), mem_of s(a, c) (by simp), mem_of s(b, c) (by simp)⟩)
  · omega

end Basic

section Iso

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- Graph isomorphisms transport `oddTripleFinset` by mapping each `3`-element vertex subset. -/
theorem Iso.map_oddTripleFinset (f : G ≃g H) :
    G.oddTripleFinset.map (mapEmbedding f.toEquiv.toEmbedding).toEmbedding =
      H.oddTripleFinset := by
  have hmap : G.map f.toEquiv.toEmbedding = H := by
    ext u v
    obtain ⟨x, rfl⟩ := f.surjective u
    obtain ⟨y, rfl⟩ := f.surjective v
    rw [map_adj]
    simp [f.apply_eq_iff_eq, f.map_adj_iff]
  have hedge : H.edgeFinset = G.edgeFinset.map f.toEquiv.toEmbedding.sym2Map := by
    rw [← edgeFinset_inj.mpr hmap, edgeFinset_map]
  have hcard (s : Finset V) :
      #(H.edgeFinset ∩ (s.map f.toEquiv.toEmbedding).sym2) = #(G.edgeFinset ∩ s.sym2) := by
    rw [hedge, sym2_map, ← map_inter, card_map]
  have huniv : (univ : Finset V).map f.toEquiv.toEmbedding = univ := by
    ext w
    obtain ⟨x, rfl⟩ := f.surjective w
    simp
  ext t
  simp only [mem_map, mem_oddTripleFinset, RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
  constructor
  · rintro ⟨s, ⟨hs3, hodd⟩, rfl⟩
    rwa [card_map, and_iff_right hs3, hcard]
  · rintro ⟨ht3, hodd⟩
    have htsub : t ∈ ((univ : Finset V).map f.toEquiv.toEmbedding).powersetCard 3 := by
      rw [huniv, mem_powersetCard]
      exact ⟨subset_univ _, ht3⟩
    rw [powersetCard_map, mem_map] at htsub
    obtain ⟨s, hs, rfl⟩ := htsub
    rw [mem_powersetCard] at hs
    rw [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, hcard] at hodd
    exact ⟨s, ⟨hs.2, hodd⟩, by rw [RelEmbedding.coe_toEmbedding, mapEmbedding_apply]⟩

/-- Isomorphic finite graphs have the same number of odd triples. -/
theorem Iso.card_oddTripleFinset_eq (f : G ≃g H) :
    #G.oddTripleFinset = #H.oddTripleFinset := by
  rw [← f.map_oddTripleFinset, card_map]

end Iso

section Order

variable [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- On a finite linearly ordered vertex type, `#G.oddTripleFinset` counts the strictly increasing
vertex triples `(u, v, w)` around which an odd number of pairs are adjacent in `G`. -/
theorem card_oddTripleFinset_eq_card_filter_lt :
    #G.oddTripleFinset =
      #{p : V × V × V | p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
        Xor (G.Adj p.1 p.2.1) (Xor (G.Adj p.2.1 p.2.2) (G.Adj p.2.2 p.1))} := by
  symm
  refine card_bij (fun p _ ↦ ({p.1, p.2.1, p.2.2} : Finset V)) ?_ ?_ ?_
  · rintro ⟨u, v, w⟩ hp
    obtain ⟨-, -, hxor⟩ := (mem_filter.mp hp).2
    rw [triple_mem_oddTripleFinset_iff, G.adj_comm u w, xor_comm (G.Adj w u)]
    exact hxor
  · rintro ⟨u₁, v₁, w₁⟩ hp₁ ⟨u₂, v₂, w₂⟩ hp₂ htri
    obtain ⟨huv₁, hvw₁, -⟩ := (mem_filter.mp hp₁).2
    obtain ⟨huv₂, hvw₂, -⟩ := (mem_filter.mp hp₂).2
    exact Set.powersetCard.eq_of_lt_lt_triple_eq huv₁ hvw₁ huv₂ hvw₂ htri
  · intro s hs
    obtain ⟨hs3, -⟩ := mem_oddTripleFinset.mp hs
    obtain ⟨u, v, w, huv, hvw, rfl⟩ := Set.powersetCard.exists_lt_lt_val_eq ⟨s, hs3⟩
    refine ⟨(u, v, w), mem_filter.mpr ⟨mem_univ _, huv, hvw, ?_⟩, rfl⟩
    have hxor := triple_mem_oddTripleFinset_iff.mp hs
    rwa [G.adj_comm u w, xor_comm (G.Adj w u)] at hxor

/-- Over a linear order, the odd triples are counted by their increasing triples `u < v < w`:
each odd triple is `{u, v, w}` for exactly one such triple. -/
theorem card_oddTripleFinset_eq_sum :
    #G.oddTripleFinset = ∑ u : V, ∑ v : V, ∑ w : V,
      if u < v ∧ v < w ∧ Xor (G.Adj u v) (Xor (G.Adj u w) (G.Adj v w)) then 1 else 0 := by
  rw [card_oddTripleFinset_eq_card_filter_lt, card_filter]
  simp_rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ ↦ sum_congr rfl fun v _ ↦ sum_congr rfl fun w _ ↦ ?_
  simp only [G.adj_comm w u, xor_comm (G.Adj v w)]

end Order

end SimpleGraph
