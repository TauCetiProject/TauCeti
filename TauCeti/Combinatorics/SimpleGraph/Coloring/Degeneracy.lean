/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

import Mathlib.Combinatorics.SimpleGraph.Finsubgraph

/-!
# Colouring graphs of bounded degeneracy

The Szekeres–Wilf deletion argument colours a graph with `k + 1` colours whenever every
nonempty finite set of vertices contains a vertex with at most `k` neighbours in that set.
In particular, a finite graph admits a colouring with one more colour than its maximum degree.

See Bondy–Murty, *Graph Theory with Applications*, Exercise 8.1.5 and Corollary 8.1.2,
and Diestel, *Graph Theory*, Proposition 5.2.2.
Mathlib's compactness theorem `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`
extends the finite colouring argument to arbitrary vertex types.
-/

public section

open Finset

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}

private theorem exists_partial_coloring_of_forall_exists_card_le
    (h : ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, #{w ∈ s | G.Adj v w} ≤ k)
    (s : Finset V) :
    ∃ f : V → Fin (k + 1), ∀ ⦃v w⦄, v ∈ s → w ∈ s → G.Adj v w → f v ≠ f w := by
  classical
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hs : s.Nonempty
  · obtain ⟨v, hv, hdegree⟩ := h s hs
    obtain ⟨f, hf⟩ := ih (s.erase v) (Finset.erase_ssubset hv)
    have hcard : #(({w ∈ s | G.Adj v w}).image f) < #(Finset.univ : Finset (Fin (k + 1))) := by
      simpa using (Finset.card_image_le.trans hdegree).trans_lt (Nat.lt_succ_self k)
    obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hcf : ∀ w ∈ s, G.Adj v w → c ≠ f w := by
      intro w hw hadj heq
      exact hc (Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hadj⟩, heq.symm⟩)
    refine ⟨fun w ↦ if w = v then c else f w, ?_⟩
    intro a b ha hb hab
    by_cases hav : a = v
    · subst a
      have hbne : b ≠ v := hab.ne.symm
      simpa [hbne] using hcf b hb hab
    · by_cases hbv : b = v
      · subst b
        simpa [hav] using (hcf a ha hab.symm).symm
      · simpa [hav, hbv] using
          hf (Finset.mem_erase.mpr ⟨hav, ha⟩) (Finset.mem_erase.mpr ⟨hbv, hb⟩) hab
  · exact ⟨fun _ ↦ 0, fun _ _ hv ↦ (hs ⟨_, hv⟩).elim⟩

variable {G} in
/-- The Szekeres–Wilf bound: if every nonempty finite vertex set contains a vertex with at most
`k` neighbours in that set, then the graph is colourable with `k + 1` colours. -/
theorem colorable_succ_of_forall_exists_card_le
    (h : ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, #{w ∈ s | G.Adj v w} ≤ k) :
    G.Colorable (k + 1) := by
  classical
  apply nonempty_hom_of_forall_finite_subgraph_hom
  intro H hH
  let hex := G.exists_partial_coloring_of_forall_exists_card_le h hH.toFinset
  let f := Classical.choose hex
  have hf := Classical.choose_spec hex
  exact Coloring.mk (fun v ↦ f v) fun {v w} hvw ↦
    hf (hH.mem_toFinset.mpr v.property) (hH.mem_toFinset.mpr w.property)
      (H.coe_adj_sub v w hvw)

/-- A finite simple graph is colourable with one more colour than its maximum degree. -/
theorem colorable_maxDegree_add_one [Fintype V] : G.Colorable (G.maxDegree + 1) := by
  apply colorable_succ_of_forall_exists_card_le
  intro s hs
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, ?_⟩
  calc
    _ ≤ #(G.neighborFinset v) := Finset.card_le_card fun w hw ↦
      (G.mem_neighborFinset v w).mpr (Finset.mem_filter.mp hw).2
    _ = G.degree v := G.card_neighborFinset_eq_degree v
    _ ≤ G.maxDegree := G.degree_le_maxDegree v

end SimpleGraph
