/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.AffineSubgraph

/-!
# Recognition of the affine simply-laced diagrams

A connected finite simple graph `G` carries a nonzero weight `a : V → ℕ` with
`∑_{j ∼ i} a j = 2 * a i` at every vertex, that is a nonzero nonnegative integral null vector of
`2I - A`, exactly when `G` is isomorphic to the graph of a valid affine simply-laced diagram other
than `Ã₁`; that diagram is then unique. The possible graphs are therefore the cycles `Ãₙ` with
`n ≥ 2`, affine `Dₙ` with `n ≥ 4`, and affine `E₆`, `E₇` and `E₈`.

The marks of an affine diagram are such a weight on its graph. Conversely, a nonzero null vector
prevents `2I - A` from being positive definite, so `G` is not a Dynkin diagram and contains a copy
of the graph of an affine diagram
(`SimpleGraph.Connected.exists_isContained_affineDynkinType_of_not_exists_dynkinType_iso`). Since
the marks of that diagram are a positive additive function, the proper-extension obstruction
`SimpleGraph.Copy.exists_iso_of_sum_le_two_mul` forces the copy to be all of `G`. The diagram is
unique because the graphs of distinct valid diagrams are already told apart by their numbers of
nodes, of leaves and of trivalent nodes.

Away from `Ã₁` this is Kac's characterisation of the connected affine diagrams by a positive null
vector, read on simple graphs; the double edge of `Ã₁` is not a simple-graph edge, so `Ã₁` is not
recognised here.

## Main results

* `TauCeti.AffineDynkinType.eq_of_graph_iso`: valid affine diagrams with isomorphic graphs are
  equal.
* `SimpleGraph.Connected.exists_sum_eq_two_mul_iff_existsUnique_affineDynkinType_iso`: **the
  recognition theorem**.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 4, Theorem 4.3 and Table Aff 1.
* P. Etingof et al., *Introduction to representation theory*, Problem 5.3, for the semidefinite
  form of the classification.
-/

public section

namespace TauCeti.AffineDynkinType

open Finset SimpleGraph

/-- A cycle `Ãₙ` with `n ≥ 2` has no leaf. -/
private lemma card_filter_degree_A_eq_zero {n : ℕ} (hn : 2 ≤ n) :
    #{v | (A n).graph.degree v = 1} = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e : (A (m + 2)).graph ≃g cycleGraph (m + 3) := by rw [graph_A]; exact .refl
  refine card_eq_zero.2 (filter_eq_empty_iff.2 fun v _ ↦ ?_)
  rw [← e.degree_eq v, cycleGraph_degree_three_le]
  omega

/-- Node `0` is a leaf of affine `Dₙ`, attached to node `1`. -/
private lemma card_filter_degree_D_pos {n : ℕ} (hn : 4 ≤ n) :
    0 < #{v | (D n).graph.degree v = 1} := by
  refine card_pos.2 ⟨0, mem_filter.2 ⟨mem_univ _, degree_eq_one_iff_existsUnique_adj.2 ?_⟩⟩
  refine ⟨⟨1, by simp; omega⟩, (graph_D_adj hn).2 (by simp; omega), fun j hj ↦ ?_⟩
  replace hj := (graph_D_adj hn).1 hj
  ext
  simp only [Fin.val_zero] at hj ⊢
  omega

/-- Affine `D₆`, `D₇` and `D₈` have two trivalent nodes. -/
private lemma card_filter_degree_D_eq_two {n : ℕ} (hn : n = 6 ∨ n = 7 ∨ n = 8) :
    #{v | (D n).graph.degree v = 3} = 2 := by
  -- `graph_D_adj` is stated on `Fin (n + 1)`; this restatement on `Fin (D n).nodes` lets `simp`
  -- match the adjacency in the goal.
  have h (i j : Fin (D n).nodes) := graph_D_adj (n := n) (i := i) (j := j) (by omega)
  simp only [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, h]
  rcases hn with rfl | rfl | rfl <;> decide

/-- Affine `E₆` has three leaves and one trivalent node. -/
private lemma card_filter_degree_E6 :
    #{v | E6.graph.degree v = 1} = 3 ∧ #{v | E6.graph.degree v = 3} = 1 := by
  simp only [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, graph_E6_adj]
  decide

/-- Affine `E₇` has three leaves and one trivalent node. -/
private lemma card_filter_degree_E7 :
    #{v | E7.graph.degree v = 1} = 3 ∧ #{v | E7.graph.degree v = 3} = 1 := by
  simp only [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, graph_E7_adj]
  decide

/-- Affine `E₈` has three leaves and one trivalent node. -/
private lemma card_filter_degree_E8 :
    #{v | E8.graph.degree v = 1} = 3 ∧ #{v | E8.graph.degree v = 3} = 1 := by
  simp only [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, graph_E8_adj]
  decide

/-- **The graph determines a valid affine diagram.** If two valid affine simply-laced diagrams
have isomorphic graphs, they are equal. This includes `Ã₁`, the only valid diagram on two nodes,
although its graph forgets its double edge. Validity is needed: the degenerate `A 0` and `D 0`
both have a single node. -/
theorem eq_of_graph_iso {t t' : AffineDynkinType} (ht : t.Valid) (ht' : t'.Valid)
    (e : t.graph ≃g t'.graph) : t = t' := by
  -- The numbers of nodes, of leaves and of trivalent nodes tell the graphs apart: a cycle on at
  -- least three nodes has no leaf, affine `Dₙ` has a leaf, and at seven, eight and nine nodes
  -- affine `Dₙ` has two trivalent nodes where affine `E₆`, `E₇` and `E₈` have one.
  have hnodes : t.nodes = t'.nodes := by simpa using Fintype.card_congr e.toEquiv
  have hcard (k : ℕ) : #{v | t.graph.degree v = k} = #{v | t'.graph.degree v = k} :=
    card_equiv e.toEquiv fun v ↦ by simp
  have hleaf := hcard 1
  have hfork := hcard 3
  obtain ⟨hE6₁, hE6₃⟩ := card_filter_degree_E6
  obtain ⟨hE7₁, hE7₃⟩ := card_filter_degree_E7
  obtain ⟨hE8₁, hE8₃⟩ := card_filter_degree_E8
  rcases t with n | n | _ | _ | _ <;> rcases t' with m | m | _ | _ | _ <;>
    simp only [valid_A, valid_D, nodes_A, nodes_D, nodes_E6, nodes_E7, nodes_E8,
      Nat.add_right_cancel_iff, A.injEq, D.injEq] at ht ht' hnodes ⊢
  all_goals first
    | omega
    | have := card_filter_degree_A_eq_zero (n := n) (by omega)
      first
        | omega
        | have := card_filter_degree_D_pos (n := m) (by omega); omega
    | have := card_filter_degree_A_eq_zero (n := m) (by omega)
      first
        | omega
        | have := card_filter_degree_D_pos (n := n) (by omega); omega
    | have := card_filter_degree_D_eq_two (n := n) (by omega); omega
    | have := card_filter_degree_D_eq_two (n := m) (by omega); omega

end TauCeti.AffineDynkinType

namespace SimpleGraph

open Finset Matrix TauCeti

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Recognition of the affine simply-laced diagrams.** A connected finite simple graph carries a
nonzero weight `a : V → ℕ` with `∑_{j ∼ i} a j = 2 * a i` at every vertex exactly when it is
isomorphic to the graph of a unique valid affine simply-laced diagram other than `Ã₁`: a cycle
`Ãₙ` with `n ≥ 2`, affine `Dₙ` with `n ≥ 4`, or affine `E₆`, `E₇` or `E₈`. -/
theorem Connected.exists_sum_eq_two_mul_iff_existsUnique_affineDynkinType_iso
    (hG : G.Connected) :
    (∃ a : V → ℕ, a ≠ 0 ∧ ∀ i, ∑ j ∈ G.neighborFinset i, a j = 2 * a i) ↔
      ∃! t : AffineDynkinType, t.Valid ∧ t.IsGraphical ∧ Nonempty (G ≃g t.graph) := by
  classical
  constructor
  · rintro ⟨a, ha, hsum⟩
    -- A nonzero null vector of `2I - A` rules out positive definiteness, so `G` is not a Dynkin
    -- diagram and contains the graph of an affine diagram.
    have hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
      rw [← exists_valid_isSimplyLaced_dynkinType_iso_iff, ← posDef_graphCartanMatrix_iff hG]
      intro hpos
      have hx : (fun i ↦ (a i : ℚ)) ≠ 0 := fun h ↦ ha (funext fun i ↦ by simpa using congrFun h i)
      have hnull : G.graphCartanMatrix ℚ *ᵥ (fun i ↦ (a i : ℚ)) = 0 :=
        graphCartanMatrix_mulVec_eq_zero G fun i ↦ by exact_mod_cast hsum i
      simpa [hnull] using hpos.dotProduct_mulVec_pos hx
    obtain ⟨t, ht, hg, ⟨f⟩⟩ :=
      hG.exists_isContained_affineDynkinType_of_not_exists_dynkinType_iso hD
    -- The marks are a positive additive function on that graph, so the copy is all of `G`.
    obtain ⟨e, -⟩ := f.exists_iso_of_sum_le_two_mul hG.preconnected AffineDynkinType.marks_pos
      (AffineDynkinType.sum_marks_neighborFinset_eq_two_mul ht hg) (a := fun i ↦ (a i : ℤ))
      (fun i ↦ by simp)
      (fun h ↦ ha (funext fun i ↦ by simpa using congrFun h i))
      (fun i ↦ by exact_mod_cast (hsum i).le)
    exact ⟨t, ⟨ht, hg, ⟨e.symm⟩⟩, fun t' ⟨ht', hg', ⟨e'⟩⟩ ↦
      AffineDynkinType.eq_of_graph_iso ht' ht (e'.symm.trans e.symm)⟩
  · rintro ⟨t, ⟨ht, hg, ⟨e⟩⟩, -⟩
    -- The marks, transported along the isomorphism.
    refine ⟨fun v ↦ (t.marks (e v)).toNat, fun h ↦ ?_, fun i ↦ ?_⟩
    · simpa using congrFun h (e.symm t.affineNode)
    · have hsum : ∑ j ∈ G.neighborFinset i, t.marks (e j) = 2 * t.marks (e i) := by
        rw [← AffineDynkinType.sum_marks_neighborFinset_eq_two_mul ht hg (e i)]
        exact sum_equiv e.toEquiv (fun j ↦ by simp [e.map_adj_iff]) fun _ _ ↦ rfl
      have hpos (v : V) : ((t.marks (e v)).toNat : ℤ) = t.marks (e v) :=
        Int.toNat_of_nonneg (AffineDynkinType.marks_pos _).le
      exact (Nat.cast_inj (R := ℤ)).1 (by push_cast [hpos]; exact hsum)

end SimpleGraph
