/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Hamiltonian paths with a large degree sum at their ends

A Hamiltonian path `u = x₀, x₁, …, xₗ = v` whose ends have degree sum at least the number `n` of
vertices closes up to a Hamilton cycle, possibly after a rotation: there is an index `i` with
`u` adjacent to `xᵢ₊₁` and `xᵢ` adjacent to `v`, and then `xᵢ₊₁ ⋯ xₗ xᵢ ⋯ x₀` is a Hamiltonian
path whose ends `xᵢ₊₁` and `u` are adjacent. This gives the lemma of Bondy and Chvátal that adding
an edge between two vertices of degree sum at least `n` does not change whether a graph is
Hamiltonian, the step from which the Bondy–Chvátal closure and the theorems of Ore and Dirac
follow.

## Main results

* `SimpleGraph.Walk.IsHamiltonian.isHamiltonian_of_adj_getVert`: a Hamiltonian path
  `x₀ ⋯ xₗ` with `x₀` adjacent to `xᵢ₊₁` and `xᵢ` adjacent to `xₗ` gives a Hamilton cycle.
* `SimpleGraph.Walk.IsHamiltonian.isHamiltonian_of_card_le_degree_add_degree`: a Hamiltonian
  path whose ends have degree sum at least the number of vertices gives a Hamilton cycle.
* `SimpleGraph.isHamiltonian_sup_edge_iff`: the Bondy–Chvátal lemma; if `n ≤ deg u + deg v`,
  then `G ⊔ edge u v` is Hamiltonian if and only if `G` is.

## References

* J. A. Bondy and U. S. R. Murty, *Graph Theory with Applications*, North-Holland, 1976,
  Lemma 4.4.1.
* J. A. Bondy and V. Chvátal, *A method in graph theory*, Discrete Math. 15 (1976).
-/

public section

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v : V}

namespace Walk

/-- **Rotation of a Hamiltonian path.** If `p = x₀ ⋯ xₗ` is a Hamiltonian path in a graph on at
least three vertices, `x₀` is adjacent to `xᵢ₊₁` and `xᵢ` is adjacent to `xₗ`, then the graph is
Hamiltonian: `xᵢ₊₁ ⋯ xₗ xᵢ ⋯ x₀` is a Hamiltonian path whose ends are adjacent. The adjacency of
`xᵢ` and `xₗ` forces `i < l`. -/
theorem IsHamiltonian.isHamiltonian_of_adj_getVert {p : G.Walk u v} (hp : p.IsHamiltonian)
    (hn : 3 ≤ Fintype.card V) {i : ℕ} (hu : G.Adj u (p.getVert (i + 1)))
    (hv : G.Adj (p.getVert i) v) : G.IsHamiltonian := by
  have hi : i < p.length := by
    by_contra! hi
    exact G.irrefl (p.getVert_of_length_le hi ▸ hv)
  let q : G.Walk (p.getVert (i + 1)) u := (p.drop (i + 1)).append (cons hv.symm (p.take i).reverse)
  have hsupp : q.support = p.support.drop (i + 1) ++ (p.support.take (i + 1)).reverse := by
    simp [q, support_append, support_take, Nat.min_eq_left hi]
  refine IsHamiltonian.isHamiltonian_of_adj (p := q) (fun a ↦ ?_) hu.symm ?_
  · rw [hsupp, List.count_append, List.count_reverse, add_comm, ← List.count_append,
      List.take_append_drop]
    exact hp a
  · have := hp.length_add_one_eq
    simp only [q, length_append, length_cons, length_reverse, drop_length, take_length]
    omega

/-- **Ore's crossing argument.** A Hamiltonian path whose ends have degree sum at least the
number of vertices, on at least three vertices, gives a Hamilton cycle. -/
theorem IsHamiltonian.isHamiltonian_of_card_le_degree_add_degree [DecidableRel G.Adj]
    {p : G.Walk u v} (hp : p.IsHamiltonian) (hn : 3 ≤ Fintype.card V)
    (hdeg : Fintype.card V ≤ G.degree u + G.degree v) : G.IsHamiltonian := by
  have hlen : p.support.length = p.length + 1 := p.length_support
  -- The indices `i` with `u ~ xᵢ₊₁` and those with `xᵢ ~ v` lie in `range p.length`, and there
  -- are at least `deg u` and `deg v` of them; as `p.length < n`, some index is in both sets.
  have hA : G.degree u ≤ #{i ∈ range p.length | G.Adj u (p.getVert (i + 1))} := by
    rw [← card_neighborFinset_eq_degree]
    refine card_le_card_of_surjOn (fun i ↦ p.getVert (i + 1)) fun w hw ↦ ?_
    rw [coe_neighborFinset, mem_neighborSet] at hw
    obtain ⟨j, rfl⟩ := hp.getVertEquiv.surjective w
    have hj : (j : ℕ) ≠ 0 := fun h ↦ by simp [h] at hw
    refine ⟨(j : ℕ) - 1, ?_, ?_⟩
    · simp only [coe_filter, mem_range, Set.mem_ofPred_eq, Nat.sub_add_cancel
        (Nat.pos_of_ne_zero hj)]
      exact ⟨by omega, hw⟩
    · simp [Nat.sub_add_cancel (Nat.pos_of_ne_zero hj)]
  have hB : G.degree v ≤ #{i ∈ range p.length | G.Adj (p.getVert i) v} := by
    rw [← card_neighborFinset_eq_degree]
    refine card_le_card_of_surjOn p.getVert fun w hw ↦ ?_
    rw [coe_neighborFinset, mem_neighborSet] at hw
    obtain ⟨j, rfl⟩ := hp.getVertEquiv.surjective w
    have hj : (j : ℕ) ≠ p.length := fun h ↦ by simp [h] at hw
    refine ⟨j, ?_, rfl⟩
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
    exact ⟨by omega, hw.symm⟩
  obtain ⟨i, hi⟩ := inter_nonempty_of_card_lt_card_add_card
    (filter_subset (fun i ↦ G.Adj u (p.getVert (i + 1))) (range p.length))
    (filter_subset (fun i ↦ G.Adj (p.getVert i) v) _)
    (by have := hp.length_add_one_eq; rw [card_range]; omega)
  simp only [mem_inter, mem_filter, mem_range] at hi
  exact hp.isHamiltonian_of_adj_getVert hn hi.1.2 hi.2.2

end Walk

/-- **The Bondy–Chvátal lemma.** If the degrees of `u` and `v` in `G` sum to at least the number
of vertices, then `G ⊔ edge u v` is Hamiltonian if and only if `G` is. The lemma is of interest when
`u ≠ v` are nonadjacent; otherwise `G ⊔ edge u v = G`. -/
theorem isHamiltonian_sup_edge_iff [DecidableRel G.Adj]
    (hdeg : Fintype.card V ≤ G.degree u + G.degree v) :
    (G ⊔ edge u v).IsHamiltonian ↔ G.IsHamiltonian := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mono le_sup_left⟩
  obtain rfl | huv := eq_or_ne u v
  · simpa using h
  have : Nontrivial V := ⟨⟨u, v, huv⟩⟩
  have hn : 3 ≤ Fintype.card V := by
    have := Fintype.one_lt_card_iff_nontrivial.mpr this
    by_contra! hlt
    exact not_isHamiltonian_of_card_eq_two (by omega) h
  have hG : ∀ e ∈ (G ⊔ edge u v).edgeSet, e ≠ s(u, v) → e ∈ G.edgeSet := fun e he hne ↦ by
    rw [edgeSet_sup, Set.mem_union] at he
    exact he.resolve_right fun h ↦ hne (by simpa using edgeSet_edge_subset h)
  obtain ⟨C, hC⟩ := h.exists_isHamiltonianCycle u
  by_cases hCe : s(u, v) ∈ C.edges
  · -- The cycle passes through `uv`, so after reversing it if necessary its first step is `uv`,
    -- and the rest of it is a Hamiltonian path of `G` from `v` to `u`.
    obtain ⟨D, hD, hDv⟩ : ∃ D : (G ⊔ edge u v).Walk u u, D.IsHamiltonianCycle ∧ v = D.snd := by
      rcases hC.isHamiltonian_dropLast.isPath.eq_snd_or_eq_penultimate_of_start_mem_edges hCe
        with h | h
      · exact ⟨C, hC, h⟩
      · exact ⟨C.reverse, hC.reverse, by simpa using h⟩
    have hDe : s(u, v) ∉ D.tail.edges := by
      have := hD.edges_nodup
      rw [← D.cons_tail_eq hD.not_nil, Walk.edges_cons] at this
      exact fun he ↦ (List.nodup_cons.mp this).1 (congrArg (s(u, ·)) hDv ▸ he)
    have hT : ∀ e ∈ D.tail.edges, e ∈ G.edgeSet := fun e he ↦
      hG e (D.tail.edges_subset_edgeSet he) (by rintro rfl; exact hDe he)
    have hP : ((D.tail.transfer G hT).copy hDv.symm rfl).IsHamiltonian := by
      simpa using hD.isHamiltonian_tail
    exact hP.isHamiltonian_of_card_le_degree_add_degree hn (by omega)
  · -- The cycle avoids `uv`, so it is a Hamilton cycle of `G`.
    have hT : ∀ e ∈ C.edges, e ∈ G.edgeSet := fun e he ↦
      hG e (C.edges_subset_edgeSet he) (by rintro rfl; exact hCe he)
    exact (hC.transfer hT).isHamiltonian

end SimpleGraph
