/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Fan

/-!
# Common cycles in two-vertex-connected graphs

This file characterizes two-vertex-connectivity of a finite simple graph by the existence of a
cycle through every pair of distinct vertices. It also gives the corresponding cycle witnesses
through a vertex and a prescribed edge. These forms let later arguments choose whichever objects
must be retained on the cycle.

The proofs use the vertex form of Menger's theorem and the fan lemma. The characterizations are
standard; see R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173, Springer,
2017, Section 3.1.
-/

public section

open Finset

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- Two distinct vertices of a two-vertex-connected finite graph lie on a common cycle. -/
theorem IsVertexConnected.exists_isCycle_support [Finite V] (hG : G.IsVertexConnected 2)
    {u v : V} (huv : u ≠ v) : ∃ c : G.Walk u u, c.IsCycle ∧ v ∈ c.support := by
  have hcard : 2 < Nat.card V := by
    have := Fintype.ofFinite V
    have h := hG.add_one_le_card
    rw [ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  obtain ⟨P, hPinj, hP, hPdisj⟩ :=
    (isVertexConnected_iff_forall_exists_paths hcard).1 hG u v huv
  let p := P 0
  let q := P 1
  have hp : p.IsPath := hP 0
  have hq : q.IsPath := hP 1
  have hpq : p.InternallyDisjoint q := hPdisj (by decide)
  refine ⟨p.append q.reverse, ?_, by simp [p, q]⟩
  apply hpq.isCycle_append_reverse hp hq
  intro hpqeq
  exact (by decide : (0 : Fin 2) ≠ 1) (hPinj hpqeq)

/-- On a finite vertex type with at least three vertices, two-vertex-connectivity is equivalent to
every pair of distinct vertices lying on a common cycle. -/
theorem isVertexConnected_two_iff_forall_exists_isCycle_support [Finite V]
    (hcard : 3 ≤ Nat.card V) :
    G.IsVertexConnected 2 ↔
      ∀ u v, u ≠ v → ∃ c : G.Walk u u, c.IsCycle ∧ v ∈ c.support := by
  constructor
  · exact fun hG u v huv ↦ hG.exists_isCycle_support huv
  · intro hcyc
    classical
    rw [isVertexConnected_def]
    refine ⟨?_, fun u v ↦ ?_⟩
    · have := Fintype.ofFinite V
      rw [ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card]
      exact_mod_cast hcard
    · obtain rfl | huv := eq_or_ne u v
      · exact .rfl
      obtain ⟨c, hc, hvc⟩ := hcyc u v huv
      let p := c.takeUntil v hvc
      let q := (c.dropUntil v hvc).reverse
      let P : Fin 2 → G.Walk u v := fun i ↦ if i = 0 then p else q
      have hpq : p.InternallyDisjoint q :=
        hc.takeUntil_internallyDisjoint_dropUntil_reverse hvc
      apply isVertexReachable_of_pairwise_internallyDisjoint (P := P)
      intro i j hij
      by_cases hi : i = 0
      · have hj : j ≠ 0 := fun hj ↦ hij (hi.trans hj.symm)
        simpa [P, hi, hj] using hpq
      · have hj : j = 0 := by omega
        simpa [P, hi, hj] using hpq.symm

/-- In a two-vertex-connected finite graph, a vertex outside an edge and that edge lie on a
common cycle. -/
theorem IsVertexConnected.exists_isCycle_mem_edges_of_not_mem [Finite V]
    (hG : G.IsVertexConnected 2) {v : V} {e : Sym2 V} (he : e ∈ G.edgeSet) (hv : v ∉ e) :
    ∃ c : G.Walk v v, c.IsCycle ∧ e ∈ c.edges := by
  classical
  let a := e.out.1
  let b := e.out.2
  have hab : a ≠ b := by
    intro hab
    apply G.not_isDiag_of_mem_edgeSet he
    rw [← Sym2.mk_fst_out_snd_out e, Sym2.mk_isDiag_iff]
    exact hab
  have hva : v ≠ a := fun h ↦ hv (h ▸ Sym2.out_fst_mem e)
  have hvb : v ≠ b := fun h ↦ hv (h ▸ Sym2.out_snd_mem e)
  let U : Finset V := {a, b}
  have hvU : v ∉ U := by simp [U, hva, hvb]
  obtain ⟨u, P, huinj, huU, hP, hint, hdisj⟩ := hG.exists_fan hvU (by simp [U, hab])
  have hu01 : u 0 ≠ u 1 := huinj.ne (by decide)
  have hu0e : u 0 ∈ e := by
    have h := huU 0
    simp only [U, mem_insert, mem_singleton] at h
    obtain h | h := h
    · exact h ▸ Sym2.out_fst_mem e
    · exact h ▸ Sym2.out_snd_mem e
  have hu1e : u 1 ∈ e := by
    have h := huU 1
    simp only [U, mem_insert, mem_singleton] at h
    obtain h | h := h
    · exact h ▸ Sym2.out_fst_mem e
    · exact h ▸ Sym2.out_snd_mem e
  have heq : s(u 0, u 1) = e := (Sym2.mem_and_mem_iff hu01).1 ⟨hu0e, hu1e⟩ |>.symm
  have hadj : G.Adj (u 0) (u 1) := by
    rw [← G.mem_edgeSet, heq]
    exact he
  have hu0P1 : u 0 ∉ (P 1).support := by
    intro hmem
    have := hint 1 (u 0) hmem hu01
    exact this (huU 0)
  let q : G.Walk (u 0) v := (P 1).reverse.cons hadj
  have hq : q.IsPath := (Walk.isPath_reverse_iff (P 1) |>.2 (hP 1)).cons (by
    simpa [Walk.support_reverse] using hu0P1)
  have htail : (P 0).support.tail.Disjoint q.support.tail := by
    rw [List.disjoint_left]
    intro x hx0 hxq
    have hx1 : x ∈ (P 1).support := by simpa [q, Walk.support_reverse] using hxq
    have hxv := hdisj (by decide : (0 : Fin 2) ≠ 1) x
      (List.mem_of_mem_tail hx0) hx1
    subst x
    have hnodup := (hP 0).support_nodup
    rw [← (P 0).cons_tail_support, List.nodup_cons] at hnodup
    exact hnodup.1 hx0
  refine ⟨(P 0).append q, (hP 0).isCycle_append hq htail ?_, ?_⟩
  · right
    simp only [q, Walk.length_cons, Walk.length_reverse]
    have hvu1 : v ≠ u 1 := fun h ↦ hvU (h ▸ huU 1)
    have := (P 1).not_nil_of_ne hvu1
    rw [Walk.not_nil_iff_lt_length] at this
    omega
  · rw [Walk.edges_append, List.mem_append]
    right
    rw [← heq]
    simp [q]

/-- Every vertex and every edge of a two-vertex-connected finite graph lie on a common cycle. -/
theorem IsVertexConnected.exists_isCycle_mem_edges [Finite V]
    (hG : G.IsVertexConnected 2) (v : V) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ∃ c : G.Walk v v, c.IsCycle ∧ e ∈ c.edges := by
  classical
  by_cases hv : v ∈ e
  · have := Fintype.ofFinite V
    have hedge : e.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag e
      (G.not_isDiag_of_mem_edgeSet he)
    obtain ⟨w, -, hw⟩ := exists_mem_notMem_of_card_lt_card (s := e.toFinset) (t := univ) (by
      rw [hedge, card_univ, ← Nat.card_eq_fintype_card]
      have hcard := hG.add_one_le_card
      rw [ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card] at hcard
      exact_mod_cast hcard)
    obtain ⟨c, hc, hec⟩ := hG.exists_isCycle_mem_edges_of_not_mem he
      (by simpa [Sym2.mem_toFinset] using hw)
    have hvc : v ∈ c.support := c.mem_support_of_mem_edges hec hv
    exact ⟨c.rotate v hvc, hc.rotate hvc, by simpa using (c.rotate_edges v hvc).mem_iff.2 hec⟩
  · exact hG.exists_isCycle_mem_edges_of_not_mem he hv

/-- In a connected finite graph with at least three vertices, two-vertex-connectivity is
equivalent to every vertex and every edge lying on a common cycle. -/
theorem isVertexConnected_two_iff_forall_exists_isCycle_mem_edges [Finite V]
    (hconn : G.Connected) (hcard : 3 ≤ Nat.card V) :
    G.IsVertexConnected 2 ↔
      ∀ (v : V) {e : Sym2 V}, e ∈ G.edgeSet →
        ∃ c : G.Walk v v, c.IsCycle ∧ e ∈ c.edges := by
  constructor
  · exact fun hG v _ he ↦ hG.exists_isCycle_mem_edges v he
  · intro hcyc
    apply (isVertexConnected_two_iff_forall_exists_isCycle_support hcard).2
    intro u v huv
    have hcardEN : (3 : ℕ∞) ≤ ENat.card V := by
      have := Fintype.ofFinite V
      rw [ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card]
      exact_mod_cast hcard
    obtain ⟨w, hwv, -⟩ := ENat.exists_ne_ne_of_three_le hcardEN v v
    obtain ⟨x, hvx⟩ := (hconn.preconnected v w).nonempty_neighborSet_left hwv.symm
    obtain ⟨c, hc, hec⟩ := hcyc u (G.mem_edgeSet.2 hvx)
    exact ⟨c, hc, c.fst_mem_support_of_mem_edges hec⟩

end SimpleGraph
