/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Fan
import TauCeti.Combinatorics.SimpleGraph.Connectivity.PrescribedCycle
import Mathlib.SetTheory.Cardinal.NatCard

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
theorem IsVertexConnected.exists_isCycle_mem_support [Finite V] (hG : G.IsVertexConnected 2)
    {u v : V} (huv : u ≠ v) : ∃ c : G.Walk u u, c.IsCycle ∧ v ∈ c.support := by
  classical
  obtain ⟨w, c, hc, hmem⟩ :=
    hG.exists_isCycle_forall_mem_support (k := 2) (by omega) (S := {u, v})
      (Finset.card_pair huv).le
  have hu : u ∈ c.support := hmem u (by simp)
  refine ⟨c.rotate u hu, hc.rotate hu, ?_⟩
  simpa using (c.mem_support_rotate_iff u hu).2 (hmem v (by simp))

/-- On a finite vertex type with at least three vertices, two-vertex-connectivity is equivalent to
every pair of distinct vertices lying on a common cycle. -/
theorem isVertexConnected_two_iff_forall_exists_isCycle_mem_support [Finite V]
    (hcard : 3 ≤ Nat.card V) :
    G.IsVertexConnected 2 ↔
      ∀ u v, u ≠ v → ∃ c : G.Walk u u, c.IsCycle ∧ v ∈ c.support := by
  constructor
  · exact fun hG u v huv ↦ hG.exists_isCycle_mem_support huv
  · intro hcyc
    classical
    rw [isVertexConnected_def]
    refine ⟨?_, fun u v ↦ ?_⟩
    · rw [ENat.card_eq_coe_natCard]
      exact Nat.cast_le.2 hcard
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
private theorem IsVertexConnected.exists_isCycle_mem_edges_of_notMem [Finite V]
    (hG : G.IsVertexConnected 2) {v : V} {e : Sym2 V} (he : e ∈ G.edgeSet) (hv : v ∉ e) :
    ∃ c : G.Walk v v, c.IsCycle ∧ e ∈ c.edges := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := G.ne_of_adj (G.mem_edgeSet.1 he)
    have hva : v ≠ a := fun h ↦ hv (by simp [h])
    have hvb : v ≠ b := fun h ↦ hv (by simp [h])
    let U : Finset V := {a, b}
    have hvU : v ∉ U := by simp [U, hva, hvb]
    obtain ⟨u, P, huinj, huU, hP, hint, hdisj⟩ := hG.exists_fan hvU (by simp [U, hab])
    have hu01 : u 0 ≠ u 1 := huinj.ne (by decide)
    have hue : ∀ i, u i ∈ s(a, b) := fun i ↦ by simpa [U, Sym2.mem_iff] using huU i
    have heq : s(u 0, u 1) = s(a, b) :=
      (Sym2.mem_and_mem_iff hu01).1 ⟨hue 0, hue 1⟩ |>.symm
    have hadj : G.Adj (u 0) (u 1) := by
      rw [← G.mem_edgeSet, heq]
      exact he
    have hcycle := (hP 0).isCycle_append_append_reverse (hP 1) hadj.symm.isPath_toWalk
      hu01 (hdisj (by decide))
      (fun x hxP hxE ↦ by
        obtain rfl | rfl : x = u 1 ∨ x = u 0 := by simpa using hxE
        · exact (hint 0 (u 1) hxP hu01.symm (huU 1)).elim
        · rfl)
      (fun x hxP hxE ↦ by
        obtain rfl | rfl : x = u 1 ∨ x = u 0 := by simpa using hxE
        · rfl
        · exact (hint 1 (u 0) hxP hu01 (huU 0)).elim)
    refine ⟨((P 1).append hadj.symm.toWalk).append (P 0).reverse, hcycle, ?_⟩
    rw [Walk.edges_append, List.mem_append, Walk.edges_append, List.mem_append]
    refine .inl (.inr ?_)
    rw [hadj.symm.edges_toWalk, List.mem_singleton]
    exact heq.symm.trans Sym2.eq_swap

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
      exact hG.add_one_le_natCard)
    obtain ⟨c, hc, hec⟩ := hG.exists_isCycle_mem_edges_of_notMem he
      (by simpa [Sym2.mem_toFinset] using hw)
    have hvc : v ∈ c.support := c.mem_support_of_mem_edges hec hv
    exact ⟨c.rotate v hvc, hc.rotate hvc, by simpa using (c.rotate_edges v hvc).mem_iff.2 hec⟩
  · exact hG.exists_isCycle_mem_edges_of_notMem he hv

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
    apply (isVertexConnected_two_iff_forall_exists_isCycle_mem_support hcard).2
    intro u v huv
    have hcardEN : (3 : ℕ∞) ≤ ENat.card V := by
      rw [ENat.card_eq_coe_natCard]
      exact Nat.cast_le.2 hcard
    obtain ⟨w, hwv, -⟩ := ENat.exists_ne_ne_of_three_le hcardEN v v
    obtain ⟨x, hvx⟩ := (hconn.preconnected v w).nonempty_neighborSet_left hwv.symm
    obtain ⟨c, hc, hec⟩ := hcyc u (G.mem_edgeSet.2 hvx)
    exact ⟨c, hc, c.fst_mem_support_of_mem_edges hec⟩

end SimpleGraph
