/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Fan
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Common cycles in two-vertex-connected graphs

This file characterizes two-vertex-connectivity of a finite simple graph with at least three
vertices by the existence of a common cycle through every pair of distinct vertices and, for a
connected graph, through every vertex and every edge, or through every pair of distinct edges.
These forms let later arguments choose whichever objects must be retained on the cycle.

The proofs use the vertex forms of Menger's theorem, between two vertices and between two vertex
sets, and the fan lemma. The characterizations are standard; see R. Diestel, *Graph Theory*,
5th ed., Graduate Texts in Mathematics 173, Springer, 2017, Section 3.1.
-/

public section

open Finset

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- Two distinct vertices of a two-vertex-connected finite graph lie on a common cycle. -/
theorem IsVertexConnected.exists_isCycle_mem_support [Finite V] (hG : G.IsVertexConnected 2)
    {u v : V} (huv : u ≠ v) : ∃ c : G.Walk u u, c.IsCycle ∧ v ∈ c.support := by
  have hcard : 2 < Nat.card V := by
    have hcard' : 2 + 1 ≤ Nat.card V := hG.add_one_le_natCard
    omega
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
    have hu0P1 : u 0 ∉ (P 1).support := by
      intro hmem
      have := hint 1 (u 0) hmem hu01
      exact this (huU 0)
    let q : G.Walk v (u 0) := (P 1).concat hadj.symm
    have hq : q.IsPath := (hP 1).concat hu0P1 hadj.symm
    have hpq : (P 0).InternallyDisjoint q := by
      rw [Walk.internallyDisjoint_def]
      intro x hx0 hxq
      obtain hx1 | rfl : x ∈ (P 1).support ∨ x = u 0 := by simpa [q] using hxq
      · exact .inl (hdisj (by decide : (0 : Fin 2) ≠ 1) x hx0 hx1)
      · exact .inr rfl
    have hu1P0 : u 1 ∉ (P 0).support :=
      fun hmem ↦ hint 0 (u 1) hmem hu01.symm (huU 1)
    have hpq_ne : P 0 ≠ q := by
      intro hpq_eq
      apply hu1P0
      rw [hpq_eq]
      simp [q]
    refine ⟨(P 0).append q.reverse, hpq.isCycle_append_reverse (hP 0) hq hpq_ne, ?_⟩
    rw [Walk.edges_append, List.mem_append]
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

/-- Any two edges of a two-vertex-connected finite graph lie on a common cycle, which may be based
at either endpoint of the first edge. -/
theorem IsVertexConnected.exists_isCycle_mem_edges_mem_edges [Finite V]
    (hG : G.IsVertexConnected 2) {v : V} {e f : Sym2 V} (he : e ∈ G.edgeSet)
    (hf : f ∈ G.edgeSet) (hv : v ∈ e) :
    ∃ c : G.Walk v v, c.IsCycle ∧ e ∈ c.edges ∧ f ∈ c.edges := by
  classical
  obtain rfl | hef := eq_or_ne e f
  · obtain ⟨c, hc, hec⟩ := hG.exists_isCycle_mem_edges v he
    exact ⟨c, hc, hec, hec⟩
  -- Two vertex-disjoint paths from the ends of `e` to the ends of `f` close up into the cycle.
  have hcard (e : Sym2 V) (he : e ∈ G.edgeSet) : #e.toFinset = 2 :=
    Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeSet he)
  obtain ⟨x, y, P, hx, hy, hP, -, hdisj⟩ :=
    (forall_exists_walk_iff_exists_paths (G := G) e.toFinset f.toFinset 2).1 fun X hX ↦ by
      obtain ⟨a, ha, haX⟩ := exists_mem_notMem_of_card_lt_card (hX.trans_eq (hcard e he).symm)
      obtain ⟨b, hb, hbX⟩ := exists_mem_notMem_of_card_lt_card (hX.trans_eq (hcard f hf).symm)
      obtain ⟨p, hp⟩ := isVertexReachable_iff_exists_walk.1 (hG.isVertexReachable a b)
        (s := ↑X) (by rw [Set.encard_coe_eq_coe_finsetCard]; exact_mod_cast hX)
        (by simpa using haX) (by simpa using hbX)
      exact ⟨a, ha, b, hb, p, fun w hw ↦ by simpa using hp w hw⟩
  have hdisj01 := hdisj (by decide : (0 : Fin 2) ≠ 1)
  have hx01 : x 0 ≠ x 1 := fun h ↦
    hdisj01 (P 0).start_mem_support (by rw [h]; exact (P 1).start_mem_support)
  have hy01 : y 0 ≠ y 1 := fun h ↦
    hdisj01 (P 0).end_mem_support (by rw [h]; exact (P 1).end_mem_support)
  have hxe : e = s(x 0, x 1) :=
    (Sym2.mem_and_mem_iff hx01).1 ⟨by simpa using hx 0, by simpa using hx 1⟩
  have hyf : f = s(y 1, y 0) :=
    (Sym2.mem_and_mem_iff hy01.symm).1 ⟨by simpa using hy 1, by simpa using hy 0⟩
  subst hxe hyf
  have hadjx : G.Adj (x 0) (x 1) := G.mem_edgeSet.1 he
  have hadjy : G.Adj (y 1) (y 0) := G.mem_edgeSet.1 hf
  obtain rfl | rfl := Sym2.mem_iff.1 hv
  · exact ⟨_, (hP 0).isCycle_cons_append_cons_reverse (hP 1) hdisj01 hadjx hadjy hef,
      by simp, by simp⟩
  · rw [Sym2.eq_swap (a := x 0), Sym2.eq_swap (a := y 1)] at hef ⊢
    exact ⟨_, (hP 1).isCycle_cons_append_cons_reverse (hP 0) hdisj01.symm hadjx.symm
      hadjy.symm hef, by simp, by simp⟩

/-- In a connected finite graph with at least three vertices, two-vertex-connectivity is
equivalent to every pair of distinct edges lying on a common cycle. -/
theorem isVertexConnected_two_iff_forall_exists_isCycle_mem_edges_mem_edges [Finite V]
    (hconn : G.Connected) (hcard : 3 ≤ Nat.card V) :
    G.IsVertexConnected 2 ↔
      ∀ ⦃e f : Sym2 V⦄, e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
        ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ e ∈ c.edges ∧ f ∈ c.edges := by
  constructor
  · intro hG e f he hf _
    induction e using Sym2.ind with
    | _ a b => exact ⟨a, hG.exists_isCycle_mem_edges_mem_edges he hf (Sym2.mem_mk_left a b)⟩
  · intro hcyc
    classical
    apply (isVertexConnected_two_iff_forall_exists_isCycle_mem_support hcard).2
    intro u v huv
    -- Choose distinct edges `e ∋ u` and `f` whose common cycle also passes through `v`.
    suffices ∃ (b : V) (c : G.Walk b b), c.IsCycle ∧ u ∈ c.support ∧ v ∈ c.support by
      obtain ⟨b, c, hc, hu, hv⟩ := this
      exact ⟨c.rotate u hu, hc.rotate hu, (c.mem_support_rotate_iff u hu).2 hv⟩
    by_cases huv' : G.Adj u v
    · have hcardEN : (3 : ℕ∞) ≤ ENat.card V := by
        rw [ENat.card_eq_coe_natCard]
        exact Nat.cast_le.2 hcard
      obtain ⟨w, hwu, hwv⟩ := ENat.exists_ne_ne_of_three_le hcardEN u v
      obtain ⟨z, hwz⟩ := (hconn.preconnected w u).nonempty_neighborSet_left hwu
      obtain ⟨b, c, hc, hec, -⟩ := hcyc (G.mem_edgeSet.2 huv') (G.mem_edgeSet.2 hwz)
        (fun h ↦ by simpa [hwu, hwv] using congrArg (w ∈ ·) h)
      exact ⟨b, c, hc, c.fst_mem_support_of_mem_edges hec, c.snd_mem_support_of_mem_edges hec⟩
    · obtain ⟨x, hux⟩ := (hconn.preconnected u v).nonempty_neighborSet_left huv
      obtain ⟨y, hvy⟩ := (hconn.preconnected v u).nonempty_neighborSet_left huv.symm
      have hne : s(u, x) ≠ s(v, y) := fun h ↦ by
        obtain rfl : v = x := by simpa [huv.symm] using congrArg (v ∈ ·) h
        exact huv' hux
      obtain ⟨b, c, hc, hec, hfc⟩ := hcyc (G.mem_edgeSet.2 hux) (G.mem_edgeSet.2 hvy) hne
      exact ⟨b, c, hc, c.fst_mem_support_of_mem_edges hec, c.fst_mem_support_of_mem_edges hfc⟩

end SimpleGraph
