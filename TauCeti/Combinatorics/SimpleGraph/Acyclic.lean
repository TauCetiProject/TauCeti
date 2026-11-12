/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.Data.List.OneDegenerateOrder

/-!
# Paths and degrees in acyclic simple graphs

This file records consequences of acyclicity for paths and for degrees (a nonempty finite
forest has a vertex of degree at most one, so a nonempty finite regular forest has degree at
most one), deduces that the letters of a list on which a graph induces a forest can be put in a
one-degenerate order by peeling off leaves, and gives a height criterion for acyclicity.

## Main results

* `SimpleGraph.isAcyclic_of_forall_adj_le_eq`: a graph with a height function for which every
  vertex has at most one neighbour of height at most its own is acyclic.
* `SimpleGraph.IsAcyclic.exists_degree_le_one`: a nonempty finite forest has a vertex of degree
  at most one.
* `SimpleGraph.IsAcyclic.degree_le_one_of_isRegularOfDegree`: a nonempty finite regular
  forest has degree at most one.
* `List.exists_perm_isOneDegenerateOrder`: a list without repeated letters on which a graph
  induces a forest can be rearranged into a one-degenerate order for the graph.
* `SimpleGraph.IsAcyclic.not_adj_getVert_of_add_one_lt`: nonconsecutive vertices of a path
  in an acyclic graph are not adjacent.
* `SimpleGraph.IsAcyclic.adj_getVert_iff_succ`: two vertices of a path in an acyclic graph are
  adjacent exactly when their indices are consecutive.
* `SimpleGraph.IsAcyclic.not_adj_getVert_of_adj_start`, `…_of_adj_end`: an off-path neighbour of an
  end of a path is not adjacent to the other path vertices; `adj_getVert_iff_eq_zero`,
  `adj_getVert_iff_eq_length` restate this as an adjacency characterization.
* `SimpleGraph.IsAcyclic.ne_of_adj_start_of_adj_end`: an off-path neighbour of a path's start
  differs from every neighbour of its end.
* `SimpleGraph.IsAcyclic.not_adj_of_adj_start_of_adj_end`: when both lie off the path, such a
  neighbour of the start and a neighbour of the end are not adjacent.
-/

public section

namespace SimpleGraph

/-- **A height criterion for acyclicity.** If `f` is a height function on the vertices such that
every vertex has at most one neighbour whose height is at most its own, then the graph is
acyclic: on a cycle, a vertex of greatest height would have two distinct such neighbours. -/
theorem isAcyclic_of_forall_adj_le_eq {V α : Type*} [LinearOrder α]
    {G : SimpleGraph V} (f : V → α)
    (h : ∀ ⦃v u w : V⦄, G.Adj v u → G.Adj v w → f u ≤ f v → f w ≤ f v → u = w) :
    G.IsAcyclic := by
  classical
  rw [SimpleGraph.isAcyclic_iff_forall_not_isCycle]
  intro v c hc
  -- Rotate the cycle so that it starts at a vertex `w` of greatest height.
  obtain ⟨w, hw, hmax⟩ := c.support.toFinset.exists_max_image f ⟨v, by simp⟩
  rw [List.mem_toFinset] at hw
  have hc' := hc.rotate hw
  have hle : ∀ i, f ((c.rotate w hw).getVert i) ≤ f w := fun i =>
    hmax _ (List.mem_toFinset.mpr ((c.mem_support_rotate_iff w hw).mp
      ((c.rotate w hw).getVert_mem_support i)))
  -- Its second and penultimate vertices are distinct neighbours of `w` of height at most `f w`.
  exact hc'.snd_ne_penultimate <| h ((c.rotate w hw).adj_snd hc'.not_nil)
    ((c.rotate w hw).adj_penultimate hc'.not_nil).symm (hle _) (hle _)

/-- A path in an acyclic graph has no chord: vertices separated by at least one intermediate
vertex cannot be adjacent. -/
theorem IsAcyclic.not_adj_getVert_of_add_one_lt {V : Type*}
    {G : SimpleGraph V} {u v : V}
    (hG : G.IsAcyclic) {p : G.Walk u v} (hp : p.IsPath) {i j : ℕ} (hij : i + 1 < j)
    (hj : j ≤ p.length) : ¬G.Adj (p.getVert i) (p.getVert j) := by
  intro hadj
  have hij' : i ≤ j := by omega
  have hmem : p.getVert j ∈ (p.drop i).support := by
    simpa [Nat.add_sub_of_le hij'] using (p.drop i).getVert_mem_support (j - i)
  have heq := hG.eq_snd_of_adj_start (hp.drop i) hadj hmem
  have hsnd : (p.drop i).snd = p.getVert (i + 1) := by simp [SimpleGraph.Walk.snd]
  rw [hsnd] at heq
  have := hp.getVert_injOn (by omega : i + 1 ≤ p.length) hj heq.symm
  omega

/-- In a path of an acyclic graph, two vertices are adjacent exactly when their indices are
consecutive. -/
theorem _root_.SimpleGraph.IsAcyclic.adj_getVert_iff_succ {V : Type*} {G : SimpleGraph V}
    {u v : V} {p : G.Walk u v} (hG : G.IsAcyclic) (hp : p.IsPath) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) :
    G.Adj (p.getVert i) (p.getVert j) ↔ i + 1 = j ∨ j + 1 = i := by
  constructor
  · intro hadj
    rcases lt_trichotomy i j with hij' | rfl | hji'
    · have : ¬i + 1 < j := fun hlt ↦ hG.not_adj_getVert_of_add_one_lt hp hlt hj hadj
      exact Or.inl (by omega)
    · exact (hadj.ne rfl).elim
    · have : ¬j + 1 < i := fun hlt ↦ hG.not_adj_getVert_of_add_one_lt hp hlt hi hadj.symm
      exact Or.inr (by omega)
  · rintro (rfl | rfl)
    · exact p.adj_getVert_succ (by omega)
    · exact (p.adj_getVert_succ (by omega)).symm

/-- **An off-path neighbour of a path's start differs from every neighbour of its end.** In an
acyclic graph, for a path with distinct endpoints. Only the start-side vertex is required to lie
off the path; the end-side one is unconstrained. -/
theorem IsAcyclic.ne_of_adj_start_of_adj_end {V : Type*} {G : SimpleGraph V}
    {u v : V} (hG : G.IsAcyclic) (huv : u ≠ v) {q : G.Walk u v} (hq : q.IsPath)
    {a b : V} (ha : G.Adj u a) (ha' : a ∉ q.support) (hb : G.Adj v b) : a ≠ b := fun hab ↦
  -- `a = b` makes `a` adjacent to the far end `v` of the path `a — u — … — v`, so acyclicity
  -- forces `v` to be that path's second vertex, which is `u`.
  huv <| (SimpleGraph.Walk.snd_cons q ha.symm).symm.trans
    (hG.eq_snd_of_adj_start (hq.cons ha' (h := ha.symm)) (hab ▸ hb).symm
      (SimpleGraph.Walk.end_mem_support _)).symm

/-- **Neighbours of a path's two ends, both lying off the path, are not adjacent.** In an acyclic
graph, no edge joins a vertex adjacent to the start of a path to one adjacent to its end. Here
both are required to lie off the path, unlike in `ne_of_adj_start_of_adj_end`. -/
theorem IsAcyclic.not_adj_of_adj_start_of_adj_end {V : Type*}
    {G : SimpleGraph V} {u v : V} (hG : G.IsAcyclic) {q : G.Walk u v} (hq : q.IsPath)
    {a b : V} (ha : G.Adj u a) (ha' : a ∉ q.support) (hb : G.Adj v b) (hb' : b ∉ q.support) :
    ¬G.Adj a b := by
  intro hadj
  -- The paths `a — u — … — v` and `a — b` leave `a` with adjacent far ends, and `v` misses the
  -- edge `a — b`, so acyclicity puts `b` on the first path; but `b` is neither `a` nor on `q`.
  have hmem := hG.mem_support_of_ne_mem_support_of_adj_of_isPath (hq.cons ha' (h := ha.symm))
    hadj.isPath_toWalk hb (by simp [hb.ne, ne_of_mem_of_not_mem q.end_mem_support ha'])
  simp [hadj.ne', hb'] at hmem

/-- **A nonempty finite forest has a vertex of degree at most one**: an isolated vertex or a
leaf. -/
theorem _root_.SimpleGraph.IsAcyclic.exists_degree_le_one {V : Type*} {G : SimpleGraph V}
    [DecidableRel G.Adj] [Fintype V] [Nonempty V] (hG : G.IsAcyclic) : ∃ v, G.degree v ≤ 1 := by
  classical
  by_contra! h
  -- Every degree is at least two, so the degree sum `2 #E` is at least `2 #V`, while a forest has
  -- at most `#V - 1` edges.
  have he := hG.ncard_edgeSet_add_one_le_card
  have hs := G.sum_degrees_eq_twice_card_edges
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset] at he
  have hle : ∑ _v : V, 2 ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ ↦ h v
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_eq_nat_card] at hle
  omega

/-- In an acyclic graph, an off-path neighbour `x` of the start of a path is not adjacent to any
later vertex of the path. -/
theorem _root_.SimpleGraph.IsAcyclic.not_adj_getVert_of_adj_start {V : Type*} {G : SimpleGraph V}
    {u v x : V} {p : G.Walk u v} (hG : G.IsAcyclic)
    (hp : p.IsPath) (hux : G.Adj u x) (hx : x ≠ p.snd) {i : ℕ} (hi0 : 0 < i) (hi : i ≤ p.length) :
    ¬G.Adj x (p.getVert i) := by
  have hx_support : x ∉ p.support := fun hxmem ↦ hx (hG.eq_snd_of_adj_start hp hux hxmem)
  intro hxy
  have h := hG.not_adj_getVert_of_add_one_lt (hp.cons hx_support (h := hux.symm)) (i := 0)
    (j := i + 1) (by omega) (by simpa using hi)
  exact h (by simpa using hxy)

/-- In an acyclic graph, an off-path neighbour `x` of the end of a path is not adjacent to any
earlier vertex of the path. -/
theorem _root_.SimpleGraph.IsAcyclic.not_adj_getVert_of_adj_end {V : Type*} {G : SimpleGraph V}
    {u v x : V} {p : G.Walk u v} (hG : G.IsAcyclic) (hp : p.IsPath) (hvx : G.Adj v x)
    (hx : x ≠ p.penultimate) {i : ℕ} (hi : i < p.length) :
    ¬G.Adj x (p.getVert i) := by
  have hget : p.reverse.getVert (p.length - i) = p.getVert i := by
    rw [p.getVert_reverse, Nat.sub_sub_self hi.le]
  rw [← hget]
  exact hG.not_adj_getVert_of_adj_start hp.reverse hvx
    (by simpa using hx) (Nat.sub_pos_of_lt hi) (by simp)

/-- In an acyclic graph, an off-path neighbour `x` of the start of a path (other than the path's
second vertex) is adjacent to the vertex `j` of the path exactly when `j = 0`. -/
theorem _root_.SimpleGraph.IsAcyclic.adj_getVert_iff_eq_zero {V : Type*}
    {G : SimpleGraph V} {u v x : V} {p : G.Walk u v} (hG : G.IsAcyclic)
    (hp : p.IsPath) (hux : G.Adj u x) (hx : x ≠ p.snd) {j : ℕ} (hj : j ≤ p.length) :
    G.Adj x (p.getVert j) ↔ j = 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simpa using hux.symm
  · exact iff_of_false (hG.not_adj_getVert_of_adj_start hp hux hx hj0 hj) hj0.ne'

/-- In an acyclic graph, an off-path neighbour `x` of the end of a path (other than the path's
penultimate vertex) is adjacent to the vertex `j` of the path exactly when `j` is the last
index. -/
theorem _root_.SimpleGraph.IsAcyclic.adj_getVert_iff_eq_length {V : Type*}
    {G : SimpleGraph V} {u v x : V} {p : G.Walk u v} (hG : G.IsAcyclic)
    (hp : p.IsPath) (hvx : G.Adj v x) (hx : x ≠ p.penultimate) {j : ℕ} (hj : j ≤ p.length) :
    G.Adj x (p.getVert j) ↔ j = p.length := by
  rcases hj.eq_or_lt with rfl | hlt
  · simpa using hvx.symm
  · exact iff_of_false (hG.not_adj_getVert_of_adj_end hp hvx hx hlt) hlt.ne

/-- A nonempty finite regular forest has degree at most one. -/
theorem IsAcyclic.degree_le_one_of_isRegularOfDegree
    {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype V] [Nonempty V] {d : ℕ}
    (hG : G.IsAcyclic) (hd : G.IsRegularOfDegree d) : d ≤ 1 := by
  obtain ⟨v, hv⟩ := hG.exists_degree_le_one
  exact hd.degree_eq v ▸ hv

/-- **A forest has a one-degenerate order.** A list without repeated letters on whose letters `G`
induces a forest can be rearranged into a one-degenerate order for `G`: peel off a letter joined to
at most one other letter, order the rest by induction, and put the peeled letter last. -/
theorem _root_.List.exists_perm_isOneDegenerateOrder {α : Type*} {G : SimpleGraph α}
    {l : List α} (hl : l.Nodup) (hG : (G.induce {i | i ∈ l}).IsAcyclic) :
    ∃ S, S.Perm l ∧ List.IsOneDegenerateOrder G.Adj S := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, l.length = n := ⟨_, rfl⟩
  induction n generalizing l with
  | zero => exact ⟨[], by simp [List.length_eq_zero_iff.mp hn], List.isOneDegenerateOrder_nil⟩
  | succ n ih =>
    -- The induced forest is finite and nonempty, so some letter `s` is joined to at most one
    -- letter of `l`.
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil l (List.ne_nil_of_length_eq_add_one hn)
    have : Nonempty {i | i ∈ l} := ⟨⟨a, ha⟩⟩
    have : Fintype {i | i ∈ l} := Set.Finite.fintype (List.finite_toSet l)
    obtain ⟨⟨s, hs⟩, hdeg⟩ := hG.exists_degree_le_one
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
    have hsub : {i | i ∈ l.erase s} ≤ {i | i ∈ l} := fun i hi ↦ List.mem_of_mem_erase hi
    obtain ⟨S, hS, hel⟩ := ih (hl.erase s) (hG.embedding (G.induceHomOfLE hsub))
      (by simp [List.length_erase_of_mem hs, hn])
    refine ⟨S ++ [s], ((List.perm_append_singleton s S).trans (hS.cons s)).trans
      (List.perm_cons_erase hs).symm, hel.append_singleton fun x hx y hy hsx hsy ↦ ?_⟩
    exact congrArg Subtype.val <| Finset.card_le_one.mp hdeg ⟨x, hsub (hS.subset hx)⟩
      (by simpa using hsx) ⟨y, hsub (hS.subset hy)⟩ (by simpa using hsy)

end SimpleGraph
