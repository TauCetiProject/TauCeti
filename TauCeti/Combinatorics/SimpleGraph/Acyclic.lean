/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

import Mathlib.Tactic.Linarith

/-!
# Paths and degrees in acyclic simple graphs

This file records consequences of acyclicity for paths, bounds the degree of a
nonempty finite regular forest, and gives a height criterion for acyclicity.

## Main results

* `SimpleGraph.isAcyclic_of_forall_adj_le_eq`: a graph with a height function for which every
  vertex has at most one neighbour of height at most its own is acyclic.
* `SimpleGraph.IsAcyclic.degree_le_one_of_isRegularOfDegree`: a nonempty finite regular
  forest has degree at most one.
* `SimpleGraph.IsAcyclic.not_adj_getVert_of_add_one_lt`: nonconsecutive vertices of a path
  in an acyclic graph are not adjacent.
* `SimpleGraph.IsAcyclic.ne_of_adj_start_of_adj_end`: an off-path neighbour of a path's start
  differs from every neighbour of its end.
* `SimpleGraph.IsAcyclic.not_adj_of_adj_start_of_adj_end`: when both lie off the path, such a
  neighbour of the start and a neighbour of the end are not adjacent.
-/

public section

namespace TauCeti

/-- **A height criterion for acyclicity.** If `f` is a height function on the vertices such that
every vertex has at most one neighbour whose height is at most its own, then the graph is
acyclic: on a cycle, a vertex of greatest height would have two distinct such neighbours. -/
theorem _root_.SimpleGraph.isAcyclic_of_forall_adj_le_eq {V α : Type*} [LinearOrder α]
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
theorem _root_.SimpleGraph.IsAcyclic.not_adj_getVert_of_add_one_lt {V : Type*}
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

/-- **An off-path neighbour of a path's start differs from every neighbour of its end.** In an
acyclic graph, for a path with distinct endpoints. Only the start-side vertex is required to lie
off the path; the end-side one is unconstrained. -/
theorem _root_.SimpleGraph.IsAcyclic.ne_of_adj_start_of_adj_end {V : Type*} {G : SimpleGraph V}
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
theorem _root_.SimpleGraph.IsAcyclic.not_adj_of_adj_start_of_adj_end {V : Type*}
    {G : SimpleGraph V} {u v : V} (hG : G.IsAcyclic) {q : G.Walk u v} (hq : q.IsPath)
    {a b : V} (ha : G.Adj u a) (ha' : a ∉ q.support) (hb : G.Adj v b) (hb' : b ∉ q.support) :
    ¬G.Adj a b := by
  intro hadj
  -- The paths `a — u — … — v` and `a — b` leave `a` with adjacent far ends, and `v` misses the
  -- edge `a — b`, so acyclicity puts `b` on the first path; but `b` is neither `a` nor on `q`.
  have hmem := hG.mem_support_of_ne_mem_support_of_adj_of_isPath (hq.cons ha' (h := ha.symm))
    hadj.isPath_toWalk hb (by simp [hb.ne, ne_of_mem_of_not_mem q.end_mem_support ha'])
  simp [hadj.ne', hb'] at hmem

/-- A nonempty finite regular forest has degree at most one. -/
theorem _root_.SimpleGraph.IsAcyclic.degree_le_one_of_isRegularOfDegree
    {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype V] [Nonempty V] {d : ℕ}
    (hG : G.IsAcyclic) (hd : G.IsRegularOfDegree d) : d ≤ 1 := by
  classical
  have he := hG.ncard_edgeSet_add_one_le_card
  have hs := G.sum_degrees_eq_twice_card_edges
  simp only [hd.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset] at he
  rw [Fintype.card_eq_nat_card] at hs
  have hv : 0 < Nat.card V := Nat.card_pos
  nlinarith

end TauCeti
