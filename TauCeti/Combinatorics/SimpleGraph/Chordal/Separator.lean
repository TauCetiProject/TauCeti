/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Chordal.Basic
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Separator
public import Mathlib.Combinatorics.SimpleGraph.Clique

import TauCeti.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Dirac's separator theorem

A graph is chordal if and only if every minimal separator of two vertices is a clique (Dirac).
Here a minimal `a`–`b` separator is a set of vertices whose deletion separates `a` from `b` and no
proper subset of which does (`SimpleGraph.IsMinimalSeparator`). No finiteness is assumed.

The two directions are proved as follows (Vandenberghe–Andersen, proof of Theorem 3.1, with the
minimal separator constructed rather than chosen by finiteness).

* If `G` is chordal and `x`, `y` are two vertices of a minimal `a`–`b` separator `S`, then each of
  `x` and `y` has a neighbour in the part `Cₐ` of `G − S` reachable from `a`, and one in the part
  `C_b` reachable from `b`. Chordless paths from `x` to `y` through `Cₐ` and through `C_b` together
  form a chordless cycle, as there are no edges between `Cₐ` and `C_b`; in a chordal graph it has
  length three, so `x` and `y` are adjacent.
* If every minimal separator is a clique and `cycleGraph n` with `n ≥ 4` is an induced subgraph,
  take the vertices `a` and `b` at positions `0` and `2` of the cycle. A minimal `a`–`b` separator
  consisting of neighbours of `a` exists
  (`SimpleGraph.exists_isMinimalSeparator_subset_neighborSet`) and contains the two neighbours of
  `a` on the cycle, at positions `1` and `n - 1`; these are not adjacent, so the separator is not a
  clique.

## Main results

* `SimpleGraph.IsChordal.isClique_of_isMinimalSeparator`: in a chordal graph every minimal
  separator is a clique.
* `SimpleGraph.isChordal_iff_forall_isMinimalSeparator_isClique`: **Dirac's theorem**, a graph is
  chordal if and only if all its minimal separators are cliques.

## References

* G. A. Dirac, *On rigid circuit graphs*, Abh. Math. Sem. Univ. Hamburg 25 (1961).
* L. Vandenberghe and M. S. Andersen, *Chordal Graphs and Semidefinite Optimization*, Foundations
  and Trends in Optimization 1 (4), 2014, Theorem 3.1.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b : V} {S : Set V}

/-- Two chordless walks `P` from `x` to `y` and `Q` from `y` to `x` form a chordless closed walk
when each vertex of `P` lies on `Q` or in `A`, each vertex of `Q` lies on `P` or in `B`, and no
edge joins `A` to `B`. -/
private theorem isChordless_append_of_forall_mem_support {A B : Set V} {x y : V}
    (hAB : ∀ u ∈ A, ∀ w ∈ B, ¬G.Adj u w) {P : G.Walk x y} {Q : G.Walk y x} (hPc : P.IsChordless)
    (hQc : Q.IsChordless) (hPA : ∀ v ∈ P.support, v ∈ Q.support ∨ v ∈ A)
    (hQB : ∀ v ∈ Q.support, v ∈ P.support ∨ v ∈ B) : (P.append Q).IsChordless := by
  rw [Walk.isChordless_iff_forall_mem_edges]
  intro u w hu hw huw
  rw [Walk.edges_append, List.mem_append]
  rw [Walk.mem_support_append_iff] at hu hw
  rcases hu with hu | hu <;> rcases hw with hw | hw
  · exact .inl (hPc.mem_edges hu hw huw)
  · rcases hPA u hu with hu' | hu'
    · exact .inr (hQc.mem_edges hu' hw huw)
    · rcases hQB w hw with hw' | hw'
      · exact .inl (hPc.mem_edges hu hw' huw)
      · exact absurd huw (hAB u hu' w hw')
  · rcases hPA w hw with hw' | hw'
    · exact .inr (hQc.mem_edges hu hw' huw)
    · rcases hQB u hu with hu' | hu'
      · exact .inl (hPc.mem_edges hu' hw huw)
      · exact absurd huw.symm (hAB w hw' u hu')
  · exact .inr (hQc.mem_edges hu hw huw)

/-- In a chordal graph, two distinct vertices `x` and `y` joined by a walk through a set `A` and by
a walk through a set `B` are adjacent, provided `A` and `B` are disjoint and no edge joins them. -/
private theorem IsChordal.adj_of_forall_mem_support (hG : G.IsChordal) {A B : Set V} {x y : V}
    (hxy : x ≠ y) (hdisj : Disjoint A B) (hAB : ∀ u ∈ A, ∀ w ∈ B, ¬G.Adj u w)
    (P : G.Walk x y) (hP : ∀ w ∈ P.support, w ∈ insert x (insert y A))
    (Q : G.Walk y x) (hQ : ∀ w ∈ Q.support, w ∈ insert x (insert y B)) : G.Adj x y := by
  by_contra hadj
  obtain ⟨P, hPp, hPc, hP⟩ := P.exists_isPath_isChordless_of_forall_mem_support hP
  obtain ⟨Q, hQp, hQc, hQ⟩ := Q.exists_isPath_isChordless_of_forall_mem_support hQ
  -- both paths have length at least two, as `x` and `y` are distinct and nonadjacent
  have hP2 := (Reachable.one_lt_dist_of_ne_of_not_adj ⟨P⟩ hxy hadj).trans_le (G.dist_le P)
  -- the two paths meet only in `x` and `y`, so together they form a cycle
  have hcyc : (P.append Q).IsCycle := by
    refine hPp.isCycle_append hQp (fun v hvP hvQ ↦ ?_) (.inl hP2)
    have hPx : x ∉ P.support.tail :=
      (List.nodup_cons.1 (P.cons_tail_support ▸ hPp.support_nodup)).1
    have hQy : y ∉ Q.support.tail :=
      (List.nodup_cons.1 (Q.cons_tail_support ▸ hQp.support_nodup)).1
    have hvA : v ∈ A := by
      rcases hP v (List.mem_of_mem_tail hvP) with rfl | rfl | hv
      exacts [absurd hvP hPx, absurd hvQ hQy, hv]
    have hvB : v ∈ B := by
      rcases hQ v (List.mem_of_mem_tail hvQ) with rfl | rfl | hv
      exacts [absurd hvP hPx, absurd hvQ hQy, hv]
    exact hdisj.notMem_of_mem_left hvA hvB
  -- the cycle is chordless, as there are no edges between `A` and `B`
  have hchord : (P.append Q).IsChordless := by
    refine isChordless_append_of_forall_mem_support hAB hPc hQc (fun v hv ↦ ?_) (fun v hv ↦ ?_)
    · rcases hP v hv with rfl | rfl | hv
      exacts [.inl Q.end_mem_support, .inl Q.start_mem_support, .inr hv]
    · rcases hQ v hv with rfl | rfl | hv
      exacts [.inl P.start_mem_support, .inl P.end_mem_support, .inr hv]
  -- so it has length three; but each of the two paths has length at least two
  have hQ2 := (Reachable.one_lt_dist_of_ne_of_not_adj ⟨Q⟩ hxy.symm
    (fun h ↦ hadj h.symm)).trans_le (G.dist_le Q)
  have := hG.length_eq_three_of_isChordless hcyc hchord
  rw [Walk.length_append] at this
  lia

/-- **Minimal separators of a chordal graph are cliques.** -/
theorem IsChordal.isClique_of_isMinimalSeparator (hG : G.IsChordal)
    (hS : G.IsMinimalSeparator a b S) : G.IsClique S := by
  classical
  have hsep := hS.isSeparator
  -- `C c` is the set of vertices reachable from `c` after deleting `S`
  let C : V → Set V := fun c ↦ {v | ∃ q : G.Walk c v, ∀ w ∈ q.support, w ∉ S}
  have hC {c v : V} (q : G.Walk c v) (hq : ∀ w ∈ q.support, w ∉ S) : ∀ w ∈ q.support, w ∈ C c :=
    fun w hw ↦ ⟨q.takeUntil w hw, fun u hu ↦ hq u (q.support_takeUntil_subset_support hw hu)⟩
  -- two vertices of a minimal `c`–`d` separator are joined by a walk through `C c`
  have hwalk {c d x y : V} (hS : G.IsMinimalSeparator c d S) (hx : x ∈ S) (hy : y ∈ S) :
      ∃ P : G.Walk x y, ∀ w ∈ P.support, w ∈ insert x (insert y (C c)) := by
    obtain ⟨wx, hwx, hxw, hrx⟩ := hS.exists_adj_reachable hx
    obtain ⟨wy, hwy, hyw, hry⟩ := hS.exists_adj_reachable hy
    obtain ⟨qx, hqx⟩ := reachable_induce_iff.1 hrx
    obtain ⟨qy, hqy⟩ := reachable_induce_iff.1 hry
    refine ⟨.cons hxw (qx.reverse.append (qy.concat hyw.symm)), fun w hw ↦ ?_⟩
    simp only [Walk.support_cons, Walk.mem_support_append_iff, Walk.support_reverse,
      Walk.support_concat, List.mem_cons, List.mem_reverse, List.mem_append, List.not_mem_nil,
      or_false] at hw
    rcases hw with rfl | hw | hw | rfl
    · exact .inl rfl
    · exact .inr (.inr (hC qx hqx w hw))
    · exact .inr (.inr (hC qy hqy w hw))
    · exact .inr (.inl rfl)
  intro x hx y hy hxy
  obtain ⟨P, hP⟩ := hwalk hS hx hy
  obtain ⟨Q, hQ⟩ := hwalk hS.symm hy hx
  refine hG.adj_of_forall_mem_support hxy (Set.disjoint_left.2 ?_) (fun u hu w hw huw ↦ ?_) P hP Q
    (by simpa only [Set.insert_comm] using hQ)
  · -- a vertex reachable from both `a` and `b` would join them outside `S`
    rintro v ⟨qa, hqa⟩ ⟨qb, hqb⟩
    obtain ⟨w, hw, hwS⟩ := hsep.exists_mem_support (qa.append qb.reverse)
    rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hw
    exact hw.elim (hqa w · hwS) (hqb w · hwS)
  · -- so would an edge between the parts reachable from `a` and from `b`
    obtain ⟨qa, hqa⟩ := hu
    obtain ⟨qb, hqb⟩ := hw
    obtain ⟨v, hv, hvS⟩ := hsep.exists_mem_support (qa.append (qb.reverse.cons huw))
    rw [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons, Walk.support_reverse,
      List.mem_reverse] at hv
    rcases hv with hv | rfl | hv
    exacts [hqa v hv hvS, hqa _ qa.end_mem_support hvS, hqb v hv hvS]

/-- Adjacency between the vertices of an induced cycle on `m + 4` vertices, by position. -/
private theorem adj_cycleGraph_embedding_iff {m : ℕ} (f : cycleGraph (m + 4) ↪g G) {i j : ℕ}
    (hi : i < m + 4) (hj : j < m + 4) :
    G.Adj (f ⟨i, hi⟩) (f ⟨j, hj⟩) ↔
      j = i + 1 ∨ i = j + 1 ∨ (i = 0 ∧ j = m + 3) ∨ (j = 0 ∧ i = m + 3) := by
  rw [f.map_adj_iff, TauCeti.cycleGraph_adj_iff_val (by lia)]
  lia

/-- On an induced cycle on `m + 4` vertices, a separator of the vertices at positions `0` and `2`
consisting of neighbours of the first contains the vertex at position `m + 3`: otherwise the long
arc of the cycle, through the positions `m + 3, m + 2, …, 2`, would avoid it. -/
private theorem mem_of_isSeparator_of_subset_neighborSet {m : ℕ} (f : cycleGraph (m + 4) ↪g G)
    (hsep : G.IsSeparator (f ⟨0, by lia⟩) (f ⟨2, by lia⟩) S)
    (hSN : S ⊆ G.neighborSet (f ⟨0, by lia⟩)) : f ⟨m + 3, by lia⟩ ∈ S := by
  by_contra h3
  -- no vertex at a position `2, …, m + 3` is in `S`, which consists of neighbours of position `0`
  have hout {j : ℕ} (hj : 2 ≤ j) (hj' : j ≤ m + 3) : f ⟨j, by lia⟩ ∉ S := fun hjS ↦ by
    rcases (by lia : j = m + 3 ∨ j < m + 3) with rfl | hj''
    · exact h3 hjS
    · have := (adj_cycleGraph_embedding_iff f (i := 0) (by lia) _).1 (hSN hjS)
      lia
  -- so the long arc joins the vertex at position `2` to the one at position `m + 3` outside `S`
  have harc (k : ℕ) (hk : k ≤ m + 1) :
      ∃ q : G.Walk (f ⟨2, by lia⟩) (f ⟨2 + k, by lia⟩), ∀ w ∈ q.support, w ∉ S := by
    induction k with
    | zero => exact ⟨.nil, by simpa using hsep.right_notMem⟩
    | succ k ih =>
      obtain ⟨q, hq⟩ := ih (by lia)
      refine ⟨q.concat ((adj_cycleGraph_embedding_iff f _ _).2 (by lia)), fun w hw ↦ ?_⟩
      rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      exacts [hq w hw, hout (by lia) (by lia)]
  obtain ⟨q, hq⟩ := harc (m + 1) le_rfl
  obtain ⟨v, hv, hvS⟩ := hsep.exists_mem_support
    (q.reverse.cons ((adj_cycleGraph_embedding_iff f (i := 0) (j := 2 + (m + 1)) _ _).2 (by lia)))
  rw [Walk.support_cons, List.mem_cons, Walk.support_reverse, List.mem_reverse] at hv
  rcases hv with rfl | hv
  exacts [hsep.left_notMem hvS, hq v hv hvS]

/-- A graph all of whose minimal separators are cliques is chordal. -/
theorem isChordal_of_forall_isMinimalSeparator_isClique
    (h : ∀ a b S, G.IsMinimalSeparator a b S → G.IsClique S) : G.IsChordal := by
  rw [isChordal_def]
  rintro n hn ⟨f⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by lia⟩
  have hadj {i j : ℕ} (hi : i < m + 4) (hj : j < m + 4) := adj_cycleGraph_embedding_iff f hi hj
  have hne {i j : ℕ} (hi : i < m + 4) (hj : j < m + 4) (hij : i ≠ j) : f ⟨i, hi⟩ ≠ f ⟨j, hj⟩ :=
    f.injective.ne (Fin.ne_of_val_ne hij)
  -- take a minimal separator of the vertices at positions `0` and `2` among neighbours of the first
  obtain ⟨S, hSN, hS⟩ := exists_isMinimalSeparator_subset_neighborSet
    (hne (i := 0) (j := 2) (by lia) (by lia) (by lia)) (by rw [hadj]; lia)
  have hsep := hS.isSeparator
  -- it contains the vertex at position `1`, on the short arc between them
  have h1 : f ⟨1, by lia⟩ ∈ S := by
    have h01 : G.Adj (f ⟨0, by lia⟩) (f ⟨1, by lia⟩) := (hadj _ _).2 (by lia)
    have h12 : G.Adj (f ⟨1, by lia⟩) (f ⟨2, by lia⟩) := (hadj _ _).2 (by lia)
    obtain ⟨v, hv, hvS⟩ := hsep.exists_mem_support (.cons h01 (.cons h12 .nil))
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    rcases hv with rfl | rfl | rfl
    exacts [absurd hvS hsep.left_notMem, hvS, absurd hvS hsep.right_notMem]
  -- and the vertex at position `m + 3`; the two are not adjacent, so `S` is not a clique
  have h3 := mem_of_isSeparator_of_subset_neighborSet f hsep hSN
  have := (hadj _ _).1 (h _ _ _ hS h1 h3 (hne _ _ (by lia)))
  lia

/-- **Dirac's theorem.** A graph is chordal if and only if every minimal separator of two of its
vertices is a clique. -/
theorem isChordal_iff_forall_isMinimalSeparator_isClique :
    G.IsChordal ↔ ∀ a b S, G.IsMinimalSeparator a b S → G.IsClique S :=
  ⟨fun hG _ _ _ hS ↦ hG.isClique_of_isMinimalSeparator hS,
    isChordal_of_forall_isMinimalSeparator_isClique⟩

end SimpleGraph
