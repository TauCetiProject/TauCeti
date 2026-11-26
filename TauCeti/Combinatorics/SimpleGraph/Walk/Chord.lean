/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Walk.Chord

import TauCeti.Combinatorics.SimpleGraph.CycleGraph

/-!
# Chordless paths and chordless cycles

A walk is chordless (`SimpleGraph.Walk.IsChordless`) when every edge of the graph between two of
its vertices is an edge of the walk. This file relates chordless walks to shortest walks and to
induced cycle graphs.

* A shortest walk between two vertices is chordless, so two reachable vertices are joined by a
  chordless path, and a walk inside a set of vertices can be replaced by a chordless path inside
  the same set.
* A chordless cycle of length `n` spans an induced copy of `cycleGraph n`: its vertices, in order,
  give an embedding of `cycleGraph n` that preserves and reflects adjacency.

These are the two facts that turn chordless cycles built from paths into induced cycle graphs, as
in the theory of chordal graphs.

## Main results

* `SimpleGraph.Walk.le_add_one_of_length_eq_dist`: on a shortest walk, a vertex adjacent to the
  vertex at position `i` lies at a position at most `i + 1`.
* `SimpleGraph.Walk.isChordless_of_length_eq_dist`: a shortest walk is chordless.
* `SimpleGraph.Reachable.exists_isPath_isChordless`: reachable vertices are joined by a chordless
  path.
* `SimpleGraph.Walk.exists_isPath_isChordless_of_forall_mem_support`: the same inside a vertex set.
* `SimpleGraph.Walk.IsChordless.append_of_forall_mem_support`: two chordless walks with no edges
  between their private parts append to a chordless walk.
* `SimpleGraph.Walk.IsChordless.cycleGraph_isIndContained`: a chordless cycle of length `n` gives an
  induced copy of `cycleGraph n`.

## Implementation notes

The embedding in `SimpleGraph.Walk.IsChordless.cycleGraph_isIndContained` is the one Mathlib's
`SimpleGraph.cycleGraph_isContained_iff` builds for a cycle, and the proof that it preserves
adjacency follows that proof; chordlessness is what makes it reflect adjacency as well.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v : V}

namespace Walk

/-- In a shortest walk, a vertex adjacent to the vertex at position `i` lies at a position at most
`i + 1`: otherwise the edge would shortcut the walk. -/
theorem le_add_one_of_length_eq_dist {p : G.Walk u v} (hp : p.length = G.dist u v)
    {i j : ℕ} (hj : j ≤ p.length) (h : G.Adj (p.getVert i) (p.getVert j)) : j ≤ i + 1 := by
  have := G.dist_le ((p.take i).append (cons h (p.drop j)))
  simp only [length_append, take_length, length_cons, drop_length] at this
  lia

/-- A shortest walk between two vertices is chordless. -/
theorem isChordless_of_length_eq_dist (p : G.Walk u v) (hp : p.length = G.dist u v) :
    p.IsChordless := by
  rw [isChordless_iff_forall_mem_edges]
  intro u' v' hu hv h
  obtain ⟨i, rfl, hi⟩ := mem_support_iff_exists_getVert.1 hu
  obtain ⟨j, rfl, hj⟩ := mem_support_iff_exists_getVert.1 hv
  have hij := le_add_one_of_length_eq_dist hp hj h
  have hji := le_add_one_of_length_eq_dist hp hi h.symm
  rcases lt_trichotomy i j with hlt | rfl | hlt
  · exact p.mk_mem_edges_iff_exists.2 ⟨i, by lia, by rw [show i + 1 = j by lia]⟩
  · exact absurd rfl h.ne
  · exact p.mk_mem_edges_iff_exists.2 ⟨j, by lia, by rw [show j + 1 = i by lia, Sym2.eq_swap]⟩

end Walk

/-- Two reachable vertices are joined by a chordless path. -/
theorem Reachable.exists_isPath_isChordless (h : G.Reachable u v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.IsChordless := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  exact ⟨p, p.isPath_of_length_eq_dist hp, p.isChordless_of_length_eq_dist hp⟩

namespace Walk

/-- Two vertices joined by a walk inside a set `s` of vertices are joined by a chordless path inside
`s`. -/
theorem exists_isPath_isChordless_of_forall_mem_support (p : G.Walk u v) {s : Set V}
    (hp : ∀ w ∈ p.support, w ∈ s) :
    ∃ q : G.Walk u v, q.IsPath ∧ q.IsChordless ∧ ∀ w ∈ q.support, w ∈ s := by
  obtain ⟨q, hq, hqc⟩ := Reachable.exists_isPath_isChordless ⟨p.induce s hp⟩
  refine ⟨q.map (Embedding.induce s).toHom, hq.map Subtype.val_injective,
    hqc.map (Embedding.induce s), fun w hw ↦ ?_⟩
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 ((q.support_map _) ▸ hw)
  exact x.property

/-- Two chordless walks `P` from `x` to `y` and `Q` from `y` to `z` append to a chordless walk
when each vertex of `P` lies on `Q` or in `A`, each vertex of `Q` lies on `P` or in `B`, and no
edge joins `A` to `B`. -/
theorem IsChordless.append_of_forall_mem_support {A B : Set V} {x y z : V} {P : G.Walk x y}
    {Q : G.Walk y z} (hPc : P.IsChordless) (hQc : Q.IsChordless)
    (hAB : ∀ u ∈ A, ∀ w ∈ B, ¬G.Adj u w) (hPA : ∀ v ∈ P.support, v ∈ Q.support ∨ v ∈ A)
    (hQB : ∀ v ∈ Q.support, v ∈ P.support ∨ v ∈ B) : (P.append Q).IsChordless := by
  rw [isChordless_iff_forall_mem_edges]
  intro u w hu hw huw
  rw [edges_append, List.mem_append]
  rw [mem_support_append_iff] at hu hw
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

/-- **A chordless cycle is an induced cycle graph.** If `p` is a chordless cycle of length `n`,
then listing its vertices in order embeds `cycleGraph n` into `G` as an induced subgraph. -/
theorem IsChordless.cycleGraph_isIndContained {p : G.Walk u u} (hc : p.IsChordless)
    (hp : p.IsCycle) : cycleGraph p.length ⊴ G := by
  have hinj := hp.getVert_injOn'
  have hlen := hp.three_le_length
  suffices h : ∀ i j : Fin p.length, G.Adj (p.getVert i) (p.getVert j) ↔ (cycleGraph _).Adj i j from
    ⟨⟨⟨fun i : Fin p.length ↦ p.getVert i, fun i j h ↦ Fin.ext (hinj i.isLt j.isLt h)⟩, h _ _⟩⟩
  intro i j
  have := i.isLt
  have := j.isLt
  have h0 : p.getVert 0 = p.getVert p.length := by simp
  rw [TauCeti.cycleGraph_adj_iff_val (by lia)]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- an adjacency between two vertices of the cycle is one of its edges, by chordlessness
    obtain ⟨k, hk, hkij⟩ := p.mk_mem_edges_iff_exists.1
      (hc.mem_edges (p.getVert_mem_support _) (p.getVert_mem_support _) h)
    -- the edge at position `k` ends at position `k + 1`, or at `0` if it closes the cycle
    obtain ⟨l, hl, hkl, hl'⟩ : ∃ l < p.length,
        p.getVert (k + 1) = p.getVert l ∧ (l = k + 1 ∨ l = 0 ∧ k + 1 = p.length) := by
      rcases Nat.lt_or_ge (k + 1) p.length with h1 | h1
      · exact ⟨k + 1, h1, rfl, .inl rfl⟩
      · exact ⟨0, by lia, by rw [h0, show k + 1 = p.length by lia], .inr ⟨rfl, by lia⟩⟩
    rw [hkl, Sym2.eq_iff] at hkij
    have : k = i ∧ l = j ∨ k = j ∧ l = i :=
      hkij.imp (fun h ↦ ⟨hinj hk i.isLt h.1, hinj hl j.isLt h.2⟩)
        (fun h ↦ ⟨hinj hk j.isLt h.1, hinj hl i.isLt h.2⟩)
    lia
  · -- consecutive vertices of the cycle, including the last and the first, are adjacent
    rcases h with h | h | ⟨hi, hj⟩ | ⟨hj, hi⟩
    · rw [h]; exact p.adj_getVert_succ (by lia)
    · rw [h]; exact (p.adj_getVert_succ (by lia)).symm
    · simpa [hi, hj] using (p.adj_getVert_succ (i := j) (by lia)).symm
    · simpa [hi, hj] using p.adj_getVert_succ (i := i) (by lia)

end Walk

end SimpleGraph
