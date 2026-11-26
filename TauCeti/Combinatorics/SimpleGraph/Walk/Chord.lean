/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Walk.Chord

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

* `SimpleGraph.Walk.isChordless_of_length_eq_dist`: a shortest walk is chordless.
* `SimpleGraph.Reachable.exists_isPath_isChordless`: reachable vertices are joined by a chordless
  path.
* `SimpleGraph.Walk.exists_isPath_isChordless_of_forall_mem_support`: the same inside a vertex set.
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
private theorem le_add_one_of_length_eq_dist {p : G.Walk u v} (hp : p.length = G.dist u v)
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

/-- **A chordless cycle is an induced cycle graph.** If `p` is a chordless cycle of length `n`,
then listing its vertices in order embeds `cycleGraph n` into `G` as an induced subgraph. -/
theorem IsChordless.cycleGraph_isIndContained {p : G.Walk u u} (hc : p.IsChordless)
    (hp : p.IsCycle) : cycleGraph p.length ⊴ G := by
  have hinj := hp.getVert_injOn'
  have hlen := hp.three_le_length
  -- consecutive vertices of the cycle, including the last and the first, are adjacent
  have key {i j : Fin p.length} (h : (j - i).val = 1) : G.Adj (p.getVert i) (p.getVert j) := by
    rcases Nat.lt_or_ge j i with hij | hij
    · rw [Fin.coe_sub_iff_lt.mpr (Fin.lt_def.mpr hij)] at h
      rw [show i = p.length - 1 by lia, show ↑j = 0 by lia, getVert_zero]
      exact p.adj_penultimate hp.not_nil
    · grind [adj_getVert_succ, Fin.sub_val_of_le]
  suffices h : ∀ i j : Fin p.length, G.Adj (p.getVert i) (p.getVert j) ↔ (cycleGraph _).Adj i j from
    ⟨⟨⟨fun i : Fin p.length ↦ p.getVert i, fun i j h ↦ Fin.ext (hinj i.isLt j.isLt h)⟩, h _ _⟩⟩
  intro i j
  refine ⟨fun h ↦ ?_, fun h ↦ cycleGraph_adj'.mp h |>.elim (key · |>.symm) key⟩
  -- an adjacency between two vertices of the cycle is one of its edges, by chordlessness
  obtain ⟨k, hk, hkij⟩ := p.mk_mem_edges_iff_exists.1
    (hc.mem_edges (p.getVert_mem_support _) (p.getVert_mem_support _) h)
  have hk1 : p.getVert (k + 1) = p.getVert ((k + 1) % p.length) := by
    rcases Nat.lt_or_ge (k + 1) p.length with h1 | h1
    · rw [Nat.mod_eq_of_lt h1]
    · rw [show k + 1 = p.length by lia, Nat.mod_self, getVert_length, getVert_zero]
  have hmod := Nat.mod_lt (k + 1) (show 0 < p.length by lia)
  rw [hk1, Sym2.eq_iff] at hkij
  rw [cycleGraph_adj']
  rcases hkij with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 := hinj hk i.isLt h1
    have e2 := hinj hmod j.isLt h2
    rcases Nat.lt_or_ge (k + 1) p.length with h3 | h3
    · rw [Nat.mod_eq_of_lt h3] at e2
      right; rw [Fin.sub_val_of_le (by simp only [Fin.le_def]; lia)]; lia
    · rw [show k + 1 = p.length by lia, Nat.mod_self] at e2
      right; rw [Fin.coe_sub_iff_lt.mpr (by simp only [Fin.lt_def]; lia)]; lia
  · have e1 := hinj hk j.isLt h1
    have e2 := hinj hmod i.isLt h2
    rcases Nat.lt_or_ge (k + 1) p.length with h3 | h3
    · rw [Nat.mod_eq_of_lt h3] at e2
      left; rw [Fin.sub_val_of_le (by simp only [Fin.le_def]; lia)]; lia
    · rw [show k + 1 = p.length by lia, Nat.mod_self] at e2
      left; rw [Fin.coe_sub_iff_lt.mpr (by simp only [Fin.lt_def]; lia)]; lia

end Walk

end SimpleGraph
