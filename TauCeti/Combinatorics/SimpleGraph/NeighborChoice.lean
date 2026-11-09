/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Choosing a neighbour at every vertex without mutual choices

A function `f : V → V` with `G.Adj u (f u)` and `f (f u) ≠ u` for every vertex `u` chooses a
neighbour at every vertex so that no two vertices choose each other. Orienting each edge
`{u, f u}` away from `u` is then consistent, and every vertex is the tail of an edge: such a
choice is the same as an orientation of `G` in which no vertex is a sink.

A preconnected graph with a cycle admits such a choice: go once around the cycle, and send every
other vertex to a neighbour strictly closer to the cycle. In a finite tree there is no such choice,
since the choice would give the tree as many edges as vertices.

## Main results

* `SimpleGraph.exists_forall_adj_and_apply_apply_ne_of_forall_reachable`: if the vertices of a set
  `S` already choose neighbours in `S` without mutual choices, and every vertex can reach `S`, then
  the choice extends to all vertices.
* `SimpleGraph.Walk.IsCycle.exists_forall_adj_and_apply_apply_ne`: the vertices of a cycle choose
  their successors along it without mutual choices.
* `SimpleGraph.Preconnected.exists_forall_adj_and_apply_apply_ne_of_not_isAcyclic`: **a
  preconnected graph which is not acyclic has a choice of neighbours without mutual choices.**
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- **Extending a choice of neighbours without mutual choices.** Suppose that `g` chooses, at every
vertex of a set `S`, a neighbour in `S`, and that no two vertices of `S` choose each other. If every
vertex can reach `S`, then some `f` chooses a neighbour at every vertex, still without mutual
choices: it agrees with `g` on `S` and moves every other vertex strictly closer to `S`. -/
theorem exists_forall_adj_and_apply_apply_ne_of_forall_reachable (G : SimpleGraph V) {S : Set V}
    (g : V → V) (hg : ∀ s ∈ S, G.Adj s (g s) ∧ g s ∈ S ∧ g (g s) ≠ s)
    (hS : ∀ u, ∃ s ∈ S, G.Reachable u s) :
    ∃ f : V → V, (∀ s ∈ S, f s = g s) ∧ ∀ u, G.Adj u (f u) ∧ f (f u) ≠ u := by
  classical
  -- `d u` is the length of a shortest walk from `u` to `S`.
  have hP : ∀ u, ∃ n, ∃ s ∈ S, ∃ p : G.Walk u s, p.length = n := fun u => by
    obtain ⟨s, hs, ⟨p⟩⟩ := hS u
    exact ⟨_, s, hs, p, rfl⟩
  let d : V → ℕ := fun u => Nat.find (hP u)
  -- A vertex outside `S` has a neighbour strictly closer to `S`.
  have hstep : ∀ u ∉ S, ∃ w, G.Adj u w ∧ d w < d u := fun u hu => by
    obtain ⟨s, hs, p, hp⟩ := Nat.find_spec (hP u)
    cases p with
    | nil => exact absurd hs hu
    | cons h q =>
      have hq : q.length + 1 = d u := (Walk.length_cons h q).symm.trans hp
      exact ⟨_, h, (Nat.find_min' (hP _) ⟨s, hs, q, rfl⟩).trans_lt (by omega)⟩
  choose! w hw using hstep
  refine ⟨S.piecewise g w, fun s hs => S.piecewise_eq_of_mem _ _ hs, fun u => ?_⟩
  by_cases hu : u ∈ S
  · obtain ⟨hadj, hgS, hne⟩ := hg u hu
    rw [S.piecewise_eq_of_mem _ _ hu, S.piecewise_eq_of_mem _ _ hgS]
    exact ⟨hadj, hne⟩
  · obtain ⟨hadj, hlt⟩ := hw u hu
    rw [S.piecewise_eq_of_notMem _ _ hu]
    refine ⟨hadj, fun heq => ?_⟩
    by_cases hwS : w u ∈ S
    · -- The choice at a vertex of `S` stays in `S`, which does not contain `u`.
      rw [S.piecewise_eq_of_mem _ _ hwS] at heq
      exact hu (heq ▸ (hg _ hwS).2.1)
    · -- Two steps outside `S` bring `u` strictly closer to `S`.
      rw [S.piecewise_eq_of_notMem _ _ hwS] at heq
      exact lt_asymm hlt (by simpa only [heq] using (hw _ hwS).2)

namespace Walk

/-- Every vertex of a cycle is `p.getVert i` for some index `i` before the end of the cycle. -/
theorem IsCycle.exists_getVert_eq {u s : V} {p : G.Walk u u} (hp : p.IsCycle)
    (hs : s ∈ p.support) : ∃ i < p.length, p.getVert i = s := by
  obtain ⟨n, rfl, hn⟩ := mem_support_iff_exists_getVert.1 hs
  rcases hn.lt_or_eq with hn | rfl
  · exact ⟨n, hn, rfl⟩
  · exact ⟨0, by have := hp.three_le_length; omega, by rw [getVert_zero, getVert_length]⟩

/-- **Going once around a cycle chooses neighbours without mutual choices.** The vertices of a
cycle `p` have a choice `g` of neighbours on `p` such that no two of them choose each other: `g`
sends `p.getVert i` to `p.getVert (i + 1)`. -/
theorem IsCycle.exists_forall_adj_and_apply_apply_ne {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    ∃ g : V → V, ∀ s ∈ p.support, G.Adj s (g s) ∧ g s ∈ p.support ∧ g (g s) ≠ s := by
  have hl := hp.three_le_length
  -- The index of a vertex of the cycle, counted from `u` and before the end of the cycle.
  choose! idx hidx using fun s (hs : s ∈ p.support) => hp.exists_getVert_eq hs
  have hinj : ∀ i < p.length, idx (p.getVert i) = i := fun i hi => by
    obtain ⟨hlt, heq⟩ := hidx _ (p.getVert_mem_support i)
    exact hp.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) heq
  refine ⟨fun s => p.getVert (idx s + 1), fun s hs => ?_⟩
  obtain ⟨i, hi, rfl⟩ := hp.exists_getVert_eq hs
  simp only [hinj i hi]
  refine ⟨p.adj_getVert_succ hi, p.getVert_mem_support _, ?_⟩
  obtain hi' | hi' : i + 1 < p.length ∨ i + 1 = p.length := by omega
  · -- Away from the end, the second successor of `p.getVert i` is `p.getVert (i + 2)`.
    rw [hinj _ hi']
    exact (hp.getVert_sub_one_ne_getVert_add_one (i := i + 1) hi'.le).symm
  · -- At the end, the successor is `u = p.getVert 0`, whose successor is `p.snd`.
    have h0 : idx u = 0 := by simpa using hinj 0 (by omega)
    have hi'' : i = p.length - 1 := by omega
    rw [hi', getVert_length, h0, hi'']
    exact hp.snd_ne_penultimate

end Walk

/-- **A preconnected graph which is not acyclic has a choice of neighbours without mutual
choices**: some `f` sends every vertex `u` to a neighbour `f u` with `f (f u) ≠ u`. Equivalently,
`G` has an orientation without sinks. -/
theorem Preconnected.exists_forall_adj_and_apply_apply_ne_of_not_isAcyclic (hG : G.Preconnected)
    (hc : ¬G.IsAcyclic) : ∃ f : V → V, ∀ u, G.Adj u (f u) ∧ f (f u) ≠ u := by
  obtain ⟨w, p, hp⟩ := not_isAcyclic_iff_exists_isCycle.1 hc
  obtain ⟨g, hg⟩ := hp.exists_forall_adj_and_apply_apply_ne
  obtain ⟨f, -, hf⟩ := G.exists_forall_adj_and_apply_apply_ne_of_forall_reachable
    (S := {s | s ∈ p.support}) g hg fun u => ⟨w, p.start_mem_support, hG u w⟩
  exact ⟨f, hf⟩

end SimpleGraph
