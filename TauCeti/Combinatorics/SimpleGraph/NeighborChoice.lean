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
      exact ⟨_, h, lt_of_le_of_lt (Nat.find_min' (hP _) ⟨s, hs, q, rfl⟩) (by omega)⟩
  let f : V → V := fun u => if hu : u ∈ S then g u else (hstep u hu).choose
  have hfS : ∀ s ∈ S, f s = g s := fun s hs => by simp only [f, hs, ↓reduceDIte]
  have hfn : ∀ u (hu : u ∉ S), G.Adj u (f u) ∧ d (f u) < d u := fun u hu => by
    simp only [f, hu, ↓reduceDIte]
    exact (hstep u hu).choose_spec
  refine ⟨f, hfS, fun u => ?_⟩
  by_cases hu : u ∈ S
  · obtain ⟨hadj, hgS, hne⟩ := hg u hu
    rw [hfS u hu, hfS _ hgS]
    exact ⟨hadj, hne⟩
  · obtain ⟨hadj, hlt⟩ := hfn u hu
    refine ⟨hadj, fun heq => ?_⟩
    by_cases hw : f u ∈ S
    · -- The choice at a vertex of `S` stays in `S`, which does not contain `u`.
      exact hu (heq ▸ hfS _ hw ▸ (hg _ hw).2.1)
    · -- Two steps outside `S` bring `u` strictly closer to `S`.
      have := (hfn _ hw).2
      rw [heq] at this
      exact lt_asymm hlt this

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
  classical
  have hl := hp.three_le_length
  -- The index of a vertex of the cycle, counted from `u` and before the end of the cycle.
  let idx : V → ℕ := fun s => if hs : s ∈ p.support then (hp.exists_getVert_eq hs).choose else 0
  have hidx : ∀ s ∈ p.support, idx s < p.length ∧ p.getVert (idx s) = s := fun s hs => by
    simp only [idx, hs, ↓reduceDIte]
    exact (hp.exists_getVert_eq hs).choose_spec
  -- Two indices before the end of the cycle with the same vertex agree.
  have hinj : ∀ i < p.length, idx (p.getVert i) = i := fun i hi => by
    obtain ⟨hlt, heq⟩ := hidx _ (p.getVert_mem_support i)
    exact hp.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) heq
  refine ⟨fun s => p.getVert (idx s + 1), fun s hs => ?_⟩
  beta_reduce
  obtain ⟨hlt, hs'⟩ := hidx s hs
  refine ⟨by simpa only [hs'] using p.adj_getVert_succ hlt, p.getVert_mem_support _, ?_⟩
  set i := idx s
  rw [← hs']
  rcases (Nat.succ_le_of_lt hlt).lt_or_eq with hi | hi
  · -- Away from the end, the second successor of `p.getVert i` is `p.getVert (i + 2)`.
    rw [hinj _ hi]
    exact (hp.getVert_sub_one_ne_getVert_add_one (i := i + 1) hi.le).symm
  · -- At the end, the successor is `u = p.getVert 0`, whose successor is `p.snd`.
    have h0 : p.getVert (i + 1) = p.getVert 0 := by
      rw [Nat.succ_eq_add_one] at hi
      rw [hi, getVert_length, getVert_zero]
    rw [h0, hinj 0 (by omega), zero_add]
    have h1 : i = p.length - 1 := by omega
    rw [h1]
    exact hp.snd_ne_penultimate

end Walk

/-- **A preconnected graph which is not acyclic has a choice of neighbours without mutual
choices**: some `f` sends every vertex `u` to a neighbour `f u` with `f (f u) ≠ u`. Equivalently,
`G` has an orientation without sinks. -/
theorem Preconnected.exists_forall_adj_and_apply_apply_ne_of_not_isAcyclic (hG : G.Preconnected)
    (hc : ¬G.IsAcyclic) : ∃ f : V → V, ∀ u, G.Adj u (f u) ∧ f (f u) ≠ u := by
  simp only [IsAcyclic, not_forall, not_not] at hc
  obtain ⟨w, p, hp⟩ := hc
  obtain ⟨g, hg⟩ := hp.exists_forall_adj_and_apply_apply_ne
  obtain ⟨f, -, hf⟩ := G.exists_forall_adj_and_apply_apply_ne_of_forall_reachable
    (S := {s | s ∈ p.support}) g hg fun u => ⟨w, p.start_mem_support, hG u w⟩
  exact ⟨f, hf⟩

end SimpleGraph
