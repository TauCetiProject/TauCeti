/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.EdgeConnected

import TauCeti.Combinatorics.Graph.Connectivity.Walk.Decomposition

/-!
# Extending a subgraph by an ear

A non-bridge edge leaving a subgraph starts an ear that returns to that subgraph.  Delete the
edge, choose a path back, and stop the path at its first old vertex.  If it returns to the starting
vertex this gives a closed ear; otherwise it gives an open ear.  In either case the new ear
strictly enlarges the subgraph and contains the original edge.

This is the extension step in the ear characterization of finite `2`-edge-connected multigraphs.
Iterating it from a single vertex constructs an ear decomposition; the finite iteration is kept
separate from this finiteness-free graph-theoretic lemma.

The argument follows R. Diestel, *Graph Theory*, Chapter 3, with edge identities retained for
parallel edges and loops.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G H : Graph α β}

/-- A non-bridge edge from an old vertex to a new vertex is contained in an open or closed ear
that strictly enlarges the old subgraph.  No finiteness assumption is needed. -/
theorem IsLink.exists_ear_of_mem_notMem {e : β} {x y : α} (h : G.IsLink e x y)
    (hHG : H ≤ G) (hx : x ∈ V(H)) (hy : y ∉ V(H)) (he : ¬G.IsBridge e) :
    ∃ ear : G.Ear H, H < ear.add ∧ e ∈ ear.toWalk.2.2.edges := by
  classical
  have hreachable : (G.deleteEdges {e}).Reachable y x :=
    (reachable_deleteEdges_iff_of_not_isBridge he).2 h.symm.reachable
  obtain ⟨-, q, hq⟩ := reachable_deleteEdges_iff_exists_walk.mp hreachable
  let p := q.bypass
  have hp : p.IsPath := q.bypass_isPath
  have hp_no_e : e ∉ p.edges := fun hep ↦ hq e (q.edges_bypass_subset_edges hep) (by simp)
  obtain ⟨z, r, hr, hz, hinter, hsupport, hedges⟩ :=
    hp.exists_initialSegment_to_set hy hx
  have hr_no_e : e ∉ r.edges := fun her ↦ hp_no_e (hedges her)
  have he_notMem : e ∉ E(H) := by
    intro heH
    exact hy ((hHG.isLink_iff heH).2 h).right_mem
  have old_vertex_eq_end {a : α} (ha : a ∈ r.support) (haH : a ∈ V(H)) : a = z := by
    by_cases hay : a = y
    · exact (hy (hay ▸ haH)).elim
    by_cases haz : a = z
    · exact haz
    · exact (hinter a ha hay haz haH).elim
  have hr_edges_new : ∀ f ∈ r.edges, f ∉ E(H) := by
    intro f hf hfH
    obtain ⟨a, b, habH⟩ := H.exists_isLink_of_mem_edgeSet hfH
    have habG := habH.mono hHG
    have haz := old_vertex_eq_end (r.mem_support_of_isLink_of_mem_edges habG hf) habH.left_mem
    have hbz :=
      old_vertex_eq_end (r.mem_support_of_isLink_of_mem_edges habG.symm hf) habH.right_mem
    subst a
    subst b
    exact hr.not_isLoopAt_of_mem_edges hf z habG
  have edges_new : ∀ f ∈ (Walk.cons e h r).edges, f ∉ E(H) := by
    intro f hf
    simp only [Walk.edges_cons, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact he_notMem
    · exact hr_edges_new f hf
  have finish (ear : G.Ear H) (hear : e ∈ ear.toWalk.2.2.edges) :
      H < ear.add ∧ e ∈ ear.toWalk.2.2.edges := by
    refine ⟨lt_of_le_of_ne ear.base_le_add ?_, hear⟩
    intro hEq
    exact he_notMem (hEq ▸ ear.edges_toWalk_subset_edgeSet_add hear)
  by_cases hxz : x = z
  · subst z
    let ear : G.Ear H := .closed hHG (Walk.cons e h r)
      ((Walk.cons_isCycle_iff e h r).2 ⟨hr, hr_no_e⟩) hx
      (by
        intro a ha hax
        simp only [Walk.support_cons, List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact (hax rfl).elim
        · exact fun haH ↦ hax (old_vertex_eq_end ha haH))
      edges_new
    refine ⟨ear, finish ear ?_⟩
    dsimp only [ear]
    rw [Ear.toWalk_closed]
    simp
  · have hx_support : x ∉ r.support := by
      intro hxr
      exact hxz (old_vertex_eq_end hxr hx)
    let ear : G.Ear H := .open hHG (Walk.cons e h r)
      ((Walk.isPath_cons e h r).2 ⟨hr, hx_support⟩) hx hz hxz
      (by
        intro a ha hax haz
        simp only [Walk.support_cons, List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact (hax rfl).elim
        · by_cases hay : a = y
          · exact hay ▸ hy
          · exact hinter a ha hay haz)
      edges_new
    refine ⟨ear, finish ear ?_⟩
    dsimp only [ear]
    rw [Ear.toWalk_open]
    simp

/-- Every proper connected subgraph of a `2`-edge-connected graph can be strictly enlarged by
adjoining one open or closed ear.  This is the extension engine for constructing an ear
decomposition; it does not require finiteness. -/
theorem Connected.exists_ear_of_lt (hH : H.Connected) (hHG : H < G)
    (hG : G.IsEdgeConnected 2) : ∃ ear : G.Ear H, H < ear.add := by
  classical
  have hV : V(G).Nonempty := hH.nonempty.mono hHG.le.vertexSet_mono
  have hG' := (isEdgeConnected_two_iff_connected_and_forall_not_isBridge hV).1 hG
  by_cases hvertices : V(G) ⊆ V(H)
  · have hedge : ∃ e, e ∈ E(G) ∧ e ∉ E(H) := by
      by_contra! hedge
      apply hHG.ne
      apply Graph.ext
      · exact Set.Subset.antisymm hHG.le.vertexSet_mono hvertices
      · intro e x y
        constructor
        · intro he
          exact he.mono hHG.le
        · intro he
          exact (hHG.le.isLink_iff (hedge e he.edge_mem)).2 he
    obtain ⟨e, heG, heH⟩ := hedge
    obtain ⟨x, y, h⟩ := G.exists_isLink_of_mem_edgeSet heG
    have hx := hvertices h.left_mem
    have hy := hvertices h.right_mem
    have finish (ear : G.Ear H) (hear : e ∈ ear.toWalk.2.2.edges) : H < ear.add := by
      refine lt_of_le_of_ne ear.base_le_add ?_
      intro hEq
      exact heH (hEq ▸ ear.edges_toWalk_subset_edgeSet_add hear)
    by_cases hxy : x = y
    · subst y
      let ear : G.Ear H := .closed hHG.le (Walk.cons e h .nil)
        ((Walk.cons_isCycle_iff e h .nil).2
          ⟨(Walk.isPath_def .nil).2 (by simp), by simp⟩)
        hx (by simp) (by simpa using heH)
      refine ⟨ear, finish ear ?_⟩
      dsimp only [ear]
      rw [Ear.toWalk_closed]
      simp
    · let ear : G.Ear H := .open hHG.le (Walk.cons e h .nil)
        ((Walk.isPath_cons e h .nil).2
          ⟨(Walk.isPath_def .nil).2 (by simp), by simpa using hxy⟩)
        hx hy hxy (by simp) (by simpa using heH)
      refine ⟨ear, finish ear ?_⟩
      dsimp only [ear]
      rw [Ear.toWalk_open]
      simp
  · obtain ⟨y, hyG, hyH⟩ := Set.not_subset.1 hvertices
    obtain ⟨x, hxH⟩ := hH.nonempty
    obtain ⟨-, ⟨p⟩⟩ := reachable_def.mp
      (hG'.1.reachable (hHG.le.vertexSet_mono hxH) hyG)
    obtain ⟨e, a, b, -, hab, haH, hbH⟩ :=
      p.exists_isLink_of_start_mem_end_notMem hxH hyH
    obtain ⟨ear, hear, -⟩ :=
      hab.exists_ear_of_mem_notMem hHG.le haH hbH (hG'.2 e)
    exact ⟨ear, hear⟩

end Graph
