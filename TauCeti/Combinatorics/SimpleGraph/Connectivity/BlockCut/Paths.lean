/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.BlockCut.Forest

/-!
# Separation along paths in the block--cut forest

The block--cut forest records exactly how cut vertices separate the original graph. If blocks
`B` and `C` contain vertices `x` and `y`, respectively, then an `x`--`y` walk avoiding a cut
vertex `c` exists exactly when a walk from `B` to `C` in the block--cut forest avoids the vertex
corresponding to `c`.

Consequently, `c` belongs to every `x`--`y` walk exactly when its block--cut vertex belongs to
every walk between `B` and `C`. Since the block--cut graph is a forest, it is enough to inspect
its unique path. This is the path correspondence that turns the block--cut forest into a usable
description of vertex separation in the original graph.
-/

public section

open Set

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- Two blocks containing the same vertex `x` can be joined in the block--cut graph without
visiting any specified different cut vertex `c`. -/
private theorem exists_blockCutGraph_walk_notMem_support_of_mem
    (B C : G.BlockVertex) {x : V} (hxB : x ∈ (B : Set V)) (hxC : x ∈ (C : Set V))
    (c : G.CutVertex) (hxc : x ≠ c) :
    ∃ q : G.blockCutGraph.Walk (.inl B) (.inl C),
      (.inr c : G.BlockCutVertex) ∉ q.support := by
  by_cases hBC : (B : Set V) = C
  · have : B = C := Subtype.ext hBC
    subst C
    exact ⟨.nil, by simp⟩
  · let w : G.CutVertex := ⟨x, B.2.isCutVertex_of_ne C.2 hBC hxB hxC⟩
    have hB : G.blockCutGraph.Adj (.inl B) (.inr w) :=
      (G.blockCutGraph_adj_block_cutVertex B w).2 hxB
    have hC : G.blockCutGraph.Adj (.inr w) (.inl C) :=
      (G.blockCutGraph_adj_cutVertex_block w C).2 hxC
    refine ⟨.cons hB (.cons hC .nil), ?_⟩
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      Sum.inr.injEq, Sum.inr_ne_inl, false_or]
    rintro (hcw | h)
    · exact hxc (congrArg Subtype.val hcw.symm)
    · exact h.elim

/-- An original walk avoiding `c` induces a walk between any blocks containing its endpoints that
avoids the block--cut vertex corresponding to `c`. -/
private theorem exists_blockCutGraph_walk_notMem_support_of_walk [Finite V]
    {x y : V} (p : G.Walk x y) (B C : G.BlockVertex) (hxB : x ∈ (B : Set V))
    (hyC : y ∈ (C : Set V)) (c : G.CutVertex) (hcp : (c : V) ∉ p.support) :
    ∃ q : G.blockCutGraph.Walk (.inl B) (.inl C),
      (.inr c : G.BlockCutVertex) ∉ q.support := by
  induction p generalizing B with
  | nil =>
      apply exists_blockCutGraph_walk_notMem_support_of_mem B C hxB hyC c
      intro hxc
      exact hcp (by simp [hxc])
  | cons h p ih =>
      simp only [Walk.support_cons, List.mem_cons, not_or] at hcp
      obtain ⟨D, hD, hxD⟩ := h.exists_isBlock_superset_pair
      let D' : G.BlockVertex := ⟨D, hD⟩
      obtain ⟨q, hq⟩ := exists_blockCutGraph_walk_notMem_support_of_mem B D' hxB
        (hxD (by simp)) c (Ne.symm hcp.1)
      obtain ⟨r, hr⟩ := ih D' (hxD (by simp)) hyC hcp.2
      exact ⟨q.append r, by simpa only [Walk.mem_support_append_iff, not_or] using ⟨hq, hr⟩⟩

/-- Walks between endpoint blocks avoid a cut vertex in the block--cut forest exactly when walks
between the corresponding original vertices avoid that cut vertex. -/
theorem exists_blockCutGraph_walk_notMem_support_iff [Finite V]
    (B C : G.BlockVertex) {x y : V} (hxB : x ∈ (B : Set V)) (hyC : y ∈ (C : Set V))
    (c : G.CutVertex) (hxc : x ≠ c) (hyc : y ≠ c) :
    (∃ q : G.blockCutGraph.Walk (.inl B) (.inl C),
        (.inr c : G.BlockCutVertex) ∉ q.support) ↔
      ∃ p : G.Walk x y, (c : V) ∉ p.support := by
  constructor
  · rintro ⟨q, hq⟩
    exact q.exists_walk_notMem_support_of_blockCutGraph_walk
      (fun w hw hwc ↦ hq (by simpa [Subtype.ext hwc] using hw)) hxB hyC hxc hyc
  · rintro ⟨p, hp⟩
    exact exists_blockCutGraph_walk_notMem_support_of_walk p B C hxB hyC c hp

/-- Mandatory occurrence of a cut vertex agrees in the original graph and the block--cut graph:
it belongs to every walk on one side precisely when it belongs to every walk on the other. -/
theorem forall_blockCutGraph_walk_mem_support_iff [Finite V]
    (B C : G.BlockVertex) {x y : V} (hxB : x ∈ (B : Set V)) (hyC : y ∈ (C : Set V))
    (c : G.CutVertex) (hxc : x ≠ c) (hyc : y ≠ c) :
    (∀ q : G.blockCutGraph.Walk (.inl B) (.inl C),
        (.inr c : G.BlockCutVertex) ∈ q.support) ↔
      ∀ p : G.Walk x y, (c : V) ∈ p.support := by
  classical
  simpa only [not_exists, not_not] using
    not_congr (exists_blockCutGraph_walk_notMem_support_iff B C hxB hyC c hxc hyc)

/-- On the unique path between two blocks of the block--cut forest, the cut-vertex node `c`
occurs exactly when `c` belongs to every walk between corresponding original vertices. -/
theorem Walk.mem_support_cutVertex_iff [Finite V]
    {B C : G.BlockVertex} (q : G.blockCutGraph.Walk (.inl B) (.inl C)) (hq : q.IsPath)
    {x y : V} (hxB : x ∈ (B : Set V)) (hyC : y ∈ (C : Set V))
    (c : G.CutVertex) (hxc : x ≠ c) (hyc : y ≠ c) :
    (.inr c : G.BlockCutVertex) ∈ q.support ↔
      ∀ p : G.Walk x y, (c : V) ∈ p.support := by
  classical
  rw [← forall_blockCutGraph_walk_mem_support_iff B C hxB hyC c hxc hyc]
  refine ⟨fun hc r ↦ ?_, fun h ↦ h q⟩
  have hpath : (⟨q, hq⟩ : G.blockCutGraph.Path (.inl B) (.inl C)) = r.toPath :=
    G.blockCutGraph_isAcyclic.subsingleton_path _ _ |>.elim _ _
  have hwalk : q = (r.toPath : G.blockCutGraph.Walk (.inl B) (.inl C)) :=
    congrArg Subtype.val hpath
  rw [hwalk] at hc
  exact r.support_toPath_subset_support hc

end SimpleGraph
