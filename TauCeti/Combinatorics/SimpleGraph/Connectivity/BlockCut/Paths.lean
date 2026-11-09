/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.BlockCut.Forest
public import TauCeti.Combinatorics.SimpleGraph.Paths

/-!
# Paths through the block--cut forest

For a finite simple graph, the block--cut forest records exactly how its cut vertices separate
its blocks. Given vertices `a` and `b` in blocks `B` and `C`, respectively, and a cut vertex `c`
different from both endpoints, there is a walk from `a` to `b` avoiding `c` precisely when there
is a walk in the block--cut forest from `B` to `C` avoiding the block--cut vertex represented by
`c`. Equivalently, every original walk passes through `c` precisely when every block--cut walk
passes through that vertex.

This correspondence lets separation questions in the original graph be read from the unique
paths in each tree component of the block--cut forest.

The results follow R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173,
Springer, 2017, Lemma 3.1.4.
-/

public section

open Set
open TauCeti

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- **Block--cut path correspondence.** For vertices `a` and `b` in blocks `B` and `C`, neither
equal to a cut vertex `c`, the original graph has an `a`--`b` walk avoiding `c` exactly when the
block--cut forest has a `B`--`C` walk avoiding its vertex corresponding to `c`. -/
theorem reachableAvoiding_blockCutGraph_iff [Finite V] (B C : G.BlockVertex)
    (c : G.CutVertex) {a b : V} (haB : a ∈ (B : Set V)) (hbC : b ∈ (C : Set V))
    (hac : a ≠ c) (hbc : b ≠ c) :
    ReachableAvoiding G.blockCutGraph.AdjHom {(.inr c : G.BlockCutVertex)} (.inl B) (.inl C) ↔
      ReachableAvoiding G.AdjHom {(c : V)} a b := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := reachableAvoiding_singleton_adjHom_iff.mp h
    obtain ⟨p, hp⟩ := q.exists_walk_notMem_support_of_blockCutGraph
      hq haB hbC hac hbc
    exact reachableAvoiding_singleton_adjHom_iff.mpr ⟨p, hp⟩
  · intro h
    obtain ⟨p, hp⟩ := reachableAvoiding_singleton_adjHom_iff.mp h
    simpa using p.reachableAvoiding_blockCutGraph B C haB hbC {c} (by simpa using hp)

/-- Deleting a cut vertex disconnects two chosen original vertices exactly when deleting its
block--cut vertex disconnects blocks containing them. This is the induced-subgraph form of
`reachableAvoiding_blockCutGraph_iff`. -/
theorem reachable_induce_compl_blockCutGraph_iff [Finite V] (B C : G.BlockVertex)
    (c : G.CutVertex) {a b : V} (haB : a ∈ (B : Set V)) (hbC : b ∈ (C : Set V))
    (hac : a ≠ c) (hbc : b ≠ c) :
    (G.blockCutGraph.induce {(.inr c : G.BlockCutVertex)}ᶜ).Reachable
        ⟨.inl B, by simp⟩ ⟨.inl C, by simp⟩ ↔
      (G.induce {(c : V)}ᶜ).Reachable ⟨a, by simpa⟩ ⟨b, by simpa⟩ := by
  rw [reachable_induce_compl_iff, reachable_induce_compl_iff]
  exact reachableAvoiding_blockCutGraph_iff B C c haB hbC hac hbc

/-- The block--cut path correspondence can be witnessed by simple paths on both sides. -/
theorem exists_isPath_notMem_support_blockCutGraph_iff [Finite V] (B C : G.BlockVertex)
    (c : G.CutVertex) {a b : V} (haB : a ∈ (B : Set V)) (hbC : b ∈ (C : Set V))
    (hac : a ≠ c) (hbc : b ≠ c) :
    (∃ q : G.blockCutGraph.Walk (.inl B) (.inl C),
        q.IsPath ∧ (.inr c : G.BlockCutVertex) ∉ q.support) ↔
      ∃ p : G.Walk a b, p.IsPath ∧ (c : V) ∉ p.support := by
  classical
  rw [exists_isPath_notMem_support_iff, exists_isPath_notMem_support_iff,
    ← reachableAvoiding_singleton_adjHom_iff, ← reachableAvoiding_singleton_adjHom_iff]
  exact reachableAvoiding_blockCutGraph_iff B C c haB hbC hac hbc

/-- A cut vertex lies on every walk between vertices in two blocks exactly when its block--cut
vertex lies on every walk between the corresponding block vertices. Thus separation in the
original graph is detected by the unique path in the block--cut forest. -/
theorem CutVertex.forall_mem_support_iff_blockCutGraph [Finite V] (c : G.CutVertex)
    (B C : G.BlockVertex) {a b : V} (haB : a ∈ (B : Set V)) (hbC : b ∈ (C : Set V))
    (hac : a ≠ c) (hbc : b ≠ c) :
    (∀ p : G.Walk a b, (c : V) ∈ p.support) ↔
      ∀ q : G.blockCutGraph.Walk (.inl B) (.inl C),
        (.inr c : G.BlockCutVertex) ∈ q.support := by
  classical
  have h := reachableAvoiding_blockCutGraph_iff B C c haB hbC hac hbc
  rw [reachableAvoiding_singleton_adjHom_iff, reachableAvoiding_singleton_adjHom_iff] at h
  simpa only [not_exists, not_not] using h.not.symm

end SimpleGraph
