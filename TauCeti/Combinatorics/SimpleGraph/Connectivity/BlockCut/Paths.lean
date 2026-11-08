/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.BlockCut.Forest
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.ArrowWalk

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

/-- Two blocks containing the same vertex `x ≠ c` are mutually reachable in the block--cut
forest without visiting the block--cut vertex represented by `c`. -/
private theorem reachableAvoiding_blockCutGraph_of_mem (B C : G.BlockVertex)
    {x : V} (hxB : x ∈ (B : Set V)) (hxC : x ∈ (C : Set V)) (c : G.CutVertex)
    (hxc : x ≠ c) :
    ReachableAvoiding G.blockCutGraph.AdjHom {(.inr c : G.BlockCutVertex)} (.inl B) (.inl C) := by
  by_cases hBC : B = C
  · subst C
    exact .refl (by simp)
  · have hBC' : (B : Set V) ≠ C := fun h ↦ hBC (Subtype.ext h)
    let w : G.CutVertex := ⟨x, B.2.isCutVertex_of_ne C.2 hBC' hxB hxC⟩
    have hwc : w ≠ c := fun h ↦ hxc (congrArg Subtype.val h)
    have hB : ReachableAvoiding G.blockCutGraph.AdjHom {(.inr c : G.BlockCutVertex)}
        (.inl B) (.inl B) := .refl (by simp)
    have hw : ReachableAvoiding G.blockCutGraph.AdjHom {(.inr c : G.BlockCutVertex)}
        (.inl B) (.inr w) :=
      hB.tail ⟨(G.blockCutGraph_adj_block_cutVertex B w).2 hxB⟩ (by simpa using hwc)
    exact hw.tail ⟨(G.blockCutGraph_adj_cutVertex_block w C).2 hxC⟩ (by simp)

/-- A walk in `G` avoiding `c` lifts to reachability between any blocks containing its endpoints,
while avoiding the cut-vertex node represented by `c` in the block--cut forest. -/
private theorem Walk.reachableAvoiding_blockCutGraph [Finite V] {a b : V} (p : G.Walk a b)
    (B C : G.BlockVertex) (haB : a ∈ (B : Set V)) (hbC : b ∈ (C : Set V))
    (c : G.CutVertex) (hp : (c : V) ∉ p.support) :
    ReachableAvoiding G.blockCutGraph.AdjHom {(.inr c : G.BlockCutVertex)} (.inl B) (.inl C) := by
  induction p generalizing B with
  | nil =>
      exact reachableAvoiding_blockCutGraph_of_mem B C haB hbC c
        (fun h ↦ hp (h ▸ Walk.start_mem_support _))
  | @cons a z b h p ih =>
      obtain ⟨D, hD, had⟩ := h.exists_isBlock_superset_pair
      let D' : G.BlockVertex := ⟨D, hD⟩
      have haD : a ∈ (D' : Set V) := had (by simp)
      have hzD : z ∈ (D' : Set V) := had (by simp)
      have hac : a ≠ (c : V) := fun hac ↦ hp (hac ▸ Walk.start_mem_support _)
      have hp' : (c : V) ∉ p.support := fun hcp ↦ hp (by simp [hcp])
      exact (reachableAvoiding_blockCutGraph_of_mem B D' haB haD c hac).trans
        (ih D' hzD hbC hp')

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
    obtain ⟨q, hq⟩ := reachableAvoiding_adjHom_iff.mp h
    obtain ⟨p, hp⟩ := q.exists_avoiding_of_blockCutGraph
      (fun hcq ↦ hq _ hcq (by simp)) haB hbC hac hbc
    exact reachableAvoiding_adjHom_iff.mpr ⟨p, fun v hv hvc ↦ hp (hvc ▸ hv)⟩
  · intro h
    obtain ⟨p, hp⟩ := reachableAvoiding_adjHom_iff.mp h
    exact p.reachableAvoiding_blockCutGraph B C haB hbC c (fun hcp ↦ hp _ hcp (by simp))

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
theorem exists_isPath_avoiding_blockCutGraph_iff [Finite V] (B C : G.BlockVertex)
    (c : G.CutVertex) {a b : V} (haB : a ∈ (B : Set V)) (hbC : b ∈ (C : Set V))
    (hac : a ≠ c) (hbc : b ≠ c) :
    (∃ q : G.blockCutGraph.Walk (.inl B) (.inl C),
        q.IsPath ∧ (.inr c : G.BlockCutVertex) ∉ q.support) ↔
      ∃ p : G.Walk a b, p.IsPath ∧ (c : V) ∉ p.support := by
  classical
  constructor
  · rintro ⟨q, -, hqc⟩
    have h : ReachableAvoiding G.blockCutGraph.AdjHom {(.inr c : G.BlockCutVertex)}
        (.inl B) (.inl C) := reachableAvoiding_adjHom_iff.mpr
      ⟨q, fun v hv hvc ↦ hqc (hvc ▸ hv)⟩
    obtain ⟨p, hp⟩ := reachableAvoiding_adjHom_iff.mp
      ((reachableAvoiding_blockCutGraph_iff B C c haB hbC hac hbc).mp h)
    exact ⟨p.bypass, p.bypass_isPath,
      fun hcp ↦ hp _ (p.support_bypass_subset_support hcp) (by simp)⟩
  · rintro ⟨p, -, hpc⟩
    have h : ReachableAvoiding G.AdjHom {(c : V)} a b := reachableAvoiding_adjHom_iff.mpr
      ⟨p, fun v hv hvc ↦ hpc (hvc ▸ hv)⟩
    obtain ⟨q, hq⟩ := reachableAvoiding_adjHom_iff.mp
      ((reachableAvoiding_blockCutGraph_iff B C c haB hbC hac hbc).mpr h)
    exact ⟨q.bypass, q.bypass_isPath,
      fun hcq ↦ hq _ (q.support_bypass_subset_support hcq) (by simp)⟩

/-- A cut vertex lies on every walk between vertices in two blocks exactly when its block--cut
vertex lies on every walk between the corresponding block vertices. Thus separation in the
original graph is detected by the unique path in the block--cut forest. -/
theorem CutVertex.forall_mem_support_iff_blockCutGraph [Finite V] (c : G.CutVertex)
    (B C : G.BlockVertex) {a b : V} (haB : a ∈ (B : Set V)) (hbC : b ∈ (C : Set V))
    (hac : a ≠ c) (hbc : b ≠ c) :
    (∀ p : G.Walk a b, (c : V) ∈ p.support) ↔
      ∀ q : G.blockCutGraph.Walk (.inl B) (.inl C),
        (.inr c : G.BlockCutVertex) ∈ q.support := by
  constructor
  · intro hG q
    by_contra hcq
    have hBCavoid : ReachableAvoiding G.blockCutGraph.AdjHom
        {(.inr c : G.BlockCutVertex)} (.inl B) (.inl C) :=
      reachableAvoiding_adjHom_iff.mpr ⟨q, fun v hv hvc ↦ hcq (hvc ▸ hv)⟩
    obtain ⟨p, hp⟩ := reachableAvoiding_adjHom_iff.mp
      ((reachableAvoiding_blockCutGraph_iff B C c haB hbC hac hbc).mp hBCavoid)
    exact hp _ (hG p) (by simp)
  · intro hBC p
    by_contra hcp
    have hGavoid : ReachableAvoiding G.AdjHom {(c : V)} a b :=
      reachableAvoiding_adjHom_iff.mpr ⟨p, fun v hv hvc ↦ hcp (hvc ▸ hv)⟩
    obtain ⟨q, hq⟩ := reachableAvoiding_adjHom_iff.mp
      ((reachableAvoiding_blockCutGraph_iff B C c haB hbC hac hbc).mpr hGavoid)
    exact hq _ (hBC q) (by simp)

end SimpleGraph
