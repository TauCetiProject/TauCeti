/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.BlockCut.Basic
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.ArrowWalk
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The block--cut forest

This file proves that the block--cut incidence graph `G.blockCutGraph` of a simple graph is a
forest, and that its connected components correspond to those of `G`.

* `SimpleGraph.blockCutGraph_isAcyclic`: the block--cut graph is acyclic.  This needs no
  finiteness: an edge between a block `B` and a cut vertex `c` is a bridge, because a walk of the
  block--cut graph from `c` back to `B` avoiding that edge would give a walk of `G` from another
  block through `c` to `B` avoiding `c`, which `SimpleGraph.IsBlock.mem_support_of_ne` forbids.
* `SimpleGraph.blockCutVertexComponent`: each vertex of the block--cut graph determines a
  connected component of `G`, namely the component containing the block or the cut vertex.
* `SimpleGraph.blockCutGraph_reachable_iff`: for a finite vertex type, two vertices of the
  block--cut graph are reachable from each other exactly when they determine the same component
  of `G`.  Finiteness ensures that every vertex and every edge of `G` lies in a block.
* `SimpleGraph.Walk.reachableAvoiding_blockCutGraph`: a walk in `G` avoiding a set of cut vertices
  lifts to reachability in the block--cut graph avoiding the corresponding cut-vertex nodes.
* `SimpleGraph.Walk.exists_walk_notMem_support_of_blockCutGraph`: a block--cut walk avoiding a
  cut-vertex node projects to a walk in `G` avoiding that cut vertex.
* `SimpleGraph.blockCutComponentEquiv`: hence the components of the block--cut graph and of `G`
  are in canonical bijection.
* `SimpleGraph.blockCutGraph_isTree_iff`: the block--cut graph of a finite graph is a tree
  exactly when the graph is connected.

The results follow R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173,
Springer, 2017, Lemma 3.1.4.
-/

public section

open Set
open TauCeti

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-! ### Acyclicity -/

/-- The original vertices carried by a vertex of the block--cut graph: the vertices of a block,
or the cut vertex itself. -/
private def blockCutCarrier : G.BlockCutVertex → Set V
  | .inl B => B
  | .inr v => {(v : V)}

/-- A block carries its own vertices. -/
@[simp]
private theorem blockCutCarrier_inl (B : G.BlockVertex) :
    blockCutCarrier (.inl B) = (B : Set V) :=
  rfl

/-- A cut vertex carries only itself. -/
@[simp]
private theorem blockCutCarrier_inr (v : G.CutVertex) :
    blockCutCarrier (.inr v) = {(v : V)} :=
  rfl

/-- A walk of the block--cut graph whose cut vertices all differ from `c` projects to a walk of
`G` avoiding `c`, between any carried vertices of its endpoints other than `c`. -/
private theorem exists_walk_notMem_support_of_blockCutGraph_walk {x y : G.BlockCutVertex}
    (q : G.blockCutGraph.Walk x y) {c : V}
    (hq : ∀ w : G.CutVertex, (.inr w : G.BlockCutVertex) ∈ q.support → (w : V) ≠ c)
    {a b : V} (ha : a ∈ blockCutCarrier x) (hb : b ∈ blockCutCarrier y) (hac : a ≠ c)
    (hbc : b ≠ c) : ∃ p : G.Walk a b, c ∉ p.support := by
  induction q generalizing a with
  | nil =>
    rename_i x
    rcases x with B | w
    · rw [blockCutCarrier_inl] at ha hb
      obtain ⟨p, hp⟩ := exists_walk_forall_mem_support_mem_and_ne B.2.connected
        B.2.not_isCutVertex ha hb hac hbc
      exact ⟨p, fun h ↦ (hp c h).2 rfl⟩
    · rw [blockCutCarrier_inr, Set.mem_singleton_iff] at ha hb
      subst ha hb
      exact ⟨.nil, by simpa using hac.symm⟩
  | cons h q ih =>
    rename_i x z y
    have hq' : ∀ w : G.CutVertex, (.inr w : G.BlockCutVertex) ∈ q.support → (w : V) ≠ c :=
      fun w hw ↦ hq w (List.mem_cons_of_mem _ hw)
    rcases x with B | w <;> rcases z with C | w'
    · simp at h
    · -- From a block to one of its cut vertices: walk inside the block to it.
      have hwc : (w' : V) ≠ c := hq w' (List.mem_cons_of_mem _ q.start_mem_support)
      rw [blockCutCarrier_inl] at ha
      obtain ⟨r, hr⟩ := exists_walk_forall_mem_support_mem_and_ne B.2.connected
        B.2.not_isCutVertex ha ((G.blockCutGraph_adj_block_cutVertex B w').1 h) hac hwc
      obtain ⟨p, hp⟩ := ih hq' (a := w') (blockCutCarrier_inr w' ▸ Set.mem_singleton _) hb hwc
      refine ⟨r.append p, fun hc ↦ ?_⟩
      rcases (Walk.mem_support_append_iff r p).mp hc with hc | hc
      · exact (hr c hc).2 rfl
      · exact hp hc
    · -- From a cut vertex to a block containing it: the cut vertex is carried by the block.
      rw [blockCutCarrier_inr, Set.mem_singleton_iff] at ha
      subst ha
      exact ih hq' (blockCutCarrier_inl C ▸ (G.blockCutGraph_adj_cutVertex_block w C).1 h) hb hac
    · simp at h

/-- A walk between two block vertices in the block--cut graph that avoids a cut vertex projects
to a walk between any chosen vertices of the blocks other than that cut vertex, while avoiding
the corresponding original vertex. -/
theorem Walk.exists_walk_notMem_support_of_blockCutGraph {B C : G.BlockVertex}
    (q : G.blockCutGraph.Walk (.inl B) (.inl C)) {c : G.CutVertex} {a b : V}
    (hq : (.inr c : G.BlockCutVertex) ∉ q.support) (ha : a ∈ (B : Set V))
    (hb : b ∈ (C : Set V)) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ p : G.Walk a b, (c : V) ∉ p.support := by
  apply exists_walk_notMem_support_of_blockCutGraph_walk q
  · intro w hw hwc
    have : w = c := Subtype.ext hwc
    exact hq (this ▸ hw)
  · exact blockCutCarrier_inl B ▸ ha
  · exact blockCutCarrier_inl C ▸ hb
  · exact hac
  · exact hbc

/-- **The block--cut graph is a forest.** No finiteness is needed. -/
theorem blockCutGraph_isAcyclic : G.blockCutGraph.IsAcyclic := by
  classical
  -- Every edge joins a block `B` to a cut vertex `c ∈ B`; it suffices that it is a bridge.
  have key (B : G.BlockVertex) (c : G.CutVertex) (hcB : (c : V) ∈ (B : Set V)) :
      G.blockCutGraph.IsBridge s(.inr c, .inl B) := by
    rw [isBridge_iff_forall_walk_mem_edges]
    intro p
    by_contra hp
    have hp' : s(.inr c, .inl B) ∉ p.bypass.edges := fun h ↦ hp (p.edges_bypass_subset_edges h)
    -- The bypass leaves `c` for a block `C` and returns to `B` without revisiting `c`.
    cases hpath : p.bypass with
    | cons h q =>
      rename_i z
      have hP := p.bypass_isPath
      rw [hpath, Walk.cons_isPath_iff] at hP
      rw [hpath, Walk.edges_cons] at hp'
      rcases z with C | w
      · have hcC : (c : V) ∈ (C : Set V) := (G.blockCutGraph_adj_cutVertex_block c C).1 h
        have hCB : (C : Set V) ≠ B := fun hCB ↦ hp' (by simp [Subtype.ext hCB])
        obtain ⟨a, haC, hca⟩ := C.2.exists_adj_of_ne B.2 hCB hcC hcB
        obtain ⟨b, hbB, hcb⟩ := B.2.exists_adj_of_ne C.2 hCB.symm hcB hcC
        have hq : ∀ w : G.CutVertex, (.inr w : G.BlockCutVertex) ∈ q.support →
            (w : V) ≠ c := fun w hw hwc ↦ hP.2 (by rwa [← Subtype.ext hwc])
        obtain ⟨r, hr⟩ := exists_walk_notMem_support_of_blockCutGraph_walk q hq
          (a := a) (b := b) (blockCutCarrier_inl C ▸ haC) (blockCutCarrier_inl B ▸ hbB) hca.ne'
          hcb.ne'
        exact hr (C.2.mem_support_of_ne B.2 hCB hcC hcB haC hbB r)
      · simp at h
  rw [isAcyclic_iff_forall_adj_isBridge]
  rintro (B | v) (C | w) h
  · simp at h
  · rw [Sym2.eq_swap]
    exact key B w ((G.blockCutGraph_adj_block_cutVertex B w).1 h)
  · exact key C v ((G.blockCutGraph_adj_cutVertex_block v C).1 h)
  · simp at h

/-! ### Components -/

variable (G) in
/-- The connected component of `G` determined by a vertex of the block--cut graph: the component
containing the vertices of a block, or the component of a cut vertex. -/
noncomputable def blockCutVertexComponent : G.BlockCutVertex → G.ConnectedComponent
  | .inl B => G.connectedComponentMk B.2.nonempty.some
  | .inr v => G.connectedComponentMk v

/-- A block determines the component of each of its vertices. -/
theorem blockCutVertexComponent_block_of_mem (B : G.BlockVertex) {x : V}
    (hx : x ∈ (B : Set V)) :
    G.blockCutVertexComponent (.inl B) = G.connectedComponentMk x := by
  rw [blockCutVertexComponent, ConnectedComponent.eq]
  exact (B.2.connected.preconnected ⟨_, B.2.nonempty.some_mem⟩ ⟨x, hx⟩).map
    (Embedding.induce _).toHom

/-- A cut vertex determines its own component. -/
@[simp]
theorem blockCutVertexComponent_cutVertex (v : G.CutVertex) :
    G.blockCutVertexComponent (.inr v) = G.connectedComponentMk v :=
  (rfl)

/-- Adjacent vertices of the block--cut graph determine the same component of `G`. -/
theorem blockCutVertexComponent_eq_of_adj {x y : G.BlockCutVertex}
    (h : G.blockCutGraph.Adj x y) :
    G.blockCutVertexComponent x = G.blockCutVertexComponent y := by
  rcases x with B | v <;> rcases y with C | w
  · simp at h
  · exact blockCutVertexComponent_block_of_mem B ((G.blockCutGraph_adj_block_cutVertex B w).1 h)
  · exact (blockCutVertexComponent_block_of_mem C
      ((G.blockCutGraph_adj_cutVertex_block v C).1 h)).symm
  · simp at h

/-- Reachable vertices of the block--cut graph determine the same component of `G`. -/
theorem Reachable.blockCutVertexComponent_eq {x y : G.BlockCutVertex}
    (h : G.blockCutGraph.Reachable x y) :
    G.blockCutVertexComponent x = G.blockCutVertexComponent y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h _ ih => exact (blockCutVertexComponent_eq_of_adj h).trans ih

/-- Two blocks sharing a vertex outside a set of cut vertices are mutually reachable in the
block--cut graph without visiting the corresponding cut-vertex nodes. -/
private theorem reachableAvoiding_blockCutGraph_block_block_of_mem (B C : G.BlockVertex) {x : V}
    (hxB : x ∈ (B : Set V)) (hxC : x ∈ (C : Set V)) (S : Set G.CutVertex)
    (hxS : ∀ c ∈ S, (c : V) ≠ x) :
    ReachableAvoiding G.blockCutGraph.AdjHom (Sum.inr '' S) (.inl B) (.inl C) := by
  by_cases hBC : (B : Set V) = C
  · rw [Subtype.ext hBC]
    exact .refl (by simp)
  · let c : G.CutVertex := ⟨x, B.2.isCutVertex_of_ne C.2 hBC hxB hxC⟩
    have hcS : (.inr c : G.BlockCutVertex) ∉ Sum.inr '' S := by
      rintro ⟨s, hs, hsc⟩
      apply hxS s hs
      simpa [c] using congrArg Subtype.val (Sum.inr.inj hsc)
    exact ((ReachableAvoiding.refl (by simp)).tail
      ⟨(G.blockCutGraph_adj_block_cutVertex B c).2 hxB⟩ hcS).tail
      ⟨(G.blockCutGraph_adj_cutVertex_block c C).2 hxC⟩ (by simp)

/-- Two blocks sharing a vertex are reachable from each other in the block--cut graph: they are
equal, or the shared vertex is a cut vertex adjacent to both. -/
theorem blockCutGraph_reachable_block_block_of_mem (B C : G.BlockVertex) {x : V}
    (hxB : x ∈ (B : Set V)) (hxC : x ∈ (C : Set V)) :
    G.blockCutGraph.Reachable (.inl B) (.inl C) :=
  (reachableAvoiding_blockCutGraph_block_block_of_mem B C hxB hxC ∅ (by simp)).reachable

/-- In a finite graph, a walk of `G` avoiding a set of cut vertices lifts to reachability between
any blocks containing its endpoints, while avoiding the corresponding cut-vertex nodes. -/
theorem Walk.reachableAvoiding_blockCutGraph [Finite V] {x y : V} (p : G.Walk x y)
    (B C : G.BlockVertex) (hxB : x ∈ (B : Set V)) (hyC : y ∈ (C : Set V))
    (S : Set G.CutVertex) (hp : ∀ c ∈ S, (c : V) ∉ p.support) :
    ReachableAvoiding G.blockCutGraph.AdjHom (Sum.inr '' S) (.inl B) (.inl C) := by
  induction p generalizing B with
  | nil =>
      exact reachableAvoiding_blockCutGraph_block_block_of_mem B C hxB hyC S fun c hc hcx ↦
        hp c hc (by simpa using hcx)
  | cons h _ ih =>
    -- Pass through the block containing the first edge.
    obtain ⟨D, hD, hxzD⟩ := h.exists_isBlock_superset_pair
    exact (reachableAvoiding_blockCutGraph_block_block_of_mem B ⟨D, hD⟩ hxB
      (hxzD (by simp)) S fun c hc hcx ↦ hp c hc (by simp [hcx])).trans
      (ih ⟨D, hD⟩ (hxzD (by simp)) hyC fun c hc hcp ↦ hp c hc (by simp [hcp]))

/-- In a finite graph, if `x` and `y` are reachable in `G`, then any block containing `x` and any
block containing `y` are reachable in the block--cut graph. -/
theorem Reachable.blockCutGraph_reachable_block_block [Finite V] {x y : V} (h : G.Reachable x y)
    (B C : G.BlockVertex) (hxB : x ∈ (B : Set V)) (hyC : y ∈ (C : Set V)) :
    G.blockCutGraph.Reachable (.inl B) (.inl C) := by
  obtain ⟨p⟩ := h
  exact (p.reachableAvoiding_blockCutGraph B C hxB hyC ∅ (by simp)).reachable

/-- In a finite graph, every vertex of the block--cut graph is reachable from a block containing
a vertex of the component it determines. -/
private theorem exists_blockCutGraph_reachable_block [Finite V] (x : G.BlockCutVertex) :
    ∃ B : G.BlockVertex, ∃ a ∈ (B : Set V), G.blockCutGraph.Reachable x (.inl B) ∧
      G.blockCutVertexComponent x = G.connectedComponentMk a := by
  rcases x with B | v
  · exact ⟨B, _, B.2.nonempty.some_mem, .rfl,
      blockCutVertexComponent_block_of_mem B B.2.nonempty.some_mem⟩
  · obtain ⟨D, hD, hvD⟩ := G.exists_isBlock_mem v
    have h : G.blockCutGraph.Adj (.inr v) (.inl ⟨D, hD⟩) :=
      (G.blockCutGraph_adj_cutVertex_block v ⟨D, hD⟩).2 hvD
    exact ⟨⟨D, hD⟩, v, hvD, h.reachable, blockCutVertexComponent_cutVertex v⟩

/-- In a finite graph, two vertices of the block--cut graph are reachable from each other exactly
when they determine the same connected component of `G`. -/
theorem blockCutGraph_reachable_iff [Finite V] {x y : G.BlockCutVertex} :
    G.blockCutGraph.Reachable x y ↔
      G.blockCutVertexComponent x = G.blockCutVertexComponent y := by
  refine ⟨Reachable.blockCutVertexComponent_eq, fun h ↦ ?_⟩
  obtain ⟨B, a, haB, hxB, hx⟩ := exists_blockCutGraph_reachable_block x
  obtain ⟨C, b, hbC, hyC, hy⟩ := exists_blockCutGraph_reachable_block y
  have hab : G.Reachable a b := ConnectedComponent.exact (hx.symm.trans (h.trans hy))
  exact hxB.trans ((hab.blockCutGraph_reachable_block_block B C haB hbC).trans hyC.symm)

/-- **Components of the block--cut forest.** For a finite graph, the connected components of the
block--cut graph correspond to those of the graph. -/
noncomputable def blockCutComponentEquiv [Finite V] :
    G.blockCutGraph.ConnectedComponent ≃ G.ConnectedComponent :=
  Equiv.ofBijective
    (ConnectedComponent.lift G.blockCutVertexComponent fun _ _ p _ ↦
      p.reachable.blockCutVertexComponent_eq) <| by
    refine ⟨fun X Y ↦ ConnectedComponent.ind₂ (fun x y h ↦ ?_) X Y, fun X ↦ X.ind fun v ↦ ?_⟩
    · exact ConnectedComponent.sound (blockCutGraph_reachable_iff.2 h)
    · obtain ⟨D, hD, hvD⟩ := G.exists_isBlock_mem v
      exact ⟨G.blockCutGraph.connectedComponentMk (.inl ⟨D, hD⟩),
        blockCutVertexComponent_block_of_mem ⟨D, hD⟩ hvD⟩

/-- `blockCutComponentEquiv` sends the component of a vertex of the block--cut graph to the
component of `G` that the vertex determines. -/
@[simp]
theorem blockCutComponentEquiv_connectedComponentMk [Finite V] (x : G.BlockCutVertex) :
    G.blockCutComponentEquiv (G.blockCutGraph.connectedComponentMk x) =
      G.blockCutVertexComponent x :=
  (rfl)

/-- The inverse of `blockCutComponentEquiv` sends the component of a vertex to the component of
any block containing it. -/
theorem blockCutComponentEquiv_symm_connectedComponentMk_of_mem [Finite V] (B : G.BlockVertex)
    {v : V} (hv : v ∈ (B : Set V)) :
    G.blockCutComponentEquiv.symm (G.connectedComponentMk v) =
      G.blockCutGraph.connectedComponentMk (.inl B) := by
  rw [Equiv.symm_apply_eq, blockCutComponentEquiv_connectedComponentMk,
    blockCutVertexComponent_block_of_mem B hv]

/-- A finite graph has a connected block--cut graph exactly when it is connected. -/
theorem blockCutGraph_connected_iff [Finite V] : G.blockCutGraph.Connected ↔ G.Connected := by
  rw [← card_connectedComponent_eq_one_iff, ← card_connectedComponent_eq_one_iff,
    Nat.card_congr G.blockCutComponentEquiv]

/-- **The block--cut tree.** The block--cut graph of a finite graph is a tree exactly when the
graph is connected. -/
theorem blockCutGraph_isTree_iff [Finite V] : G.blockCutGraph.IsTree ↔ G.Connected := by
  rw [isTree_iff, blockCutGraph_connected_iff, and_iff_left blockCutGraph_isAcyclic]

end SimpleGraph
