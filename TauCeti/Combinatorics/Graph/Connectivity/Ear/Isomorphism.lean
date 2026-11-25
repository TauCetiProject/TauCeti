/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Basic
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Isomorphism

/-!
# Transporting ear decompositions along multigraph isomorphisms

A multigraph isomorphism `f : G.Iso H` transports ears, initial stages, and ear decompositions of
subgraphs of `G` to those of the corresponding subgraphs of `H`. Edges are transported
individually along `f.edgeEquiv`, so loops, parallel edges, and the kind of every ear are
preserved. The transport sends each stage graph to its image under `Graph.Iso.mapSubgraph` and
each ear walk to its image under `Graph.Iso.mapWalk`; transporting back along the inverse
isomorphism recovers the original data. Consequently the existence of ear decompositions, of open
ear decompositions, and of vertex-started ear decompositions is invariant under isomorphism.

## Main definitions

* `Graph.Iso.mapEar`: transport of an ear over a subgraph.
* `Graph.Iso.mapEarStart`: transport of the initial vertex or cycle.
* `Graph.Iso.mapEarDecomposition`: transport of an ear decomposition.
* `Graph.Iso.earDecompositionEquiv`: the equivalence between the ear decompositions of a subgraph
  and those of its image.

## Main statements

* `Graph.Iso.isOpen_mapEarDecomposition`, `Graph.Iso.isVertexStart_mapEarDecomposition`: transport
  preserves and reflects open and vertex-started decompositions.
* `Graph.Iso.nonempty_earDecomposition_iff`, `Graph.Iso.exists_isOpen_earDecomposition_iff`,
  `Graph.Iso.exists_isVertexStart_earDecomposition_iff`: isomorphism invariance of the existence of
  ear decompositions of the whole graph.
-/

public section

universe u v u' v'

namespace Graph.Iso

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {G : Graph α β} {H : Graph α' β'} {L : Graph α β}

/-- Transport an ear along a graph isomorphism. The transported ear is an ear over the transported
base graph, of the same kind, along the transported walk. -/
def mapEar (f : Iso G H) : (e : G.Ear L) → H.Ear (f.mapSubgraph ⟨L, e.base_le⟩)
  | @Ear.open _ _ _ _ hLG s t p hp hs ht hst hinter hedges =>
      have hs' := hLG.vertexSet_mono hs
      have ht' := hLG.vertexSet_mono ht
      .open (f.mapSubgraph_le _) (f.mapWalk (x := ⟨s, hs'⟩) (y := ⟨t, ht'⟩) p)
        ((f.isPath_mapWalk (x := ⟨s, hs'⟩) (y := ⟨t, ht'⟩) p).mpr hp)
        (by simpa using hs) (by simpa using ht)
        (fun h ↦ hst (congrArg Subtype.val (f.vertexEquiv.injective (Subtype.ext h))))
        (fun z hz hzs hzt hzL ↦ by
          obtain ⟨w, hw, rfl⟩ :=
            (f.mem_support_mapWalk_iff (x := ⟨s, hs'⟩) (y := ⟨t, ht'⟩) p z).mp hz
          refine hinter w hw (fun h ↦ hzs ?_) (fun h ↦ hzt ?_) (by simpa using hzL)
          · simp [← h]
          · simp [← h])
        (fun e he heL ↦ by
          obtain ⟨a, ha, rfl⟩ :=
            (f.mem_edges_mapWalk_iff (x := ⟨s, hs'⟩) (y := ⟨t, ht'⟩) p e).mp he
          exact hedges a ha (by simpa using heL))
  | @Ear.closed _ _ _ _ hLG s p hp hs hinter hedges =>
      have hs' := hLG.vertexSet_mono hs
      .closed (f.mapSubgraph_le _) (f.mapWalk (x := ⟨s, hs'⟩) (y := ⟨s, hs'⟩) p)
        ((f.isCycle_mapWalk (x := ⟨s, hs'⟩) p).mpr hp) (by simpa using hs)
        (fun z hz hzs hzL ↦ by
          obtain ⟨w, hw, rfl⟩ :=
            (f.mem_support_mapWalk_iff (x := ⟨s, hs'⟩) (y := ⟨s, hs'⟩) p z).mp hz
          refine hinter w hw (fun h ↦ hzs ?_) (by simpa using hzL)
          simp [← h])
        (fun e he heL ↦ by
          obtain ⟨a, ha, rfl⟩ :=
            (f.mem_edges_mapWalk_iff (x := ⟨s, hs'⟩) (y := ⟨s, hs'⟩) p e).mp he
          exact hedges a ha (by simpa using heL))

/-- Transport preserves the kind of an ear. -/
@[simp]
theorem kind_mapEar (f : Iso G H) (e : G.Ear L) : (f.mapEar e).kind = e.kind := by
  cases e <;> simp only [mapEar, Ear.kind_open, Ear.kind_closed]

/-- The walk of a transported ear is the transported walk. -/
@[simp]
theorem toWalk_mapEar (f : Iso G H) (e : G.Ear L) :
    (f.mapEar e).toWalk =
      ⟨_, _, f.mapWalk (x := ⟨e.toWalk.1, e.base_le.vertexSet_mono e.toWalk_fst_mem⟩)
        (y := ⟨e.toWalk.2.1, e.base_le.vertexSet_mono e.toWalk_snd_mem⟩) e.toWalk.2.2⟩ := by
  -- Name the endpoints and walk of `e` so that they can be matched against its constructor.
  suffices ∀ {s t : α} {p : G.Walk s t}, e.toWalk = ⟨s, t, p⟩ → ∀ (hs : s ∈ V(G)) (ht : t ∈ V(G)),
      (f.mapEar e).toWalk = ⟨_, _, f.mapWalk (x := ⟨s, hs⟩) (y := ⟨t, ht⟩) p⟩ from this rfl _ _
  intro s t p he _ _
  cases e <;> simp only [Ear.toWalk_open, Ear.toWalk_closed] at he <;> cases he <;>
    simp only [mapEar, Ear.toWalk_open, Ear.toWalk_closed]

/-- The graph traced by a transported ear is the transported traced graph. -/
@[simp]
theorem toGraph_mapEar (f : Iso G H) (e : G.Ear L) :
    (f.mapEar e).toGraph = f.mapSubgraph ⟨e.toGraph, e.toGraph_le⟩ := by
  cases e with
  | @«open» hLG s t p =>
      simp only [mapEar, Ear.toGraph_open]
      exact (f.mapSubgraph_walkGraph (x := ⟨s, _⟩) (y := ⟨t, _⟩) p).symm
  | @«closed» hLG s p =>
      simp only [mapEar, Ear.toGraph_closed]
      exact (f.mapSubgraph_walkGraph (x := ⟨s, _⟩) (y := ⟨s, _⟩) p).symm

/-- Adjoining a transported ear to the transported base gives the transport of adjoining the
ear. -/
@[simp]
theorem add_mapEar (f : Iso G H) (e : G.Ear L) :
    (f.mapEar e).add = f.mapSubgraph ⟨e.add, e.add_le⟩ := by
  simp only [Ear.add_eq_union, mapSubgraph_union, toGraph_mapEar]

/-- Transport the initial vertex or cycle of an ear decomposition along a graph isomorphism. -/
def mapEarStart (f : Iso G H) :
    (start : G.EarStart L) → H.EarStart (f.mapSubgraph ⟨L, start.le⟩)
  | .vertex v => cast (by rw [mapSubgraph_noEdge, mapVertexSet_singleton])
      (EarStart.vertex (f.vertexEquiv v))
  | @EarStart.cycle _ _ _ s p hp =>
      cast (congrArg H.EarStart (f.mapSubgraph_walkGraph (x := ⟨s, hp.start_mem⟩)
        (y := ⟨s, hp.start_mem⟩) p).symm)
        (.cycle (f.mapWalk (x := ⟨s, hp.start_mem⟩) (y := ⟨s, hp.start_mem⟩) p)
          ((f.isCycle_mapWalk (x := ⟨s, hp.start_mem⟩) p).mpr hp))

/-- A transported initial vertex is the corresponding initial vertex. -/
theorem heq_mapEarStart_vertex (f : Iso G H) (v : V(G)) :
    HEq (f.mapEarStart (.vertex v)) (EarStart.vertex (f.vertexEquiv v)) :=
  cast_heq _ _

/-- A transported initial cycle is the transported cycle. -/
theorem heq_mapEarStart_cycle (f : Iso G H) {s : α} (p : G.Walk s s) (hp : p.IsCycle) :
    HEq (f.mapEarStart (.cycle p hp))
      (EarStart.cycle (f.mapWalk (x := ⟨s, hp.start_mem⟩) (y := ⟨s, hp.start_mem⟩) p)
        ((f.isCycle_mapWalk (x := ⟨s, hp.start_mem⟩) p).mpr hp)) :=
  cast_heq _ _

/-- Transport preserves whether an initial stage is a cycle. -/
@[simp]
theorem isCycle_mapEarStart (f : Iso G H) (start : G.EarStart L) :
    (f.mapEarStart start).IsCycle ↔ start.IsCycle := by
  cases start with
  | vertex v =>
      rw [EarStart.isCycle_iff_of_heq (by rw [mapSubgraph_noEdge, mapVertexSet_singleton])
        (f.heq_mapEarStart_vertex v)]
      simp
  | @cycle s p hp =>
      rw [EarStart.isCycle_iff_of_heq (f.mapSubgraph_walkGraph (x := ⟨s, hp.start_mem⟩)
        (y := ⟨s, hp.start_mem⟩) p) (f.heq_mapEarStart_cycle p hp)]
      simp

/-- Transport an ear decomposition along a graph isomorphism. Every stage graph, the initial
vertex or cycle, and every ear are transported. -/
def mapEarDecomposition (f : Iso G H) (d : G.EarDecomposition L) :
    H.EarDecomposition (f.mapSubgraph ⟨L, d.final_le⟩) where
  length := d.length
  graphAfter i := f.mapSubgraph ⟨d.graphAfter i, d.graphAfter_le i⟩
  start := f.mapEarStart d.start
  earAt i := ⟨f.mapSubgraph ⟨(d.earAt i).1, (d.earAt i).2.base_le⟩, f.mapEar (d.earAt i).2⟩
  earAt_fst i := congrArg f.mapSubgraph (Subtype.ext (d.earAt_fst i))
  graphAfter_succ i := by
    rw [add_mapEar]
    exact congrArg f.mapSubgraph (Subtype.ext (d.graphAfter_succ i))
  graphAfter_last := congrArg f.mapSubgraph (Subtype.ext d.graphAfter_last)

/-- Transport preserves the number of ears. -/
@[simp]
theorem length_mapEarDecomposition (f : Iso G H) (d : G.EarDecomposition L) :
    (f.mapEarDecomposition d).length = d.length :=
  (rfl)

/-- Each stage graph of a transported decomposition is the transported stage graph. -/
@[simp]
theorem graphAfter_mapEarDecomposition (f : Iso G H) (d : G.EarDecomposition L)
    (i : Fin ((f.mapEarDecomposition d).length + 1)) :
    (f.mapEarDecomposition d).graphAfter i =
      f.mapSubgraph ⟨d.graphAfter (i.cast (congrArg (· + 1) (f.length_mapEarDecomposition d))),
        d.graphAfter_le _⟩ :=
  (rfl)

/-- The initial graph of a transported decomposition is the transported initial graph. -/
theorem initial_mapEarDecomposition (f : Iso G H) (d : G.EarDecomposition L) :
    (f.mapEarDecomposition d).initial = f.mapSubgraph ⟨d.initial, d.initial_le.trans d.final_le⟩ :=
  (EarDecomposition.initial_eq_graphAfter _).trans
    (congrArg f.mapSubgraph (Subtype.ext d.initial_eq_graphAfter.symm))

/-- The initial stage of a transported decomposition is the transported initial stage. -/
theorem heq_start_mapEarDecomposition (f : Iso G H) (d : G.EarDecomposition L) :
    HEq (f.mapEarDecomposition d).start (f.mapEarStart d.start) :=
  HEq.rfl

/-- Each ear of a transported decomposition is the transported ear over the transported base. -/
@[simp]
theorem earAt_mapEarDecomposition (f : Iso G H) (d : G.EarDecomposition L)
    (i : Fin (f.mapEarDecomposition d).length) :
    (f.mapEarDecomposition d).earAt i =
      ⟨f.mapSubgraph ⟨(d.earAt (i.cast (f.length_mapEarDecomposition d))).1,
        (d.earAt (i.cast (f.length_mapEarDecomposition d))).2.base_le⟩,
        f.mapEar (d.earAt (i.cast (f.length_mapEarDecomposition d))).2⟩ :=
  (rfl)

/-- Transport preserves the kind of every ear of a decomposition. -/
theorem kindAt_mapEarDecomposition (f : Iso G H) (d : G.EarDecomposition L)
    (i : Fin (f.mapEarDecomposition d).length) :
    (f.mapEarDecomposition d).kindAt i = d.kindAt (i.cast (f.length_mapEarDecomposition d)) := by
  rw [EarDecomposition.kindAt_eq, earAt_mapEarDecomposition, kind_mapEar,
    EarDecomposition.kindAt_eq]

/-- The walk of every ear of a transported decomposition is the walk of the transported ear. -/
theorem walkAt_mapEarDecomposition (f : Iso G H) (d : G.EarDecomposition L)
    (i : Fin (f.mapEarDecomposition d).length) :
    (f.mapEarDecomposition d).walkAt i =
      (f.mapEar (d.earAt (i.cast (f.length_mapEarDecomposition d))).2).toWalk := by
  rw [EarDecomposition.walkAt_eq, earAt_mapEarDecomposition]

/-- Transport preserves whether a decomposition starts from a cycle. -/
@[simp]
theorem start_isCycle_mapEarDecomposition (f : Iso G H) (d : G.EarDecomposition L) :
    (f.mapEarDecomposition d).start.IsCycle ↔ d.start.IsCycle :=
  f.isCycle_mapEarStart d.start

/-- Transport preserves and reflects open ear decompositions. -/
@[simp]
theorem isOpen_mapEarDecomposition (f : Iso G H) (d : G.EarDecomposition L) :
    (f.mapEarDecomposition d).IsOpen ↔ d.IsOpen := by
  rw [EarDecomposition.isOpen_iff, EarDecomposition.isOpen_iff,
    start_isCycle_mapEarDecomposition]
  refine and_congr_right fun _ ↦ ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩
  · exact (f.kindAt_mapEarDecomposition d i).symm.trans (h i)
  · rw [kindAt_mapEarDecomposition]
    exact h _

/-- Transport preserves and reflects vertex-started ear decompositions. -/
@[simp]
theorem isVertexStart_mapEarDecomposition (f : Iso G H) (d : G.EarDecomposition L) :
    (f.mapEarDecomposition d).IsVertexStart ↔ d.IsVertexStart := by
  rw [EarDecomposition.isVertexStart_iff_not_start_isCycle,
    EarDecomposition.isVertexStart_iff_not_start_isCycle, start_isCycle_mapEarDecomposition]

/-- Transporting an ear along an isomorphism and back recovers its walk. -/
theorem toWalk_symm_mapEar_mapEar (f : Iso G H) (e : G.Ear L) :
    (f.symm.mapEar (f.mapEar e)).toWalk = e.toWalk := by
  cases e <;> simp only [mapEar, Ear.toWalk_open, Ear.toWalk_closed] <;>
    exact (Walk.sigma_mk_copy _ (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv _))
      (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv _))).symm.trans
      (by rw [mapWalk_symm_mapWalk])

/-- Heterogeneously equal initial stages remain heterogeneously equal after transport. -/
theorem heq_mapEarStart_of_heq (f : Iso G H) {L' : Graph α β} (hLL' : L = L')
    {s : G.EarStart L} {s' : G.EarStart L'} (hs : HEq s s') :
    HEq (f.mapEarStart s) (f.mapEarStart s') := by
  subst hLL'
  cases eq_of_heq hs
  rfl

/-- Transporting an initial stage along an isomorphism and back recovers it. -/
theorem heq_symm_mapEarStart_mapEarStart (f : Iso G H) (start : G.EarStart L) :
    HEq (f.symm.mapEarStart (f.mapEarStart start)) start := by
  cases start with
  | vertex v =>
      refine (f.symm.heq_mapEarStart_of_heq (by rw [mapSubgraph_noEdge, mapVertexSet_singleton])
        (f.heq_mapEarStart_vertex v)).trans ((f.symm.heq_mapEarStart_vertex _).trans ?_)
      rw [symm_vertexEquiv_apply_vertexEquiv]
  | @cycle s p hp =>
      refine (f.symm.heq_mapEarStart_of_heq (f.mapSubgraph_walkGraph (x := ⟨s, hp.start_mem⟩)
        (y := ⟨s, hp.start_mem⟩) p) (f.heq_mapEarStart_cycle p hp)).trans
        ((f.symm.heq_mapEarStart_cycle _ _).trans ?_)
      exact EarStart.heq_cycle_of_copy_eq _ hp
        (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv _))
        (mapWalk_symm_mapWalk f (x := ⟨s, hp.start_mem⟩) (y := ⟨s, hp.start_mem⟩) p)

/-- Transport commutes with reindexing the final graph. -/
theorem mapEarDecomposition_copy (f : Iso G H) {L' : Graph α β} (d : G.EarDecomposition L)
    (h : L = L') :
    f.mapEarDecomposition (d.copy h) =
      (f.mapEarDecomposition d).copy (congrArg f.mapSubgraph (Subtype.ext h)) := by
  subst h
  simp only [EarDecomposition.copy_rfl]
  exact eq_of_heq (congr_arg_heq f.mapEarDecomposition d.copy_rfl)

/-- Transporting an ear decomposition along an isomorphism and back recovers it. -/
theorem symm_mapEarDecomposition_mapEarDecomposition (f : Iso G H)
    (d : G.EarDecomposition L) :
    (f.symm.mapEarDecomposition (f.mapEarDecomposition d)).copy
      (by simp) = d :=
  EarDecomposition.ext _ _ (by simp)
    ((EarDecomposition.heq_start_copy _ _).trans <|
      (f.symm.heq_start_mapEarDecomposition _).trans ((f.symm.heq_mapEarStart_of_heq rfl
        (f.heq_start_mapEarDecomposition d)).trans (f.heq_symm_mapEarStart_mapEarStart d.start)))
    -- The `i`-th ear of the round trip unfolds to the twice-transported `i`-th ear of `d`.
    ((Fin.heq_fun_iff (by simp)).mpr fun ⟨i, hi⟩ ↦ by
      rw [EarDecomposition.earAt_copy, earAt_mapEarDecomposition, earAt_mapEarDecomposition]
      simp only [Fin.cast_mk]
      exact Ear.sigma_ext (by simp) (f.toWalk_symm_mapEar_mapEar (d.earAt _).2))

/-- Transporting an ear decomposition along the inverse of an isomorphism and back recovers
it. -/
theorem mapEarDecomposition_symm_mapEarDecomposition (f : Iso G H) {M : Graph α' β'}
    (d : H.EarDecomposition M)
    (h : f.mapSubgraph ⟨f.symm.mapSubgraph ⟨M, d.final_le⟩, f.symm.mapSubgraph_le _⟩ = M) :
    (f.mapEarDecomposition (f.symm.mapEarDecomposition d)).copy h = d := by
  -- The round trip along `f.symm` transports along `f.symm.symm`, which equals `f` only
  -- propositionally (`symm_symm`). The reindexing proof mentions the isomorphism, so generalize
  -- the isomorphism together with that proof before substituting.
  have key : ∀ (k : Iso G H), k = f.symm.symm →
      ∀ hk : k.mapSubgraph ⟨f.symm.mapSubgraph ⟨M, d.final_le⟩, f.symm.mapSubgraph_le _⟩ = M,
        (k.mapEarDecomposition (f.symm.mapEarDecomposition d)).copy hk = d := by
    rintro k rfl -
    exact f.symm.symm_mapEarDecomposition_mapEarDecomposition d
  exact key f f.symm_symm.symm h

/-- An isomorphism identifies the ear decompositions of a subgraph with those of its image. -/
def earDecompositionEquiv (f : Iso G H) (S : Set.Iic G) :
    G.EarDecomposition S.val ≃ H.EarDecomposition (f.mapSubgraph S) where
  toFun := f.mapEarDecomposition
  invFun d := (f.symm.mapEarDecomposition d).copy (by simp)
  left_inv := f.symm_mapEarDecomposition_mapEarDecomposition
  right_inv d := by
    rw [f.mapEarDecomposition_copy, f.mapEarDecomposition_symm_mapEarDecomposition]

@[simp]
theorem earDecompositionEquiv_apply (f : Iso G H) (S : Set.Iic G)
    (d : G.EarDecomposition S.val) :
    f.earDecompositionEquiv S d = f.mapEarDecomposition d :=
  (rfl)

@[simp]
theorem earDecompositionEquiv_symm_apply (f : Iso G H) (S : Set.Iic G)
    (d : H.EarDecomposition (f.mapSubgraph S)) :
    (f.earDecompositionEquiv S).symm d =
      (f.symm.mapEarDecomposition d).copy (by simp) :=
  (rfl)

/-- A graph has an ear decomposition exactly when an isomorphic graph has one. -/
theorem nonempty_earDecomposition_iff (f : Iso G H) :
    Nonempty (H.EarDecomposition H) ↔ Nonempty (G.EarDecomposition G) :=
  ((f.earDecompositionEquiv ⊤).trans
    (EarDecomposition.copyEquiv f.mapSubgraph_top)).nonempty_congr.symm

/-- A graph has an open ear decomposition exactly when an isomorphic graph has one. -/
theorem exists_isOpen_earDecomposition_iff (f : Iso G H) :
    (∃ d : H.EarDecomposition H, d.IsOpen) ↔ ∃ d : G.EarDecomposition G, d.IsOpen :=
  (((f.earDecompositionEquiv ⊤).trans
    (EarDecomposition.copyEquiv f.mapSubgraph_top)).exists_congr fun _ ↦ by
    simp only [Equiv.trans_apply, EarDecomposition.copyEquiv_apply, earDecompositionEquiv_apply,
      EarDecomposition.isOpen_copy, isOpen_mapEarDecomposition]).symm

/-- A graph has a vertex-started ear decomposition exactly when an isomorphic graph has one. -/
theorem exists_isVertexStart_earDecomposition_iff (f : Iso G H) :
    (∃ d : H.EarDecomposition H, d.IsVertexStart) ↔
      ∃ d : G.EarDecomposition G, d.IsVertexStart :=
  (((f.earDecompositionEquiv ⊤).trans
    (EarDecomposition.copyEquiv f.mapSubgraph_top)).exists_congr fun _ ↦ by
    simp only [Equiv.trans_apply, EarDecomposition.copyEquiv_apply, earDecompositionEquiv_apply,
      EarDecomposition.isVertexStart_copy, isVertexStart_mapEarDecomposition]).symm

end Graph.Iso
