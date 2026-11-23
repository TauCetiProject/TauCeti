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
subgraphs of `G` to those of the corresponding subgraphs of `H`. Edge identities are retained, so
loops, parallel edges, and the kind of every ear are preserved. The transport sends each stage
graph to its image under `Graph.Iso.mapSubgraph` and each ear walk to its image under
`Graph.Iso.mapWalk`; transporting back along the inverse isomorphism recovers the original data.
Consequently the existence of ear decompositions, of open ear decompositions, and of
vertex-started ear decompositions is invariant under isomorphism.

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

/-- Transport along an isomorphism and its inverse recovers a subgraph. -/
private theorem symm_mapSubgraph_mapSubgraph (f : Iso G H) (S : Set.Iic G) :
    f.symm.mapSubgraph ⟨f.mapSubgraph S, f.mapSubgraph_le S⟩ = S.val := by
  rw [mk_mapSubgraph, symm_mapSubgraph_subgraphOrderIso]

/-- An isomorphism transports an edgeless single-vertex subgraph to the edgeless graph on the
corresponding vertex. -/
private theorem mapSubgraph_noEdge_singleton (f : Iso G H) (x : G.vertexSet)
    (h : noEdge {(x : α)} β ≤ G) :
    f.mapSubgraph ⟨noEdge {(x : α)} β, h⟩ = noEdge {(f.vertexEquiv x : α')} β' := by
  simp

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

/-- The walk of a transported open ear is the transported walk. -/
@[simp]
theorem toWalk_mapEar_open (f : Iso G H) {s t : α} (hLG : L ≤ G) (p : G.Walk s t)
    (hp : p.IsPath) (hs : s ∈ V(L)) (ht : t ∈ V(L)) (hst : s ≠ t)
    (hinter : ∀ x ∈ p.support, x ≠ s → x ≠ t → x ∉ V(L)) (hedges : ∀ e ∈ p.edges, e ∉ E(L)) :
    (f.mapEar (.open hLG p hp hs ht hst hinter hedges)).toWalk =
      ⟨_, _, f.mapWalk (x := ⟨s, hLG.vertexSet_mono hs⟩) (y := ⟨t, hLG.vertexSet_mono ht⟩) p⟩ := by
  simp only [mapEar, Ear.toWalk_open]

/-- The walk of a transported closed ear is the transported cycle. -/
@[simp]
theorem toWalk_mapEar_closed (f : Iso G H) {s : α} (hLG : L ≤ G) (p : G.Walk s s)
    (hp : p.IsCycle) (hs : s ∈ V(L)) (hinter : ∀ x ∈ p.support, x ≠ s → x ∉ V(L))
    (hedges : ∀ e ∈ p.edges, e ∉ E(L)) :
    (f.mapEar (.closed hLG p hp hs hinter hedges)).toWalk =
      ⟨_, _, f.mapWalk (x := ⟨s, hLG.vertexSet_mono hs⟩) (y := ⟨s, hLG.vertexSet_mono hs⟩) p⟩ := by
  simp only [mapEar, Ear.toWalk_closed]

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
    (f.mapEar e).add = f.mapSubgraph ⟨e.add, e.add_le⟩ :=
  (Compatible.of_le_le (f.mapEar e).add_le (f.mapSubgraph_le _)).ext
    (by simp only [Ear.vertexSet_add, toGraph_mapEar, vertexSet_mapSubgraph, mapVertexSet_union])
    (by simp only [Ear.edgeSet_add, toGraph_mapEar, edgeSet_mapSubgraph, mapEdgeSet_union])

/-- Transport the initial vertex or cycle of an ear decomposition along a graph isomorphism. -/
def mapEarStart (f : Iso G H) :
    (start : G.EarStart L) → H.EarStart (f.mapSubgraph ⟨L, start.le⟩)
  | .vertex v => cast (congrArg H.EarStart (f.mapSubgraph_noEdge_singleton v _).symm)
      (.vertex (f.vertexEquiv v))
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
      rw [EarStart.isCycle_iff_of_heq (f.mapSubgraph_noEdge_singleton v _)
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
    (i : Fin (d.length + 1)) :
    (f.mapEarDecomposition d).graphAfter
      (Fin.cast (congrArg (· + 1) (f.length_mapEarDecomposition d).symm) i) =
        f.mapSubgraph ⟨d.graphAfter i, d.graphAfter_le i⟩ :=
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
theorem earAt_mapEarDecomposition (f : Iso G H) (d : G.EarDecomposition L) (i : Fin d.length) :
    (f.mapEarDecomposition d).earAt (Fin.cast (f.length_mapEarDecomposition d).symm i) =
      ⟨f.mapSubgraph ⟨(d.earAt i).1, (d.earAt i).2.base_le⟩, f.mapEar (d.earAt i).2⟩ :=
  (rfl)

/-- Transport preserves the kind of every ear of a decomposition. -/
theorem kindAt_mapEarDecomposition (f : Iso G H) (d : G.EarDecomposition L) (i : Fin d.length) :
    (f.mapEarDecomposition d).kindAt (Fin.cast (f.length_mapEarDecomposition d).symm i) =
      d.kindAt i := by
  rw [EarDecomposition.kindAt_eq, earAt_mapEarDecomposition, kind_mapEar,
    EarDecomposition.kindAt_eq]

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
  · rw [← kindAt_mapEarDecomposition]
    exact h _
  · simpa using (kindAt_mapEarDecomposition f d (Fin.cast (f.length_mapEarDecomposition d) i)).trans
      (h _)

/-- Transport preserves and reflects vertex-started ear decompositions. -/
@[simp]
theorem isVertexStart_mapEarDecomposition (f : Iso G H) (d : G.EarDecomposition L) :
    (f.mapEarDecomposition d).IsVertexStart ↔ d.IsVertexStart := by
  rw [EarDecomposition.isVertexStart_iff_not_start_isCycle,
    EarDecomposition.isVertexStart_iff_not_start_isCycle, start_isCycle_mapEarDecomposition]

/-- A graph has an ear decomposition exactly when an isomorphic graph has one. -/
theorem nonempty_earDecomposition_iff (f : Iso G H) :
    Nonempty (H.EarDecomposition H) ↔ Nonempty (G.EarDecomposition G) :=
  ⟨fun ⟨d⟩ ↦ ⟨(f.symm.mapEarDecomposition d).copy f.symm.mapSubgraph_top⟩,
    fun ⟨d⟩ ↦ ⟨(f.mapEarDecomposition d).copy f.mapSubgraph_top⟩⟩

/-- A graph has an open ear decomposition exactly when an isomorphic graph has one. -/
theorem exists_isOpen_earDecomposition_iff (f : Iso G H) :
    (∃ d : H.EarDecomposition H, d.IsOpen) ↔ ∃ d : G.EarDecomposition G, d.IsOpen :=
  ⟨fun ⟨d, hd⟩ ↦ ⟨(f.symm.mapEarDecomposition d).copy f.symm.mapSubgraph_top, by simpa using hd⟩,
    fun ⟨d, hd⟩ ↦ ⟨(f.mapEarDecomposition d).copy f.mapSubgraph_top, by simpa using hd⟩⟩

/-- A graph has a vertex-started ear decomposition exactly when an isomorphic graph has one. -/
theorem exists_isVertexStart_earDecomposition_iff (f : Iso G H) :
    (∃ d : H.EarDecomposition H, d.IsVertexStart) ↔
      ∃ d : G.EarDecomposition G, d.IsVertexStart :=
  ⟨fun ⟨d, hd⟩ ↦ ⟨(f.symm.mapEarDecomposition d).copy f.symm.mapSubgraph_top, by simpa using hd⟩,
    fun ⟨d, hd⟩ ↦ ⟨(f.mapEarDecomposition d).copy f.mapSubgraph_top, by simpa using hd⟩⟩

private theorem sigma_walk_eq_copy {a b c d : α} (p : G.Walk a b) (hac : a = c) (hbd : b = d) :
    (⟨a, b, p⟩ : Σ x y : α, G.Walk x y) = ⟨c, d, p.copy hac hbd⟩ := by
  subst hac hbd
  rw [Walk.copy_rfl_rfl]

/-- Transporting an ear along an isomorphism and back recovers its walk. -/
theorem toWalk_symm_mapEar_mapEar (f : Iso G H) (e : G.Ear L) :
    (f.symm.mapEar (f.mapEar e)).toWalk = e.toWalk := by
  cases e with
  | @«open» hLG s t p =>
      simp only [mapEar, Ear.toWalk_open]
      exact (sigma_walk_eq_copy _ (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv _))
        (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv _))).trans
        (by rw [mapWalk_symm_mapWalk])
  | @«closed» hLG s p =>
      simp only [mapEar, Ear.toWalk_closed]
      exact (sigma_walk_eq_copy _ (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv _))
        (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv _))).trans
        (by rw [mapWalk_symm_mapWalk])

/-- Heterogeneously equal initial stages remain heterogeneously equal after transport. -/
theorem heq_mapEarStart_of_heq (f : Iso G H) {L' : Graph α β} (hLL' : L = L')
    {s : G.EarStart L} {s' : G.EarStart L'} (hs : HEq s s') :
    HEq (f.mapEarStart s) (f.mapEarStart s') := by
  subst hLL'
  cases eq_of_heq hs
  rfl

private theorem heq_earStart_cycle_of_copy_eq {a b : α} (q : G.Walk a a) (hq : q.IsCycle)
    (p : G.Walk b b) (hp : p.IsCycle) (h : a = b) (hqp : q.copy h h = p) :
    HEq (EarStart.cycle q hq) (EarStart.cycle p hp) := by
  subst h
  rw [Walk.copy_rfl_rfl] at hqp
  subst hqp
  rfl

/-- Transporting an initial stage along an isomorphism and back recovers it. -/
theorem heq_symm_mapEarStart_mapEarStart (f : Iso G H) (start : G.EarStart L) :
    HEq (f.symm.mapEarStart (f.mapEarStart start)) start := by
  cases start with
  | vertex v =>
      refine (f.symm.heq_mapEarStart_of_heq (f.mapSubgraph_noEdge_singleton v _)
        (f.heq_mapEarStart_vertex v)).trans ((f.symm.heq_mapEarStart_vertex _).trans ?_)
      rw [symm_vertexEquiv_apply_vertexEquiv]
  | @cycle s p hp =>
      refine (f.symm.heq_mapEarStart_of_heq (f.mapSubgraph_walkGraph (x := ⟨s, hp.start_mem⟩)
        (y := ⟨s, hp.start_mem⟩) p) (f.heq_mapEarStart_cycle p hp)).trans
        ((f.symm.heq_mapEarStart_cycle _ _).trans ?_)
      exact heq_earStart_cycle_of_copy_eq _ _ _ hp
        (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv _))
        (mapWalk_symm_mapWalk f (x := ⟨s, hp.start_mem⟩) (y := ⟨s, hp.start_mem⟩) p)

private theorem heq_ear_of_toWalk_eq {L' : Graph α β} (hLL' : L = L') {e : G.Ear L}
    {e' : G.Ear L'} (hw : e.toWalk = e'.toWalk) : HEq e e' := by
  subst hLL'
  exact heq_of_eq (Ear.ext e e' hw)

private theorem copy_eq_of_earAt_eq {M M' : Graph α β} (X : G.EarDecomposition M) (h : M = M')
    (d : G.EarDecomposition M') (hlen : X.length = d.length) (hstart : HEq X.start d.start)
    (hearAt : ∀ i, X.earAt i = d.earAt (Fin.cast hlen i)) : X.copy h = d :=
  EarDecomposition.ext _ _ ((EarDecomposition.length_copy X h).trans hlen)
    ((EarDecomposition.heq_start_copy X h).trans hstart)
    ((Fin.heq_fun_iff ((EarDecomposition.length_copy X h).trans hlen)).mpr fun i ↦ by
      rw [EarDecomposition.earAt_copy, hearAt]
      exact congrArg d.earAt (Fin.ext rfl))

/-- Transport commutes with reindexing the final graph. -/
theorem mapEarDecomposition_copy (f : Iso G H) {L' : Graph α β} (d : G.EarDecomposition L)
    (h : L = L') :
    f.mapEarDecomposition (d.copy h) =
      (f.mapEarDecomposition d).copy (congrArg f.mapSubgraph (Subtype.ext h)) :=
  (copy_eq_of_earAt_eq _ _ _ (by simp)
    ((f.heq_start_mapEarDecomposition d).trans ((f.heq_mapEarStart_of_heq (by simp)
      (d.heq_start_copy h).symm).trans (f.heq_start_mapEarDecomposition _).symm))
    fun i ↦ by
      have hi : d.earAt i = (d.copy h).earAt (Fin.cast (d.length_copy h).symm i) := by
        rw [EarDecomposition.earAt_copy]
        exact congrArg d.earAt (Fin.ext rfl)
      -- Both sides unfold to the transported ears of `d` and of `d.copy h`.
      exact congrArg
        (fun x : Σ K, G.Ear K ↦
          (⟨f.mapSubgraph ⟨x.1, x.2.base_le⟩, f.mapEar x.2⟩ : Σ K, H.Ear K)) hi).symm

/-- Transporting an ear decomposition along an isomorphism and back recovers it. -/
theorem symm_mapEarDecomposition_mapEarDecomposition (f : Iso G H)
    (d : G.EarDecomposition L) :
    (f.symm.mapEarDecomposition (f.mapEarDecomposition d)).copy
      (by simp) = d :=
  copy_eq_of_earAt_eq _ _ d rfl
    ((f.symm.heq_start_mapEarDecomposition _).trans ((f.symm.heq_mapEarStart_of_heq rfl
      (f.heq_start_mapEarDecomposition d)).trans (f.heq_symm_mapEarStart_mapEarStart d.start)))
    -- The `i`-th ear of the round trip unfolds to the twice-transported `i`-th ear of `d`.
    fun i ↦ Sigma.ext (f.symm_mapSubgraph_mapSubgraph ⟨_, (d.earAt i).2.base_le⟩)
      (heq_ear_of_toWalk_eq (f.symm_mapSubgraph_mapSubgraph ⟨_, (d.earAt i).2.base_le⟩)
        (f.toWalk_symm_mapEar_mapEar (d.earAt i).2))

/-- Transporting an ear decomposition along the inverse of an isomorphism and back recovers
it. -/
theorem mapEarDecomposition_symm_mapEarDecomposition (f : Iso G H) {M : Graph α' β'}
    (d : H.EarDecomposition M)
    (h : f.mapSubgraph ⟨f.symm.mapSubgraph ⟨M, d.final_le⟩, f.symm.mapSubgraph_le _⟩ = M) :
    (f.mapEarDecomposition (f.symm.mapEarDecomposition d)).copy h = d := by
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

theorem earDecompositionEquiv_symm_apply (f : Iso G H) (S : Set.Iic G)
    (d : H.EarDecomposition (f.mapSubgraph S)) :
    (f.earDecompositionEquiv S).symm d =
      (f.symm.mapEarDecomposition d).copy (by simp) :=
  (rfl)

end Graph.Iso
