/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.Basic
public import TauCeti.Combinatorics.Graph.Delete

/-!
# The bridge forest of a multigraph

Deleting every bridge of a multigraph `G : Graph α β` leaves the graph
`G.deleteEdges G.bridgeSet`, whose connected components are the *bridge components* of `G`.
The **bridge forest** `G.bridgeForest` has these components as its vertices and the bridges of
`G` as its edges, each bridge joining the components that contain its two ends.  It is
constructed directly from the component subgraphs, without a general theory of graph
contraction.

The bridge forest records how the bridgeless pieces of `G` are held together:

* `Graph.isForest_bridgeForest`: the bridge forest is a forest, and in particular no two bridges
  join the same pair of bridge components (`Graph.IsForest.eq_of_isLink`).
* `Graph.IsBridge.bridgeComponentOf_ne`: the two ends of a bridge lie in distinct bridge
  components.
* `Graph.Walk.toBridgeForest`: a walk projects to the bridge forest by omitting precisely its
  non-bridge edge traversals.  Paths project to paths.
* `Graph.Walk.liftBridgeForest`: a forest walk lifts to a path between any prescribed vertices
  of its endpoint components, without introducing bridge identities absent from the forest walk.
* `Graph.reachable_deleteEdges_iff_reachable_bridgeForest_deleteEdges`: after deleting any set
  `F` of bridges, two actual vertices of `G` are reachable from each other exactly when their
  bridge components are reachable in the bridge forest with the edges of `F` deleted.  For
  `F = ∅` this is `Graph.reachable_iff_reachable_bridgeForest`, and for `F = {e}` it says that
  deleting a bridge `e` separates two vertices exactly when deleting the forest edge `e`
  separates their bridge components.
* `Graph.connectedComponentEquivBridgeForest`: the connected components of `G` correspond to
  those of its bridge forest, so the two graphs have the same number of components and the
  bridge forest is a tree exactly when `G` is connected (`Graph.connected_bridgeForest_iff`).
* `Graph.BridgeComponent.not_isBridge`: every bridge component is a connected graph without
  bridges, since deleting all bridges leaves none (`Graph.not_isBridge_deleteEdges_bridgeSet`).

No statement here assumes finiteness.  Loops, parallel edges, disconnected graphs and the empty
graph are all allowed; the empty graph has the empty bridge forest.

The construction is an edge analogue of the block graph of R. Diestel, *Graph Theory*, 5th ed.,
Graduate Texts in Mathematics 173, Springer, 2017, Section 3.1.  That graph is the bipartite
forest whose vertices are the blocks and cut vertices of a graph, each block joined to the cut
vertices it contains; blocks may share cut vertices, whereas bridge components are disjoint and
are joined directly by the bridges.  The choice of the bridge components as vertices, and
the names `Graph.bridgeSet`, `Graph.BridgeComponent` and `Graph.bridgeComponentOf`, follow an
earlier Tau Ceti attempt at this construction, https://github.com/TauCetiProject/TauCeti/pull/20726
by @fzaiser.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {e : β} {x y : α}

/-! ### Bridge components -/

/-- The **bridge components** of `G` are the connected components left after deleting every
bridge of `G`; they are the vertices of the bridge forest. -/
abbrev BridgeComponent (G : Graph α β) := (G.deleteEdges G.bridgeSet).ConnectedComponent

/-- The bridge component containing an actual vertex. -/
def bridgeComponentOf (G : Graph α β) (x : α) (hx : x ∈ V(G)) : G.BridgeComponent :=
  (G.deleteEdges G.bridgeSet).connectedComponentOf x (by rwa [vertexSet_deleteEdges])

/-- The bridge component of `x` consists of the vertices reachable from `x` once all bridges are
deleted. -/
@[simp]
theorem mem_vertexSet_bridgeComponentOf_iff (hx : x ∈ V(G)) :
    y ∈ V((G.bridgeComponentOf x hx).1) ↔ (G.deleteEdges G.bridgeSet).Reachable x y :=
  mem_vertexSet_connectedComponentOf_iff _

/-- An actual vertex lies in its own bridge component. -/
theorem mem_vertexSet_bridgeComponentOf_self (hx : x ∈ V(G)) :
    x ∈ V((G.bridgeComponentOf x hx).1) :=
  mem_vertexSet_connectedComponentOf_self _

/-- Two actual vertices have the same bridge component exactly when they are reachable from each
other once all bridges are deleted. -/
@[simp]
theorem bridgeComponentOf_eq_bridgeComponentOf_iff (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.bridgeComponentOf x hx = G.bridgeComponentOf y hy ↔
      (G.deleteEdges G.bridgeSet).Reachable x y :=
  connectedComponentOf_eq_connectedComponentOf_iff _ _

/-- A vertex of a bridge component is an actual vertex of `G`. -/
theorem BridgeComponent.mem_vertexSet {C : G.BridgeComponent} (hx : x ∈ V(C.1)) : x ∈ V(G) := by
  simpa using C.2.le.vertexSet_mono hx

/-- A bridge component is the bridge component of each of its vertices. -/
theorem BridgeComponent.eq_bridgeComponentOf {C : G.BridgeComponent} (hx : x ∈ V(C.1)) :
    C = G.bridgeComponentOf x (BridgeComponent.mem_vertexSet hx) :=
  ConnectedComponent.eq_connectedComponentOf hx

/-- Any two vertices of a bridge component are reachable from each other once all bridges are
deleted. -/
theorem BridgeComponent.reachable {C : G.BridgeComponent} (hx : x ∈ V(C.1)) (hy : y ∈ V(C.1)) :
    (G.deleteEdges G.bridgeSet).Reachable x y :=
  (C.2.connected.reachable hx hy).mono C.2.le

/-- Every bridge component is the bridge component of some actual vertex. -/
theorem BridgeComponent.exists_bridgeComponentOf_eq (C : G.BridgeComponent) :
    ∃ x, ∃ hx : x ∈ V(G), G.bridgeComponentOf x hx = C := by
  obtain ⟨x, hx⟩ := C.2.nonempty
  exact ⟨x, BridgeComponent.mem_vertexSet hx, (BridgeComponent.eq_bridgeComponentOf hx).symm⟩

/-- The ends of a bridge lie in distinct bridge components. -/
theorem IsBridge.bridgeComponentOf_ne (he : G.IsBridge e) (h : G.IsLink e x y) :
    G.bridgeComponentOf x h.left_mem ≠ G.bridgeComponentOf y h.right_mem := by
  rw [Ne, bridgeComponentOf_eq_bridgeComponentOf_iff]
  exact fun hxy ↦ he.not_reachable_deleteEdges h
    (hxy.mono (G.deleteEdges_anti_right (singleton_subset_iff.mpr (mem_bridgeSet.mpr he))))

/-- Every bridge component is a graph without bridges. -/
theorem BridgeComponent.not_isBridge (C : G.BridgeComponent) (e : β) : ¬ C.1.IsBridge e :=
  fun he ↦ G.not_isBridge_deleteEdges_bridgeSet e (he.of_isClosedSubgraph C.2.isClosedSubgraph)

/-! ### The bridge forest -/

/-- The **bridge forest** of `G`.  Its vertices are the bridge components of `G`, the connected
components left after deleting every bridge, and its edges are the bridges of `G`, each joining
the bridge components that contain its two ends. -/
def bridgeForest (G : Graph α β) : Graph G.BridgeComponent β where
  vertexSet := univ
  IsLink e C D := G.IsBridge e ∧ ∃ x ∈ V(C.1), ∃ y ∈ V(D.1), G.IsLink e x y
  isLink_symm _ _ := ⟨fun _ _ ⟨he, x, hx, y, hy, h⟩ ↦ ⟨he, y, hy, x, hx, h.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e C D C' D' ⟨-, x, hx, y, hy, h⟩ ⟨-, x', hx', y', hy', h'⟩
    obtain rfl | rfl := h.left_eq_or_eq h'
    · exact .inl (ConnectedComponent.eq_of_mem_of_mem hx hx')
    · exact .inr (ConnectedComponent.eq_of_mem_of_mem hx hy')
  left_mem_of_isLink _ _ _ _ := mem_univ _

@[simp]
theorem vertexSet_bridgeForest : V(G.bridgeForest) = univ := (rfl)

@[simp]
theorem bridgeForest_isLink {C D : G.BridgeComponent} :
    G.bridgeForest.IsLink e C D ↔ G.IsBridge e ∧ ∃ x ∈ V(C.1), ∃ y ∈ V(D.1), G.IsLink e x y :=
  (Iff.rfl)

/-- A bridge joins the bridge components of its ends in the bridge forest. -/
theorem IsBridge.isLink_bridgeForest (he : G.IsBridge e) (h : G.IsLink e x y) :
    G.bridgeForest.IsLink e (G.bridgeComponentOf x h.left_mem)
      (G.bridgeComponentOf y h.right_mem) :=
  ⟨he, x, mem_vertexSet_bridgeComponentOf_self _, y, mem_vertexSet_bridgeComponentOf_self _, h⟩

/-- The edges of the bridge forest are exactly the bridges of `G`. -/
@[simp]
theorem edgeSet_bridgeForest : E(G.bridgeForest) = G.bridgeSet := by
  ext e
  refine ⟨fun he ↦ ?_, fun he ↦ ?_⟩
  · obtain ⟨C, D, h⟩ := exists_isLink_of_mem_edgeSet he
    exact mem_bridgeSet.mpr h.1
  · obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet (IsBridge.mem_edgeSet (mem_bridgeSet.mp he))
    exact (IsBridge.isLink_bridgeForest (mem_bridgeSet.mp he) h).edge_mem

/-! ### Projection of walks -/

private def Walk.copyBridgeForest {C D C' D' : G.BridgeComponent}
    (p : G.bridgeForest.Walk C D) (hC : C = C') (hD : D = D') :
    G.bridgeForest.Walk C' D' := by
  subst C'
  subst D'
  exact p

@[simp]
private theorem Walk.edges_copyBridgeForest {C D C' D' : G.BridgeComponent}
    (p : G.bridgeForest.Walk C D) (hC : C = C') (hD : D = D') :
    (p.copyBridgeForest hC hD).edges = p.edges := by
  subst C'
  subst D'
  rfl

@[simp]
private theorem Walk.support_copyBridgeForest {C D C' D' : G.BridgeComponent}
    (p : G.bridgeForest.Walk C D) (hC : C = C') (hD : D = D') :
    (p.copyBridgeForest hC hD).support = p.support := by
  subst C'
  subst D'
  rfl

/-- Project a walk to the bridge forest by omitting each traversal of a non-bridge edge.

The endpoint-membership arguments identify the bridge components containing the endpoints. -/
noncomputable def Walk.toBridgeForest (p : G.Walk x y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.bridgeForest.Walk (G.bridgeComponentOf x hx) (G.bridgeComponentOf y hy) := by
  classical
  induction p with
  | nil => exact .nil
  | @cons x y z e h p ih =>
      by_cases he : G.IsBridge e
      · exact .cons e (he.isLink_bridgeForest h) (ih h.right_mem hy)
      · exact (ih h.right_mem hy).copyBridgeForest
          ((bridgeComponentOf_eq_bridgeComponentOf_iff hx h.right_mem).2
            (h.reachable_deleteEdges_bridgeSet he)).symm rfl

@[simp]
theorem Walk.toBridgeForest_nil (hx : x ∈ V(G)) :
    (Walk.nil : G.Walk x x).toBridgeForest hx hx = Walk.nil := by
  simp [Walk.toBridgeForest]

/-- Projecting a bridge traversal retains that traversal. -/
@[simp]
theorem Walk.toBridgeForest_cons_of_isBridge (h : G.IsLink e x y) (p : G.Walk y z)
    (he : G.IsBridge e) (hx : x ∈ V(G)) (hz : z ∈ V(G)) :
    (Walk.cons e h p).toBridgeForest hx hz =
      Walk.cons e (he.isLink_bridgeForest h) (p.toBridgeForest h.right_mem hz) := by
  simp [Walk.toBridgeForest, he]

open Classical in
/-- Projection retains exactly the original bridge identities, in their original order. -/
@[simp]
theorem Walk.edges_toBridgeForest (p : G.Walk x y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toBridgeForest hx hy).edges = p.edges.filter (fun e ↦ decide (G.IsBridge e)) := by
  classical
  induction p with
  | nil => simp
  | cons e h p ih =>
      by_cases he : G.IsBridge e
      · rw [Walk.toBridgeForest_cons_of_isBridge h p he]
        simp [he, ih]
      · simpa [Walk.toBridgeForest, he] using ih h.right_mem hy

/-- A nonbridge traversal is omitted; only the identification of its end components remains. -/
theorem Walk.toBridgeForest_cons_of_not_isBridge (h : G.IsLink e x y)
    (p : G.Walk y z) (he : ¬ G.IsBridge e) (hx : x ∈ V(G)) (hz : z ∈ V(G)) :
    (Walk.cons e h p).toBridgeForest hx hz =
      (p.toBridgeForest h.right_mem hz).copy
        ((G.bridgeComponentOf_eq_bridgeComponentOf_iff hx h.right_mem).mpr
          (h.reachable_deleteEdges_bridgeSet he)).symm rfl := by
  apply Walk.ext_edges
  simp [he]

/-- Projection retains the order and identity of the bridge traversals that remain. -/
theorem Walk.edges_toBridgeForest_sublist (p : G.Walk x y) (hx : x ∈ V(G))
    (hy : y ∈ V(G)) : List.Sublist (p.toBridgeForest hx hy).edges p.edges := by
  classical
  rw [Walk.edges_toBridgeForest]
  exact List.filter_sublist

/-! ### Reachability -/

/-- A walk avoiding `F` maps to a walk in the bridge forest avoiding `F`, by omitting the edges
that are not bridges. -/
private theorem Walk.reachable_bridgeForest_deleteEdges {F : Set β} {x y : α} (p : G.Walk x y)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) (hp : ∀ f ∈ p.edges, f ∉ F) :
    (G.bridgeForest.deleteEdges F).Reachable (G.bridgeComponentOf x hx)
      (G.bridgeComponentOf y hy) := by
  apply reachable_deleteEdges_iff_exists_walk.mpr
  refine ⟨by simp, p.toBridgeForest hx hy, ?_⟩
  intro f hf
  exact hp f ((p.edges_toBridgeForest_sublist hx hy).subset hf)

/-- A walk of the bridge forest avoiding a set `F` of bridges lifts to walks of `G` avoiding `F`
between any vertices of its end components. -/
private theorem Walk.reachable_deleteEdges_of_bridgeForest {F : Set β} (hF : F ⊆ G.bridgeSet)
    {C D : G.BridgeComponent} (q : G.bridgeForest.Walk C D) (hq : ∀ f ∈ q.edges, f ∉ F)
    (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) : (G.deleteEdges F).Reachable x y := by
  induction q generalizing x with
  | nil => exact (BridgeComponent.reachable hx hy).mono (G.deleteEdges_anti_right hF)
  | cons e h q ih =>
    have heF : e ∉ F := hq e (by simp)
    have hq' : ∀ f ∈ q.edges, f ∉ F := fun f hf ↦ hq f (by simp [hf])
    obtain ⟨-, a, ha, b, hb, hab⟩ := h
    have hxa := (BridgeComponent.reachable hx ha).mono (G.deleteEdges_anti_right hF)
    have hab' : (G.deleteEdges F).Reachable a b :=
      IsLink.reachable (e := e) ((deleteEdges_isLink ..).mpr ⟨hab, heF⟩)
    exact hxa.trans (hab'.trans (ih hq' hb hy))

/-- A bridge-forest walk admits a path lift between any prescribed vertices of its endpoint
components. The lift uses no bridge identity absent from the forest walk. -/
theorem Walk.exists_liftBridgeForest_isPath {C D : G.BridgeComponent}
    (q : G.bridgeForest.Walk C D) (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) :
    ∃ p : G.Walk x y, p.IsPath ∧ ∀ e, e ∈ p.edges → G.IsBridge e → e ∈ q.edges := by
  classical
  let F : Set β := G.bridgeSet \ {e | e ∈ q.edges}
  have hF : F ⊆ G.bridgeSet := sdiff_subset
  have hq : ∀ e ∈ q.edges, e ∉ F := by
    intro e he hFmem
    exact hFmem.2 he
  have hr : (G.deleteEdges F).Reachable x y :=
    q.reachable_deleteEdges_of_bridgeForest hF hq hx hy
  obtain ⟨p, hp⟩ := hr.exists_isPath
  refine ⟨p.mapLe deleteEdges_le, hp.mapLe deleteEdges_le, ?_⟩
  intro e he heBridge
  have hep : e ∈ p.edges := by simpa using he
  have heG := p.edges_subset_edgeSet hep
  rw [edgeSet_deleteEdges] at heG
  by_contra heq
  exact heG.2 ⟨mem_bridgeSet.mpr heBridge, heq⟩

/-- Lift a bridge-forest walk to a path between prescribed vertices in its endpoint components. -/
noncomputable def Walk.liftBridgeForest {C D : G.BridgeComponent}
    (q : G.bridgeForest.Walk C D) (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) : G.Walk x y :=
  Classical.choose (q.exists_liftBridgeForest_isPath hx hy)

/-- A lifted bridge-forest walk is a path. -/
@[simp]
theorem Walk.isPath_liftBridgeForest {C D : G.BridgeComponent}
    (q : G.bridgeForest.Walk C D) (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) :
    (q.liftBridgeForest hx hy).IsPath :=
  (Classical.choose_spec (q.exists_liftBridgeForest_isPath hx hy)).1

/-- Every bridge in a lifted path already occurs in the bridge-forest walk. -/
theorem Walk.mem_edges_of_mem_edges_liftBridgeForest {C D : G.BridgeComponent}
    (q : G.bridgeForest.Walk C D) (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1))
    (he : e ∈ (q.liftBridgeForest hx hy).edges) (heBridge : G.IsBridge e) : e ∈ q.edges :=
  (Classical.choose_spec (q.exists_liftBridgeForest_isPath hx hy)).2 e he heBridge

/-- **Separation in the bridge forest.**  After deleting a set `F` of bridges, two actual
vertices are reachable from each other exactly when their bridge components are reachable in the
bridge forest with the edges of `F` deleted. -/
theorem reachable_deleteEdges_iff_reachable_bridgeForest_deleteEdges {F : Set β}
    (hF : F ⊆ G.bridgeSet) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (G.deleteEdges F).Reachable x y ↔
      (G.bridgeForest.deleteEdges F).Reachable (G.bridgeComponentOf x hx)
        (G.bridgeComponentOf y hy) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨-, p, hp⟩ := reachable_deleteEdges_iff_exists_walk.mp h
    exact Walk.reachable_bridgeForest_deleteEdges p hx hy hp
  · obtain ⟨-, q, hq⟩ := reachable_deleteEdges_iff_exists_walk.mp h
    exact Walk.reachable_deleteEdges_of_bridgeForest hF q hq
      (mem_vertexSet_bridgeComponentOf_self hx) (mem_vertexSet_bridgeComponentOf_self hy)

/-- Two actual vertices are reachable from each other exactly when their bridge components are
reachable in the bridge forest. -/
theorem reachable_iff_reachable_bridgeForest (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.Reachable x y ↔ G.bridgeForest.Reachable (G.bridgeComponentOf x hx)
      (G.bridgeComponentOf y hy) := by
  simpa using reachable_deleteEdges_iff_reachable_bridgeForest_deleteEdges (empty_subset _) hx hy

/-- **The bridge forest is a forest.** -/
theorem isForest_bridgeForest (G : Graph α β) : G.bridgeForest.IsForest := by
  refine isForest_iff_forall_isBridge.mpr fun e he ↦ ?_
  obtain ⟨C, D, hCD⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨hbr, x, hx, y, hy, h⟩ := id hCD
  rw [hCD.isBridge_iff_not_reachable_deleteEdges, BridgeComponent.eq_bridgeComponentOf hx,
    BridgeComponent.eq_bridgeComponentOf hy,
    ← reachable_deleteEdges_iff_reachable_bridgeForest_deleteEdges
      (singleton_subset_iff.mpr (mem_bridgeSet.mpr hbr))]
  exact hbr.not_reachable_deleteEdges h

/-- The projection of a trail to the bridge forest is a path. -/
theorem Walk.IsTrail.toBridgeForest {p : G.Walk x y} (hp : p.IsTrail)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) : (p.toBridgeForest hx hy).IsPath := by
  apply (G.isForest_bridgeForest.isPath_iff_isTrail _).mpr
  rw [Walk.isTrail_def, Walk.edges_toBridgeForest]
  exact ((Walk.isTrail_def p).mp hp).filter _

/-! ### Connected components -/

/-- The connected components of the underlying simple graphs of `G` and of its bridge forest
correspond. -/
private noncomputable def toSimpleGraphComponentEquivBridgeForest (G : Graph α β) :
    G.toSimpleGraph.ConnectedComponent ≃ G.bridgeForest.toSimpleGraph.ConnectedComponent := by
  refine Equiv.ofBijective (SimpleGraph.ConnectedComponent.lift
    (fun z ↦ G.bridgeForest.toSimpleGraph.connectedComponentMk
      ⟨G.bridgeComponentOf z.1 z.2, by simp⟩) fun z w p _ ↦ ?_) ⟨fun C D hCD ↦ ?_, fun C ↦ ?_⟩
  · rw [toSimpleGraph_connectedComponentMk_eq_iff, ← reachable_iff_reachable_bridgeForest]
    exact toSimpleGraph_reachable_iff.mp p.reachable
  · induction C using SimpleGraph.ConnectedComponent.ind with | h z => ?_
    induction D using SimpleGraph.ConnectedComponent.ind with | h w => ?_
    simp only [SimpleGraph.ConnectedComponent.lift_mk,
      toSimpleGraph_connectedComponentMk_eq_iff] at hCD ⊢
    exact (reachable_iff_reachable_bridgeForest z.2 w.2).mpr hCD
  · induction C using SimpleGraph.ConnectedComponent.ind with | h c => ?_
    obtain ⟨x, hx, hc⟩ := c.1.exists_bridgeComponentOf_eq
    exact ⟨G.toSimpleGraph.connectedComponentMk ⟨x, hx⟩, by simp [hc]⟩

private theorem toSimpleGraphComponentEquivBridgeForest_connectedComponentMk (z : V(G)) :
    G.toSimpleGraphComponentEquivBridgeForest (G.toSimpleGraph.connectedComponentMk z) =
      G.bridgeForest.toSimpleGraph.connectedComponentMk ⟨G.bridgeComponentOf z.1 z.2, by simp⟩ :=
  rfl

/-- The connected components of `G` correspond to those of its bridge forest: the component of an
actual vertex `x` corresponds to the component of the bridge component of `x`. -/
noncomputable def connectedComponentEquivBridgeForest (G : Graph α β) :
    G.ConnectedComponent ≃ G.bridgeForest.ConnectedComponent :=
  G.connectedComponentEquiv.trans <|
    G.toSimpleGraphComponentEquivBridgeForest.trans G.bridgeForest.connectedComponentEquiv.symm

@[simp]
theorem connectedComponentEquivBridgeForest_connectedComponentOf (hx : x ∈ V(G)) :
    G.connectedComponentEquivBridgeForest (G.connectedComponentOf x hx) =
      G.bridgeForest.connectedComponentOf (G.bridgeComponentOf x hx) (by simp) := by
  apply G.bridgeForest.connectedComponentEquiv.injective
  simp [connectedComponentEquivBridgeForest,
    toSimpleGraphComponentEquivBridgeForest_connectedComponentMk]

/-- A multigraph and its bridge forest have the same number of connected components. -/
@[simp]
theorem componentCount_bridgeForest (G : Graph α β) :
    G.bridgeForest.componentCount = G.componentCount := by
  rw [componentCount_def, componentCount_def]
  exact (Nat.card_congr G.connectedComponentEquivBridgeForest).symm

/-- The bridge forest is connected, hence a tree, exactly when `G` is connected. -/
@[simp]
theorem connected_bridgeForest_iff : G.bridgeForest.Connected ↔ G.Connected := by
  rw [← componentCount_eq_one_iff, ← componentCount_eq_one_iff, componentCount_bridgeForest]

end Graph
