/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Bridge

/-!
# The bridge forest of a multigraph

Delete every bridge of a multigraph and contract each connected component that remains to a
vertex. The original bridges then form a forest on these components. This construction retains
the identities of parallel edges in the original graph, while proving that distinct bridges can
never become parallel in the contracted graph.

The canonical vertex map preserves reachability. Conversely, a walk in the bridge forest lifts,
between any prescribed vertices in its endpoint components, to a walk in the original graph.
The lifting result also holds after deleting any set of bridges and is the key fact showing that
every edge of the contracted graph is itself a bridge.

This is the standard bridge forest (or bridge tree in the connected case); see Reinhard Diestel,
*Graph Theory*, Chapter 3.

## Main definitions

* `Graph.bridgeDeletion` is the graph obtained by deleting all bridges.
* `Graph.BridgeComponent` is the type of connected components of `bridgeDeletion`.
* `Graph.bridgeComponentOf` sends an actual vertex to its bridge-free component.
* `Graph.bridgeForest` has the bridge-free components as vertices and the original bridges as
  edges.

## Main results

* `Graph.bridgeComponentOf_surjective` says that every bridge-free component contains an
  original vertex.
* `Graph.reachable_deleteEdges_of_bridgeForest_reachable` lifts reachability after deleting any
  set of bridges.
* `Graph.isForest_bridgeForest` proves that the contracted graph is a forest.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- The set of all bridges of a multigraph. -/
def bridgeSet (G : Graph α β) : Set β := {e | G.IsBridge e}

@[simp]
theorem mem_bridgeSet {e : β} : e ∈ G.bridgeSet ↔ G.IsBridge e := Iff.rfl

/-- The spanning subgraph obtained by deleting every bridge. -/
def bridgeDeletion (G : Graph α β) : Graph α β := G.deleteEdges G.bridgeSet

@[simp]
theorem vertexSet_bridgeDeletion : V(G.bridgeDeletion) = V(G) := by
  simp [bridgeDeletion]

@[simp]
theorem edgeSet_bridgeDeletion : E(G.bridgeDeletion) = E(G) \ G.bridgeSet := by
  simp [bridgeDeletion]

@[simp]
theorem bridgeDeletion_isLink {e : β} {x y : α} :
    G.bridgeDeletion.IsLink e x y ↔ G.IsLink e x y ∧ ¬G.IsBridge e := by
  simp [bridgeDeletion, bridgeSet]

/-- A bridge-free component is a connected component after all bridges have been deleted. -/
abbrev BridgeComponent (G : Graph α β) := G.bridgeDeletion.ConnectedComponent

noncomputable section

/-- The bridge-free component containing an actual vertex. -/
def bridgeComponentOf (G : Graph α β) (x : V(G)) : G.BridgeComponent :=
  G.bridgeDeletion.connectedComponentOf x (by simp)

/-- An actual vertex belongs to the bridge-free component to which it is sent. -/
theorem mem_bridgeComponentOf (G : Graph α β) (x : V(G)) :
    (x : α) ∈ V((G.bridgeComponentOf x).1) :=
  mem_vertexSet_connectedComponentOf_self _

/-- Every bridge-free component contains an original vertex. -/
theorem bridgeComponentOf_surjective (G : Graph α β) :
    Function.Surjective G.bridgeComponentOf := by
  intro C
  obtain ⟨x, hx⟩ := C.property.nonempty
  let xG : V(G) := ⟨x, by simpa using C.property.le.vertexSet_mono hx⟩
  exact ⟨xG, (C.eq_connectedComponentOf hx).symm⟩

/-- The bridge forest has one vertex for each component left after deleting all bridges and one
edge, with its original identity, for each bridge. -/
def bridgeForest (G : Graph α β) : Graph G.BridgeComponent β where
  vertexSet := univ
  IsLink e C D := G.IsBridge e ∧ ∃ x y, ∃ h : G.IsLink e x y,
    C = G.bridgeComponentOf ⟨x, h.left_mem⟩ ∧
      D = G.bridgeComponentOf ⟨y, h.right_mem⟩
  edgeSet := G.bridgeSet
  isLink_symm := by
    simp only [symm_def]
    rintro e _ C D ⟨he, x, y, h, rfl, rfl⟩
    exact ⟨he, y, x, h.symm, rfl, rfl⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e C D C' D' ⟨_, x, y, h, rfl, rfl⟩ ⟨_, x', y', h', rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.eq_and_eq_or_eq_and_eq h'
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · intro he
      obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he.mem_edgeSet
      exact ⟨_, _, he, x, y, h, rfl, rfl⟩
    · rintro ⟨_, _, he, _, _, _, _, _⟩
      exact he
  left_mem_of_isLink := by simp

@[simp]
theorem vertexSet_bridgeForest : V(G.bridgeForest) = univ := by
  simp [bridgeForest]

@[simp]
theorem edgeSet_bridgeForest : E(G.bridgeForest) = G.bridgeSet := by
  simp [bridgeForest]

/-- Characterization of incidence in the bridge forest by the original endpoints of a bridge. -/
theorem bridgeForest_isLink_iff {e : β} {C D : G.BridgeComponent} :
    G.bridgeForest.IsLink e C D ↔ G.IsBridge e ∧ ∃ x y, ∃ h : G.IsLink e x y,
      C = G.bridgeComponentOf ⟨x, h.left_mem⟩ ∧
        D = G.bridgeComponentOf ⟨y, h.right_mem⟩ := by
  simp [bridgeForest]

/-- A bridge becomes an edge between the bridge-free components of either choice of its ends. -/
theorem IsBridge.isLink_bridgeForest (he : G.IsBridge e) (h : G.IsLink e x y) :
    G.bridgeForest.IsLink e (G.bridgeComponentOf ⟨x, h.left_mem⟩)
      (G.bridgeComponentOf ⟨y, h.right_mem⟩) :=
  ⟨he, x, y, h, rfl, rfl⟩

/-- Deleting all bridges gives a subgraph of the graph obtained by deleting any selected set of
bridges. -/
theorem bridgeDeletion_le_deleteEdges {F : Set β} (hF : F ⊆ G.bridgeSet) :
    G.bridgeDeletion ≤ G.deleteEdges F := by
  refine ⟨by simp, fun e x y h ↦ ?_⟩
  rw [bridgeDeletion_isLink] at h
  rw [deleteEdges_isLink]
  exact ⟨h.1, fun heF ↦ h.2 (hF heF)⟩

/-- Any two vertices in one bridge-free component remain reachable after deleting an arbitrary
set of bridges. -/
theorem BridgeComponent.reachable_deleteEdges {F : Set β} (hF : F ⊆ G.bridgeSet)
    (C : G.BridgeComponent) {x y : α} (hx : x ∈ V(C.1)) (hy : y ∈ V(C.1)) :
    (G.deleteEdges F).Reachable x y :=
  (C.property.connected.reachable hx hy).mono
    (C.property.le.trans (G.bridgeDeletion_le_deleteEdges hF))

/-- Reachability in the bridge forest after deleting bridges lifts to reachability in the
original graph after deleting the same edges, between any prescribed vertices in the endpoint
components. -/
theorem reachable_deleteEdges_of_bridgeForest_reachable {F : Set β}
    (hF : F ⊆ G.bridgeSet) {C D : G.BridgeComponent}
    (hCD : (G.bridgeForest.deleteEdges F).Reachable C D)
    {x y : α} (hx : x ∈ V(C.1)) (hy : y ∈ V(D.1)) :
    (G.deleteEdges F).Reachable x y := by
  obtain ⟨_, ⟨p⟩⟩ := reachable_def.mp hCD
  have lift : ∀ {C D : G.BridgeComponent}
      (p : (G.bridgeForest.deleteEdges F).Walk C D) {x y : α},
      x ∈ V(C.1) → y ∈ V(D.1) → (G.deleteEdges F).Reachable x y := by
    intro C D p x y hx hy
    induction p generalizing x with
    | nil => exact BridgeComponent.reachable_deleteEdges hF _ hx hy
    | @cons C D E e hCD p ih =>
        rw [deleteEdges_isLink] at hCD
        obtain ⟨⟨he, a, b, hab, rfl, rfl⟩, heF⟩ := hCD
        have hxa : (G.deleteEdges F).Reachable x a :=
          (G.bridgeComponentOf ⟨a, hab.left_mem⟩).reachable_deleteEdges hF hx
            (G.mem_bridgeComponentOf ⟨a, hab.left_mem⟩)
        have habF : (G.deleteEdges F).Reachable a b := by
          apply IsLink.reachable
          rw [deleteEdges_isLink]
          exact ⟨hab, heF⟩
        exact hxa.trans (habF.trans (ih (G.mem_bridgeComponentOf ⟨b, hab.right_mem⟩) hy))
  exact lift p hx hy

/-- The component map sends every original link to reachable bridge-forest vertices. A bridge
gives one forest edge; a nonbridge stays inside a single bridge-free component. -/
theorem IsLink.bridgeComponentOf_reachable (h : G.IsLink e x y) :
    G.bridgeForest.Reachable (G.bridgeComponentOf ⟨x, h.left_mem⟩)
      (G.bridgeComponentOf ⟨y, h.right_mem⟩) := by
  by_cases he : G.IsBridge e
  · exact (he.isLink_bridgeForest h).reachable
  · have hcomp : G.bridgeComponentOf ⟨x, h.left_mem⟩ =
        G.bridgeComponentOf ⟨y, h.right_mem⟩ := by
      unfold bridgeComponentOf
      rw [connectedComponentOf_eq_connectedComponentOf_iff]
      exact (bridgeDeletion_isLink.mpr ⟨h, he⟩).reachable
    rw [hcomp]
    exact Reachable.refl (by simp)

/-- The canonical map from original vertices to bridge-free components preserves reachability. -/
theorem Reachable.bridgeComponentOf {x y : α} (h : G.Reachable x y) :
    G.bridgeForest.Reachable (G.bridgeComponentOf ⟨x, h.left_mem⟩)
      (G.bridgeComponentOf ⟨y, h.right_mem⟩) := by
  obtain ⟨_, ⟨p⟩⟩ := reachable_def.mp h
  have mapWalk : ∀ {x y : α} (p : G.Walk x y) (hx : x ∈ V(G)),
      G.bridgeForest.Reachable (G.bridgeComponentOf ⟨x, hx⟩)
        (G.bridgeComponentOf ⟨y, p.end_mem_vertexSet hx⟩) := by
    intro x y p hx
    induction p with
    | nil => exact Reachable.refl (by simp)
    | cons e hxy p ih => exact hxy.bridgeComponentOf_reachable.trans (ih hxy.right_mem)
  simpa only using mapWalk p h.left_mem

/-- Two original vertices are reachable exactly when their bridge-free components are reachable
in the bridge forest. -/
theorem bridgeForest_reachable_iff (x y : V(G)) :
    G.bridgeForest.Reachable (G.bridgeComponentOf x) (G.bridgeComponentOf y) ↔
      G.Reachable x y := by
  constructor
  · intro h
    have h' := G.reachable_deleteEdges_of_bridgeForest_reachable (F := ∅) (by simp)
      (by simpa using h) (G.mem_bridgeComponentOf x) (G.mem_bridgeComponentOf y)
    simpa using h'
  · exact fun h ↦ h.bridgeComponentOf

/-- Contracting bridge-free components neither joins nor separates connected components. In
particular, the bridge forest is connected exactly when the original graph is connected. -/
theorem connected_bridgeForest_iff : G.bridgeForest.Connected ↔ G.Connected := by
  rw [connected_iff_forall_reachable, connected_iff_forall_reachable]
  constructor
  · rintro ⟨hne, hreach⟩
    obtain ⟨C, -⟩ := hne
    obtain ⟨x, hx⟩ := C.property.nonempty
    refine ⟨⟨x, by simpa using C.property.le.vertexSet_mono hx⟩, ?_⟩
    intro x y hx hy
    exact (G.bridgeForest_reachable_iff ⟨x, hx⟩ ⟨y, hy⟩).mp (hreach (by simp) (by simp))
  · rintro ⟨⟨x, hx⟩, hreach⟩
    refine ⟨⟨G.bridgeComponentOf ⟨x, hx⟩, by simp⟩, ?_⟩
    intro C D _ _
    obtain ⟨x, rfl⟩ := G.bridgeComponentOf_surjective C
    obtain ⟨y, rfl⟩ := G.bridgeComponentOf_surjective D
    exact (G.bridgeForest_reachable_iff x y).mpr (hreach x.property y.property)

/-- The two ends of a bridge belong to distinct bridge-free components. -/
theorem IsBridge.bridgeComponentOf_ne (he : G.IsBridge e) (h : G.IsLink e x y) :
    G.bridgeComponentOf ⟨x, h.left_mem⟩ ≠ G.bridgeComponentOf ⟨y, h.right_mem⟩ := by
  intro hxy
  have hreach : (G.bridgeDeletion).Reachable x y := by
    unfold bridgeComponentOf at hxy
    rw [← connectedComponentOf_eq_connectedComponentOf_iff]
    exact hxy
  exact he.not_reachable_deleteEdges h
    (hreach.mono (G.bridgeDeletion_le_deleteEdges (F := {e}) (by simpa [bridgeSet] using he)))

/-- Every edge of the bridge forest is a bridge. -/
private theorem isBridge_bridgeForest_of_mem {e : β} (he : e ∈ E(G.bridgeForest)) :
    G.bridgeForest.IsBridge e := by
  rw [isBridge_iff_exists_not_reachable_deleteEdges]
  obtain ⟨C, D, hCD⟩ := exists_isLink_of_mem_edgeSet he
  refine ⟨C, D, hCD, fun hreach ↦ ?_⟩
  obtain ⟨heG, x, y, hxy, rfl, rfl⟩ := hCD
  exact heG.not_reachable_deleteEdges hxy
    (G.reachable_deleteEdges_of_bridgeForest_reachable (F := {e})
      (by simpa [bridgeSet] using heG) hreach
      (G.mem_bridgeComponentOf ⟨x, hxy.left_mem⟩)
      (G.mem_bridgeComponentOf ⟨y, hxy.right_mem⟩))

/-- The bridge forest of every multigraph is a forest. -/
theorem isForest_bridgeForest (G : Graph α β) : G.bridgeForest.IsForest :=
  isForest_iff_forall_isBridge.mpr fun _ he ↦ isBridge_bridgeForest_of_mem he

end

end Graph
