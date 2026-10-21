/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Order.Minimal

/-!
# Connected components of multigraphs

A connected component of a multigraph is a minimal nonempty closed subgraph.  This formulation
retains every loop and parallel-edge identity in a component, while the component partition of
the actual vertices agrees with the connected components of the underlying simple graph.

The definitions of `Graph.IsConnectedComponentOf` and `Graph.Connected`, together with their
elementary order API, follow Peter Nelson and Jun Kwon's Mathlib proposal
[mathlib4#37861](https://github.com/leanprover-community/mathlib4/pull/37861).  The comparison with
`SimpleGraph.ConnectedComponent` and the finite component count are developed here.

## Main definitions

* `Graph.IsConnectedComponentOf H G` says that `H` is a minimal nonempty closed subgraph of `G`.
* `Graph.Connected G` says that `G` is its own connected component.
* `Graph.ConnectedComponent G` is the type of connected-component subgraphs of `G`.
* `Graph.connectedComponentEquiv` identifies these subgraphs with the connected components of
  `G.toSimpleGraph`.
* `Graph.componentCount G` counts the components when the actual vertex set is finite.
-/

public section

open Set

variable {α β : Type*} {G H K : Graph α β}

namespace Graph

/-! ### Component subgraphs and connectedness -/

/-- A connected component of `G` is a minimal nonempty closed subgraph of `G`. -/
@[expose] def IsConnectedComponentOf (H G : Graph α β) : Prop :=
  Minimal (fun H ↦ H ≤c G ∧ V(H).Nonempty) H

namespace IsConnectedComponentOf

/-- A connected component is closed in its ambient graph. -/
@[simp] theorem isClosedSubgraph (h : H.IsConnectedComponentOf G) : H ≤c G := h.prop.1

/-- A connected component is induced in its ambient graph. -/
theorem isInducedSubgraph (h : H.IsConnectedComponentOf G) : H ≤i G :=
  h.isClosedSubgraph.isInducedSubgraph

/-- A connected component is a subgraph of its ambient graph. -/
@[simp] theorem le (h : H.IsConnectedComponentOf G) : H ≤ G := h.isClosedSubgraph.le

/-- A connected component has an actual vertex. -/
@[grind →] theorem nonempty (h : H.IsConnectedComponentOf G) : V(H).Nonempty := h.prop.2

/-- A component of `G` contained in an intermediate graph is a component of that graph. -/
theorem anti_right (hKH : K ≤ H) (hHG : H ≤ G) (h : K.IsConnectedComponentOf G) :
    K.IsConnectedComponentOf H :=
  ⟨⟨h.isClosedSubgraph.anti_right hKH hHG, h.nonempty⟩, fun _ ⟨hK'H, hK'ne⟩ hK'K ↦
    h.le_of_le ⟨(hK'H.anti_right hK'K hKH).trans h.isClosedSubgraph, hK'ne⟩ hK'K⟩

end IsConnectedComponentOf

/-- A multigraph is connected when it is a connected component of itself.  In particular, the
empty graph is not connected. -/
@[expose] protected def Connected (G : Graph α β) : Prop := G.IsConnectedComponentOf G

/-- A connected graph has an actual vertex. -/
theorem Connected.nonempty (hG : G.Connected) : V(G).Nonempty :=
  IsConnectedComponentOf.nonempty hG

@[simp]
theorem not_connected_bot : ¬(⊥ : Graph α β).Connected := by
  intro h
  simpa using h.nonempty

/-- A nonempty graph is connected exactly when it has no proper nonempty closed subgraph. -/
theorem connected_iff_forall_closed (hG : V(G).Nonempty) :
    G.Connected ↔ ∀ {H}, H ≤c G → V(H).Nonempty → H = G := by
  refine ⟨fun h H hHG hHne ↦ ?_, fun h ↦ ⟨by simpa, fun H ⟨hle, hH⟩ _ ↦
    (h hle hH).symm.le⟩⟩
  rw [Graph.Connected] at h
  exact h.eq_of_le ⟨hHG, hHne⟩ hHG.le

/-- A nonempty graph is connected exactly when every nonempty closed subgraph contains it. -/
theorem connected_iff_forall_closed_ge (hG : V(G).Nonempty) :
    G.Connected ↔ ∀ {H}, H ≤c G → V(H).Nonempty → G ≤ H := by
  rw [connected_iff_forall_closed hG]
  exact ⟨fun h H hle hne ↦ (h hle hne).symm.le,
    fun h H hle hne ↦ (h hle hne).antisymm' hle.le⟩

/-- A nonempty closed subgraph of a connected graph is the whole graph. -/
theorem Connected.ext_of_isClosedSubgraph (hH : H ≤c G) (hne : V(H).Nonempty)
    (hG : G.Connected) : H = G := by
  rw [connected_iff_forall_closed (hne.mono hH.le.vertexSet_mono)] at hG
  exact hG hH hne

/-- Every connected-component subgraph is connected. -/
theorem IsConnectedComponentOf.connected (h : H.IsConnectedComponentOf G) : H.Connected :=
  h.anti_right le_rfl h.le

/-- The connected-component subgraphs of `G`. -/
abbrev ConnectedComponent (G : Graph α β) := {H : Graph α β // H.IsConnectedComponentOf G}

/-! ### Comparison with the underlying simple graph -/

/-- Membership in a closed subgraph propagates along reachability in the underlying simple graph. -/
theorem IsClosedSubgraph.mem_vertexSet_of_toSimpleGraph_reachable (hHG : H ≤c G)
    {x y : V(G)} (hx : (x : α) ∈ V(H)) (hxy : G.toSimpleGraph.Reachable x y) :
    (y : α) ∈ V(H) := by
  apply hxy.elim
  intro p
  induction p with
  | nil => exact hx
  | @cons u v w huv p ih =>
      apply ih
      · exact (hHG.mem_iff_of_adj huv.2).mp hx
      · exact p.reachable

/-- The actual vertices belonging to a component of the underlying simple graph. -/
def connectedComponentVertexSet (G : Graph α β)
    (C : G.toSimpleGraph.ConnectedComponent) : Set α :=
  Subtype.val '' C.supp

/-- A point belongs to the lifted vertex set exactly when it has a proof of membership in the
ambient graph whose corresponding actual vertex lies in the simple component. -/
theorem mem_connectedComponentVertexSet_iff {C : G.toSimpleGraph.ConnectedComponent} {x : α} :
    x ∈ connectedComponentVertexSet G C ↔
      ∃ hx : x ∈ V(G), (Subtype.mk x hx : V(G)) ∈ C.supp := by
  constructor
  · rintro ⟨x, hxC, rfl⟩
    exact ⟨x.property, hxC⟩
  · rintro ⟨hx, hxC⟩
    exact ⟨Subtype.mk x hx, hxC, rfl⟩

/-- The multigraph induced on a component of its underlying simple graph.  It retains all loops
and all parallel-edge identities whose endpoints lie in the component. -/
def connectedComponentSubgraph (G : Graph α β)
    (C : G.toSimpleGraph.ConnectedComponent) : Graph α β :=
  G.induce (connectedComponentVertexSet G C)

@[simp]
theorem vertexSet_connectedComponentSubgraph (C : G.toSimpleGraph.ConnectedComponent) :
    V(G.connectedComponentSubgraph C) = connectedComponentVertexSet G C := (rfl)

/-- Links of a component subgraph are precisely the ambient links with both endpoints in its
component vertex set. -/
@[simp]
theorem connectedComponentSubgraph_isLink (C : G.toSimpleGraph.ConnectedComponent)
    (e : β) (x y : α) :
    (G.connectedComponentSubgraph C).IsLink e x y ↔
      G.IsLink e x y ∧ x ∈ connectedComponentVertexSet G C ∧
        y ∈ connectedComponentVertexSet G C := by
  simp [connectedComponentSubgraph]

/-- The edges of a component subgraph are the ambient edges with both endpoints in its component
vertex set. -/
theorem edgeSet_connectedComponentSubgraph (C : G.toSimpleGraph.ConnectedComponent) :
    E(G.connectedComponentSubgraph C) =
      {e | ∃ x y, G.IsLink e x y ∧ x ∈ connectedComponentVertexSet G C ∧
        y ∈ connectedComponentVertexSet G C} := by
  simp [connectedComponentSubgraph, Graph.edgeSet_induce]

/-- The component subgraph induced by a simple connected component is closed in the multigraph. -/
theorem connectedComponentSubgraph_isClosedSubgraph
    (C : G.toSimpleGraph.ConnectedComponent) : G.connectedComponentSubgraph C ≤c G := by
  refine IsClosedSubgraph.mk'
    (G.induce_le fun _ hx ↦ (mem_connectedComponentVertexSet_iff.mp hx).1) ?_
  intro e x hex hx
  obtain ⟨vx, hvxC, rfl⟩ := hx
  obtain ⟨y, hxy⟩ := hex
  let vy : V(G) := ⟨y, hxy.right_mem⟩
  have hvyC : vy ∈ C.supp := by
    by_cases h : vx = vy
    · simpa [h] using hvxC
    · apply (C.mem_supp_congr_adj ?_).mp hvxC
      rw [Graph.toSimpleGraph_adj]
      exact ⟨h, ⟨e, hxy⟩⟩
  exact ⟨vx, vy, hxy, ⟨vx, hvxC, rfl⟩, ⟨vy, hvyC, rfl⟩⟩

/-- The component subgraph induced by a simple connected component is nonempty. -/
theorem connectedComponentVertexSet_nonempty (C : G.toSimpleGraph.ConnectedComponent) :
    (connectedComponentVertexSet G C).Nonempty := by
  obtain ⟨v, hv⟩ := C.nonempty_supp
  exact ⟨v, v, hv, rfl⟩

/-- Lifting an underlying simple component gives a connected component of the multigraph. -/
theorem connectedComponentSubgraph_isConnectedComponentOf
    (C : G.toSimpleGraph.ConnectedComponent) :
    (G.connectedComponentSubgraph C).IsConnectedComponentOf G := by
  refine ⟨⟨G.connectedComponentSubgraph_isClosedSubgraph C,
    G.connectedComponentVertexSet_nonempty C⟩, ?_⟩
  intro H hH hHG
  obtain ⟨x, hxH⟩ := hH.2
  have hxCset : x ∈ connectedComponentVertexSet G C := hHG.vertexSet_mono hxH
  obtain ⟨_, hxC⟩ := mem_connectedComponentVertexSet_iff.mp hxCset
  apply hH.1.isInducedSubgraph.le_of_le_subset
    (G.induce_le (fun _ hy ↦ (mem_connectedComponentVertexSet_iff.mp hy).1))
  intro y hy
  obtain ⟨_, hyC⟩ := mem_connectedComponentVertexSet_iff.mp hy
  exact hH.1.mem_vertexSet_of_toSimpleGraph_reachable hxH
    (C.reachable_of_mem_supp hxC hyC)

/-- Regard an underlying simple component as a connected-component subgraph. -/
def connectedComponentOfSimple (G : Graph α β)
    (C : G.toSimpleGraph.ConnectedComponent) : G.ConnectedComponent :=
  ⟨G.connectedComponentSubgraph C, G.connectedComponentSubgraph_isConnectedComponentOf C⟩

/-- The subgraph underlying the lifted simple component is its induced component subgraph. -/
@[simp]
theorem coe_connectedComponentOfSimple (C : G.toSimpleGraph.ConnectedComponent) :
    (G.connectedComponentOfSimple C : Graph α β) = G.connectedComponentSubgraph C := (rfl)

noncomputable section

/-- The underlying simple component containing a connected-component subgraph. -/
def ConnectedComponent.toSimple {G : Graph α β} (C : G.ConnectedComponent) :
    G.toSimpleGraph.ConnectedComponent :=
  G.toSimpleGraph.connectedComponentMk
    ⟨Classical.choose C.property.nonempty,
      C.property.le.vertexSet_mono (Classical.choose_spec C.property.nonempty)⟩

/-- A connected-component subgraph is the induced graph on the support of its underlying simple
component. -/
theorem ConnectedComponent.ofSimple_toSimple {G : Graph α β}
    (C : G.ConnectedComponent) : G.connectedComponentOfSimple C.toSimple = C := by
  have hle : G.connectedComponentSubgraph C.toSimple ≤ C := by
    let x : α := Classical.choose C.property.nonempty
    have hxC : x ∈ V(C.1) := Classical.choose_spec C.property.nonempty
    apply C.property.isInducedSubgraph.le_of_le_subset
      (G.induce_le (fun _ hy ↦ (mem_connectedComponentVertexSet_iff.mp hy).1))
    intro y hy
    obtain ⟨_, hyC⟩ := mem_connectedComponentVertexSet_iff.mp hy
    exact C.property.isClosedSubgraph.mem_vertexSet_of_toSimpleGraph_reachable hxC
      (SimpleGraph.ConnectedComponent.exact hyC.symm)
  apply Subtype.ext
  apply le_antisymm
  · exact hle
  · exact C.property.le_of_le
      ⟨G.connectedComponentSubgraph_isClosedSubgraph C.toSimple,
        G.connectedComponentVertexSet_nonempty C.toSimple⟩ hle

/-- The support of the underlying simple component is exactly the actual vertex set of the
component subgraph. -/
theorem ConnectedComponent.mem_toSimple_iff {G : Graph α β} (C : G.ConnectedComponent)
    (x : V(G)) : x ∈ C.toSimple.supp ↔ (x : α) ∈ V(C.1) := by
  have hC : G.connectedComponentSubgraph C.toSimple = C.1 :=
    congrArg Subtype.val C.ofSimple_toSimple
  rw [← hC, vertexSet_connectedComponentSubgraph, mem_connectedComponentVertexSet_iff]
  simp

/-- A vertex lies in the underlying simple component of a connected-component subgraph exactly
when it is a vertex of that subgraph. -/
@[simp]
theorem ConnectedComponent.connectedComponentMk_eq_toSimple_iff {G : Graph α β}
    (C : G.ConnectedComponent) (x : V(G)) :
    G.toSimpleGraph.connectedComponentMk x = C.toSimple ↔ (x : α) ∈ V(C.1) := by
  rw [← SimpleGraph.ConnectedComponent.mem_supp_iff, C.mem_toSimple_iff]

/-- Passing from an underlying simple component to its component subgraph and back recovers the
simple component. -/
@[simp]
theorem connectedComponentOfSimple_toSimple (C : G.toSimpleGraph.ConnectedComponent) :
    (G.connectedComponentOfSimple C).toSimple = C := by
  rw [ConnectedComponent.toSimple]
  apply SimpleGraph.ConnectedComponent.eq_of_common_vertex
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  · have hx := Classical.choose_spec
      (G.connectedComponentOfSimple C).property.nonempty
    exact (mem_connectedComponentVertexSet_iff.mp hx).2

/-- Connected-component subgraphs are equivalent to connected components of the underlying simple
graph. -/
def connectedComponentEquiv (G : Graph α β) :
    G.ConnectedComponent ≃ G.toSimpleGraph.ConnectedComponent where
  toFun := ConnectedComponent.toSimple
  invFun := G.connectedComponentOfSimple
  left_inv := ConnectedComponent.ofSimple_toSimple
  right_inv := connectedComponentOfSimple_toSimple

/-- The component equivalence sends a component subgraph to its underlying simple component. -/
@[simp]
theorem connectedComponentEquiv_apply (C : G.ConnectedComponent) :
    G.connectedComponentEquiv C = C.toSimple := (rfl)

/-- The inverse component equivalence induces the ambient multigraph on a simple component. -/
@[simp]
theorem connectedComponentEquiv_symm_apply (C : G.toSimpleGraph.ConnectedComponent) :
    G.connectedComponentEquiv.symm C = G.connectedComponentOfSimple C := (rfl)

/-! ### Connectedness and the finite component count -/

/-- Multigraph connectedness agrees with connectedness of the underlying simple graph. -/
theorem connected_iff_toSimpleGraph_connected : G.Connected ↔ G.toSimpleGraph.Connected := by
  constructor
  · intro hG
    obtain ⟨x, hxG⟩ := hG.nonempty
    let vx : V(G) := ⟨x, hxG⟩
    apply @SimpleGraph.Connected.mk _ _ (fun u v ↦ ?_) ⟨vx⟩
    let C := G.toSimpleGraph.connectedComponentMk v
    have hCeq : G.connectedComponentSubgraph C = G :=
      (hG.ext_of_isClosedSubgraph (G.connectedComponentSubgraph_isClosedSubgraph C)
        (G.connectedComponentVertexSet_nonempty C))
    apply SimpleGraph.ConnectedComponent.exact
    have hu : (u : α) ∈ connectedComponentVertexSet G C := by
      rw [← vertexSet_connectedComponentSubgraph, hCeq]
      exact u.property
    exact (mem_connectedComponentVertexSet_iff.mp hu).2
  · intro hG
    have hne : V(G).Nonempty := by
      let v : V(G) := Classical.choice hG.nonempty
      exact ⟨v, v.property⟩
    apply (connected_iff_forall_closed hne).2
    intro H hHG hHne
    obtain ⟨x, hxH⟩ := hHne
    apply hHG.isInducedSubgraph.ext_of_vertexSet
    apply Set.Subset.antisymm hHG.le.vertexSet_mono
    intro y hyG
    let vx : V(G) := ⟨x, hHG.le.vertexSet_mono hxH⟩
    let vy : V(G) := ⟨y, hyG⟩
    exact hHG.mem_vertexSet_of_toSimpleGraph_reachable hxH (hG vx vy)

/-- Finitely many actual vertices give finitely many connected-component subgraphs. -/
noncomputable instance instFiniteConnectedComponent (G : Graph α β) [Finite V(G)] :
    Finite G.ConnectedComponent := by
  apply G.connectedComponentEquiv.finite_iff.mpr
  apply Finite.of_surjective G.toSimpleGraph.connectedComponentMk
  intro C
  obtain ⟨v, rfl⟩ := C.exists_rep
  exact ⟨v, rfl⟩

/-- The number of connected-component subgraphs of a graph with finitely many actual vertices. -/
noncomputable def componentCount (G : Graph α β) [Finite V(G)] : Nat :=
  @Fintype.card G.ConnectedComponent (Fintype.ofFinite G.ConnectedComponent)

/-- The component count is the cardinality of the native component-subgraph type. -/
theorem componentCount_eq_natCard_connectedComponent [Finite V(G)] :
    G.componentCount = Nat.card G.ConnectedComponent := by
  exact (@Nat.card_eq_fintype_card G.ConnectedComponent
    (Fintype.ofFinite G.ConnectedComponent)).symm

/-- The component count is the number of connected components of the underlying simple graph. -/
theorem componentCount_eq_natCard_toSimpleGraph [Finite V(G)] :
    G.componentCount = Nat.card G.toSimpleGraph.ConnectedComponent := by
  rw [componentCount_eq_natCard_connectedComponent]
  exact Nat.card_congr G.connectedComponentEquiv

/-- The component count of a simple graph regarded as a multigraph is its usual number of
connected components. -/
theorem componentCount_ofSimpleGraph [Finite α] (H : SimpleGraph α) :
    (Graph.ofSimpleGraph H).componentCount = Nat.card H.ConnectedComponent := by
  rw [componentCount_eq_natCard_toSimpleGraph]
  exact Nat.card_congr (Graph.toSimpleGraphOfSimpleGraphIso H).connectedComponentEquiv

/-- A finite multigraph has no components exactly when it has no actual vertices. -/
@[simp]
theorem componentCount_eq_zero_iff [Finite V(G)] : G.componentCount = 0 ↔ V(G) = ∅ := by
  rw [componentCount_eq_natCard_toSimpleGraph]
  have hfinite : Finite G.toSimpleGraph.ConnectedComponent :=
    G.connectedComponentEquiv.finite_iff.mp inferInstance
  rw [Nat.card_eq_zero, or_iff_left (not_infinite_iff_finite.mpr hfinite),
    SimpleGraph.isEmpty_connectedComponent_iff, Set.isEmpty_coe_sort]

/-- A finite multigraph has one component exactly when it is connected. -/
@[simp]
theorem componentCount_eq_one_iff [Finite V(G)] : G.componentCount = 1 ↔ G.Connected := by
  rw [componentCount_eq_natCard_toSimpleGraph,
    SimpleGraph.card_connectedComponent_eq_one_iff, ← connected_iff_toSimpleGraph_connected]

/-! ### Basic examples -/

/-- The empty graph has no connected components. -/
@[simp]
theorem componentCount_bot :
    @componentCount α β (⊥ : Graph α β) (Set.finite_coe_iff.mpr (by simp)) = 0 := by
  apply (@componentCount_eq_zero_iff α β (⊥ : Graph α β)
    (Set.finite_coe_iff.mpr (by simp))).2
  rfl

/-- A single isolated vertex is one connected component. -/
@[simp]
theorem componentCount_noEdge_singleton (x : α) :
    @componentCount α β (Graph.noEdge ({x} : Set α) β)
      (Set.finite_coe_iff.mpr (by simp)) = 1 := by
  apply (@componentCount_eq_one_iff α β (Graph.noEdge ({x} : Set α) β)
    (Set.finite_coe_iff.mpr (by simp))).2
  rw [connected_iff_toSimpleGraph_connected]
  apply @SimpleGraph.Connected.mk _ _ (fun u v ↦ ?_) ⟨Subtype.mk x (by simp)⟩
  have huv : u = v := by
    apply Subtype.ext
    have hu : (u : α) = x := by simpa using u.property
    have hv : (v : α) = x := by simpa using v.property
    exact hu.trans hv.symm
  subst v
  exact SimpleGraph.Reachable.rfl

/-- A single edge joining two distinct vertices is connected. -/
@[simp]
theorem componentCount_banana_singleton {x y : α} (hxy : x ≠ y) (e : β) :
    @componentCount α β (Graph.banana x y {e})
      (Set.finite_coe_iff.mpr (by simp)) = 1 := by
  apply (@componentCount_eq_one_iff α β (Graph.banana x y {e})
    (Set.finite_coe_iff.mpr (by simp))).2
  rw [connected_iff_toSimpleGraph_connected]
  apply @SimpleGraph.Connected.mk _ _ (fun u v ↦ ?_) ⟨Subtype.mk x (by simp)⟩
  rcases u with ⟨u, hu⟩
  rcases v with ⟨v, hv⟩
  simp only [Graph.vertexSet_banana, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact SimpleGraph.Reachable.rfl
  · exact SimpleGraph.Adj.reachable (by
      rw [Graph.toSimpleGraph_adj]
      exact ⟨by simpa, ⟨e, by simp⟩⟩)
  · exact (SimpleGraph.Adj.reachable (by
      rw [Graph.toSimpleGraph_adj]
      exact ⟨by simpa using hxy, ⟨e, by simp⟩⟩)).symm
  · exact SimpleGraph.Reachable.rfl

end

end Graph
