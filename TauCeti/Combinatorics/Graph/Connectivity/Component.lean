/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.Minimal
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.OfSimpleGraph

import Mathlib.Basic.Finite.Sum
import Mathlib.SetTheory.Cardinal.Finite

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
* `Graph.connectedComponentOf G x hx` is the connected component containing the vertex `x`.
* `Graph.connectedComponentEquiv` identifies these subgraphs with the connected components of
  `G.toSimpleGraph`.
* `Graph.componentCount G` counts the components via `Nat.card`, so it is `0` if there are
  infinitely many; it is exact whenever there are finitely many components.
* `Graph.toSimpleGraphHomOfLE` is the homomorphism of underlying simple graphs induced by a
  subgraph inclusion, along which simple components can be mapped.
* `Graph.ConnectedComponent.mapOfLE` maps native components along a subgraph inclusion.

Component membership is described by the walk-based `Graph.Reachable`, which agrees with
reachability in the underlying simple graph.
-/

public section

open Set

variable {α β : Type*} {G H K : Graph α β}

namespace Graph

/-! ### Component subgraphs and connectedness -/

/-- A connected component of `G` is a minimal nonempty closed subgraph of `G`. -/
def IsConnectedComponentOf (H G : Graph α β) : Prop :=
  Minimal (fun H ↦ H ≤c G ∧ V(H).Nonempty) H

/-- A connected component of `G` is a nonempty closed subgraph of `G` that contains no smaller
nonempty closed subgraph of `G`. -/
theorem isConnectedComponentOf_iff : H.IsConnectedComponentOf G ↔
    H ≤c G ∧ V(H).Nonempty ∧ ∀ ⦃K⦄, K ≤c G → V(K).Nonempty → K ≤ H → K = H := by
  rw [IsConnectedComponentOf, minimal_iff, and_assoc]
  exact and_congr_right fun _ ↦ and_congr_right fun _ ↦
    ⟨fun h _ hK hne hle ↦ (h ⟨hK, hne⟩ hle).symm, fun h _ hK hle ↦ (h hK.1 hK.2 hle).symm⟩

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
protected def Connected (G : Graph α β) : Prop := G.IsConnectedComponentOf G

/-- A multigraph is connected exactly when it is a connected component of itself. -/
theorem connected_iff_isConnectedComponentOf_self : G.Connected ↔ G.IsConnectedComponentOf G :=
  Iff.rfl

/-- A connected graph has an actual vertex. -/
theorem Connected.nonempty (hG : G.Connected) : V(G).Nonempty :=
  IsConnectedComponentOf.nonempty hG

/-- The empty graph is not connected. -/
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

/-- The actual vertices belonging to a component of the underlying simple graph. -/
def connectedComponentVertexSet (G : Graph α β)
    (C : G.toSimpleGraph.ConnectedComponent) : Set α :=
  Subtype.val '' C.supp

/-- A point belongs to the lifted vertex set exactly when it has a proof of membership in the
ambient graph whose corresponding actual vertex lies in the simple component. -/
@[simp]
theorem mem_connectedComponentVertexSet_iff {C : G.toSimpleGraph.ConnectedComponent} {x : α} :
    x ∈ connectedComponentVertexSet G C ↔
      ∃ hx : x ∈ V(G), (Subtype.mk x hx : V(G)) ∈ C.supp := by
  rw [connectedComponentVertexSet, Subtype.coe_image]
  rfl

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

/-- The component subgraph induced by a simple connected component is a subgraph of the
multigraph. -/
theorem connectedComponentSubgraph_le (C : G.toSimpleGraph.ConnectedComponent) :
    G.connectedComponentSubgraph C ≤ G :=
  G.induce_le fun _ hx ↦ (mem_connectedComponentVertexSet_iff.mp hx).1

/-- The component subgraph induced by a simple connected component is closed in the multigraph. -/
theorem connectedComponentSubgraph_isClosedSubgraph
    (C : G.toSimpleGraph.ConnectedComponent) : G.connectedComponentSubgraph C ≤c G := by
  refine IsClosedSubgraph.mk' (G.connectedComponentSubgraph_le C) ?_
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

/-- A closed subgraph sharing a vertex with a simple component contains the whole component
subgraph. -/
theorem connectedComponentSubgraph_le_of_isClosedSubgraph
    {C : G.toSimpleGraph.ConnectedComponent} (hH : H ≤c G) {x : V(G)} (hxC : x ∈ C.supp)
    (hxH : (x : α) ∈ V(H)) : G.connectedComponentSubgraph C ≤ H := by
  apply hH.isInducedSubgraph.le_of_le_subset (G.connectedComponentSubgraph_le C)
  intro y hy
  obtain ⟨_, hyC⟩ := mem_connectedComponentVertexSet_iff.mp hy
  exact hH.mem_vertexSet_of_reachable hxH
    (toSimpleGraph_reachable_iff.mp (C.reachable_of_mem_supp hxC hyC))

/-- Lifting an underlying simple component gives a connected component of the multigraph. -/
theorem connectedComponentSubgraph_isConnectedComponentOf
    (C : G.toSimpleGraph.ConnectedComponent) :
    (G.connectedComponentSubgraph C).IsConnectedComponentOf G := by
  refine ⟨⟨G.connectedComponentSubgraph_isClosedSubgraph C,
    G.connectedComponentVertexSet_nonempty C⟩, ?_⟩
  intro H hH hHG
  obtain ⟨x, hxH⟩ := hH.2
  obtain ⟨_, hxC⟩ := mem_connectedComponentVertexSet_iff.mp (hHG.vertexSet_mono hxH)
  exact connectedComponentSubgraph_le_of_isClosedSubgraph hH.1 hxC hxH

/-- Regard an underlying simple component as a connected-component subgraph. -/
def ConnectedComponent.ofSimple (C : G.toSimpleGraph.ConnectedComponent) :
    G.ConnectedComponent :=
  ⟨G.connectedComponentSubgraph C, G.connectedComponentSubgraph_isConnectedComponentOf C⟩

/-- The subgraph underlying the lifted simple component is its induced component subgraph. -/
@[simp]
theorem ConnectedComponent.coe_ofSimple (C : G.toSimpleGraph.ConnectedComponent) :
    (ConnectedComponent.ofSimple C : Graph α β) = G.connectedComponentSubgraph C := (rfl)

noncomputable section

/-- The underlying simple component containing a connected-component subgraph. -/
def ConnectedComponent.toSimple {G : Graph α β} (C : G.ConnectedComponent) :
    G.toSimpleGraph.ConnectedComponent :=
  G.toSimpleGraph.connectedComponentMk
    ⟨Classical.choose C.property.nonempty,
      C.property.le.vertexSet_mono (Classical.choose_spec C.property.nonempty)⟩

/-- A connected-component subgraph is the induced graph on the support of its underlying simple
component. -/
@[simp]
theorem ConnectedComponent.ofSimple_toSimple {G : Graph α β}
    (C : G.ConnectedComponent) : ofSimple C.toSimple = C := by
  have hle : G.connectedComponentSubgraph C.toSimple ≤ C :=
    connectedComponentSubgraph_le_of_isClosedSubgraph C.property.isClosedSubgraph
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      (Classical.choose_spec C.property.nonempty)
  apply Subtype.ext
  apply le_antisymm
  · exact hle
  · exact C.property.le_of_le
      ⟨G.connectedComponentSubgraph_isClosedSubgraph C.toSimple,
        G.connectedComponentVertexSet_nonempty C.toSimple⟩ hle

/-- The support of the underlying simple component is exactly the actual vertex set of the
component subgraph. -/
theorem ConnectedComponent.mem_supp_toSimple_iff {G : Graph α β} (C : G.ConnectedComponent)
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
  rw [← SimpleGraph.ConnectedComponent.mem_supp_iff, C.mem_supp_toSimple_iff]

/-- Passing from an underlying simple component to its component subgraph and back recovers the
simple component. -/
@[simp]
theorem ConnectedComponent.toSimple_ofSimple (C : G.toSimpleGraph.ConnectedComponent) :
    (ofSimple C).toSimple = C := by
  rw [ConnectedComponent.toSimple]
  apply SimpleGraph.ConnectedComponent.eq_of_common_vertex
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  · have hx := Classical.choose_spec (ofSimple C).property.nonempty
    exact (mem_connectedComponentVertexSet_iff.mp hx).2

/-- Connected-component subgraphs are equivalent to connected components of the underlying simple
graph. -/
def connectedComponentEquiv (G : Graph α β) :
    G.ConnectedComponent ≃ G.toSimpleGraph.ConnectedComponent where
  toFun := ConnectedComponent.toSimple
  invFun := ConnectedComponent.ofSimple
  left_inv := ConnectedComponent.ofSimple_toSimple
  right_inv := ConnectedComponent.toSimple_ofSimple

/-- The component equivalence sends a component subgraph to its underlying simple component. -/
@[simp]
theorem connectedComponentEquiv_apply (C : G.ConnectedComponent) :
    G.connectedComponentEquiv C = C.toSimple := (rfl)

/-- The inverse component equivalence induces the ambient multigraph on a simple component. -/
@[simp]
theorem connectedComponentEquiv_symm_apply (C : G.toSimpleGraph.ConnectedComponent) :
    G.connectedComponentEquiv.symm C = ConnectedComponent.ofSimple C := (rfl)

/-- Two connected components sharing a vertex are equal. -/
theorem IsConnectedComponentOf.eq_of_mem_of_mem (hH : H.IsConnectedComponentOf G)
    (hK : K.IsConnectedComponentOf G) {x : α} (hxH : x ∈ V(H)) (hxK : x ∈ V(K)) : H = K := by
  let vx : V(G) := ⟨x, hH.le.vertexSet_mono hxH⟩
  have h : ConnectedComponent.toSimple ⟨H, hH⟩ = ConnectedComponent.toSimple ⟨K, hK⟩ := by
    rw [← (ConnectedComponent.connectedComponentMk_eq_toSimple_iff _ vx).mpr hxH,
      ← (ConnectedComponent.connectedComponentMk_eq_toSimple_iff _ vx).mpr hxK]
  exact congrArg Subtype.val (G.connectedComponentEquiv.injective h)

/-- Two connected-component subgraphs sharing a vertex are equal. -/
theorem ConnectedComponent.eq_of_mem_of_mem {C D : G.ConnectedComponent} {x : α}
    (hxC : x ∈ V(C.1)) (hxD : x ∈ V(D.1)) : C = D :=
  Subtype.ext (C.property.eq_of_mem_of_mem D.property hxC hxD)

/-- Two actual vertices have the same simple component exactly when they are reachable from each
other. -/
theorem toSimpleGraph_connectedComponentMk_eq_iff {z w : V(G)} :
    G.toSimpleGraph.connectedComponentMk z = G.toSimpleGraph.connectedComponentMk w ↔
      G.Reachable z w := by
  rw [SimpleGraph.ConnectedComponent.eq, toSimpleGraph_reachable_iff]

/-- The connected-component subgraph containing an actual vertex. -/
def connectedComponentOf (G : Graph α β) (x : α) (hx : x ∈ V(G)) : G.ConnectedComponent :=
  ConnectedComponent.ofSimple (G.toSimpleGraph.connectedComponentMk ⟨x, hx⟩)

/-- The underlying simple component of the component of `x` is the simple component of `x`. -/
@[simp]
theorem ConnectedComponent.toSimple_connectedComponentOf {x : α} (hx : x ∈ V(G)) :
    (G.connectedComponentOf x hx).toSimple = G.toSimpleGraph.connectedComponentMk ⟨x, hx⟩ :=
  toSimple_ofSimple _

/-- A vertex lies in the component of `x` exactly when it is reachable from `x`. -/
@[simp]
theorem mem_vertexSet_connectedComponentOf_iff {x y : α} (hx : x ∈ V(G)) :
    y ∈ V((G.connectedComponentOf x hx).1) ↔ G.Reachable x y := by
  rw [connectedComponentOf, ConnectedComponent.coe_ofSimple,
    vertexSet_connectedComponentSubgraph, mem_connectedComponentVertexSet_iff]
  simp only [SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.eq, toSimpleGraph_reachable_iff]
  exact ⟨fun ⟨_, h⟩ ↦ h.symm, fun h ↦ ⟨h.right_mem, h.symm⟩⟩

/-- A vertex lies in its own connected component. -/
theorem mem_vertexSet_connectedComponentOf_self {x : α} (hx : x ∈ V(G)) :
    x ∈ V((G.connectedComponentOf x hx).1) :=
  (mem_vertexSet_connectedComponentOf_iff hx).mpr (Reachable.refl hx)

/-- Two vertices have the same connected component exactly when they are reachable from each
other. -/
@[simp]
theorem connectedComponentOf_eq_connectedComponentOf_iff {x y : α} (hx : x ∈ V(G))
    (hy : y ∈ V(G)) :
    G.connectedComponentOf x hx = G.connectedComponentOf y hy ↔ G.Reachable x y := by
  rw [← G.connectedComponentEquiv.injective.eq_iff, connectedComponentEquiv_apply,
    connectedComponentEquiv_apply, ConnectedComponent.toSimple_connectedComponentOf,
    ConnectedComponent.toSimple_connectedComponentOf, SimpleGraph.ConnectedComponent.eq,
    toSimpleGraph_reachable_iff]

/-- A connected-component subgraph is the component of each of its vertices. -/
theorem ConnectedComponent.eq_connectedComponentOf {C : G.ConnectedComponent} {x : α}
    (hx : x ∈ V(C.1)) : C = G.connectedComponentOf x (C.property.le.vertexSet_mono hx) :=
  eq_of_mem_of_mem hx (mem_vertexSet_connectedComponentOf_self _)

/-- A subgraph is a connected component exactly when it is induced on a component of the
underlying simple graph. -/
theorem isConnectedComponentOf_iff_exists_eq_connectedComponentSubgraph :
    H.IsConnectedComponentOf G ↔
      ∃ C : G.toSimpleGraph.ConnectedComponent, H = G.connectedComponentSubgraph C := by
  refine ⟨fun h ↦ ⟨ConnectedComponent.toSimple ⟨H, h⟩, ?_⟩, ?_⟩
  · exact (congrArg Subtype.val (ConnectedComponent.ofSimple_toSimple ⟨H, h⟩)).symm
  · rintro ⟨C, rfl⟩
    exact G.connectedComponentSubgraph_isConnectedComponentOf C

/-! ### Connectedness and the component count -/

/-- Multigraph connectedness agrees with connectedness of the underlying simple graph. -/
theorem connected_iff_toSimpleGraph_connected : G.Connected ↔ G.toSimpleGraph.Connected := by
  constructor
  · intro hG
    obtain ⟨x, hxG⟩ := hG.nonempty
    let vx : V(G) := ⟨x, hxG⟩
    refine (SimpleGraph.connected_iff _).mpr ⟨fun u v ↦ ?_, ⟨vx⟩⟩
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
    obtain ⟨v⟩ := hG.nonempty
    refine (connected_iff_forall_closed_ge (G := G) ⟨v, v.property⟩).2
      fun {H} hHG ⟨x, hxH⟩ ↦ ?_
    let vx : V(G) := ⟨x, hHG.le.vertexSet_mono hxH⟩
    have hle := connectedComponentSubgraph_le_of_isClosedSubgraph hHG
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem (x := vx) hxH
    refine hHG.isInducedSubgraph.le_of_le_subset le_rfl fun y hy ↦ hle.vertexSet_mono ?_
    exact mem_connectedComponentVertexSet_iff.mpr
      ⟨hy, SimpleGraph.ConnectedComponent.sound (hG ⟨y, hy⟩ vx)⟩

/-- A multigraph is connected exactly when it has an actual vertex and any two actual vertices
are reachable from each other. -/
theorem connected_iff_forall_reachable :
    G.Connected ↔ V(G).Nonempty ∧ ∀ ⦃x y : α⦄, x ∈ V(G) → y ∈ V(G) → G.Reachable x y := by
  rw [connected_iff_toSimpleGraph_connected, SimpleGraph.connected_iff, and_comm]
  refine and_congr Set.nonempty_coe_sort ⟨fun h x y hx hy ↦ ?_, fun h u v ↦ ?_⟩
  · exact toSimpleGraph_reachable_iff.mp (h ⟨x, hx⟩ ⟨y, hy⟩)
  · exact toSimpleGraph_reachable_iff.mpr (h u.2 v.2)

/-- Any two actual vertices of a connected multigraph are reachable from each other. -/
theorem Connected.reachable (hG : G.Connected) {x y : α} (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.Reachable x y :=
  (connected_iff_forall_reachable.mp hG).2 hx hy

/-- Finitely many actual vertices give finitely many connected-component subgraphs. -/
instance [Finite V(G)] : Finite G.ConnectedComponent :=
  G.connectedComponentEquiv.finite_iff.mpr inferInstance

/-- The number of connected-component subgraphs of `G`, or `0` if there are infinitely many. -/
noncomputable def componentCount (G : Graph α β) : Nat :=
  Nat.card G.ConnectedComponent

/-- The component count is the cardinality of the native component-subgraph type. -/
theorem componentCount_def :
    G.componentCount = Nat.card G.ConnectedComponent := (rfl)

/-- The component count is the number of connected components of the underlying simple graph. -/
theorem componentCount_eq_natCard_toSimpleGraph :
    G.componentCount = Nat.card G.toSimpleGraph.ConnectedComponent := by
  rw [componentCount_def]
  exact Nat.card_congr G.connectedComponentEquiv

/-- The component count of a simple graph regarded as a multigraph is its usual number of
connected components. -/
theorem componentCount_ofSimpleGraph (H : SimpleGraph α) :
    (Graph.ofSimpleGraph H).componentCount = Nat.card H.ConnectedComponent := by
  rw [componentCount_eq_natCard_toSimpleGraph]
  exact Nat.card_congr (Graph.toSimpleGraphOfSimpleGraphIso H).connectedComponentEquiv

/-- A multigraph with finitely many components has no components exactly when it has no actual
vertices. -/
@[simp]
theorem componentCount_eq_zero_iff [Finite G.ConnectedComponent] :
    G.componentCount = 0 ↔ V(G) = ∅ := by
  simp [componentCount_def, Nat.card_eq_zero, not_infinite_iff_finite.mpr ‹_›,
    G.connectedComponentEquiv.isEmpty_congr, SimpleGraph.isEmpty_connectedComponent_iff]

/-- A multigraph has one component exactly when it is connected. -/
@[simp]
theorem componentCount_eq_one_iff : G.componentCount = 1 ↔ G.Connected := by
  rw [componentCount_eq_natCard_toSimpleGraph,
    SimpleGraph.card_connectedComponent_eq_one_iff, ← connected_iff_toSimpleGraph_connected]

/-! ### Subgraph inclusions -/

/-- A subgraph inclusion `H ≤ G` induces a homomorphism of underlying simple graphs, sending each
actual vertex of `H` to itself. -/
def toSimpleGraphHomOfLE (hHG : H ≤ G) : H.toSimpleGraph →g G.toSimpleGraph where
  toFun z := ⟨z, hHG.vertexSet_mono z.2⟩
  map_rel' hzw :=
    ⟨fun h ↦ hzw.1 (Subtype.ext (Subtype.mk.inj h)), hzw.2.mono hHG⟩

@[simp]
theorem coe_toSimpleGraphHomOfLE_apply (hHG : H ≤ G) (z : V(H)) :
    (toSimpleGraphHomOfLE hHG z : α) = z := (rfl)

/-- Along a subgraph inclusion `H ≤ G`, the simple component of `z` in `H` maps to the simple
component of `w` in `G` exactly when `w` is reachable from `z` in `G`. -/
theorem map_toSimpleGraphHomOfLE_connectedComponentMk_eq_iff (hHG : H ≤ G) {z : V(H)}
    {w : V(G)} : (H.toSimpleGraph.connectedComponentMk z).map (toSimpleGraphHomOfLE hHG) =
      G.toSimpleGraph.connectedComponentMk w ↔ G.Reachable z w := by
  rw [SimpleGraph.ConnectedComponent.map_mk, toSimpleGraph_connectedComponentMk_eq_iff,
    coe_toSimpleGraphHomOfLE_apply]

/-- Along a subgraph inclusion `H ≤ G`, the simple components in `H` of `z` and `w` have the same
image exactly when `w` is reachable from `z` in `G`. -/
theorem map_toSimpleGraphHomOfLE_connectedComponentMk_eq_map_iff (hHG : H ≤ G) {z w : V(H)} :
    (H.toSimpleGraph.connectedComponentMk z).map (toSimpleGraphHomOfLE hHG) =
      (H.toSimpleGraph.connectedComponentMk w).map (toSimpleGraphHomOfLE hHG) ↔
        G.Reachable z w := by
  rw [SimpleGraph.ConnectedComponent.map_mk _ w,
    map_toSimpleGraphHomOfLE_connectedComponentMk_eq_iff, coe_toSimpleGraphHomOfLE_apply]

/-- A subgraph inclusion maps each native connected component to the ambient connected component
containing it. -/
def ConnectedComponent.mapOfLE (hHG : H ≤ G) : H.ConnectedComponent → G.ConnectedComponent :=
  fun C ↦ ConnectedComponent.ofSimple
    (SimpleGraph.ConnectedComponent.map (toSimpleGraphHomOfLE hHG) C.toSimple)

/-- The component containing a vertex maps along an inclusion to the ambient component containing
that vertex. -/
@[simp]
theorem ConnectedComponent.mapOfLE_connectedComponentOf (hHG : H ≤ G) {x : α}
    (hx : x ∈ V(H)) :
    ConnectedComponent.mapOfLE hHG (H.connectedComponentOf x hx) =
      G.connectedComponentOf x (hHG.vertexSet_mono hx) := by
  apply G.connectedComponentEquiv.injective
  simp only [ConnectedComponent.mapOfLE, connectedComponentEquiv_apply,
    ConnectedComponent.toSimple_ofSimple, ConnectedComponent.toSimple_connectedComponentOf]
  exact (map_toSimpleGraphHomOfLE_connectedComponentMk_eq_iff hHG).mpr
    (Reachable.refl (hHG.vertexSet_mono hx))

/-- Every vertex of a component remains in the ambient component obtained by mapping along a
subgraph inclusion. -/
theorem ConnectedComponent.mem_vertexSet_mapOfLE (hHG : H ≤ G) (C : H.ConnectedComponent)
    {x : α} (hx : x ∈ V(C.1)) : x ∈ V((ConnectedComponent.mapOfLE hHG C).1) := by
  have hxH : x ∈ V(H) := C.property.le.vertexSet_mono hx
  rw [C.eq_connectedComponentOf hx, ConnectedComponent.mapOfLE_connectedComponentOf]
  exact mem_vertexSet_connectedComponentOf_self (hHG.vertexSet_mono hxH)

/-- A component maps along a subgraph inclusion to exactly the ambient component containing all
of its vertices. -/
theorem ConnectedComponent.mapOfLE_eq_iff (hHG : H ≤ G) {C : H.ConnectedComponent}
    {D : G.ConnectedComponent} :
    ConnectedComponent.mapOfLE hHG C = D ↔ V(C.1) ⊆ V(D.1) := by
  constructor
  · intro h x hx
    rw [← h]
    exact C.mem_vertexSet_mapOfLE hHG hx
  · intro h
    obtain ⟨x, hx⟩ := C.property.nonempty
    exact ConnectedComponent.eq_of_mem_of_mem (C.mem_vertexSet_mapOfLE hHG hx) (h hx)

/-- If deleting a finite set of vertices leaves finitely many connected components, then the
original graph also has finitely many connected components. -/
theorem finite_connectedComponent_of_finite_deleteVerts (S : Set α) [Finite S]
    [Finite (G.deleteVerts S).ConnectedComponent] : Finite G.ConnectedComponent := by
  classical
  let _ : Finite ↥(S ∩ V(G)) := Finite.of_injective
    (fun x : ↥(S ∩ V(G)) ↦ (⟨x.1, x.2.1⟩ : ↥S))
    (fun _ _ h ↦ Subtype.ext (Subtype.mk.inj h))
  let f : ↥(S ∩ V(G)) ⊕ (G.deleteVerts S).ConnectedComponent → G.ConnectedComponent
    | Sum.inl x => G.connectedComponentOf x.1 x.2.2
    | Sum.inr C => ConnectedComponent.mapOfLE deleteVerts_le C
  apply Finite.of_surjective f
  intro C
  obtain ⟨x, hxC⟩ := C.property.nonempty
  have hxG : x ∈ V(G) := C.property.le.vertexSet_mono hxC
  by_cases hxS : x ∈ S
  · refine ⟨Sum.inl ⟨x, hxS, hxG⟩, ?_⟩
    exact ConnectedComponent.eq_of_mem_of_mem
      (mem_vertexSet_connectedComponentOf_self hxG) hxC
  · have hx : x ∈ V(G.deleteVerts S) := by simp [hxG, hxS]
    refine ⟨Sum.inr ((G.deleteVerts S).connectedComponentOf x hx), ?_⟩
    simp only [f]
    rw [ConnectedComponent.mapOfLE_connectedComponentOf]
    exact ConnectedComponent.eq_of_mem_of_mem
      (mem_vertexSet_connectedComponentOf_self hxG) hxC

/-! ### Basic examples -/

/-- The empty graph has no connected components. -/
@[simp]
theorem componentCount_bot : (⊥ : Graph α β).componentCount = 0 := by
  have : Finite V((⊥ : Graph α β)) := by rw [vertexSet_bot]; infer_instance
  exact componentCount_eq_zero_iff.mpr vertexSet_bot

/-- A graph with a single actual vertex is connected, whatever loops it carries. -/
theorem connected_of_vertexSet_eq_singleton {x : α} (h : V(G) = {x}) : G.Connected := by
  rw [connected_iff_toSimpleGraph_connected]
  have : Nonempty V(G) := ⟨⟨x, h ▸ Set.mem_singleton x⟩⟩
  have : Subsingleton V(G) := by rw [h]; infer_instance
  exact .of_subsingleton

/-- A graph with a single actual vertex has exactly one component, whatever loops it carries. -/
theorem componentCount_eq_one_of_vertexSet_eq_singleton {x : α} (h : V(G) = {x}) :
    G.componentCount = 1 :=
  componentCount_eq_one_iff.mpr (connected_of_vertexSet_eq_singleton h)

/-- A single isolated vertex is one connected component. -/
@[simp]
theorem componentCount_noEdge_singleton (x : α) : (noEdge {x} β).componentCount = 1 :=
  componentCount_eq_one_of_vertexSet_eq_singleton (vertexSet_noEdge _ _)

/-- Two vertices joined by a nonempty set of edges form one component.  When `x = y` the edges
are loops at a single vertex; otherwise they are parallel edges joining `x` to `y`. -/
@[simp]
theorem componentCount_banana {x y : α} {F : Set β} (hF : F.Nonempty) :
    (banana x y F).componentCount = 1 := by
  obtain ⟨e, he⟩ := hF
  rw [componentCount_eq_one_iff, connected_iff_toSimpleGraph_connected]
  refine (SimpleGraph.connected_iff _).mpr ⟨fun u v ↦ ?_, ⟨⟨x, by simp⟩⟩⟩
  by_cases huv : u = v
  · exact huv ▸ SimpleGraph.Reachable.rfl
  refine SimpleGraph.Adj.reachable ⟨huv, e, ?_⟩
  obtain ⟨u, hu⟩ := u
  obtain ⟨v, hv⟩ := v
  simp only [vertexSet_banana, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  simp only [Subtype.mk.injEq] at huv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all

end

end Graph
