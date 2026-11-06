/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.EdgeConnectivity
public import TauCeti.Combinatorics.Graph.Connectivity.VertexConnectivity
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Bidirected
public import TauCeti.Combinatorics.Network.Connectivity

/-!
# Connectivity of the bidirected arrow family of a multigraph

The bidirected arrow family `G.BidirectedHom` of a multigraph `G : Graph α β` has one arrow in each
direction for every nonloop edge and one loop arrow for every loop. This file shows that its
directed connectivity is the undirected connectivity of `G`: arc reachability and arc strength are
edge reachability and edge connectivity, and vertex strength is vertex connectivity. These
identifications let results about the directed connectivity of arrow families be read off for
multigraphs.

## Main results

* `Graph.isArcReachable_bidirectedHom_iff`: two actual vertices are `k`-arc-reachable in the
  bidirected arrow family exactly when they are `k`-edge-reachable in `G`.
* `Graph.isArcStrong_bidirectedHom_iff`, `Graph.arcConnectivity_bidirectedHom`: the bidirected
  arrow family is `k`-arc-strong exactly when `G` is `k`-edge-connected, and its arc connectivity
  is the edge connectivity of `G`.
* `Graph.isVertexStrong_bidirectedHom_iff`, `Graph.vertexStrongConnectivity_bidirectedHom`: the
  bidirected arrow family is `k`-vertex-strong exactly when `G` is `k`-vertex-connected, and its
  vertex strong connectivity is the vertex connectivity of `G`.

## Implementation notes

For vertices the comparison translates walks avoiding a vertex set. For arrows it is not a
translation, since deleting an arrow deletes only one direction of an edge. Deleting an edge
deletes both of its arrows, so edge reachability gives arc reachability. Conversely, if deleting a
set of edges separates `y` from `x`, the arrows leaving the set of vertices still reachable from
`x` have distinct underlying edges in that set, and deleting these arrows separates `y` from `x`.

## References

* J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed., Springer,
  2009, Section 5.1.
-/

public section

open Set TauCeti

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {k : ℕ}

/-- Two actual vertices of a multigraph are `k`-arc-reachable in its bidirected arrow family exactly
when they are `k`-edge-reachable. -/
@[simp]
theorem isArcReachable_bidirectedHom_iff {x y : V(G)} :
    IsArcReachable G.BidirectedHom k x y ↔ G.IsEdgeReachable k x y := by
  rw [isEdgeReachable_def, isArcReachable_def]
  refine ⟨fun h F hF ↦ by_contra fun hxy ↦ ?_, fun h F hF ↦ ?_⟩
  · -- The arrows leaving the vertices reachable from `x` without `F` have their edges in `F`.
    set C : Set V(G) := {v | (G.deleteEdges F).Reachable x v}
    set A : Set (Σ v w, G.BidirectedHom v w) := {a | a.1 ∈ C ∧ a.2.1 ∉ C}
    have hAF : (fun a : Σ v w, G.BidirectedHom v w ↦ a.2.2.1) '' A ⊆ F := by
      rintro _ ⟨⟨v, w, e, hvw⟩, ⟨hv, hw⟩, rfl⟩
      by_contra he
      exact hw (Reachable.trans hv (IsLink.reachable (G := G.deleteEdges F) ⟨hvw, he⟩))
    have hinj := bidirectedHom_edge_injOn_cut C
    have hA : A.Finite := Finite.of_finite_image ((finite_of_encard_le_coe hF.le).subset hAF) hinj
    have hx : (G.deleteEdges F).Reachable x x := .refl x.2
    refine ((isArcReachable_def.2 h).le_card (C := C) (F := hA.toFinset) hx hxy
      fun v w e hv hw ↦ hA.mem_toFinset.2 ⟨hv, hw⟩).not_gt ?_
    rw [← Nat.cast_lt (α := ℕ∞), ← hA.encard_eq_coe_toFinset_card, ← hinj.encard_image]
    exact (encard_le_encard hAF).trans_lt hF
  · -- Deleting the edges of the deleted arrows deletes these arrows and possibly more.
    have hE : ((fun a : Σ v w, G.BidirectedHom v w ↦ a.2.2.1) '' F).encard < k := by
      rw [← Nat.cast_lt (α := ℕ∞)] at hF
      exact (encard_image_le _ _).trans_lt (by simpa using hF)
    refine (reachableWithout_bidirectedHom_iff.2 (h hE)).mono fun a ha ↦ ?_
    exact mem_image_of_mem (fun a : Σ v w, G.BidirectedHom v w ↦ a.2.2.1) ha

/-- The bidirected arrow family of a multigraph is `k`-arc-strong exactly when the multigraph is
`k`-edge-connected. -/
@[simp]
theorem isArcStrong_bidirectedHom_iff : IsArcStrong G.BidirectedHom k ↔ G.IsEdgeConnected k :=
  ⟨fun h ↦ isEdgeConnected_def.2 fun x hx y hy ↦
      isArcReachable_bidirectedHom_iff.1 (h.isArcReachable ⟨x, hx⟩ ⟨y, hy⟩),
    fun h ↦ isArcStrong_def.2 fun x y ↦
      isArcReachable_bidirectedHom_iff.2 (h.isEdgeReachable x.2 y.2)⟩

/-- The arc connectivity of the bidirected arrow family of a multigraph is its edge
connectivity. -/
@[simp]
theorem arcConnectivity_bidirectedHom : arcConnectivity G.BidirectedHom = G.edgeConnectivity :=
  ENat.eq_of_forall_natCast_le_iff fun k ↦ by
    rw [← isArcStrong_iff_le_arcConnectivity, ← isEdgeConnected_iff_le_edgeConnectivity,
      isArcStrong_bidirectedHom_iff]

/-- The bidirected arrow family of a multigraph is `k`-vertex-strong exactly when the multigraph is
`k`-vertex-connected. -/
@[simp]
theorem isVertexStrong_bidirectedHom_iff :
    IsVertexStrong G.BidirectedHom k ↔ G.IsVertexConnected k := by
  rw [isVertexStrong_def, IsVertexConnected, SimpleGraph.isVertexConnected_def,
    ENat.add_one_le_iff (ENat.natCast_ne_top k)]
  refine and_congr_right fun _ ↦ ⟨fun h s t ↦ isVertexReachable_iff.2 fun X hX hs ht ↦ ?_,
    fun h X hX s hs t ht ↦ ?_⟩
  · have hfin : (Subtype.val ⁻¹' X : Set V(G)).Finite :=
      (finite_of_encard_le_coe hX.le).preimage Subtype.val_injective.injOn
    rw [← reachableAvoiding_bidirectedHom_iff, ← hfin.coe_toFinset]
    refine h hfin.toFinset ?_ (by simpa using hs) (by simpa using ht)
    rw [← Nat.cast_lt (α := ℕ∞), ← hfin.encard_eq_coe_toFinset_card]
    exact (encard_preimage_val_le_encard_right _ X).trans_lt hX
  · have hr := isVertexReachable_iff.1 (h s t) (X := Subtype.val '' (X : Set V(G)))
      (by rwa [Subtype.val_injective.encard_image, encard_coe_eq_coe_finsetCard, Nat.cast_lt])
      (by simpa using hs) (by simpa using ht)
    rwa [← reachableAvoiding_bidirectedHom_iff,
      preimage_image_eq _ Subtype.val_injective] at hr

/-- The vertex strong connectivity of the bidirected arrow family of a multigraph is its vertex
connectivity. -/
@[simp]
theorem vertexStrongConnectivity_bidirectedHom :
    vertexStrongConnectivity G.BidirectedHom = G.vertexConnectivity := by
  cases isEmpty_or_nonempty V(G)
  · rw [vertexStrongConnectivity_eq_zero_of_subsingleton, vertexConnectivity_of_subsingleton]
  · exact ENat.eq_of_forall_natCast_le_iff fun k ↦ by
      rw [← isVertexStrong_iff_le_vertexStrongConnectivity,
        ← isVertexConnected_iff_le_vertexConnectivity, isVertexStrong_bidirectedHom_iff]

end Graph
