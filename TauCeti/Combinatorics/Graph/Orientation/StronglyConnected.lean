/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.EdgeConnectivity
public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Basic
public import TauCeti.Combinatorics.Graph.Orientation.OfSimpleGraph
public import TauCeti.Combinatorics.Graph.Orientation.Subgraph
public import TauCeti.Combinatorics.Network.DirectedCycle

/-!
# Strong orientations and edge connectivity

This file develops strong orientations toward Robbins' theorem. It proves the necessary
direction: a multigraph admitting a strongly connected orientation is `2`-edge-connected. It
also supplies the inductive construction step in the converse direction: orienting an added ear
from start to end extends a strongly connected orientation of its base.

The argument retains edge identities. Every oriented edge of a strongly connected component lies
on a directed cycle; forgetting its direction gives an undirected cycle through the same edge, so
that edge cannot be a bridge. The result requires no finiteness assumptions and includes loops,
parallel edges, disconnected graphs in the componentwise statement, and graphs with no vertices.
For the converse construction, the directed ear reaches every new vertex from the old graph and
returns from it to the old graph, so strong connectivity is preserved.

## References

* H. E. Robbins, *A theorem on graphs, with an application to a problem of traffic control*,
  Amer. Math. Monthly 46 (1939), 281--283.
-/

public section

namespace Graph

open TauCeti

universe u v

variable {V : Type u} {E : Type v} {G : Graph V E}

namespace Ear

variable {H : Graph V E} (ear : G.Ear H)

/-- Every edge of an enlarged graph that is absent from the base is traversed by the adjoined
ear. -/
theorem mem_edges_of_mem_add_notMem_base (e : E(ear.add)) (he : e.1 ∉ E(H)) :
    e.1 ∈ ear.toWalk.2.2.edges := by
  let f : E := e.1
  have hf : f ∈ E(H) ∪ E(ear.toGraph) := by
    rw [← ear.edgeSet_add]
    exact e.2
  have hf' := hf.resolve_left he
  rw [ear.edgeSet_toGraph] at hf'
  exact hf'

/-- Extend an orientation across an ear by directing the ear from its start to its end. -/
noncomputable def extendOrientation (o : H.Orientation) : ear.add.Orientation := by
  classical
  let head : E(ear.add) → V(ear.add) := fun e ↦
    if he : e.1 ∈ E(H) then
      Set.inclusion ear.base_le_add.vertexSet_mono (o.head ⟨e, he⟩)
    else
      let he' := ear.mem_edges_of_mem_add_notMem_base e he
      ⟨ear.toWalk.2.2.edgeHead e.1 he', by
        obtain ⟨v, hev⟩ := ear.toWalk.2.2.edgeHead_inc e.1 he'
        exact ((ear.add_le.isLink_iff e.2).2 hev).left_mem⟩
  exact .ofHead head fun e ↦ by
    dsimp only [head]
    split
    next he =>
      exact (ear.base_le_add.isLink_mono (o.isLink ⟨e, he⟩)).inc_right
    next he =>
      have hinc := ear.toWalk.2.2.edgeHead_inc e.1
        (ear.mem_edges_of_mem_add_notMem_base e he)
      obtain ⟨v, hev⟩ := hinc
      exact ⟨v, (ear.add_le.isLink_iff e.2).2 hev⟩

/-- An extended orientation keeps the head chosen by the base orientation on every old edge. -/
@[simp]
theorem coe_extendOrientation_head_of_mem (o : H.Orientation) (e : E(ear.add))
    (he : e.1 ∈ E(H)) :
    ((ear.extendOrientation o).head e : V) = o.head ⟨e, he⟩ := by
  classical
  simp [extendOrientation, he]

/-- An extended orientation directs every new edge toward the endpoint following it in the ear
walk. -/
@[simp]
theorem coe_extendOrientation_head_of_notMem (o : H.Orientation) (e : E(ear.add))
    (he : e.1 ∉ E(H)) :
    ((ear.extendOrientation o).head e : V) = ear.toWalk.2.2.edgeHead e.1
      (ear.mem_edges_of_mem_add_notMem_base e he) := by
  classical
  simp [extendOrientation, he]

/-- Restricting an extended orientation to the base recovers the original orientation. -/
@[simp]
theorem restrict_extendOrientation (o : H.Orientation) :
    (ear.extendOrientation o).restrict ear.base_le_add = o := by
  apply Orientation.ext_of_head
  intro e
  apply Subtype.ext
  simp

/-- The underlying walk of an ear, restricted to the graph obtained by adjoining it. -/
def forwardWalk : ear.add.Walk ear.toWalk.1 ear.toWalk.2.1 :=
  ear.toWalk.2.2.transfer ear.add_le fun _e he ↦ ear.edges_toWalk_subset_edgeSet_add he

@[simp]
theorem edges_forwardWalk : ear.forwardWalk.edges = ear.toWalk.2.2.edges :=
  Walk.edges_transfer _ _ _

/-- The ear walk follows the orientation extended across it. -/
theorem followsOrientation_forwardWalk (o : H.Orientation) :
    ear.forwardWalk.FollowsOrientation (ear.extendOrientation o) := by
  have htrail : ear.forwardWalk.IsTrail :=
    (Walk.isTrail_transfer ear.add_le _ _).2 ear.isTrail_toWalk
  apply htrail.followsOrientation_of_head_eq_edgeHead
  intro e he
  have he' : e ∈ ear.toWalk.2.2.edges := by simpa using he
  have heH : e ∉ E(H) := ear.edge_notMem_base he'
  rw [ear.coe_extendOrientation_head_of_notMem o _ heH]
  exact (ear.toWalk.2.2.edgeHead_transfer ear.add_le _ e he).symm

/-- A walk following the base orientation still follows the orientation extended across an
ear. -/
theorem followsOrientation_mapLe_extendOrientation (o : H.Orientation)
    {x y : V} {p : H.Walk x y} (hp : p.FollowsOrientation o) :
    (p.mapLe ear.base_le_add).FollowsOrientation (ear.extendOrientation o) := by
  rw [Walk.followsOrientation_mapLe_iff_restrict, ear.restrict_extendOrientation]
  exact hp

/-- Include a directed walk of the base orientation into the orientation extended across an
ear. -/
noncomputable def liftBaseArrowWalk (o : H.Orientation) {x y : V(H)}
    (p : ArrowWalk o.Hom x y) :
    ArrowWalk (ear.extendOrientation o).Hom
      (Set.inclusion ear.base_le_add.vertexSet_mono x)
      (Set.inclusion ear.base_le_add.vertexSet_mono y) :=
  let q := (o.forgetWalk p).mapLe ear.base_le_add
  q.toOriented (ear.followsOrientation_mapLe_extendOrientation o
    (o.followsOrientation_forgetWalk p))
    (Set.inclusion ear.base_le_add.vertexSet_mono x).2

/-- Adjoining a forward-oriented ear to a strongly connected orientation preserves strong
connectivity. -/
theorem isStronglyConnected_extendOrientation (o : H.Orientation)
    (ho : @Quiver.IsStronglyConnected V(H) ⟨o.Hom⟩) :
    @Quiver.IsStronglyConnected V(ear.add) ⟨(ear.extendOrientation o).Hom⟩ := by
  let P : ArrowWalk (ear.extendOrientation o).Hom
      ⟨ear.toWalk.1, ear.base_le_add.vertexSet_mono ear.toWalk_fst_mem⟩
      ⟨ear.toWalk.2.1, ear.base_le_add.vertexSet_mono ear.toWalk_snd_mem⟩ :=
    ear.forwardWalk.toOriented (ear.followsOrientation_forwardWalk o)
      (ear.base_le_add.vertexSet_mono ear.toWalk_fst_mem)
  have mem_vertices_of_mem_toGraph {x : V(ear.add)} (hx : x.1 ∈ V(ear.toGraph)) :
      x ∈ P.vertices := by
    rw [ear.vertexSet_toGraph] at hx
    have hx' : (x : V) ∈ P.vertices.unattach := by
      rw [Walk.vertices_toOriented]
      simpa only [forwardWalk, Walk.support_transfer, Set.mem_ofPred_eq] using hx
    obtain ⟨_, hxP⟩ := List.mem_unattach.mp hx'
    simpa using hxP
  have fromBase (x : V(ear.add)) :
      ∃ a : V(H), Nonempty (ArrowWalk (ear.extendOrientation o).Hom
        (Set.inclusion ear.base_le_add.vertexSet_mono a) x) := by
    let x₀ : V := x
    have hxAdd : x₀ ∈ V(ear.add) := x.2
    rw [ear.vertexSet_add] at hxAdd
    rcases hxAdd with hx | hx
    · exact ⟨⟨x₀, hx⟩, ⟨ArrowWalk.nil x⟩⟩
    · have hxP := mem_vertices_of_mem_toGraph hx
      obtain ⟨q, r, -⟩ := @Quiver.Path.exists_eq_comp_of_mem_vertices
        V(ear.add) ⟨(ear.extendOrientation o).Hom⟩ _ _ P x hxP
      exact ⟨⟨ear.toWalk.1, ear.toWalk_fst_mem⟩, ⟨q⟩⟩
  have toBase (x : V(ear.add)) :
      ∃ a : V(H), Nonempty (ArrowWalk (ear.extendOrientation o).Hom x
        (Set.inclusion ear.base_le_add.vertexSet_mono a)) := by
    let x₀ : V := x
    have hxAdd : x₀ ∈ V(ear.add) := x.2
    rw [ear.vertexSet_add] at hxAdd
    rcases hxAdd with hx | hx
    · exact ⟨⟨x₀, hx⟩, ⟨ArrowWalk.nil x⟩⟩
    · have hxP := mem_vertices_of_mem_toGraph hx
      obtain ⟨q, r, -⟩ := @Quiver.Path.exists_eq_comp_of_mem_vertices
        V(ear.add) ⟨(ear.extendOrientation o).Hom⟩ _ _ P x hxP
      exact ⟨⟨ear.toWalk.2.1, ear.toWalk_snd_mem⟩, ⟨r⟩⟩
  intro x y
  obtain ⟨a, ⟨p⟩⟩ := toBase x
  obtain ⟨b, ⟨r⟩⟩ := fromBase y
  obtain ⟨q⟩ := ho a b
  exact ⟨p.comp ((ear.liftBaseArrowWalk o q).comp r)⟩

end Ear

namespace Orientation

/-- If the arrow chosen for an edge by an orientation lies on a directed cycle, the underlying
edge is not a bridge. -/
theorem not_isBridge_of_liesOnCycle (o : G.Orientation) (e : E(G))
    (hcycle : ArrowWalk.LiesOnCycle (o.arrow e)) : ¬ G.IsBridge e.1 := by
  rw [ArrowWalk.liesOnCycle_def] at hcycle
  rintro he
  obtain ⟨x, p, hp, hep⟩ := hcycle
  have hcycle' : (o.forgetWalk p).IsCycle := (o.isCycle_forgetWalk_iff p).2 hp
  apply he.notMem_edges_of_isCycle hcycle'
  rw [o.edges_forgetWalk]
  exact List.mem_map.mpr ⟨⟨_, _, o.arrow e⟩, hep, by simp⟩

/-- If the head of an oriented edge can reach its tail in the orientation, the edge is not a
bridge. -/
theorem not_isBridge_of_nonempty_returnWalk (o : G.Orientation) (e : E(G))
    (hreturn : Nonempty (ArrowWalk o.Hom (o.head e) (o.tail e))) : ¬ G.IsBridge e.1 :=
  o.not_isBridge_of_liesOnCycle e
    ((ArrowWalk.liesOnCycle_iff_nonempty (o.arrow e)).2 hreturn)

/-- An orientation that is strongly connected within every connected component has no bridge.

The hypothesis only asks for a directed walk when the two vertices are already connected in the
underlying undirected graph, so the statement also applies to disconnected graphs. -/
theorem forall_not_isBridge_of_componentwiseStrong (o : G.Orientation)
    (hstrong : ∀ x y : V(G), G.Reachable x y → Nonempty (ArrowWalk o.Hom x y)) :
    ∀ e, ¬ G.IsBridge e := by
  intro e he
  let e' : E(G) := ⟨e, he.mem_edgeSet⟩
  exact o.not_isBridge_of_nonempty_returnWalk e'
    (hstrong (o.head e') (o.tail e') (o.arrow e').isLink.reachable.symm) he

/-- Every edge of a graph with a strongly connected orientation is not a bridge. -/
theorem forall_not_isBridge (o : G.Orientation)
    (hstrong : @Quiver.IsStronglyConnected V(G) ⟨o.Hom⟩) :
    ∀ e, ¬ G.IsBridge e :=
  o.forall_not_isBridge_of_componentwiseStrong fun x y _ ↦ hstrong x y

/-- The necessary direction of Robbins' theorem: a strongly connected orientation forces
`2`-edge-connectivity. No finiteness or nonemptiness assumption is needed. -/
theorem isEdgeConnected_two (o : G.Orientation)
    (hstrong : @Quiver.IsStronglyConnected V(G) ⟨o.Hom⟩) : G.IsEdgeConnected 2 := by
  rw [Graph.isEdgeConnected_two_iff_forall_reachable_and_forall_not_isBridge]
  refine ⟨?_, o.forall_not_isBridge hstrong⟩
  intro x hx y hy
  exact Graph.reachable_def.mpr ⟨hx, (hstrong ⟨x, hx⟩ ⟨y, hy⟩).map o.forgetWalk⟩

end Graph.Orientation

namespace Graph

open TauCeti

universe u v

variable {V : Type u} {E : Type v} {G : Graph V E}

/-- If a multigraph admits a strongly connected orientation, it is `2`-edge-connected. -/
theorem isEdgeConnected_two_of_exists_stronglyConnected_orientation
    (h : ∃ o : G.Orientation, @Quiver.IsStronglyConnected V(G) ⟨o.Hom⟩) :
    G.IsEdgeConnected 2 := by
  obtain ⟨o, ho⟩ := h
  exact o.isEdgeConnected_two ho

end Graph

namespace SimpleGraph

open TauCeti

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- If a simple graph admits a strongly connected dart orientation, it is `2`-edge-connected. -/
theorem isEdgeConnected_two_of_exists_stronglyConnected_orientation
    (h : ∃ o : TauCeti.DoubledQuiver.Orientation G,
      Quiver.IsStronglyConnected (TauCeti.DoubledQuiver.OrientedQuiver G o)) :
    G.IsEdgeConnected 2 := by
  obtain ⟨o, ho⟩ := h
  let o' : (Graph.ofSimpleGraph G).Orientation := G.graphOrientationEquiv.symm o
  have ho_eq : o'.toDartOrientation = o := by
    rw [← G.graphOrientationEquiv_apply]
    exact G.graphOrientationEquiv.apply_symm_apply o
  have ho' : @Quiver.IsStronglyConnected (Graph.ofSimpleGraph G).vertexSet ⟨o'.Hom⟩ := by
    apply (o'.isStronglyConnected_orientedQuiver_iff).1
    rw [ho_eq]
    exact ho
  exact (Graph.isEdgeConnected_ofSimpleGraph_iff G 2).mp (o'.isEdgeConnected_two ho')

end SimpleGraph
