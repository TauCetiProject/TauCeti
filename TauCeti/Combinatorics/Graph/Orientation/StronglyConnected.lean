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

This file proves Robbins' theorem: a multigraph with finitely many actual edges has a strongly
connected orientation exactly when it is `2`-edge-connected. More generally, it has an
orientation that is strongly connected within each undirected connected component exactly when
it has no bridge. Loops, parallel edges, disconnected graphs in the componentwise statement, and
graphs with no vertices are all included.

The necessary direction retains edge identities and needs no finiteness. Every oriented edge of a
strongly connected component lies on a directed cycle; forgetting its direction gives an
undirected cycle through the same edge, so that edge cannot be a bridge.

For the sufficient direction, call a set `F` of edges settled by an orientation when the two ends
of every edge of `F` reach each other along directed walks using only edges of `F`. The empty
set is settled by any orientation. If `F` is settled and `e` is not a bridge, choose a cycle
through `e` and direct its edges outside `F` along the cycle. Each step of the cycle can then be
followed in the orientation, either directly or inside the settled part, so `F` together with
the edges of the cycle is settled. Finitely many such steps settle every actual edge, and then
any two vertices joined by a walk are joined by a directed walk.

The file also supplies the ear-based inductive construction: directing an added ear from start to
end extends a strongly connected orientation of its base. The directed ear reaches every new
vertex from the old graph and returns from it to the old graph, so strong connectivity is
preserved without finiteness assumptions.

## Main results

* `Graph.Ear.isStronglyConnected_extendOrientation`: adjoining a forward-oriented ear preserves
  strong connectivity.
* `Graph.exists_componentwiseStrong_orientation_iff`: an orientation strongly connected within
  every connected component exists exactly when there is no bridge.
* `Graph.exists_stronglyConnected_orientation_iff`: Robbins' theorem for multigraphs.
* `Graph.Connected.exists_stronglyConnected_orientation_iff`: the classical form for connected
  multigraphs.
* `SimpleGraph.exists_stronglyConnected_orientation_iff`: Robbins' theorem for simple graphs, with
  dart orientations.

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

/-! ### Constructing a strong orientation -/

/-- `x` reaches `y` along a walk following `o` that uses only edges of `F`. -/
private def ReachableWithin (o : G.Orientation) (F : Set E) (x y : V) : Prop :=
  ∃ p : G.Walk x y, p.FollowsOrientation o ∧ ∀ f ∈ p.edges, f ∈ F

private theorem reachableWithin_refl (o : G.Orientation) (F : Set E) (x : V) :
    ReachableWithin o F x x :=
  ⟨.nil, Walk.followsOrientation_nil x, by simp⟩

private theorem reachableWithin_trans {o : G.Orientation} {F : Set E} {x y z : V}
    (hxy : ReachableWithin o F x y) (hyz : ReachableWithin o F y z) :
    ReachableWithin o F x z := by
  obtain ⟨p, hp, hpF⟩ := hxy
  obtain ⟨q, hq, hqF⟩ := hyz
  refine ⟨p.append q, (Walk.followsOrientation_append p q).2 ⟨hp, hq⟩, fun f hf ↦ ?_⟩
  rw [Walk.edges_append, List.mem_append] at hf
  exact hf.elim (hpF f) (hqF f)

private theorem reachableWithin_mono {o : G.Orientation} {F F' : Set E} {x y : V}
    (hFF' : F ⊆ F') (h : ReachableWithin o F x y) : ReachableWithin o F' x y := by
  obtain ⟨p, hp, hpF⟩ := h
  exact ⟨p, hp, fun f hf ↦ hFF' (hpF f hf)⟩

/-- Reachability within `F` only depends on the directions of the edges of `F`. -/
private theorem reachableWithin_congr {o o' : G.Orientation} {F : Set E} {x y : V}
    (hoo' : ∀ e : G.edgeSet, e.1 ∈ F → o.head e = o'.head e) (h : ReachableWithin o F x y) :
    ReachableWithin o' F x y := by
  obtain ⟨p, hp, hpF⟩ := h
  exact ⟨p, (Walk.followsOrientation_congr fun e he ↦ hoo' e (hpF e he)).1 hp, hpF⟩

/-- The ends of every edge of `F` reach each other along `o` using only edges of `F`, so the
edges of `F` span a subgraph that `o` orients strongly within each of its components. -/
private def Settled (o : G.Orientation) (F : Set E) : Prop :=
  ∀ ⦃f x y⦄, f ∈ F → G.IsLink f x y → ReachableWithin o F x y

/-- If the edges of `F` are settled, every walk using only edges of `F` can be replaced by a
walk following the orientation. -/
private theorem reachableWithin_of_settled {o : G.Orientation} {F : Set E} (hF : Settled o F)
    {x y : V} (p : G.Walk x y) (hp : ∀ f ∈ p.edges, f ∈ F) : ReachableWithin o F x y := by
  induction p with
  | nil => exact reachableWithin_refl o F _
  | cons e h p ih =>
    exact reachableWithin_trans (hF (hp e (by simp)) h) (ih fun f hf ↦ hp f (by simp [hf]))

open Classical in
/-- Direct the edge `e` from `x` to `y`, keeping the direction of every other edge. -/
private noncomputable def orientEdge (o : G.Orientation) {e : E} {x y : V}
    (h : G.IsLink e x y) : G.Orientation :=
  ofHead (Function.update o.head ⟨e, h.edge_mem⟩ ⟨y, h.right_mem⟩) fun f ↦ by
    by_cases hf : f = ⟨e, h.edge_mem⟩
    · subst hf
      simpa using h.inc_right
    · simpa [Function.update_of_ne hf] using o.head_inc f

open Classical in
private theorem orientEdge_head_of_ne (o : G.Orientation) {e : E} {x y : V}
    (h : G.IsLink e x y) {f : G.edgeSet} (hf : f.1 ≠ e) : (o.orientEdge h).head f = o.head f := by
  rw [orientEdge, ofHead_head, Function.update_of_ne fun hfe ↦ hf (congrArg Subtype.val hfe)]

private theorem followsOrientation_orientEdge (o : G.Orientation) {e : E} {x y : V}
    (h : G.IsLink e x y) : h.toWalk.FollowsOrientation (o.orientEdge h) := by
  have hhead : ((o.orientEdge h).head ⟨e, h.edge_mem⟩ : V) = y := by
    simp [orientEdge]
  refine h.followsOrientation_toWalk_iff.2 ⟨?_, hhead⟩
  have hlink := (o.orientEdge h).isLink ⟨e, h.edge_mem⟩
  rw [hhead] at hlink
  exact hlink.left_unique h

/-- Orient the edges of a trail outside `F` along the trail. Every vertex of the trail is then
reachable from its start and reaches its end, using edges of `F` and of the trail. -/
private theorem exists_forall_mem_support_reachableWithin (o : G.Orientation) {F : Set E}
    (hF : Settled o F) {a b : V} (q : G.Walk a b) (hq : q.IsTrail) :
    ∃ o' : G.Orientation, (∀ e : G.edgeSet, e.1 ∈ F → o.head e = o'.head e) ∧
      ∀ v ∈ q.support, ReachableWithin o' (F ∪ {f | f ∈ q.edges}) a v ∧
        ReachableWithin o' (F ∪ {f | f ∈ q.edges}) v b := by
  induction q with
  | nil =>
    refine ⟨o, fun _ _ ↦ rfl, fun v hv ↦ ?_⟩
    rw [Walk.support_nil, List.mem_singleton] at hv
    subst hv
    exact ⟨reachableWithin_refl _ _ _, reachableWithin_refl _ _ _⟩
  | @cons x y b e h p ih =>
    rw [Walk.isTrail_cons] at hq
    obtain ⟨o₁, ho₁, hp⟩ := ih hq.1
    have hsub : F ∪ {f | f ∈ p.edges} ⊆ F ∪ {f | f ∈ (Walk.cons e h p).edges} :=
      Set.union_subset_union_right F fun f (hf : f ∈ p.edges) ↦ by simp [hf]
    -- Direct `e` along the trail unless it is already settled.
    obtain ⟨o', ho', hxy⟩ : ∃ o' : G.Orientation,
        (∀ f : G.edgeSet, f.1 ∈ F ∪ {f | f ∈ p.edges} → o₁.head f = o'.head f) ∧
          ReachableWithin o' (F ∪ {f | f ∈ (Walk.cons e h p).edges}) x y := by
      by_cases heF : e ∈ F
      · refine ⟨o₁, fun _ _ ↦ rfl, ?_⟩
        exact reachableWithin_mono (Set.subset_union_left.trans hsub)
          (reachableWithin_congr ho₁ (hF heF h))
      · refine ⟨o₁.orientEdge h, fun f hf ↦ (orientEdge_head_of_ne o₁ h ?_).symm,
          h.toWalk, followsOrientation_orientEdge o₁ h, fun f hf ↦ Or.inr ?_⟩
        · rintro rfl
          exact hf.elim heF hq.2
        · rw [IsLink.edges_toWalk, List.mem_singleton] at hf
          simp [hf]
    refine ⟨o', fun f hf ↦ (ho₁ f hf).trans (ho' f (Or.inl hf)), fun v hv ↦ ?_⟩
    have hp' : ∀ v ∈ p.support,
        ReachableWithin o' (F ∪ {f | f ∈ (Walk.cons e h p).edges}) y v ∧
          ReachableWithin o' (F ∪ {f | f ∈ (Walk.cons e h p).edges}) v b := fun v hv ↦
      ⟨reachableWithin_mono hsub (reachableWithin_congr ho' (hp v hv).1),
        reachableWithin_mono hsub (reachableWithin_congr ho' (hp v hv).2)⟩
    rw [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨reachableWithin_refl _ _ _,
        reachableWithin_trans hxy (hp' y p.start_mem_support).2⟩
    · exact ⟨reachableWithin_trans hxy (hp' v hv).1, (hp' v hv).2⟩

/-- A settled edge set can be enlarged by any edge that is not a bridge: orient the unsettled
edges of a cycle through that edge along the cycle. -/
private theorem exists_settled_insert (o : G.Orientation) {F : Set E} (hF : Settled o F)
    {e : E} (he : e ∈ E(G)) (hb : ¬ G.IsBridge e) :
    ∃ (o' : G.Orientation) (F' : Set E), F ⊆ F' ∧ e ∈ F' ∧ Settled o' F' := by
  obtain ⟨u, C, hC, heC⟩ : ∃ u, ∃ C : G.Walk u u, C.IsCycle ∧ e ∈ C.edges := by
    simpa [isBridge_iff_forall_cycle_notMem he] using hb
  obtain ⟨o', ho', hC'⟩ := exists_forall_mem_support_reachableWithin o hF C hC.isTrail
  refine ⟨o', F ∪ {f | f ∈ C.edges}, Set.subset_union_left, Or.inr heC, ?_⟩
  intro f x y hf hxy
  rcases hf with hf | hf
  · exact reachableWithin_mono Set.subset_union_left (reachableWithin_congr ho' (hF hf hxy))
  · exact reachableWithin_trans (hC' x (C.mem_support_of_isLink_of_mem_edges hxy hf)).2
      (hC' y (C.mem_support_of_isLink_of_mem_edges hxy.symm hf)).1

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

/-- **Robbins' theorem, componentwise form.** A multigraph with finitely many actual edges has an
orientation that is strongly connected within every connected component exactly when it has no
bridge. -/
theorem exists_componentwiseStrong_orientation_iff [Finite E(G)] :
    (∃ o : G.Orientation, ∀ x y : V(G), G.Reachable x y → Nonempty (ArrowWalk o.Hom x y)) ↔
      ∀ e, ¬ G.IsBridge e := by
  refine ⟨fun ⟨o, ho⟩ ↦ o.forall_not_isBridge_of_componentwiseStrong ho, fun h ↦ ?_⟩
  -- Settle the actual edges one at a time; each step settles a whole cycle.
  obtain ⟨o, F, hEF, hF⟩ :
      ∃ (o : G.Orientation) (F : Set E), E(G) ⊆ F ∧ Orientation.Settled o F := by
    refine Set.Finite.induction_on_subset
      (motive := fun S _ ↦ ∃ (o : G.Orientation) (F : Set E), S ⊆ F ∧ Orientation.Settled o F)
      E(G) (Set.toFinite _) ⟨Orientation.ofEdgeEnds G, ∅, subset_rfl, fun _ _ _ hf ↦ hf.elim⟩ ?_
    rintro e S he - - ⟨o, F, hSF, hF⟩
    obtain ⟨o', F', hFF', heF', hF'⟩ := Orientation.exists_settled_insert o hF he (h e)
    exact ⟨o', F', Set.insert_subset heF' (hSF.trans hFF'), hF'⟩
  refine ⟨o, fun x y hxy ↦ ?_⟩
  obtain ⟨-, ⟨p⟩⟩ := reachable_def.mp hxy
  obtain ⟨q, hq, -⟩ :=
    Orientation.reachableWithin_of_settled hF p fun f hf ↦ hEF (p.edges_subset_edgeSet hf)
  exact (o.nonempty_arrowWalk_iff x y).2 ⟨q, hq⟩

/-- **Robbins' theorem.** A multigraph with finitely many actual edges has a strongly connected
orientation exactly when it is `2`-edge-connected. Loops and parallel edges are allowed, and no
connectedness or size assumption is needed: both sides hold when there is at most one actual
vertex. -/
theorem exists_stronglyConnected_orientation_iff [Finite E(G)] :
    (∃ o : G.Orientation, @Quiver.IsStronglyConnected V(G) ⟨o.Hom⟩) ↔ G.IsEdgeConnected 2 := by
  refine ⟨isEdgeConnected_two_of_exists_stronglyConnected_orientation, fun hG ↦ ?_⟩
  rw [isEdgeConnected_two_iff_forall_reachable_and_forall_not_isBridge] at hG
  obtain ⟨o, ho⟩ := exists_componentwiseStrong_orientation_iff.2 hG.2
  exact ⟨o, fun x y ↦ ho x y (hG.1 x.2 y.2)⟩

/-- **Robbins' theorem, classical form.** A connected multigraph with finitely many actual edges
has a strongly connected orientation exactly when it has no bridge. -/
theorem Connected.exists_stronglyConnected_orientation_iff [Finite E(G)] (hG : G.Connected) :
    (∃ o : G.Orientation, @Quiver.IsStronglyConnected V(G) ⟨o.Hom⟩) ↔ ∀ e, ¬ G.IsBridge e := by
  rw [Graph.exists_stronglyConnected_orientation_iff,
    isEdgeConnected_two_iff_connected_and_forall_not_isBridge hG.nonempty, and_iff_right hG]

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

/-- **Robbins' theorem for simple graphs.** A simple graph with finitely many edges has a strongly
connected dart orientation exactly when it is `2`-edge-connected. -/
theorem exists_stronglyConnected_orientation_iff [Finite G.edgeSet] :
    (∃ o : TauCeti.DoubledQuiver.Orientation G,
      Quiver.IsStronglyConnected (TauCeti.DoubledQuiver.OrientedQuiver G o)) ↔
      G.IsEdgeConnected 2 := by
  refine ⟨isEdgeConnected_two_of_exists_stronglyConnected_orientation, fun hG ↦ ?_⟩
  have : Finite (Graph.ofSimpleGraph G).edgeSet := by
    rwa [Graph.edgeSet_ofSimpleGraph]
  obtain ⟨o, ho⟩ := Graph.exists_stronglyConnected_orientation_iff.2
    ((Graph.isEdgeConnected_ofSimpleGraph_iff G 2).2 hG)
  exact ⟨o.toDartOrientation, o.isStronglyConnected_orientedQuiver_iff.2 ho⟩

end SimpleGraph
