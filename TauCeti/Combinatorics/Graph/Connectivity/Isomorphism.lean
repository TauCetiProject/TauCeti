/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Bidirected
public import TauCeti.Combinatorics.Quiver.Prefunctor

/-!
# Isomorphisms of multigraphs

An isomorphism between Mathlib multigraphs consists of equivalences between their actual vertex
and edge types which preserve the link relation. Edge identities are part of the data, so this
notion distinguishes parallel edges and retains loops.

This file supplies identity, inverse, and composition of multigraph isomorphisms. It transports
edge-labelled walks between actual vertices, preserving length, concatenation, trails, paths, and
cycles. Applying inverse transport reflects each of these properties, so reachability between
corresponding actual vertices is invariant under isomorphism.

## Main definitions

* `Graph.Iso`: an isomorphism of multigraphs on possibly different ambient types.
* `Graph.Iso.mapWalk`: transport of walks between corresponding actual vertices.
-/

public section

universe u v u' v' u'' v''

open TauCeti

namespace Graph

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {α'' : Type u''} {β'' : Type v''}
variable {G : Graph α β} {H : Graph α' β'} {K : Graph α'' β''}

/-- An isomorphism of multigraphs is an equivalence of their actual vertices and actual edges
which preserves the link relation. -/
@[ext]
structure Iso (G : Graph α β) (H : Graph α' β') where
  /-- The equivalence between actual vertices. -/
  vertexEquiv : G.vertexSet ≃ H.vertexSet
  /-- The equivalence between actual edge identities. -/
  edgeEquiv : G.edgeSet ≃ H.edgeSet
  /-- Corresponding edges link corresponding vertices. -/
  map_isLink_iff : ∀ (e : G.edgeSet) (x y : G.vertexSet),
    H.IsLink (edgeEquiv e) (vertexEquiv x) (vertexEquiv y) ↔ G.IsLink e x y

namespace Iso

/-- The identity isomorphism of a multigraph. -/
@[refl]
def refl (G : Graph α β) : Iso G G where
  vertexEquiv := Equiv.refl G.vertexSet
  edgeEquiv := Equiv.refl G.edgeSet
  map_isLink_iff _ _ _ := Iff.rfl

/-- The composite of two multigraph isomorphisms. -/
@[trans]
def trans (f : Iso G H) (g : Iso H K) : Iso G K where
  vertexEquiv := f.vertexEquiv.trans g.vertexEquiv
  edgeEquiv := f.edgeEquiv.trans g.edgeEquiv
  map_isLink_iff e x y := (g.map_isLink_iff (f.edgeEquiv e)
    (f.vertexEquiv x) (f.vertexEquiv y)).trans (f.map_isLink_iff e x y)

/-- The inverse of a multigraph isomorphism. -/
@[symm]
def symm (f : Iso G H) : Iso H G where
  vertexEquiv := f.vertexEquiv.symm
  edgeEquiv := f.edgeEquiv.symm
  map_isLink_iff e x y := by
    rw [← f.map_isLink_iff (f.edgeEquiv.symm e) (f.vertexEquiv.symm x)
      (f.vertexEquiv.symm y)]
    simp

/-- The identity isomorphism fixes actual vertices. -/
@[simp]
theorem refl_vertexEquiv_apply (G : Graph α β) (x : G.vertexSet) :
    (refl G).vertexEquiv x = x :=
  (rfl)

/-- The identity isomorphism fixes actual edges. -/
@[simp]
theorem refl_edgeEquiv_apply (G : Graph α β) (e : G.edgeSet) :
    (refl G).edgeEquiv e = e :=
  (rfl)

/-- A composite isomorphism applies the two vertex equivalences in order. -/
@[simp]
theorem trans_vertexEquiv_apply (f : Iso G H) (g : Iso H K) (x : G.vertexSet) :
    (f.trans g).vertexEquiv x = g.vertexEquiv (f.vertexEquiv x) :=
  (rfl)

/-- A composite isomorphism applies the two edge equivalences in order. -/
@[simp]
theorem trans_edgeEquiv_apply (f : Iso G H) (g : Iso H K) (e : G.edgeSet) :
    (f.trans g).edgeEquiv e = g.edgeEquiv (f.edgeEquiv e) :=
  (rfl)

/-- The inverse isomorphism applies the inverse vertex equivalence. -/
@[simp]
theorem symm_vertexEquiv_apply (f : Iso G H) (x : H.vertexSet) :
    f.symm.vertexEquiv x = f.vertexEquiv.symm x :=
  (rfl)

/-- The inverse isomorphism applies the inverse edge equivalence. -/
@[simp]
theorem symm_edgeEquiv_apply (f : Iso G H) (e : H.edgeSet) :
    f.symm.edgeEquiv e = f.edgeEquiv.symm e :=
  (rfl)

/-- A graph isomorphism sends a link to a link. -/
theorem map_isLink (f : Iso G H) {e : β} {x y : α} (he : G.IsLink e x y) :
    H.IsLink (f.edgeEquiv ⟨e, he.edge_mem⟩) (f.vertexEquiv ⟨x, he.left_mem⟩)
      (f.vertexEquiv ⟨y, he.right_mem⟩) :=
  (f.map_isLink_iff ⟨e, he.edge_mem⟩ ⟨x, he.left_mem⟩ ⟨y, he.right_mem⟩).2 he

/-- Transport an arrow of the bidirected arrow family. -/
def mapHom (f : Iso G H) {x y : G.vertexSet} (a : G.BidirectedHom x y) :
    H.BidirectedHom (f.vertexEquiv x) (f.vertexEquiv y) :=
  ⟨f.edgeEquiv ⟨a.1, a.2.edge_mem⟩,
    (f.map_isLink_iff ⟨a.1, a.2.edge_mem⟩ _ _).2 a.2⟩

/-- A graph isomorphism as a prefunctor between the two bidirected arrow families. -/
def toPrefunctor (f : Iso G H) :
    @Prefunctor G.vertexSet (Quiver.mk G.BidirectedHom)
      H.vertexSet (Quiver.mk H.BidirectedHom) :=
  @Prefunctor.mk G.vertexSet (Quiver.mk G.BidirectedHom)
    H.vertexSet (Quiver.mk H.BidirectedHom) f.vertexEquiv fun {_ _} a ↦ f.mapHom a

/-- The identity graph isomorphism induces the identity prefunctor. -/
@[simp]
theorem toPrefunctor_refl (G : Graph α β) :
    (refl G).toPrefunctor = @Prefunctor.id G.vertexSet (Quiver.mk G.BidirectedHom) :=
  (rfl)

/-- Composition of graph isomorphisms induces composition of bidirected prefunctors. -/
@[simp]
theorem toPrefunctor_trans (f : Iso G H) (g : Iso H K) :
    (f.trans g).toPrefunctor =
      @Prefunctor.comp G.vertexSet (Quiver.mk G.BidirectedHom)
        H.vertexSet (Quiver.mk H.BidirectedHom) K.vertexSet (Quiver.mk K.BidirectedHom)
        f.toPrefunctor g.toPrefunctor :=
  (rfl)

/-- Transport a directed walk of the bidirected arrow family. -/
def mapPath (f : Iso G H) {x y : G.vertexSet} (p : ArrowWalk G.BidirectedHom x y) :
    ArrowWalk H.BidirectedHom (f.vertexEquiv x) (f.vertexEquiv y) :=
  @Prefunctor.mapPath G.vertexSet (Quiver.mk G.BidirectedHom)
    H.vertexSet (Quiver.mk H.BidirectedHom) f.toPrefunctor x y p

/-- Directed-walk transport preserves the empty walk. -/
@[simp]
theorem mapPath_nil (f : Iso G H) (x : G.vertexSet) :
    f.mapPath (ArrowWalk.nil x) = ArrowWalk.nil (f.vertexEquiv x) :=
  by simpa only [mapPath, toPrefunctor] using
    @Prefunctor.mapPath_nil G.vertexSet (Quiver.mk G.BidirectedHom)
      H.vertexSet (Quiver.mk H.BidirectedHom) f.toPrefunctor x

/-- Directed-walk transport commutes with appending one arrow. -/
@[simp]
theorem mapPath_cons (f : Iso G H) {x y z : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) (a : G.BidirectedHom y z) :
    f.mapPath (p.cons a) = (f.mapPath p).cons (f.mapHom a) := by
  simpa only [mapPath, toPrefunctor] using
    @Prefunctor.mapPath_cons G.vertexSet (Quiver.mk G.BidirectedHom)
      H.vertexSet (Quiver.mk H.BidirectedHom) f.toPrefunctor x y z p a

/-- The identity graph isomorphism fixes directed walks of the bidirected family. -/
@[simp]
theorem mapPath_refl (G : Graph α β) {x y : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) :
    @Quiver.Path.cast G.vertexSet (Quiver.mk G.BidirectedHom) _ _ x y
      (refl_vertexEquiv_apply G x) (refl_vertexEquiv_apply G y) ((refl G).mapPath p) = p :=
  @Prefunctor.mapPath_id G.vertexSet (Quiver.mk G.BidirectedHom) x y p

/-- Transport along a composite isomorphism applies the two directed-walk transports in order. -/
@[simp]
theorem mapPath_trans (f : Iso G H) (g : Iso H K) {x y : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) :
    @Quiver.Path.cast K.vertexSet (Quiver.mk K.BidirectedHom) _ _ _ _
      (trans_vertexEquiv_apply f g x) (trans_vertexEquiv_apply f g y) ((f.trans g).mapPath p) =
        g.mapPath (f.mapPath p) :=
  @Prefunctor.mapPath_comp_apply G.vertexSet (Quiver.mk G.BidirectedHom)
    H.vertexSet (Quiver.mk H.BidirectedHom) f.toPrefunctor K.vertexSet
    (Quiver.mk K.BidirectedHom) g.toPrefunctor x y p

/-- Directed-walk transport preserves length. -/
@[simp]
theorem length_mapPath (f : Iso G H) {x y : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) : (f.mapPath p).length = p.length := by
  simpa only [mapPath, toPrefunctor] using
    @Prefunctor.length_mapPath G.vertexSet H.vertexSet (Quiver.mk G.BidirectedHom)
      (Quiver.mk H.BidirectedHom) f.toPrefunctor x y p

/-- Directed-walk transport applies the vertex equivalence to the visited vertices. -/
@[simp]
theorem vertices_mapPath (f : Iso G H) {x y : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) :
    (f.mapPath p).vertices = p.vertices.map f.vertexEquiv := by
  simpa only [mapPath, toPrefunctor] using
    @Prefunctor.vertices_mapPath G.vertexSet H.vertexSet (Quiver.mk G.BidirectedHom)
      (Quiver.mk H.BidirectedHom) f.toPrefunctor x y p

/-- Directed-walk transport preserves concatenation. -/
@[simp]
theorem mapPath_comp (f : Iso G H) {x y z : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) (q : ArrowWalk G.BidirectedHom y z) :
    f.mapPath (p.comp q) = (f.mapPath p).comp (f.mapPath q) := by
  simpa only [mapPath, toPrefunctor] using
    @Prefunctor.mapPath_comp G.vertexSet (Quiver.mk G.BidirectedHom)
      H.vertexSet (Quiver.mk H.BidirectedHom) f.toPrefunctor x y p z q

/-- Transport an edge-labelled walk between actual vertices along a graph isomorphism. -/
def mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    H.Walk (f.vertexEquiv x) (f.vertexEquiv y) :=
  (f.mapPath (p.toBidirected x.2)).toGraphWalk

/-- Walk transport preserves the empty walk. -/
@[simp]
theorem mapWalk_nil (f : Iso G H) (x : G.vertexSet) :
    f.mapWalk (.nil : G.Walk x x) = .nil := by
  simp [mapWalk]

/-- Walk transport preserves length. -/
@[simp]
theorem length_mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    (f.mapWalk p).length = p.length := by
  rw [mapWalk, ArrowWalk.length_toGraphWalk, length_mapPath, Walk.length_toBidirected]

/-- Walk transport preserves concatenation. -/
@[simp]
theorem mapWalk_append (f : Iso G H) {x y z : G.vertexSet}
    (p : G.Walk x y) (q : G.Walk y z) :
    f.mapWalk (p.append q) = (f.mapWalk p).append (f.mapWalk q) := by
  simp [mapWalk, Walk.toBidirected_append]

/-- The support of a transported walk is obtained by transporting each actual vertex in the
support of the original walk. -/
theorem support_mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    (f.mapWalk p).support =
      ((p.toBidirected x.2).vertices.map f.vertexEquiv).unattach := by
  simp [mapWalk]

/-- A vertex occurs on a transported walk exactly when its inverse image occurs on the original
walk. -/
@[simp]
theorem vertexEquiv_mem_support_mapWalk_iff (f : Iso G H) {x y : G.vertexSet}
    (p : G.Walk x y) (z : G.vertexSet) :
    (f.vertexEquiv z : α') ∈ (f.mapWalk p).support ↔ (z : α) ∈ p.support := by
  rw [support_mapWalk, ← Walk.vertices_toBidirected p x.2]
  simp only [List.mem_unattach, List.mem_map]
  constructor
  · rintro ⟨hz, w, hw, hfw⟩
    have hwz : w = z := f.vertexEquiv.injective
      (Subtype.ext (congrArg Subtype.val hfw))
    exact ⟨z.2, hwz ▸ hw⟩
  · rintro ⟨hz, hzl⟩
    exact ⟨(f.vertexEquiv z).2, z, hzl, rfl⟩

/-- The actual edge identities traversed by a directed walk of the bidirected family. -/
private def pathEdges {x y : G.vertexSet} (p : ArrowWalk G.BidirectedHom x y) :
    List G.edgeSet :=
  p.arrows.map fun a ↦ ⟨a.2.2.1, a.2.2.2.edge_mem⟩

private theorem pathEdges_mapPath (f : Iso G H) {x y : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) :
    pathEdges (f.mapPath p) = (pathEdges p).map f.edgeEquiv := by
  induction p with
  | nil => simp [pathEdges]
  | cons p a ih =>
      rw [mapPath_cons]
      simp only [pathEdges, ArrowWalk.arrows_cons, List.map_append]
      congr 1

private theorem pathEdges_toBidirected_unattach {x y : G.vertexSet} (p : G.Walk x y) :
    (pathEdges (p.toBidirected x.2)).unattach = p.edges := by
  simp [pathEdges, List.unattach, List.map_map, Function.comp_def]

private theorem edges_mapWalk_eq_pathEdges (f : Iso G H) {x y : G.vertexSet}
    (p : G.Walk x y) :
    (f.mapWalk p).edges =
      ((pathEdges (p.toBidirected x.2)).map f.edgeEquiv).unattach := by
  calc
    (f.mapWalk p).edges =
        (pathEdges (f.mapPath (p.toBidirected x.2))).unattach := by
      simp [mapWalk, pathEdges, List.unattach, List.map_map, Function.comp_def]
    _ = ((pathEdges (p.toBidirected x.2)).map f.edgeEquiv).unattach :=
      congrArg List.unattach (pathEdges_mapPath f (p.toBidirected x.2))

/-- The edges of a transported walk are obtained by transporting each actual edge traversed by
the original walk. -/
theorem edges_mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    (f.mapWalk p).edges =
      (((p.toBidirected x.2).arrows.map fun a ↦
        (f.edgeEquiv ⟨a.2.2.1, a.2.2.2.edge_mem⟩ : H.edgeSet)).map Subtype.val) := by
  rw [edges_mapWalk_eq_pathEdges]
  simp [pathEdges, List.unattach, List.map_map, Function.comp_def]

/-- An edge occurs on a transported walk exactly when its inverse image occurs on the original
walk. -/
@[simp]
theorem edgeEquiv_mem_edges_mapWalk_iff (f : Iso G H) {x y : G.vertexSet}
    (p : G.Walk x y) (e : G.edgeSet) :
    (f.edgeEquiv e : β') ∈ (f.mapWalk p).edges ↔ (e : β) ∈ p.edges := by
  rw [edges_mapWalk_eq_pathEdges, ← pathEdges_toBidirected_unattach p]
  -- Unfolding the two `unattach` operations exposes the injective list maps.
  change Subtype.val (f.edgeEquiv e) ∈
      ((pathEdges (p.toBidirected x.2)).map f.edgeEquiv).map Subtype.val ↔
    Subtype.val e ∈ (pathEdges (p.toBidirected x.2)).map Subtype.val
  rw [List.mem_map_of_injective Subtype.val_injective,
    List.mem_map_of_injective f.edgeEquiv.injective,
    List.mem_map_of_injective Subtype.val_injective]

/-- Walk transport preserves and reflects trails. -/
@[simp]
theorem isTrail_mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    (f.mapWalk p).IsTrail ↔ p.IsTrail := by
  rw [Walk.isTrail_def, edges_mapWalk_eq_pathEdges, Walk.isTrail_def,
    ← pathEdges_toBidirected_unattach p]
  -- Unfolding the two `unattach` operations exposes the injective list maps.
  change (((pathEdges (p.toBidirected x.2)).map f.edgeEquiv).map Subtype.val).Nodup ↔
    ((pathEdges (p.toBidirected x.2)).map Subtype.val).Nodup
  rw [List.nodup_map_iff Subtype.val_injective,
    List.nodup_map_iff f.edgeEquiv.injective, List.nodup_map_iff Subtype.val_injective]

/-- Walk transport preserves and reflects paths. -/
@[simp]
theorem isPath_mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    (f.mapWalk p).IsPath ↔ p.IsPath := by
  rw [Walk.isPath_def, support_mapWalk, Walk.isPath_def,
    ← Walk.vertices_toBidirected p x.2]
  -- Unfolding the two `unattach` operations exposes the injective list maps.
  change ((((p.toBidirected x.2).vertices.map f.vertexEquiv).map Subtype.val).Nodup ↔
    ((p.toBidirected x.2).vertices.map Subtype.val).Nodup)
  rw [List.nodup_map_iff Subtype.val_injective,
    List.nodup_map_iff f.vertexEquiv.injective, List.nodup_map_iff Subtype.val_injective]

private theorem isCycle_mapPath (f : Iso G H) {x : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x x) :
    (f.mapPath p).IsCycle ↔ p.IsCycle := by
  rw [ArrowWalk.isCycle_def, ArrowWalk.isCycle_def, length_mapPath, vertices_mapPath]
  have htail (l : List G.vertexSet) : (l.map f.vertexEquiv).tail =
      l.tail.map f.vertexEquiv := by
    cases l <;> rfl
  rw [htail, List.nodup_map_iff f.vertexEquiv.injective]

/-- Walk transport preserves and reflects cycles. -/
@[simp]
theorem isCycle_mapWalk (f : Iso G H) {x : G.vertexSet} (p : G.Walk x x) :
    (f.mapWalk p).IsCycle ↔ p.IsCycle := by
  rw [Walk.isCycle_iff_isCycle_toBidirected_and_isTrail (f.mapWalk p)
    (f.vertexEquiv x).2, Walk.isCycle_iff_isCycle_toBidirected_and_isTrail p x.2]
  rw [isTrail_mapWalk]
  simp only [mapWalk, Walk.toBidirected_toGraphWalk, isCycle_mapPath]

/-- Reachability between actual vertices is invariant under graph isomorphism. -/
theorem reachable_iff (f : Iso G H) (x y : G.vertexSet) :
    H.Reachable (f.vertexEquiv x) (f.vertexEquiv y) ↔ G.Reachable x y := by
  simp only [Graph.reachable_def, Subtype.prop, true_and]
  constructor
  · rintro ⟨p⟩
    have q := f.symm.mapWalk p
    simpa using (show Nonempty (G.Walk _ _) from ⟨q⟩)
  · rintro ⟨p⟩
    exact ⟨f.mapWalk p⟩

end Iso

end Graph
