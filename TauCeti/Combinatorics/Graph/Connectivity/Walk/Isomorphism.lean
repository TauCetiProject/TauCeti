/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Isomorphism.Basic
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Bidirected

import TauCeti.Data.List.Attach

/-!
# Transporting multigraph walks along isomorphisms

A multigraph isomorphism induces a prefunctor between the bidirected arrow families and hence
transports edge-labelled walks between actual vertices. Transport respects the constructors,
identity, composition, inverse, reversal, support, traversed edges, trails, paths, cycles, and
reachability, including after deleting a transported edge set. It preserves and reflects
edge, support, and internal vertex disjointness. It also gives equivalences of indexed walk and
path families with potentially different endpoints for each member.

## Main definitions

* `Graph.Iso.bidirectedHomEquiv`: the induced equivalence between corresponding bidirected arrows.
* `Graph.Iso.toPrefunctor`: the induced prefunctor between bidirected arrow families.
* `Graph.Iso.mapPath`: transport of directed walks of the bidirected family.
* `Graph.Iso.mapWalk`: transport of edge-labelled multigraph walks.
* `Graph.Iso.walkEquiv`: equivalence of walks between corresponding actual vertices.
* `Graph.Iso.walkFamilyEquiv`: equivalence of indexed walk families with corresponding endpoints.
* `Graph.Iso.pathFamilyEquiv`: equivalence of indexed simple-path families with corresponding
  endpoints.
-/

public section

universe u v u' v' u'' v'' w

open TauCeti

namespace Graph

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {α'' : Type u''} {β'' : Type v''}
variable {G : Graph α β} {H : Graph α' β'} {K : Graph α'' β''}

namespace Iso

/-- Transport an arrow of the bidirected arrow family. -/
def mapHom (f : Iso G H) {x y : G.vertexSet} (a : G.BidirectedHom x y) :
    H.BidirectedHom (f.vertexEquiv x) (f.vertexEquiv y) :=
  ⟨f.edgeEquiv ⟨a.val, a.property.edge_mem⟩,
    (f.map_isLink_iff ⟨a.val, a.property.edge_mem⟩ _ _).2 a.property⟩

/-- The underlying edge of a transported bidirected arrow is the transported edge. -/
@[simp]
theorem mapHom_fst (f : Iso G H) {x y : G.vertexSet} (a : G.BidirectedHom x y) :
    (f.mapHom a).val = f.edgeEquiv ⟨a.val, a.property.edge_mem⟩ :=
  (rfl)

/-- Transporting a bidirected arrow along the identity isomorphism fixes it. -/
@[simp]
theorem mapHom_refl (G : Graph α β) {x y : G.vertexSet} (a : G.BidirectedHom x y) :
    @Quiver.Hom.cast G.vertexSet (Quiver.mk G.BidirectedHom) _ _ x y
      (by simp) (by simp) ((refl G).mapHom a) = a := by
  apply Subtype.ext
  simp [mapHom]

/-- Transporting a bidirected arrow along a composite applies the two transports in order. -/
@[simp]
theorem mapHom_trans (f : Iso G H) (g : Iso H K) {x y : G.vertexSet}
    (a : G.BidirectedHom x y) :
    @Quiver.Hom.cast K.vertexSet (Quiver.mk K.BidirectedHom) _ _ _ _
      (by simp) (by simp) ((f.trans g).mapHom a) =
        g.mapHom (f.mapHom a) := by
  apply Subtype.ext
  simp [mapHom]

/-- The equivalence between bidirected arrows induced by a graph isomorphism. It sends an arrow
to the arrow of the corresponding edge between the corresponding vertices. -/
def bidirectedHomEquiv (f : Iso G H) (x y : V(G)) :
    G.BidirectedHom x y ≃ H.BidirectedHom (f.vertexEquiv x) (f.vertexEquiv y) where
  toFun := f.mapHom
  invFun b := ⟨f.edgeEquiv.symm ⟨b.val, b.property.edge_mem⟩,
    (f.map_isLink_iff (f.edgeEquiv.symm ⟨b.val, b.property.edge_mem⟩) x y).1
        (by simpa using b.property)⟩
  left_inv a := Subtype.ext (by simp)
  right_inv b := Subtype.ext (by simp)

/-- The isomorphism of bidirected arrows is arrow transport along the graph isomorphism. -/
@[simp]
theorem bidirectedHomEquiv_apply (f : Iso G H) {x y : V(G)} (a : G.BidirectedHom x y) :
    f.bidirectedHomEquiv x y a = f.mapHom a :=
  (rfl)

/-- The underlying edge of the inverse image of a bidirected arrow is the inverse image of its
edge. -/
@[simp]
theorem bidirectedHomEquiv_symm_apply_fst (f : Iso G H) {x y : V(G)}
    (b : H.BidirectedHom (f.vertexEquiv x) (f.vertexEquiv y)) :
    ((f.bidirectedHomEquiv x y).symm b).val = f.edgeEquiv.symm ⟨b.val, b.property.edge_mem⟩ :=
  (rfl)

/-- A graph isomorphism as a prefunctor between the two bidirected arrow families. -/
def toPrefunctor (f : Iso G H) :
    @Prefunctor G.vertexSet (Quiver.mk G.BidirectedHom)
      H.vertexSet (Quiver.mk H.BidirectedHom) :=
  @Prefunctor.mk G.vertexSet (Quiver.mk G.BidirectedHom)
    H.vertexSet (Quiver.mk H.BidirectedHom) f.vertexEquiv fun {_ _} a ↦ f.mapHom a

/-- The object map of the induced prefunctor is the vertex equivalence. -/
@[simp]
theorem toPrefunctor_obj (f : Iso G H) (x : G.vertexSet) :
    @Prefunctor.obj G.vertexSet (Quiver.mk G.BidirectedHom)
      H.vertexSet (Quiver.mk H.BidirectedHom) f.toPrefunctor x = f.vertexEquiv x :=
  (rfl)

/-- The arrow map of the induced prefunctor transports the underlying edge. -/
@[simp]
theorem toPrefunctor_map_fst (f : Iso G H) {x y : G.vertexSet} (a : G.BidirectedHom x y) :
    (@Prefunctor.map G.vertexSet (Quiver.mk G.BidirectedHom)
      H.vertexSet (Quiver.mk H.BidirectedHom) f.toPrefunctor x y a).val =
        f.edgeEquiv ⟨a.val, a.property.edge_mem⟩ :=
  (rfl)

/-- The identity graph isomorphism induces the identity prefunctor. -/
@[simp]
theorem toPrefunctor_refl (G : Graph α β) :
    (refl G).toPrefunctor = @Prefunctor.id G.vertexSet (Quiver.mk G.BidirectedHom) := by
  refine @Prefunctor.ext G.vertexSet (Quiver.mk G.BidirectedHom)
    G.vertexSet (Quiver.mk G.BidirectedHom) _ _ (fun _ ↦ by simp)
      fun x y a ↦ eq_of_heq ?_
  rw [heq_eqRec_iff, heq_eqRec_iff]
  exact (@Quiver.Hom.cast_heq G.vertexSet (Quiver.mk G.BidirectedHom) _ _ _ _ _ _ _).symm.trans
    (heq_of_eq (mapHom_refl G a))

/-- Composition of graph isomorphisms induces composition of bidirected prefunctors. -/
@[simp]
theorem toPrefunctor_trans (f : Iso G H) (g : Iso H K) :
    (f.trans g).toPrefunctor =
      @Prefunctor.comp G.vertexSet (Quiver.mk G.BidirectedHom)
        H.vertexSet (Quiver.mk H.BidirectedHom) K.vertexSet (Quiver.mk K.BidirectedHom)
        f.toPrefunctor g.toPrefunctor := by
  refine @Prefunctor.ext G.vertexSet (Quiver.mk G.BidirectedHom)
    K.vertexSet (Quiver.mk K.BidirectedHom) _ _ (fun _ ↦ by simp)
      fun x y a ↦ eq_of_heq ?_
  rw [heq_eqRec_iff, heq_eqRec_iff]
  exact (@Quiver.Hom.cast_heq K.vertexSet (Quiver.mk K.BidirectedHom) _ _ _ _ _ _ _).symm.trans
    (heq_of_eq (mapHom_trans f g a))

/-- Transport a directed walk of the bidirected arrow family. -/
def mapPath (f : Iso G H) {x y : G.vertexSet} (p : ArrowWalk G.BidirectedHom x y) :
    ArrowWalk H.BidirectedHom (f.vertexEquiv x) (f.vertexEquiv y) :=
  @Prefunctor.mapPath G.vertexSet (Quiver.mk G.BidirectedHom)
    H.vertexSet (Quiver.mk H.BidirectedHom) f.toPrefunctor x y p

/-- Directed-walk transport preserves the empty walk. -/
@[simp]
theorem mapPath_nil (f : Iso G H) (x : G.vertexSet) :
    f.mapPath (ArrowWalk.nil x) = ArrowWalk.nil (f.vertexEquiv x) :=
  @Prefunctor.mapPath_nil G.vertexSet (Quiver.mk G.BidirectedHom)
    H.vertexSet (Quiver.mk H.BidirectedHom) f.toPrefunctor x

/-- Directed-walk transport commutes with appending one arrow. -/
@[simp]
theorem mapPath_cons (f : Iso G H) {x y z : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) (a : G.BidirectedHom y z) :
    f.mapPath (p.cons a) = (f.mapPath p).cons (f.mapHom a) :=
  @Prefunctor.mapPath_cons G.vertexSet (Quiver.mk G.BidirectedHom)
    H.vertexSet (Quiver.mk H.BidirectedHom) f.toPrefunctor x y z p a

/-- The identity graph isomorphism fixes directed walks of the bidirected family. -/
@[simp]
theorem mapPath_refl (G : Graph α β) {x y : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) :
    @Quiver.Path.cast G.vertexSet (Quiver.mk G.BidirectedHom) _ _ x y
      (by simp) (by simp) ((refl G).mapPath p) = p :=
  -- The public prefunctor law identifies this transport with the identity prefunctor.
  by
    exact (@Prefunctor.cast_mapPath_eq_of_eq G.vertexSet G.vertexSet
      (Quiver.mk G.BidirectedHom) (Quiver.mk G.BidirectedHom) _ _
      (toPrefunctor_refl G) _ _ p).trans
      (@Prefunctor.mapPath_id G.vertexSet (Quiver.mk G.BidirectedHom) x y p)

/-- Transport along a composite isomorphism applies the two directed-walk transports in order. -/
@[simp]
theorem mapPath_trans (f : Iso G H) (g : Iso H K) {x y : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) :
    @Quiver.Path.cast K.vertexSet (Quiver.mk K.BidirectedHom) _ _ _ _
      (by simp) (by simp) ((f.trans g).mapPath p) =
        g.mapPath (f.mapPath p) :=
  -- The public prefunctor law identifies this transport with composite prefunctor transport.
  by
    exact (@Prefunctor.cast_mapPath_eq_of_eq G.vertexSet K.vertexSet
      (Quiver.mk G.BidirectedHom) (Quiver.mk K.BidirectedHom) _ _
      (toPrefunctor_trans f g) _ _ p).trans
      (@Prefunctor.mapPath_comp_apply G.vertexSet (Quiver.mk G.BidirectedHom)
          H.vertexSet (Quiver.mk H.BidirectedHom) f.toPrefunctor
          K.vertexSet (Quiver.mk K.BidirectedHom) g.toPrefunctor x y p)

/-- Mapping a directed walk forward and then along the inverse isomorphism fixes it. -/
@[simp]
theorem mapPath_symm_mapPath (f : Iso G H) {x y : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) :
    @Quiver.Path.cast G.vertexSet (Quiver.mk G.BidirectedHom) _ _ x y
      (symm_vertexEquiv_apply_vertexEquiv f x) (symm_vertexEquiv_apply_vertexEquiv f y)
      (f.symm.mapPath (f.mapPath p)) = p := by
  apply @Prefunctor.cast_mapPath_mapPath G.vertexSet H.vertexSet
    (Quiver.mk G.BidirectedHom) (Quiver.mk H.BidirectedHom) f.toPrefunctor
    f.symm.toPrefunctor _ _ x y p
  intro a b e
  apply Subtype.ext
  simp [toPrefunctor, mapHom]

/-- Mapping a directed walk along the inverse and then forward fixes it. -/
@[simp]
theorem mapPath_mapPath_symm (f : Iso G H) {x y : H.vertexSet}
    (p : ArrowWalk H.BidirectedHom x y) :
    @Quiver.Path.cast H.vertexSet (Quiver.mk H.BidirectedHom) _ _ x y
      (vertexEquiv_apply_symm_vertexEquiv f x) (vertexEquiv_apply_symm_vertexEquiv f y)
      (f.mapPath (f.symm.mapPath p)) = p := by
  apply @Prefunctor.cast_mapPath_mapPath H.vertexSet G.vertexSet
    (Quiver.mk H.BidirectedHom) (Quiver.mk G.BidirectedHom) f.symm.toPrefunctor
    f.toPrefunctor _ _ x y p
  intro a b e
  apply Subtype.ext
  simp [toPrefunctor, mapHom]

/-- Directed-walk transport preserves length. -/
@[simp]
theorem length_mapPath (f : Iso G H) {x y : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) : (f.mapPath p).length = p.length :=
  @Prefunctor.length_mapPath G.vertexSet H.vertexSet (Quiver.mk G.BidirectedHom)
    (Quiver.mk H.BidirectedHom) f.toPrefunctor x y p

/-- Directed-walk transport applies the vertex equivalence to the visited vertices. -/
@[simp]
theorem vertices_mapPath (f : Iso G H) {x y : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) :
    (f.mapPath p).vertices = p.vertices.map f.vertexEquiv :=
  @Prefunctor.vertices_mapPath G.vertexSet H.vertexSet (Quiver.mk G.BidirectedHom)
    (Quiver.mk H.BidirectedHom) f.toPrefunctor x y p

/-- Directed-walk transport preserves concatenation. -/
@[simp]
theorem mapPath_comp (f : Iso G H) {x y z : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) (q : ArrowWalk G.BidirectedHom y z) :
    f.mapPath (p.comp q) = (f.mapPath p).comp (f.mapPath q) :=
  @Prefunctor.mapPath_comp G.vertexSet (Quiver.mk G.BidirectedHom)
    H.vertexSet (Quiver.mk H.BidirectedHom) f.toPrefunctor x y p z q

/-- Directed-walk transport preserves and reflects paths. -/
@[simp]
theorem isPath_mapPath (f : Iso G H) {x y : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) :
    (f.mapPath p).IsPath ↔ p.IsPath := by
  rw [ArrowWalk.isPath_def, ArrowWalk.isPath_def, vertices_mapPath,
    List.nodup_map_iff f.vertexEquiv.injective]

/-- Directed-walk transport preserves and reflects cycles. -/
@[simp]
theorem isCycle_mapPath (f : Iso G H) {x : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x x) :
    (f.mapPath p).IsCycle ↔ p.IsCycle := by
  rw [ArrowWalk.isCycle_def, ArrowWalk.isCycle_def, length_mapPath, vertices_mapPath]
  rw [← List.map_tail, List.nodup_map_iff f.vertexEquiv.injective]

/-- Transport an edge-labelled walk between actual vertices along a graph isomorphism. -/
def mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    H.Walk (f.vertexEquiv x) (f.vertexEquiv y) :=
  (f.mapPath (p.toBidirected x.property)).toGraphWalk

/-- Converting a transported walk to the bidirected family recovers directed-walk transport. -/
@[simp]
theorem toBidirected_mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    (f.mapWalk p).toBidirected (f.vertexEquiv x).property = f.mapPath (p.toBidirected x.property)
        := by
  rw [mapWalk, Walk.toBidirected_toGraphWalk]

/-- Walk transport preserves the empty walk. -/
@[simp]
theorem mapWalk_nil (f : Iso G H) (x : G.vertexSet) :
    f.mapWalk (.nil : G.Walk x x) = .nil := by
  simp [mapWalk]

/-- Walk transport commutes with adding one edge. -/
@[simp]
theorem mapWalk_cons (f : Iso G H) {x y z : G.vertexSet}
    (e : β) (h : G.IsLink e x y) (p : G.Walk y z) :
    f.mapWalk (.cons e h p) = .cons (f.edgeEquiv ⟨e, h.edge_mem⟩) (f.map_isLink h)
      (f.mapWalk p) := by
  simp only [mapWalk, Walk.toBidirected_cons, mapPath_comp, mapPath_cons, mapPath_nil,
    ArrowWalk.toGraphWalk_comp, ArrowWalk.toGraphWalk_cons, ArrowWalk.toGraphWalk_nil,
    Walk.nil_append, Graph.IsLink.toWalk_eq_cons, Walk.cons_append]
  congr 1

/-- Transporting a one-edge walk gives the one-edge walk of the transported link. -/
@[simp]
theorem mapWalk_toWalk (f : Iso G H) {x y : G.vertexSet} {e : β}
    (h : G.IsLink e x y) : f.mapWalk h.toWalk = (f.map_isLink h).toWalk := by
  rw [Graph.IsLink.toWalk_eq_cons, mapWalk_cons]
  rw [mapWalk_nil, Graph.IsLink.toWalk_eq_cons]

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

private theorem mapWalk_reverse_aux (f : Iso G H) {x y : α} (p : G.Walk x y)
    (hx : x ∈ G.vertexSet) (hy : y ∈ G.vertexSet) :
    f.mapWalk (x := ⟨y, hy⟩) (y := ⟨x, hx⟩) p.reverse =
      (f.mapWalk (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) p).reverse := by
  induction p with
  | nil => simp
  | @cons x y z e h p ih =>
      have happ := mapWalk_append f
        (x := (⟨z, hy⟩ : G.vertexSet)) (y := ⟨y, h.right_mem⟩) (z := ⟨x, hx⟩)
        p.reverse h.symm.toWalk
      have hc := mapWalk_cons f (x := (⟨x, hx⟩ : G.vertexSet))
        (y := ⟨y, h.right_mem⟩) (z := ⟨z, hy⟩) e h p
      rw [Walk.reverse_cons, happ, ih h.right_mem hy, hc, Walk.reverse_cons]
      rw [mapWalk_toWalk]

/-- Walk transport commutes with reversal. -/
@[simp]
theorem mapWalk_reverse (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    f.mapWalk p.reverse = (f.mapWalk p).reverse := by
  exact mapWalk_reverse_aux f p x.property y.property

/-- The identity graph isomorphism fixes walks. -/
@[simp]
theorem mapWalk_refl (G : Graph α β) {x y : G.vertexSet} (p : G.Walk x y) :
    ((refl G).mapWalk p).copy
      (by simp) (by simp) = p := by
  simp [mapWalk, ← ArrowWalk.toGraphWalk_cast]

/-- Transport along a composite isomorphism applies the two walk transports in order. -/
@[simp]
theorem mapWalk_trans (f : Iso G H) (g : Iso H K) {x y : G.vertexSet} (p : G.Walk x y) :
    ((f.trans g).mapWalk p).copy
      (by simp) (by simp) =
        g.mapWalk (f.mapWalk p) := by
  simp [mapWalk, ← ArrowWalk.toGraphWalk_cast]

/-- Mapping a walk forward and then along the inverse isomorphism fixes it. -/
@[simp]
theorem mapWalk_symm_mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    (f.symm.mapWalk (f.mapWalk p)).copy
      (congrArg Subtype.val (symm_vertexEquiv_apply_vertexEquiv f x))
      (congrArg Subtype.val (symm_vertexEquiv_apply_vertexEquiv f y)) = p := by
  simp [mapWalk, ← ArrowWalk.toGraphWalk_cast]

/-- Mapping a walk along the inverse and then forward fixes it. -/
@[simp]
theorem mapWalk_mapWalk_symm (f : Iso G H) {x y : H.vertexSet} (p : H.Walk x y) :
    (f.mapWalk (f.symm.mapWalk p)).copy
      (congrArg Subtype.val (vertexEquiv_apply_symm_vertexEquiv f x))
      (congrArg Subtype.val (vertexEquiv_apply_symm_vertexEquiv f y)) = p := by
  simp [mapWalk, ← ArrowWalk.toGraphWalk_cast]

/-- Transport commutes with changing the endpoints by equalities of actual vertices. -/
@[simp]
theorem mapWalk_copy (f : Iso G H) {x y x' y' : G.vertexSet} (p : G.Walk x y)
    (hx : x = x') (hy : y = y') :
    f.mapWalk (p.copy (congrArg Subtype.val hx) (congrArg Subtype.val hy)) =
      (f.mapWalk p).copy (congrArg (fun z ↦ (f.vertexEquiv z : α')) hx)
        (congrArg (fun z ↦ (f.vertexEquiv z : α')) hy) := by
  subst x'
  subst y'
  simp

/-- An isomorphism identifies walks between corresponding actual vertices. -/
def walkEquiv (f : Iso G H) (x y : G.vertexSet) :
    G.Walk x y ≃ H.Walk (f.vertexEquiv x) (f.vertexEquiv y) where
  toFun := f.mapWalk
  invFun p := (f.symm.mapWalk p).copy
    (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv x))
    (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv y))
  left_inv := f.mapWalk_symm_mapWalk
  right_inv p := by
    rw [mapWalk_copy f _ (f.symm_vertexEquiv_apply_vertexEquiv x)
      (f.symm_vertexEquiv_apply_vertexEquiv y)]
    exact f.mapWalk_mapWalk_symm p

/-- The walk equivalence applies the existing walk transport. -/
@[simp]
theorem walkEquiv_apply (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    f.walkEquiv x y p = f.mapWalk p := (rfl)

/-- Its inverse transports along the inverse isomorphism and identifies the endpoints. -/
@[simp]
theorem walkEquiv_symm_apply (f : Iso G H) {x y : G.vertexSet}
    (p : H.Walk (f.vertexEquiv x) (f.vertexEquiv y)) :
    (f.walkEquiv x y).symm p = (f.symm.mapWalk p).copy
      (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv x))
      (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv y)) := (rfl)

/-- Walk transport is injective, including for distinct parallel-edge paths. -/
theorem mapWalk_injective (f : Iso G H) (x y : G.vertexSet) :
    Function.Injective (f.mapWalk (x := x) (y := y)) :=
  (f.walkEquiv x y).injective

/-- The support of a transported walk is the pointwise image of the original support. -/
theorem support_mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    (f.mapWalk p).support = ((p.toBidirected x.property).vertices.map f.vertexEquiv).unattach := by
  rw [mapWalk, ArrowWalk.support_toGraphWalk, vertices_mapPath]

/-- A vertex occurs on a transported walk exactly when its inverse image occurs on the original
walk. -/
@[simp]
theorem vertexEquiv_mem_support_mapWalk_iff (f : Iso G H) {x y : G.vertexSet}
    (p : G.Walk x y) (z : G.vertexSet) :
    (f.vertexEquiv z : α') ∈ (f.mapWalk p).support ↔ (z : α) ∈ p.support := by
  rw [support_mapWalk, ← Walk.vertices_toBidirected p x.property, List.val_mem_unattach_iff,
    List.val_mem_unattach_iff,
    List.mem_map_of_injective f.vertexEquiv.injective]

private theorem edges_mapWalk_aux (f : Iso G H) {x y : α} (p : G.Walk x y)
    (hx : x ∈ G.vertexSet) (hy : y ∈ G.vertexSet) :
    (f.mapWalk (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) p).edges =
      (p.edgesAttach.map f.edgeEquiv).unattach := by
  induction p with
  | nil => simp
  | @cons x y z e h p ih =>
      have hc := mapWalk_cons f (x := (⟨x, hx⟩ : G.vertexSet))
        (y := ⟨y, h.right_mem⟩) (z := ⟨z, hy⟩) e h p
      simp [hc, ih h.right_mem hy]

/-- The edges of a transported walk are the pointwise image of the original traversed edges. -/
theorem edges_mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    (f.mapWalk p).edges = (p.edgesAttach.map f.edgeEquiv).unattach := by
  exact edges_mapWalk_aux f p x.property y.property

/-- An edge occurs on a transported walk exactly when its inverse image occurs on the original
walk. -/
@[simp]
theorem edgeEquiv_mem_edges_mapWalk_iff (f : Iso G H) {x y : G.vertexSet}
    (p : G.Walk x y) (e : G.edgeSet) :
    (f.edgeEquiv e : β') ∈ (f.mapWalk p).edges ↔ (e : β) ∈ p.edges := by
  rw [edges_mapWalk, ← Walk.edgesAttach_unattach p, List.val_mem_unattach_iff,
    List.val_mem_unattach_iff,
    List.mem_map_of_injective f.edgeEquiv.injective]

/-- An isomorphism preserves and reflects disjointness of traversed edge identities. -/
@[simp]
theorem disjoint_edges_mapWalk_iff (f : G.Iso H) {x y z t : V(G)}
    (p : G.Walk x y) (q : G.Walk z t) :
    (f.mapWalk p).edges.Disjoint (f.mapWalk q).edges ↔ p.edges.Disjoint q.edges := by
  simp only [edges_mapWalk, List.unattach, List.Disjoint.map_iff Subtype.val_injective,
    List.Disjoint.map_iff f.edgeEquiv.injective]
  simpa only [List.map_subtype, List.map_id', Walk.edgesAttach_unattach] using
    (List.Disjoint.map_iff (s := p.edgesAttach) (t := q.edgesAttach)
      Subtype.val_injective).symm

/-- An isomorphism preserves and reflects disjointness including the walk endpoints. -/
@[simp]
theorem disjoint_support_mapWalk_iff (f : G.Iso H) {x y z t : V(G)}
    (p : G.Walk x y) (q : G.Walk z t) :
    (f.mapWalk p).support.Disjoint (f.mapWalk q).support ↔ p.support.Disjoint q.support := by
  simp only [support_mapWalk, List.unattach, List.Disjoint.map_iff Subtype.val_injective,
    List.Disjoint.map_iff f.vertexEquiv.injective]
  simpa only [List.map_subtype, List.map_id', Walk.vertices_toBidirected] using
    (List.Disjoint.map_iff (s := (p.toBidirected x.property).vertices)
      (t := (q.toBidirected z.property).vertices) Subtype.val_injective).symm

/-- An isomorphism preserves and reflects internal disjointness for common endpoints. -/
@[simp]
theorem internallyDisjoint_mapWalk_iff (f : G.Iso H) {x y : V(G)} (p q : G.Walk x y) :
    (f.mapWalk p).InternallyDisjoint (f.mapWalk q) ↔ p.InternallyDisjoint q := by
  rw [Walk.internallyDisjoint_def, Walk.internallyDisjoint_def]
  constructor
  · intro h a hap haq
    let a' : V(G) := ⟨a, p.support_subset_vertexSet x.property a hap⟩
    have ha := h (f.vertexEquiv a')
      ((f.vertexEquiv_mem_support_mapWalk_iff p a').2 hap)
      ((f.vertexEquiv_mem_support_mapWalk_iff q a').2 haq)
    exact ha.imp
      (fun hx ↦ congrArg Subtype.val (f.vertexEquiv.injective (Subtype.ext hx)))
      (fun hy ↦ congrArg Subtype.val (f.vertexEquiv.injective (Subtype.ext hy)))
  · intro h a hap haq
    let a' : V(H) := ⟨a, (f.mapWalk p).support_subset_vertexSet (f.vertexEquiv x).property a hap⟩
    have hp : (f.vertexEquiv (f.vertexEquiv.symm a') : α') ∈ (f.mapWalk p).support := by
      simpa [a'] using hap
    have hq : (f.vertexEquiv (f.vertexEquiv.symm a') : α') ∈ (f.mapWalk q).support := by
      simpa [a'] using haq
    have ha := h _ ((f.vertexEquiv_mem_support_mapWalk_iff p _).1 hp)
      ((f.vertexEquiv_mem_support_mapWalk_iff q _).1 hq)
    rcases ha with hx | hy
    · left
      exact congrArg Subtype.val (by simpa using congrArg f.vertexEquiv (Subtype.ext hx))
    · right
      exact congrArg Subtype.val (by simpa using congrArg f.vertexEquiv (Subtype.ext hy))

/-- Walk transport preserves and reflects trails. -/
@[simp]
theorem isTrail_mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    (f.mapWalk p).IsTrail ↔ p.IsTrail := by
  rw [Walk.isTrail_def, edges_mapWalk, List.nodup_unattach_iff,
    List.nodup_map_iff f.edgeEquiv.injective, Walk.isTrail_def,
    ← Walk.edgesAttach_unattach p, List.nodup_unattach_iff]

/-- Walk transport preserves and reflects paths. -/
@[simp]
theorem isPath_mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    (f.mapWalk p).IsPath ↔ p.IsPath := by
  rw [mapWalk, ArrowWalk.isPath_toGraphWalk_iff, isPath_mapPath,
    Walk.isPath_toBidirected_iff]

/-- Walk transport preserves and reflects cycles. -/
@[simp]
theorem isCycle_mapWalk (f : Iso G H) {x : G.vertexSet} (p : G.Walk x x) :
    (f.mapWalk p).IsCycle ↔ p.IsCycle := by
  rw [Walk.isCycle_iff_isCycle_toBidirected_and_isTrail (f.mapWalk p)
    (f.vertexEquiv x).property, Walk.isCycle_iff_isCycle_toBidirected_and_isTrail p x.property]
  rw [isTrail_mapWalk]
  simp only [toBidirected_mapWalk, isCycle_mapPath]

/-- Relabel an indexed walk family, allowing each member to have its own endpoints. -/
def walkFamilyEquiv (f : G.Iso H) {ι : Type w} (a b : ι → V(G)) :
    (∀ i, G.Walk (a i) (b i)) ≃
      (∀ i, H.Walk (f.vertexEquiv (a i)) (f.vertexEquiv (b i))) :=
  Equiv.piCongrRight fun i ↦ f.walkEquiv (a i) (b i)

/-- The transported member is the ordinary walk transport. -/
@[simp]
theorem walkFamilyEquiv_apply (f : G.Iso H) {ι : Type w} (a b : ι → V(G))
    (P : ∀ i, G.Walk (a i) (b i)) (i : ι) :
    f.walkFamilyEquiv a b P i = f.mapWalk (P i) := by
  simp [walkFamilyEquiv]

/-- Inverse family transport acts memberwise by inverse walk transport. -/
@[simp]
theorem walkFamilyEquiv_symm_apply (f : G.Iso H) {ι : Type w} (a b : ι → V(G))
    (P : ∀ i, H.Walk (f.vertexEquiv (a i)) (f.vertexEquiv (b i))) (i : ι) :
    (f.walkFamilyEquiv a b).symm P i = (f.walkEquiv (a i) (b i)).symm (P i) := (rfl)

/-- Relabel a family of simple paths, with index-dependent endpoints. -/
def pathFamilyEquiv (f : G.Iso H) {ι : Type w} (a b : ι → V(G)) :
    (∀ i, {p : G.Walk (a i) (b i) // p.IsPath}) ≃
      (∀ i, {p : H.Walk (f.vertexEquiv (a i)) (f.vertexEquiv (b i)) // p.IsPath}) :=
  Equiv.piCongrRight fun i ↦ (f.walkEquiv (a i) (b i)).subtypeEquiv
    (fun p ↦ by simp)

/-- Relabelling a path family transports its underlying walks. -/
@[simp]
theorem pathFamilyEquiv_apply_val (f : G.Iso H) {ι : Type w} (a b : ι → V(G))
    (P : ∀ i, {p : G.Walk (a i) (b i) // p.IsPath}) (i : ι) :
    (f.pathFamilyEquiv a b P i).val = f.mapWalk (P i).val := by
  simp [pathFamilyEquiv]

/-- Inverse path-family transport recovers each underlying walk by the inverse equivalence. -/
@[simp]
theorem pathFamilyEquiv_symm_apply_val (f : G.Iso H) {ι : Type w} (a b : ι → V(G))
    (P : ∀ i, {p : H.Walk (f.vertexEquiv (a i)) (f.vertexEquiv (b i)) // p.IsPath})
    (i : ι) :
    ((f.pathFamilyEquiv a b).symm P i).val =
      (f.walkEquiv (a i) (b i)).symm (P i).val := (rfl)

/-- Reachability between actual vertices is invariant under graph isomorphism. -/
theorem reachable_iff (f : Iso G H) (x y : G.vertexSet) :
    H.Reachable (f.vertexEquiv x) (f.vertexEquiv y) ↔ G.Reachable x y := by
  simp only [Graph.reachable_def, Subtype.prop, true_and]
  constructor
  · rintro ⟨p⟩
    exact ⟨(f.symm.mapWalk p).copy
      (congrArg Subtype.val (symm_vertexEquiv_apply_vertexEquiv f x))
      (congrArg Subtype.val (symm_vertexEquiv_apply_vertexEquiv f y))⟩
  · rintro ⟨p⟩
    exact ⟨f.mapWalk p⟩

/-- An isomorphism transports reachability after deleting an edge set. Edges outside the
actual edge set are discarded by `mapEdgeSet` and have no effect on reachability. -/
theorem reachable_deleteEdges_mapEdgeSet_iff (f : Iso G H) (F : Set β) (x y : V(G)) :
    (H.deleteEdges (f.mapEdgeSet F)).Reachable (f.vertexEquiv x) (f.vertexEquiv y) ↔
      (G.deleteEdges F).Reachable x y := by
  simp only [reachable_deleteEdges_iff_exists_walk, Subtype.prop, true_and]
  constructor
  · rintro ⟨p, hp⟩
    have havoid : ∀ e ∈ (f.symm.mapWalk p).edges, e ∉ F := by
      intro e he heF
      let e' : G.edgeSet := ⟨e, (f.symm.mapWalk p).edges_subset_edgeSet he⟩
      have hem : (f.edgeEquiv e' : β') ∈ p.edges :=
        (f.symm.edgeEquiv_mem_edges_mapWalk_iff p (f.edgeEquiv e')).mp
          (by simpa [e'] using he)
      exact hp _ hem (by simpa using heF)
    exact ⟨(f.symm.mapWalk p).copy
      (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv x))
      (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv y)), by
        simpa using havoid⟩
  · rintro ⟨p, hp⟩
    refine ⟨f.mapWalk p, fun e he heF ↦ ?_⟩
    let e' : H.edgeSet := ⟨e, (f.mapWalk p).edges_subset_edgeSet he⟩
    have hem : (f.edgeEquiv.symm e' : β) ∈ p.edges :=
      (f.edgeEquiv_mem_edges_mapWalk_iff p (f.edgeEquiv.symm e')).mp
        (by simpa [e'] using he)
    exact hp _ hem ((f.mem_mapEdgeSet_iff F e').mp heF)

end Iso

end Graph
