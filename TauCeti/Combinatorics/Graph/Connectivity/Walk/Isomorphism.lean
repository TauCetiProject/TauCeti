/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Isomorphism
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Bidirected

/-!
# Transporting multigraph walks along isomorphisms

A multigraph isomorphism induces a prefunctor between the bidirected arrow families and hence
transports edge-labelled walks between actual vertices. Transport respects the constructors,
identity, composition, inverse, reversal, support, traversed edges, trails, paths, cycles, and
reachability.

## Main definitions

* `Graph.Iso.toPrefunctor`: the induced prefunctor between bidirected arrow families.
* `Graph.Iso.mapPath`: transport of directed walks of the bidirected family.
* `Graph.Iso.mapWalk`: transport of edge-labelled multigraph walks.
-/

public section

universe u v u' v' u'' v''

open TauCeti

namespace Graph

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {α'' : Type u''} {β'' : Type v''}
variable {G : Graph α β} {H : Graph α' β'} {K : Graph α'' β''}

namespace Iso

/-- Transport an arrow of the bidirected arrow family. -/
def mapHom (f : Iso G H) {x y : G.vertexSet} (a : G.BidirectedHom x y) :
    H.BidirectedHom (f.vertexEquiv x) (f.vertexEquiv y) :=
  ⟨f.edgeEquiv ⟨a.1, a.2.edge_mem⟩,
    (f.map_isLink_iff ⟨a.1, a.2.edge_mem⟩ _ _).2 a.2⟩

/-- The underlying edge of a transported bidirected arrow is the transported edge. -/
@[simp]
theorem mapHom_fst (f : Iso G H) {x y : G.vertexSet} (a : G.BidirectedHom x y) :
    (f.mapHom a).1 = f.edgeEquiv ⟨a.1, a.2.edge_mem⟩ :=
  (rfl)

/-- Transporting a bidirected arrow along the identity isomorphism fixes it. -/
@[simp]
theorem mapHom_refl (G : Graph α β) {x y : G.vertexSet} (a : G.BidirectedHom x y) :
    @Quiver.Hom.cast G.vertexSet (Quiver.mk G.BidirectedHom) _ _ x y
      (refl_vertexEquiv_apply G x) (refl_vertexEquiv_apply G y) ((refl G).mapHom a) = a := by
  apply Subtype.ext
  simp [mapHom]

/-- Transporting a bidirected arrow along a composite applies the two transports in order. -/
@[simp]
theorem mapHom_trans (f : Iso G H) (g : Iso H K) {x y : G.vertexSet}
    (a : G.BidirectedHom x y) :
    @Quiver.Hom.cast K.vertexSet (Quiver.mk K.BidirectedHom) _ _ _ _
      (trans_vertexEquiv_apply f g x) (trans_vertexEquiv_apply f g y) ((f.trans g).mapHom a) =
        g.mapHom (f.mapHom a) := by
  apply Subtype.ext
  simp [mapHom]

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

/-- The arrow map of the induced prefunctor is `Graph.Iso.mapHom`. -/
@[simp]
theorem toPrefunctor_map (f : Iso G H) {x y : G.vertexSet} (a : G.BidirectedHom x y) :
    @Quiver.Hom.cast H.vertexSet (Quiver.mk H.BidirectedHom)
      (@Prefunctor.obj G.vertexSet (Quiver.mk G.BidirectedHom)
        H.vertexSet (Quiver.mk H.BidirectedHom) f.toPrefunctor x)
      (@Prefunctor.obj G.vertexSet (Quiver.mk G.BidirectedHom)
        H.vertexSet (Quiver.mk H.BidirectedHom) f.toPrefunctor y)
      (f.vertexEquiv x) (f.vertexEquiv y) (toPrefunctor_obj f x) (toPrefunctor_obj f y)
      (@Prefunctor.map G.vertexSet (Quiver.mk G.BidirectedHom)
        H.vertexSet (Quiver.mk H.BidirectedHom) f.toPrefunctor x y a) = f.mapHom a := by
  simp [toPrefunctor, mapHom]

/-- The identity graph isomorphism induces the identity prefunctor. -/
@[simp]
theorem toPrefunctor_refl (G : Graph α β) :
    (refl G).toPrefunctor = @Prefunctor.id G.vertexSet (Quiver.mk G.BidirectedHom) := by
  refine @Prefunctor.ext G.vertexSet (Quiver.mk G.BidirectedHom)
    G.vertexSet (Quiver.mk G.BidirectedHom) _ _ (refl_vertexEquiv_apply G)
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
    K.vertexSet (Quiver.mk K.BidirectedHom) _ _ (trans_vertexEquiv_apply f g)
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
      (refl_vertexEquiv_apply G x) (refl_vertexEquiv_apply G y) ((refl G).mapPath p) = p := by
  induction p with
  | nil => simp
  | cons p a ih =>
      rw [mapPath_cons, @Quiver.Path.cast_eq_iff_heq G.vertexSet (Quiver.mk G.BidirectedHom)]
      congr 1
      exacts [refl_vertexEquiv_apply G _, refl_vertexEquiv_apply G _,
        refl_vertexEquiv_apply G _,
        (@Quiver.Path.cast_eq_iff_heq G.vertexSet (Quiver.mk G.BidirectedHom) _ _ _ _ _ _ _ _).1 ih,
        (@Quiver.Hom.cast_eq_iff_heq G.vertexSet (Quiver.mk G.BidirectedHom) _ _ _ _ _ _ _ _).1
          (mapHom_refl G a)]

/-- Transport along a composite isomorphism applies the two directed-walk transports in order. -/
@[simp]
theorem mapPath_trans (f : Iso G H) (g : Iso H K) {x y : G.vertexSet}
    (p : ArrowWalk G.BidirectedHom x y) :
    @Quiver.Path.cast K.vertexSet (Quiver.mk K.BidirectedHom) _ _ _ _
      (trans_vertexEquiv_apply f g x) (trans_vertexEquiv_apply f g y) ((f.trans g).mapPath p) =
        g.mapPath (f.mapPath p) := by
  induction p with
  | nil => simp
  | cons p a ih =>
      rw [mapPath_cons, mapPath_cons, mapPath_cons,
        @Quiver.Path.cast_eq_iff_heq K.vertexSet (Quiver.mk K.BidirectedHom)]
      congr 1
      exacts [trans_vertexEquiv_apply f g _, trans_vertexEquiv_apply f g _,
        trans_vertexEquiv_apply f g _,
        (@Quiver.Path.cast_eq_iff_heq K.vertexSet (Quiver.mk K.BidirectedHom) _ _ _ _ _ _ _ _).1 ih,
        (@Quiver.Hom.cast_eq_iff_heq K.vertexSet (Quiver.mk K.BidirectedHom) _ _ _ _ _ _ _ _).1
          (mapHom_trans f g a)]

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
  (f.mapPath (p.toBidirected x.2)).toGraphWalk

/-- Converting a transported walk to the bidirected family recovers directed-walk transport. -/
@[simp]
theorem toBidirected_mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    (f.mapWalk p).toBidirected (f.vertexEquiv x).2 = f.mapPath (p.toBidirected x.2) := by
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

private theorem mapWalk_cons' (f : Iso G H) {x y z : α} (e : β) (h : G.IsLink e x y)
    (p : G.Walk y z) (hx : x ∈ G.vertexSet) (hz : z ∈ G.vertexSet) :
    f.mapWalk (x := ⟨x, hx⟩) (y := ⟨z, hz⟩) (.cons e h p) =
      .cons (f.edgeEquiv ⟨e, h.edge_mem⟩) (f.map_isLink h)
        (f.mapWalk (x := ⟨y, h.right_mem⟩) (y := ⟨z, hz⟩) p) :=
  mapWalk_cons f (x := (⟨x, hx⟩ : G.vertexSet)) (y := ⟨y, h.right_mem⟩)
    (z := ⟨z, hz⟩) e h p

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

/-- Walk transport commutes with reversal. -/
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
      have hc := mapWalk_cons' f e h p hx hy
      rw [Walk.reverse_cons, happ, ih h.right_mem hy, hc, Walk.reverse_cons]
      rw [mapWalk_toWalk]

@[simp]
theorem mapWalk_reverse (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    f.mapWalk p.reverse = (f.mapWalk p).reverse := by
  exact mapWalk_reverse_aux f p x.2 y.2

/-- The identity graph isomorphism fixes walks. -/
@[simp]
theorem mapWalk_refl (G : Graph α β) {x y : G.vertexSet} (p : G.Walk x y) :
    ((refl G).mapWalk p).copy
      (congrArg Subtype.val (refl_vertexEquiv_apply G x))
      (congrArg Subtype.val (refl_vertexEquiv_apply G y)) = p := by
  simp [mapWalk, ← ArrowWalk.toGraphWalk_cast]

/-- Transport along a composite isomorphism applies the two walk transports in order. -/
@[simp]
theorem mapWalk_trans (f : Iso G H) (g : Iso H K) {x y : G.vertexSet} (p : G.Walk x y) :
    ((f.trans g).mapWalk p).copy
      (congrArg Subtype.val (trans_vertexEquiv_apply f g x))
      (congrArg Subtype.val (trans_vertexEquiv_apply f g y)) =
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

/-- The support of a transported walk is the pointwise image of the original support. -/
private theorem support_mapWalk_aux (f : Iso G H) {x y : α} (p : G.Walk x y)
    (hx : x ∈ G.vertexSet) (hy : y ∈ G.vertexSet) :
    (f.mapWalk (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) p).support =
      ((p.supportAttach hx).map f.vertexEquiv).unattach := by
  induction p with
  | nil => rw [mapWalk_nil, Walk.support_nil, Walk.supportAttach_nil, List.map_cons,
      List.map_nil, List.unattach_cons, List.unattach_nil]
  | @cons x y z e h p ih =>
      have hc := mapWalk_cons' f e h p hx hy
      rw [hc, Walk.support_cons, Walk.supportAttach_cons, List.map_cons, List.unattach_cons,
        ih h.right_mem hy]

theorem support_mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    (f.mapWalk p).support = ((p.supportAttach x.2).map f.vertexEquiv).unattach := by
  exact support_mapWalk_aux f p x.2 y.2

/-- A vertex occurs on a transported walk exactly when its inverse image occurs on the original
walk. -/
private theorem vertexEquiv_mem_support_mapWalk_iff_aux (f : Iso G H) {x y : α}
    (p : G.Walk x y) (hx : x ∈ G.vertexSet) (hy : y ∈ G.vertexSet) (z : G.vertexSet) :
    (f.vertexEquiv z : α') ∈
      (f.mapWalk (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) p).support ↔ (z : α) ∈ p.support := by
  induction p with
  | nil =>
      simp only [mapWalk_nil, Walk.support_nil, List.mem_singleton]
      rw [Subtype.coe_injective.eq_iff, f.vertexEquiv.injective.eq_iff, Subtype.ext_iff]
  | @cons x y z' a h p ih =>
      have hc := mapWalk_cons' f a h p hx hy
      rw [hc]
      simp only [Walk.support_cons, List.mem_cons]
      rw [Subtype.coe_injective.eq_iff, f.vertexEquiv.injective.eq_iff, Subtype.ext_iff,
        ih h.right_mem hy]

@[simp]
theorem vertexEquiv_mem_support_mapWalk_iff (f : Iso G H) {x y : G.vertexSet}
    (p : G.Walk x y) (z : G.vertexSet) :
    (f.vertexEquiv z : α') ∈ (f.mapWalk p).support ↔ (z : α) ∈ p.support := by
  exact vertexEquiv_mem_support_mapWalk_iff_aux f p x.2 y.2 z

/-- The edges of a transported walk are the pointwise image of the original traversed edges. -/
private theorem edges_mapWalk_aux (f : Iso G H) {x y : α} (p : G.Walk x y)
    (hx : x ∈ G.vertexSet) (hy : y ∈ G.vertexSet) :
    (f.mapWalk (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) p).edges =
      (p.edgesAttach.map f.edgeEquiv).unattach := by
  induction p with
  | nil => rw [mapWalk_nil, Walk.edges_nil, Walk.edgesAttach_nil, List.map_nil,
      List.unattach_nil]
  | @cons x y z e h p ih =>
      have hc := mapWalk_cons' f e h p hx hy
      rw [hc, Walk.edges_cons, Walk.edgesAttach_cons, List.map_cons, List.unattach_cons,
        ih h.right_mem hy]

theorem edges_mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    (f.mapWalk p).edges = (p.edgesAttach.map f.edgeEquiv).unattach := by
  exact edges_mapWalk_aux f p x.2 y.2

/-- An edge occurs on a transported walk exactly when its inverse image occurs on the original
walk. -/
private theorem edgeEquiv_mem_edges_mapWalk_iff_aux (f : Iso G H) {x y : α}
    (p : G.Walk x y) (hx : x ∈ G.vertexSet) (hy : y ∈ G.vertexSet) (e : G.edgeSet) :
    (f.edgeEquiv e : β') ∈
      (f.mapWalk (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) p).edges ↔ (e : β) ∈ p.edges := by
  induction p with
  | nil => simp
  | @cons x y z a h p ih =>
      have hc := mapWalk_cons' f a h p hx hy
      rw [hc]
      simp only [Walk.edges_cons, List.mem_cons]
      rw [Subtype.coe_injective.eq_iff, f.edgeEquiv.injective.eq_iff, Subtype.ext_iff,
        ih h.right_mem hy]

@[simp]
theorem edgeEquiv_mem_edges_mapWalk_iff (f : Iso G H) {x y : G.vertexSet}
    (p : G.Walk x y) (e : G.edgeSet) :
    (f.edgeEquiv e : β') ∈ (f.mapWalk p).edges ↔ (e : β) ∈ p.edges := by
  exact edgeEquiv_mem_edges_mapWalk_iff_aux f p x.2 y.2 e

/-- Walk transport preserves and reflects trails. -/
@[simp]
theorem isTrail_mapWalk (f : Iso G H) {x y : G.vertexSet} (p : G.Walk x y) :
    (f.mapWalk p).IsTrail ↔ p.IsTrail := by
  rw [Walk.isTrail_def, edges_mapWalk, Walk.isTrail_def]
  constructor
  · intro h
    have hmap : (p.edgesAttach.map f.edgeEquiv).Nodup := h.of_map Subtype.val
    have hattach : p.edgesAttach.Nodup := hmap.of_map f.edgeEquiv
    have hunattach : p.edgesAttach.unattach.Nodup := hattach.map Subtype.val_injective
    rw [Walk.edgesAttach_unattach] at hunattach
    exact hunattach
  · intro h
    have hattachVal : p.edgesAttach.unattach.Nodup := by
      simpa only [Walk.edgesAttach_unattach] using h
    have hattach : p.edgesAttach.Nodup := hattachVal.of_map Subtype.val
    exact (hattach.map f.edgeEquiv.injective).map Subtype.val_injective

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
    (f.vertexEquiv x).2, Walk.isCycle_iff_isCycle_toBidirected_and_isTrail p x.2]
  rw [isTrail_mapWalk]
  simp only [toBidirected_mapWalk, isCycle_mapPath]

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

end Iso

end Graph
