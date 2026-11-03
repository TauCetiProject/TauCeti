/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import TauCeti.Combinatorics.Graph.Orientation.Basic
public import TauCeti.Combinatorics.Network.Walk
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation

/-!
# Orientations of simple graphs as multigraph orientations

Orienting the edges of `Graph.ofSimpleGraph H` is equivalent to choosing one dart from each
reversed pair in `H`. The comparison retains the ordered endpoints of each edge and identifies
the associated directed walks and strong connectivity. It lets results about multigraph
orientations specialize to the existing `DoubledQuiver.Orientation` interface.

The simple-graph side uses `TauCeti.DoubledQuiver.Orientation` and its
`OrientedQuiver.homEquiv` to describe the selected arrows.
-/

public section

open TauCeti

universe u

namespace Graph.Orientation

variable {V : Type u} {H : SimpleGraph V}

/-- The dart determined by the ordered ends of an oriented edge of a simple graph. -/
def dart (o : (Graph.ofSimpleGraph H).Orientation) (e : (Graph.ofSimpleGraph H).edgeSet) :
    H.Dart :=
  ⟨((o.tail e).1, (o.head e).1), by
    have he := o.isLink e
    simpa only [ofSimpleGraph_isLink, SimpleGraph.mem_edgeSet, he.1] using he.2⟩

/-- The first endpoint of the dart is the chosen tail. -/
@[simp]
theorem dart_fst (o : (Graph.ofSimpleGraph H).Orientation)
    (e : (Graph.ofSimpleGraph H).edgeSet) : (o.dart e).fst = (o.tail e).1 := by
  rfl

/-- The second endpoint of the dart is the chosen head. -/
@[simp]
theorem dart_snd (o : (Graph.ofSimpleGraph H).Orientation)
    (e : (Graph.ofSimpleGraph H).edgeSet) : (o.dart e).snd = (o.head e).1 := by
  rfl

/-- The dart lies over the original edge. -/
@[simp]
theorem dart_edge (o : (Graph.ofSimpleGraph H).Orientation)
    (e : (Graph.ofSimpleGraph H).edgeSet) : (o.dart e).edge = e.1 :=
  (o.isLink e).1.symm

private theorem tail_head_eq_or_eq_symm (o : (Graph.ofSimpleGraph H).Orientation) (d : H.Dart) :
    (o.tail ⟨d.edge, d.edge_mem⟩).1 = d.fst ∧
        (o.head ⟨d.edge, d.edge_mem⟩).1 = d.snd ∨
      (o.tail ⟨d.edge, d.edge_mem⟩).1 = d.snd ∧
        (o.head ⟨d.edge, d.edge_mem⟩).1 = d.fst :=
  Sym2.eq_iff.mp (o.isLink ⟨d.edge, d.edge_mem⟩).1.symm

/-- The dart orientation determined by the ordered ends of the edges of a simple graph. -/
def toDartOrientation (o : (Graph.ofSimpleGraph H).Orientation) :
    DoubledQuiver.Orientation H where
  carrier := {d | (o.tail ⟨d.edge, d.edge_mem⟩).1 = d.fst}
  symm_mem_iff_not_mem d := by
    have he := o.tail_head_eq_or_eq_symm d
    -- Reduce membership in the carrier being defined; its membership lemma is not available yet.
    change (o.tail ⟨d.symm.edge, d.symm.edge_mem⟩).1 = d.symm.fst ↔
      ¬ (o.tail ⟨d.edge, d.edge_mem⟩).1 = d.fst
    have hedge : (⟨d.symm.edge, d.symm.edge_mem⟩ : (Graph.ofSimpleGraph H).edgeSet) =
        ⟨d.edge, d.edge_mem⟩ := Subtype.ext (SimpleGraph.Dart.edge_symm d)
    rw [hedge]
    simp only [SimpleGraph.Dart.symm, Prod.fst_swap]
    grind [d.fst_ne_snd]

/-- A dart is selected exactly when its first endpoint is the chosen tail. -/
@[simp]
theorem mem_toDartOrientation_iff (o : (Graph.ofSimpleGraph H).Orientation) (d : H.Dart) :
    d ∈ o.toDartOrientation ↔ (o.tail ⟨d.edge, d.edge_mem⟩).1 = d.fst :=
  Iff.rfl

/-- The chosen head of a selected dart is its second endpoint. -/
theorem head_eq_of_mem_toDartOrientation (o : (Graph.ofSimpleGraph H).Orientation)
    {d : H.Dart} (hd : d ∈ o.toDartOrientation) :
    (o.head ⟨d.edge, d.edge_mem⟩).1 = d.snd := by
  have ht := (o.mem_toDartOrientation_iff d).1 hd
  rcases o.tail_head_eq_or_eq_symm d with h | h
  · exact h.2
  · exact (d.fst_ne_snd (ht.symm.trans h.1)).elim

/-- Two edge orientations inducing the same dart choices coincide. -/
theorem toDartOrientation_injective :
    Function.Injective (toDartOrientation (H := H)) := by
  intro o p h
  apply ext_of_tail
  intro e
  let d := o.dart e
  have hed : (⟨d.edge, d.edge_mem⟩ : (Graph.ofSimpleGraph H).edgeSet) = e := by
    apply Subtype.ext
    exact o.dart_edge e
  have hd : d ∈ o.toDartOrientation := by
    rw [mem_toDartOrientation_iff, hed]
    exact (o.dart_fst e).symm
  have hp := (p.mem_toDartOrientation_iff d).1 (h ▸ hd)
  apply Subtype.ext
  simpa only [hed] using (o.dart_fst e).symm.trans hp.symm

/-- Construct an edge orientation by choosing the unique selected dart over each edge. -/
noncomputable def ofDartOrientation (o : DoubledQuiver.Orientation H) :
    (Graph.ofSimpleGraph H).Orientation := by
  have hex (e : (Graph.ofSimpleGraph H).edgeSet) : ∃ d : H.Dart, d ∈ o ∧ d.edge = e.1 := by
    obtain ⟨⟨x, y⟩, he⟩ := Sym2.mk_surjective e.1
    have hxy : H.Adj x y := by
      simpa only [← he, edgeSet_ofSimpleGraph, Function.uncurry_apply_pair,
        SimpleGraph.mem_edgeSet] using e.2
    let d : H.Dart := ⟨(x, y), hxy⟩
    by_cases hd : d ∈ o
    · exact ⟨d, hd, he⟩
    · exact ⟨d.symm, (o.symm_mem_iff_not_mem d).2 hd,
        (SimpleGraph.Dart.edge_symm d).trans he⟩
  exact
    { tail := fun e ↦ ⟨(hex e).choose.fst, Set.mem_univ _⟩
      head := fun e ↦ ⟨(hex e).choose.snd, Set.mem_univ _⟩
      isLink := fun e ↦ ⟨(hex e).choose_spec.2.symm, e.2⟩ }

/-- The ordered ends recovered from a dart orientation form one of its selected darts. -/
theorem dart_ofDartOrientation_mem (o : DoubledQuiver.Orientation H)
    (e : (Graph.ofSimpleGraph H).edgeSet) :
    (ofDartOrientation o).dart e ∈ o := by
  dsimp only [dart, ofDartOrientation]
  exact (Classical.choose_spec (p := fun d : H.Dart ↦ d ∈ o ∧ d.edge = e.1) _).1

/-- Recovering an orientation sends a selected dart's edge back to that dart. -/
@[simp]
theorem dart_ofDartOrientation (o : DoubledQuiver.Orientation H) {d : H.Dart} (hd : d ∈ o) :
    (ofDartOrientation o).dart ⟨d.edge, d.edge_mem⟩ = d := by
  have hc := dart_ofDartOrientation_mem o ⟨d.edge, d.edge_mem⟩
  obtain h | h := (SimpleGraph.dart_edge_eq_iff _ d).mp
    ((ofDartOrientation o).dart_edge ⟨d.edge, d.edge_mem⟩)
  · exact h
  · exact ((o.symm_mem_iff_not_mem d).1 (h ▸ hc) hd).elim

/-- The recovered tail of a selected dart's edge is its first endpoint. -/
@[simp]
theorem tail_ofDartOrientation (o : DoubledQuiver.Orientation H) {d : H.Dart} (hd : d ∈ o) :
    ((ofDartOrientation o).tail ⟨d.edge, d.edge_mem⟩).1 = d.fst :=
  congrArg (fun d : H.Dart ↦ d.fst) (dart_ofDartOrientation o hd)

/-- The recovered head of a selected dart's edge is its second endpoint. -/
@[simp]
theorem head_ofDartOrientation (o : DoubledQuiver.Orientation H) {d : H.Dart} (hd : d ∈ o) :
    ((ofDartOrientation o).head ⟨d.edge, d.edge_mem⟩).1 = d.snd :=
  congrArg (fun d : H.Dart ↦ d.snd) (dart_ofDartOrientation o hd)

/-- Recovering an edge orientation and then its dart choices returns the original orientation. -/
@[simp]
theorem toDartOrientation_ofDartOrientation (o : DoubledQuiver.Orientation H) :
    (ofDartOrientation o).toDartOrientation = o := by
  apply DoubledQuiver.Orientation.ext
  intro d
  let e : (Graph.ofSimpleGraph H).edgeSet := ⟨d.edge, d.edge_mem⟩
  let c := (ofDartOrientation o).dart e
  have hc : c ∈ o := dart_ofDartOrientation_mem o e
  have he : c.edge = d.edge := (ofDartOrientation o).dart_edge e
  obtain h | h := (SimpleGraph.dart_edge_eq_iff c d).mp he
  · have ht : ((ofDartOrientation o).tail e).1 = d.fst := congrArg (fun d : H.Dart ↦ d.fst) h
    exact iff_of_true ht (h ▸ hc)
  · have hn : d ∉ o := (o.symm_mem_iff_not_mem d).1 (h ▸ hc)
    have ht : ((ofDartOrientation o).tail e).1 = d.snd := congrArg (fun d : H.Dart ↦ d.fst) h
    rw [mem_toDartOrientation_iff]
    exact iff_of_false (fun htail ↦ d.snd_ne_fst (ht.symm.trans htail)) hn

/-- Orientations of `Graph.ofSimpleGraph H` and dart orientations of `H` are the same data. -/
noncomputable def _root_.SimpleGraph.graphOrientationEquiv (H : SimpleGraph V) :
    (Graph.ofSimpleGraph H).Orientation ≃ DoubledQuiver.Orientation H where
  toFun := toDartOrientation
  invFun := ofDartOrientation
  left_inv _ := toDartOrientation_injective (toDartOrientation_ofDartOrientation _)
  right_inv := toDartOrientation_ofDartOrientation

/-- Reading off the dart choices is the forward map of the orientation equivalence. -/
@[simp]
theorem _root_.SimpleGraph.graphOrientationEquiv_apply
    (o : (Graph.ofSimpleGraph H).Orientation) :
    H.graphOrientationEquiv o = o.toDartOrientation :=
  (rfl)

/-- The inverse orientation equivalence recovers the ordered ends of every edge. -/
@[simp]
theorem _root_.SimpleGraph.graphOrientationEquiv_symm_apply (o : DoubledQuiver.Orientation H) :
    H.graphOrientationEquiv.symm o = ofDartOrientation o :=
  (rfl)

/-- Recovering the ordered ends after reading their dart choices changes nothing. -/
@[simp]
theorem ofDartOrientation_toDartOrientation (o : (Graph.ofSimpleGraph H).Orientation) :
    ofDartOrientation o.toDartOrientation = o :=
  H.graphOrientationEquiv.symm_apply_apply o

/-- The actual vertices of the multigraph and the vertices of its oriented quiver correspond. -/
def orientedVertexEquiv (o : (Graph.ofSimpleGraph H).Orientation) :
    (Graph.ofSimpleGraph H).vertexSet ≃ DoubledQuiver.OrientedQuiver H o.toDartOrientation :=
  (Equiv.Set.univ V).trans (DoubledQuiver.OrientedQuiver.vertexEquiv H o.toDartOrientation)

/-- The vertex comparison sends an actual vertex to its oriented-quiver vertex. -/
@[simp]
theorem orientedVertexEquiv_apply (o : (Graph.ofSimpleGraph H).Orientation)
    (x : (Graph.ofSimpleGraph H).vertexSet) :
    o.orientedVertexEquiv x = DoubledQuiver.OrientedQuiver.vertex H o.toDartOrientation x.1 :=
  DoubledQuiver.OrientedQuiver.vertexEquiv_apply H o.toDartOrientation x.1

/-- The endpoints of an oriented simple-graph arrow are adjacent. -/
theorem Hom.adj {o : (Graph.ofSimpleGraph H).Orientation}
    {x y : (Graph.ofSimpleGraph H).vertexSet} (a : o.Hom x y) : H.Adj x.1 y.1 := by
  rw [← SimpleGraph.mem_edgeSet, ← a.isLink.1]
  exact a.isLink.2

/-- The dart given by an oriented arrow's endpoints is selected. -/
theorem Hom.dart_mem_toDartOrientation {o : (Graph.ofSimpleGraph H).Orientation}
    {x y : (Graph.ofSimpleGraph H).vertexSet} (a : o.Hom x y) :
    (⟨(x.1, y.1), a.adj⟩ : H.Dart) ∈ o.toDartOrientation := by
  rw [mem_toDartOrientation_iff]
  have he : (⟨s(x.1, y.1), (SimpleGraph.mem_edgeSet H).2 a.adj⟩ :
      (Graph.ofSimpleGraph H).edgeSet) = a.edge := Subtype.ext a.isLink.1.symm
  simpa only [SimpleGraph.Dart.edge, he] using congrArg Subtype.val a.tail_eq

/-- The arrows in the two orientation interfaces correspond, preserving their ordered ends. -/
def orientedHomEquiv (o : (Graph.ofSimpleGraph H).Orientation)
    (x y : (Graph.ofSimpleGraph H).vertexSet) :
    o.Hom x y ≃ (o.orientedVertexEquiv x ⟶ o.orientedVertexEquiv y) :=
  -- The imported vertex equivalence is opaque, so its application lemma supplies the endpoint cast.
  (Equiv.trans
    { toFun := fun a ↦ ⟨a.adj, a.dart_mem_toDartOrientation⟩
      invFun := fun a ↦ ⟨⟨s(x.1, y.1), (SimpleGraph.mem_edgeSet H).2 a.1⟩,
        Subtype.ext ((o.mem_toDartOrientation_iff ⟨(x.1, y.1), a.1⟩).1 a.2),
        Subtype.ext (o.head_eq_of_mem_toDartOrientation (d := ⟨(x.1, y.1), a.1⟩) a.2)⟩
      left_inv := fun (a : o.Hom x y) ↦ Hom.ext (Subtype.ext a.isLink.1.symm)
      right_inv := fun _ ↦ Subsingleton.elim _ _ }
    (DoubledQuiver.OrientedQuiver.homEquiv H o.toDartOrientation x.1 y.1).symm).trans
      (Equiv.cast (congrArg₂
        (fun a b : DoubledQuiver.OrientedQuiver H o.toDartOrientation ↦ (a ⟶ b))
        (o.orientedVertexEquiv_apply x).symm (o.orientedVertexEquiv_apply y).symm))

/-- The arrow comparison records adjacency and selection of the ordered endpoints. -/
@[simp]
theorem homEquiv_orientedHomEquiv (o : (Graph.ofSimpleGraph H).Orientation)
    {x y : (Graph.ofSimpleGraph H).vertexSet} (a : o.Hom x y) :
    DoubledQuiver.OrientedQuiver.homEquiv H o.toDartOrientation x.1 y.1
      (Quiver.homOfEq (o.orientedHomEquiv x y a)
        (o.orientedVertexEquiv_apply x) (o.orientedVertexEquiv_apply y)) =
      ⟨a.adj, a.dart_mem_toDartOrientation⟩ :=
  Subsingleton.elim _ _

/-- The inverse arrow comparison recovers the edge of a selected dart. -/
@[simp]
theorem orientedHomEquiv_symm_arrow (o : (Graph.ofSimpleGraph H).Orientation)
    (x y : (Graph.ofSimpleGraph H).vertexSet) (h : H.Adj x.1 y.1)
    (ho : (⟨(x.1, y.1), h⟩ : H.Dart) ∈ o.toDartOrientation) :
    ((o.orientedHomEquiv x y).symm
      (Quiver.homOfEq (DoubledQuiver.OrientedQuiver.arrow H _ h ho)
        (o.orientedVertexEquiv_apply x).symm (o.orientedVertexEquiv_apply y).symm)).edge =
      ⟨s(x.1, y.1), (SimpleGraph.mem_edgeSet H).2 h⟩ := by
  exact Subtype.ext (@Hom.isLink V (Sym2 V) (ofSimpleGraph H) o x y _).1

/-- The prefunctor from the edge-labelled orientation quiver to the selected-dart quiver,
given by the vertex and arrow equivalences. -/
def toOrientedQuiver (o : (Graph.ofSimpleGraph H).Orientation) :
    @Prefunctor (Graph.ofSimpleGraph H).vertexSet ⟨o.Hom⟩
      (DoubledQuiver.OrientedQuiver H o.toDartOrientation) inferInstance :=
  @Prefunctor.mk _ ⟨o.Hom⟩ _ inferInstance o.orientedVertexEquiv
    (fun a ↦ o.orientedHomEquiv _ _ a)

/-- The comparison on vertices is the canonical vertex equivalence. -/
@[simp]
theorem toOrientedQuiver_obj (o : (Graph.ofSimpleGraph H).Orientation)
    (x : (Graph.ofSimpleGraph H).vertexSet) :
    @Prefunctor.obj _ ⟨o.Hom⟩ _ inferInstance o.toOrientedQuiver x = o.orientedVertexEquiv x :=
  (rfl)

/-- The comparison on arrows is the canonical arrow equivalence. -/
@[simp]
theorem toOrientedQuiver_map (o : (Graph.ofSimpleGraph H).Orientation)
    {x y : (Graph.ofSimpleGraph H).vertexSet} (a : o.Hom x y) :
    Quiver.homOfEq (@Prefunctor.map _ ⟨o.Hom⟩ _ inferInstance o.toOrientedQuiver x y a)
      (o.toOrientedQuiver_obj x) (o.toOrientedQuiver_obj y) = o.orientedHomEquiv x y a :=
  (rfl)

/-- The prefunctor from the selected-dart quiver to the edge-labelled orientation quiver,
given by the inverse vertex and arrow equivalences. -/
def fromOrientedQuiver (o : (Graph.ofSimpleGraph H).Orientation) :
    @Prefunctor (DoubledQuiver.OrientedQuiver H o.toDartOrientation) inferInstance
      (Graph.ofSimpleGraph H).vertexSet ⟨o.Hom⟩ :=
  @Prefunctor.mk _ inferInstance _ ⟨o.Hom⟩ o.orientedVertexEquiv.symm
    (fun {x y} a ↦ (o.orientedHomEquiv _ _).symm
      (Quiver.homOfEq a (o.orientedVertexEquiv.apply_symm_apply x).symm
        (o.orientedVertexEquiv.apply_symm_apply y).symm))

/-- The inverse comparison on vertices is the inverse vertex equivalence. -/
@[simp]
theorem fromOrientedQuiver_obj (o : (Graph.ofSimpleGraph H).Orientation)
    (x : DoubledQuiver.OrientedQuiver H o.toDartOrientation) :
    @Prefunctor.obj _ inferInstance _ ⟨o.Hom⟩ o.fromOrientedQuiver x =
      o.orientedVertexEquiv.symm x :=
  (rfl)

/-- The inverse comparison on arrows is the inverse arrow equivalence after endpoint transport. -/
@[simp]
theorem fromOrientedQuiver_map (o : (Graph.ofSimpleGraph H).Orientation)
    {x y : DoubledQuiver.OrientedQuiver H o.toDartOrientation} (a : x ⟶ y) :
    @Quiver.Hom.cast _ ⟨o.Hom⟩ _ _ _ _ (o.fromOrientedQuiver_obj x) (o.fromOrientedQuiver_obj y)
      (@Prefunctor.map _ inferInstance _ ⟨o.Hom⟩ o.fromOrientedQuiver x y a) =
        (o.orientedHomEquiv _ _).symm
          (Quiver.homOfEq a (o.orientedVertexEquiv.apply_symm_apply x).symm
            (o.orientedVertexEquiv.apply_symm_apply y).symm) :=
  (rfl)

/-- Transport a directed walk to the selected-dart quiver. -/
def toOrientedWalk (o : (Graph.ofSimpleGraph H).Orientation)
    {x y : (Graph.ofSimpleGraph H).vertexSet} (p : ArrowWalk o.Hom x y) :
    Quiver.Path (o.orientedVertexEquiv x) (o.orientedVertexEquiv y) :=
  @Prefunctor.mapPath _ ⟨o.Hom⟩ _ inferInstance o.toOrientedQuiver x y p

/-- Transport a selected-dart walk back to the edge-labelled orientation. -/
def fromOrientedWalk (o : (Graph.ofSimpleGraph H).Orientation)
    {x y : DoubledQuiver.OrientedQuiver H o.toDartOrientation} (p : Quiver.Path x y) :
    ArrowWalk o.Hom (o.orientedVertexEquiv.symm x) (o.orientedVertexEquiv.symm y) :=
  @Prefunctor.mapPath _ inferInstance _ ⟨o.Hom⟩ o.fromOrientedQuiver x y p

/-- The zero-length walk transports to the zero-length walk. -/
@[simp]
theorem toOrientedWalk_nil (o : (Graph.ofSimpleGraph H).Orientation)
    (x : (Graph.ofSimpleGraph H).vertexSet) :
    o.toOrientedWalk (ArrowWalk.nil x) = Quiver.Path.nil :=
  @Prefunctor.mapPath_nil _ ⟨o.Hom⟩ _ inferInstance o.toOrientedQuiver x

/-- Walk transport preserves extension by an arrow. -/
@[simp]
theorem toOrientedWalk_cons (o : (Graph.ofSimpleGraph H).Orientation)
    {x y z : (Graph.ofSimpleGraph H).vertexSet} (p : ArrowWalk o.Hom x y) (a : o.Hom y z) :
    o.toOrientedWalk (p.cons a) = (o.toOrientedWalk p).cons (o.orientedHomEquiv y z a) :=
  @Prefunctor.mapPath_cons _ ⟨o.Hom⟩ _ inferInstance o.toOrientedQuiver x y z p a

/-- Walk transport preserves concatenation. -/
@[simp]
theorem toOrientedWalk_comp (o : (Graph.ofSimpleGraph H).Orientation)
    {x y z : (Graph.ofSimpleGraph H).vertexSet} (p : ArrowWalk o.Hom x y)
    (q : ArrowWalk o.Hom y z) :
    o.toOrientedWalk (p.comp q) = (o.toOrientedWalk p).comp (o.toOrientedWalk q) :=
  @Prefunctor.mapPath_comp _ ⟨o.Hom⟩ _ inferInstance o.toOrientedQuiver x y p z q

/-- The zero-length walk is preserved by inverse transport. -/
@[simp]
theorem fromOrientedWalk_nil (o : (Graph.ofSimpleGraph H).Orientation)
    (x : DoubledQuiver.OrientedQuiver H o.toDartOrientation) :
    o.fromOrientedWalk (Quiver.Path.nil : Quiver.Path x x) = ArrowWalk.nil _ :=
  @Prefunctor.mapPath_nil _ inferInstance _ ⟨o.Hom⟩ o.fromOrientedQuiver x

/-- Inverse walk transport preserves extension by an arrow after endpoint transport. -/
@[simp]
theorem fromOrientedWalk_cons (o : (Graph.ofSimpleGraph H).Orientation)
    {x y z : DoubledQuiver.OrientedQuiver H o.toDartOrientation}
    (p : Quiver.Path x y) (a : y ⟶ z) :
    o.fromOrientedWalk (p.cons a) = (o.fromOrientedWalk p).cons
      ((o.orientedHomEquiv _ _).symm
        (Quiver.homOfEq a (o.orientedVertexEquiv.apply_symm_apply y).symm
          (o.orientedVertexEquiv.apply_symm_apply z).symm)) :=
  @Prefunctor.mapPath_cons _ inferInstance _ ⟨o.Hom⟩ o.fromOrientedQuiver x y z p a

/-- Inverse walk transport preserves concatenation. -/
@[simp]
theorem fromOrientedWalk_comp (o : (Graph.ofSimpleGraph H).Orientation)
    {x y z : DoubledQuiver.OrientedQuiver H o.toDartOrientation}
    (p : Quiver.Path x y) (q : Quiver.Path y z) :
    o.fromOrientedWalk (p.comp q) = (o.fromOrientedWalk p).comp (o.fromOrientedWalk q) :=
  @Prefunctor.mapPath_comp _ inferInstance _ ⟨o.Hom⟩ o.fromOrientedQuiver x y p z q

/-- Transport preserves the number of arrows in a directed walk. -/
@[simp]
theorem length_toOrientedWalk (o : (Graph.ofSimpleGraph H).Orientation)
    {x y : (Graph.ofSimpleGraph H).vertexSet} (p : ArrowWalk o.Hom x y) :
    (o.toOrientedWalk p).length = p.length :=
  @Prefunctor.length_mapPath _ _ ⟨o.Hom⟩ inferInstance o.toOrientedQuiver x y p

/-- Transport maps the vertex sequence along the canonical vertex equivalence. -/
@[simp]
theorem vertices_toOrientedWalk (o : (Graph.ofSimpleGraph H).Orientation)
    {x y : (Graph.ofSimpleGraph H).vertexSet} (p : ArrowWalk o.Hom x y) :
    (o.toOrientedWalk p).vertices = p.vertices.map o.orientedVertexEquiv :=
  @Prefunctor.vertices_mapPath _ _ ⟨o.Hom⟩ inferInstance o.toOrientedQuiver x y p

/-- Transport preserves and reflects simplicity of directed paths. -/
theorem nodup_vertices_toOrientedWalk_iff (o : (Graph.ofSimpleGraph H).Orientation)
    {x y : (Graph.ofSimpleGraph H).vertexSet} (p : ArrowWalk o.Hom x y) :
    (o.toOrientedWalk p).vertices.Nodup ↔ p.IsPath := by
  rw [vertices_toOrientedWalk, ArrowWalk.isPath_def,
    List.nodup_map_iff o.orientedVertexEquiv.injective]

/-- Inverse transport preserves the number of arrows in a directed walk. -/
@[simp]
theorem length_fromOrientedWalk (o : (Graph.ofSimpleGraph H).Orientation)
    {x y : DoubledQuiver.OrientedQuiver H o.toDartOrientation} (p : Quiver.Path x y) :
    (o.fromOrientedWalk p).length = p.length :=
  @Prefunctor.length_mapPath _ _ inferInstance ⟨o.Hom⟩ o.fromOrientedQuiver x y p

/-- Inverse transport maps the vertex sequence along the inverse vertex equivalence. -/
@[simp]
theorem vertices_fromOrientedWalk (o : (Graph.ofSimpleGraph H).Orientation)
    {x y : DoubledQuiver.OrientedQuiver H o.toDartOrientation} (p : Quiver.Path x y) :
    (o.fromOrientedWalk p).vertices = p.vertices.map o.orientedVertexEquiv.symm :=
  @Prefunctor.vertices_mapPath _ _ inferInstance ⟨o.Hom⟩ o.fromOrientedQuiver x y p

/-- Inverse transport preserves and reflects simplicity of directed paths. -/
@[simp]
theorem isPath_fromOrientedWalk_iff (o : (Graph.ofSimpleGraph H).Orientation)
    {x y : DoubledQuiver.OrientedQuiver H o.toDartOrientation} (p : Quiver.Path x y) :
    (o.fromOrientedWalk p).IsPath ↔ p.vertices.Nodup := by
  rw [ArrowWalk.isPath_def, vertices_fromOrientedWalk,
    List.nodup_map_iff o.orientedVertexEquiv.symm.injective]

/-- Walking through both arrow comparisons recovers the original edge-labelled walk. -/
@[simp]
theorem fromOrientedWalk_toOrientedWalk (o : (Graph.ofSimpleGraph H).Orientation)
    {x y : (Graph.ofSimpleGraph H).vertexSet} (p : ArrowWalk o.Hom x y) :
    @Quiver.Path.cast _ ⟨o.Hom⟩ _ _ _ _
      (o.orientedVertexEquiv.symm_apply_apply x)
      (o.orientedVertexEquiv.symm_apply_apply y)
      (o.fromOrientedWalk (o.toOrientedWalk p)) = p := by
  apply @Prefunctor.cast_mapPath_mapPath _ _ ⟨o.Hom⟩ inferInstance
    o.toOrientedQuiver o.fromOrientedQuiver
  intro a b e
  apply Hom.ext
  apply Subtype.ext
  calc
    _ = s(a.1, b.1) := (@Hom.isLink V (Sym2 V) (ofSimpleGraph H) o a b _).1
    _ = _ := e.isLink.1.symm

/-- Walking through both arrow comparisons recovers the original selected-dart walk. -/
@[simp]
theorem toOrientedWalk_fromOrientedWalk (o : (Graph.ofSimpleGraph H).Orientation)
    {x y : DoubledQuiver.OrientedQuiver H o.toDartOrientation} (p : Quiver.Path x y) :
    ((o.toOrientedWalk (o.fromOrientedWalk p)).cast
      (o.orientedVertexEquiv.apply_symm_apply x)
      (o.orientedVertexEquiv.apply_symm_apply y)) = p := by
  apply @Prefunctor.cast_mapPath_mapPath _ _ inferInstance ⟨o.Hom⟩
    o.fromOrientedQuiver o.toOrientedQuiver
  intro a b e
  exact Subsingleton.elim _ _

/-- Directed reachability agrees in the two orientation interfaces. -/
theorem nonempty_oriented_path_iff (o : (Graph.ofSimpleGraph H).Orientation)
    (x y : (Graph.ofSimpleGraph H).vertexSet) :
    Nonempty (Quiver.Path (o.orientedVertexEquiv x) (o.orientedVertexEquiv y)) ↔
      Nonempty (ArrowWalk o.Hom x y) := by
  refine ⟨fun ⟨p⟩ ↦ ⟨@Quiver.Path.cast _ ⟨o.Hom⟩ _ _ _ _
    (o.orientedVertexEquiv.symm_apply_apply x) (o.orientedVertexEquiv.symm_apply_apply y)
    (o.fromOrientedWalk p)⟩,
    fun ⟨p⟩ ↦ ⟨o.toOrientedWalk p⟩⟩

/-- Strong connectivity is independent of which orientation interface is used. -/
theorem isStronglyConnected_orientedQuiver_iff (o : (Graph.ofSimpleGraph H).Orientation) :
    Quiver.IsStronglyConnected (DoubledQuiver.OrientedQuiver H o.toDartOrientation) ↔
      @Quiver.IsStronglyConnected (Graph.ofSimpleGraph H).vertexSet ⟨o.Hom⟩ := by
  constructor
  · intro h x y
    exact (o.nonempty_oriented_path_iff x y).1 (h _ _)
  · intro h x y
    obtain ⟨x, rfl⟩ := o.orientedVertexEquiv.surjective x
    obtain ⟨y, rfl⟩ := o.orientedVertexEquiv.surjective y
    exact (o.nonempty_oriented_path_iff x y).2 (h x y)

end Graph.Orientation
