/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Basic

/-!
# Orienting a simple graph and recovering its doubled quiver

An orientation of a simple graph chooses exactly one dart over every edge. The chosen darts form a
quiver with one arrow over each edge, and symmetrifying that quiver recovers the doubled quiver of
the graph. This file constructs mutually inverse, reversal-preserving prefunctors which implement
that identification.

The definition keeps the choice of orientation separate from the doubled quiver. In particular,
the comparison does not impose an ordering on the graph's vertices: a linear order merely supplies
one convenient witness that every graph admits an orientation.

## Main definitions

* `TauCeti.DoubledQuiver.Orientation`: a choice of one dart from each reversed pair.
* `TauCeti.DoubledQuiver.Orientation.ofLinearOrder`: orient every edge from its smaller endpoint
  to its larger endpoint.
* `TauCeti.DoubledQuiver.Orientation.IsSourceSink`: the property that every vertex is a source or
  a sink.
* `TauCeti.DoubledQuiver.Orientation.ofBipartition`: the source--sink orientation attached to a
  bipartition, directing every edge out of its endpoint in the chosen part, with
  `TauCeti.DoubledQuiver.Orientation.ofIsBipartite` its form for a bipartite graph.
* `TauCeti.DoubledQuiver.OrientedQuiver`: the quiver of the chosen darts.
* `TauCeti.DoubledQuiver.OrientedQuiver.homEquiv`: its arrows over a pair of graph vertices are
  exactly the adjacency proofs whose dart the orientation selects.
* `TauCeti.DoubledQuiver.symmetrifyMap`: the canonical prefunctor from the symmetrification of an
  oriented graph to its doubled quiver.
* `TauCeti.DoubledQuiver.unsymmetrifyMap`: its inverse prefunctor.

## Main results

* `TauCeti.DoubledQuiver.Orientation.isSourceSink_iff`: the defining condition of a source--sink
  orientation.
* `TauCeti.DoubledQuiver.Orientation.isSourceSink_ofBipartition` and
  `TauCeti.DoubledQuiver.exists_isSourceSink_of_isBipartite`: a bipartite graph admits a
  source--sink orientation.
* `TauCeti.DoubledQuiver.isBipartite_iff_exists_isSourceSink`: conversely a source--sink
  orientation bipartitions the graph, so the two conditions are equivalent.
* `TauCeti.DoubledQuiver.OrientedQuiver.sum_hom_eq_zero_of_forall_notMem` and
  `TauCeti.DoubledQuiver.OrientedQuiver.sum_eq_sum_vertex`: the two ways an oriented quiver indexes
  a finite sum, over the arrows above a pair of vertices and over the vertices themselves.

## References

This is the orientation comparison required in Layer 0 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`. It uses Mathlib's universal property
`Quiver.Symmetrify.lift`.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u

namespace DoubledQuiver

variable {V : Type u} (G : SimpleGraph V)

/-- An orientation of a simple graph is a set of darts containing exactly one dart over each
edge. The displayed condition says that a reversed dart is chosen exactly when the original dart
is not chosen. -/
structure Orientation where
  /-- The set of darts belonging to the orientation. -/
  carrier : Set G.Dart
  symm_mem_iff_not_mem : ∀ d, d.symm ∈ carrier ↔ d ∉ carrier

namespace Orientation

instance : SetLike (Orientation G) G.Dart where
  coe := Orientation.carrier
  coe_injective := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩ h
    congr

@[ext]
theorem ext {o₁ o₂ : Orientation G} (h : ∀ d, d ∈ o₁ ↔ d ∈ o₂) : o₁ = o₂ := by
  apply SetLike.ext
  exact h

attribute [simp] Orientation.symm_mem_iff_not_mem

/-- A reversed dart is not chosen exactly when the original dart is chosen. -/
@[simp]
theorem symm_notMem_iff_mem (o : Orientation G) (d : G.Dart) : d.symm ∉ o ↔ d ∈ o := by
  constructor
  · intro h
    by_contra hd
    exact h ((o.symm_mem_iff_not_mem d).2 hd)
  · intro hd hs
    exact ((o.symm_mem_iff_not_mem d).1 hs) hd

/-- The orientation induced by a linear order, with each edge directed from its smaller endpoint
to its larger endpoint. -/
def ofLinearOrder [LinearOrder V] : Orientation G where
  carrier := {d | d.fst < d.snd}
  symm_mem_iff_not_mem d := by
    -- `Dart.symm` stores the swapped endpoint pair, which reduces the orientation law to
    -- asymmetry and totality of the chosen linear order.
    change d.snd < d.fst ↔ ¬d.fst < d.snd
    constructor
    · exact fun h h' => (asymm h h')
    · intro h
      exact lt_of_le_of_ne (le_of_not_gt h) d.snd_ne_fst

/-- A dart belongs to the linear-order orientation exactly when its source is smaller than its
target. -/
@[simp]
theorem mem_ofLinearOrder_iff [LinearOrder V] (d : G.Dart) :
    d ∈ ofLinearOrder G ↔ d.fst < d.snd :=
  Iff.rfl

/-- An orientation is **source--sink** when every vertex is a source or a sink: at each vertex
either every incident edge is oriented away from it, or every incident edge is oriented towards
it. Such an orientation exists exactly for a bipartite graph. -/
def IsSourceSink (o : Orientation G) : Prop :=
  ∀ v : V, (∀ ⦃w : V⦄ (h : G.Adj v w), (⟨(v, w), h⟩ : G.Dart) ∈ o) ∨
    ∀ ⦃w : V⦄ (h : G.Adj v w), (⟨(v, w), h⟩ : G.Dart) ∉ o

/-- The defining condition of a source--sink orientation, exposed for use outside this module. -/
theorem isSourceSink_iff (o : Orientation G) :
    o.IsSourceSink ↔ ∀ v : V, (∀ ⦃w : V⦄ (h : G.Adj v w), (⟨(v, w), h⟩ : G.Dart) ∈ o) ∨
      ∀ ⦃w : V⦄ (h : G.Adj v w), (⟨(v, w), h⟩ : G.Dart) ∉ o := Iff.rfl

/-- The **source--sink orientation of a bipartition**: every edge is oriented from its endpoint
in `s` to its endpoint outside `s`. The hypothesis says that `s` meets every edge in exactly one
endpoint. -/
def ofBipartition (s : Set V) (hs : ∀ ⦃i j : V⦄, G.Adj i j → (i ∈ s ↔ j ∉ s)) : Orientation G where
  carrier := {d | d.fst ∈ s}
  symm_mem_iff_not_mem d := by
    -- Reversing a dart swaps its endpoints, so the condition to check is that exactly one of the
    -- two endpoints of an edge lies in `s`.
    change d.snd ∈ s ↔ d.fst ∉ s
    refine ⟨fun hsnd hfst => (hs d.adj).1 hfst hsnd, fun hfst => ?_⟩
    by_contra hsnd
    exact hfst ((hs d.adj).2 hsnd)

/-- A dart belongs to the orientation of a bipartition exactly when it leaves the chosen part. -/
@[simp]
theorem mem_ofBipartition_iff (s : Set V) (hs : ∀ ⦃i j : V⦄, G.Adj i j → (i ∈ s ↔ j ∉ s))
    (d : G.Dart) : d ∈ ofBipartition G s hs ↔ d.fst ∈ s :=
  Iff.rfl

/-- **The orientation of a bipartition is source--sink**: a vertex of the chosen part is a source,
and a vertex outside it is a sink. -/
theorem isSourceSink_ofBipartition (s : Set V) (hs : ∀ ⦃i j : V⦄, G.Adj i j → (i ∈ s ↔ j ∉ s)) :
    (ofBipartition G s hs).IsSourceSink := by
  intro v
  by_cases hv : v ∈ s
  · exact Or.inl fun _ _ => hv
  · exact Or.inr fun _ _ hmem => hv hmem

/-- The source--sink orientation attached to one of Mathlib's bipartitions. -/
def ofIsBipartiteWith {s t : Set V} (h : G.IsBipartiteWith s t) : Orientation G :=
  ofBipartition G s fun i j hij => by
    rcases h.mem_of_adj hij with ⟨his, hjt⟩ | ⟨hit, hjs⟩
    · exact iff_of_true his (Set.disjoint_left.1 h.disjoint · hjt)
    · exact iff_of_false (Set.disjoint_left.1 h.disjoint · hit) (not_not_intro hjs)

/-- The orientation attached to a bipartition of Mathlib is source--sink. -/
theorem isSourceSink_ofIsBipartiteWith {s t : Set V} (h : G.IsBipartiteWith s t) :
    (ofIsBipartiteWith G h).IsSourceSink :=
  isSourceSink_ofBipartition G s _

/-- **The source--sink orientation of a bipartite graph**, obtained by orienting every edge out of
the chosen part of a bipartition of `G`. Which bipartition is chosen is not determined by the
statement `G.IsBipartite`, so the construction is noncomputable; what is canonical is that the
result is source--sink, which is `TauCeti.DoubledQuiver.Orientation.isSourceSink_ofIsBipartite`. -/
noncomputable def ofIsBipartite (h : G.IsBipartite) : Orientation G :=
  ofIsBipartiteWith G (G.isBipartite_iff_exists_isBipartiteWith.1 h).choose_spec.choose_spec

/-- The orientation attached to a bipartite graph is source--sink. -/
theorem isSourceSink_ofIsBipartite (h : G.IsBipartite) : (ofIsBipartite G h).IsSourceSink :=
  isSourceSink_ofIsBipartiteWith G _

/-- **A source--sink orientation bipartitions the graph**: its sources and its non-sources are
disjoint, and every edge joins a source to a non-source. -/
theorem IsSourceSink.isBipartiteWith {o : Orientation G} (hss : o.IsSourceSink) :
    G.IsBipartiteWith {v : V | ∀ ⦃w : V⦄ (h : G.Adj v w), (⟨(v, w), h⟩ : G.Dart) ∈ o}
      {v : V | ¬ ∀ ⦃w : V⦄ (h : G.Adj v w), (⟨(v, w), h⟩ : G.Dart) ∈ o} where
  disjoint := Set.disjoint_left.2 fun _ hv hv' => hv' hv
  mem_of_adj i j hij := by
    by_cases hi : ∀ ⦃w : V⦄ (h : G.Adj i w), (⟨(i, w), h⟩ : G.Dart) ∈ o
    · -- The edge leaves the source `i`, so it enters `j`, which is therefore not a source.
      exact Or.inl ⟨hi, fun hj => (o.symm_mem_iff_not_mem ⟨(i, j), hij⟩).1 (hj hij.symm) (hi hij)⟩
    · -- Not being a source, `i` is a sink; the edge enters `i`, so it leaves `j`, a source.
      have hji : (⟨(j, i), hij.symm⟩ : G.Dart) ∈ o :=
        (o.symm_mem_iff_not_mem ⟨(i, j), hij⟩).2 ((hss i).resolve_left hi hij)
      exact Or.inr ⟨hi, (hss j).resolve_right fun hj => hj hij.symm hji⟩

end Orientation

/-- **A bipartite graph admits a source--sink orientation.** -/
theorem exists_isSourceSink_of_isBipartite (h : G.IsBipartite) :
    ∃ o : Orientation G, o.IsSourceSink :=
  ⟨Orientation.ofIsBipartite G h, Orientation.isSourceSink_ofIsBipartite G h⟩

/-- **A graph carrying a source--sink orientation is bipartite.** This is the converse of
`TauCeti.DoubledQuiver.exists_isSourceSink_of_isBipartite`, and the obstruction it records is the
classical one: an odd cycle cannot be oriented with every vertex a source or a sink. -/
theorem isBipartite_of_isSourceSink {o : Orientation G} (hss : o.IsSourceSink) : G.IsBipartite :=
  hss.isBipartiteWith.isBipartite

/-- **A graph is bipartite exactly when it admits a source--sink orientation.** -/
theorem isBipartite_iff_exists_isSourceSink :
    G.IsBipartite ↔ ∃ o : Orientation G, o.IsSourceSink :=
  ⟨exists_isSourceSink_of_isBipartite G, fun ⟨_, hss⟩ => isBipartite_of_isSourceSink G hss⟩

/-- The quiver obtained by retaining only the darts selected by an orientation. -/
@[expose]
def OrientedQuiver (_o : Orientation G) := V

namespace OrientedQuiver

variable (o : Orientation G)

/-- Include a graph vertex into the oriented quiver. -/
def vertex (v : V) : OrientedQuiver G o := v

/-- The graph vertices and the vertices of an oriented quiver are canonically equivalent. -/
def vertexEquiv : V ≃ OrientedQuiver G o where
  toFun := vertex G o
  invFun := fun v => v
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem vertexEquiv_apply (v : V) : vertexEquiv G o v = vertex G o v :=
  (rfl)

@[simp]
theorem vertexEquiv_symm_vertex (v : V) :
    (vertexEquiv G o).symm (vertex G o v) = v := by
  rw [← vertexEquiv_apply]
  exact (vertexEquiv G o).symm_apply_apply v

instance : _root_.Quiver (OrientedQuiver G o) where
  Hom i j := {h : G.Adj ((vertexEquiv G o).symm i) ((vertexEquiv G o).symm j) //
    ⟨((vertexEquiv G o).symm i, (vertexEquiv G o).symm j), h⟩ ∈ o}

instance : Quiver.IsThin (OrientedQuiver G o) := fun _ _ =>
  ⟨fun e f => Subtype.ext (Subsingleton.elim e.1 f.1)⟩

instance [Finite V] : Finite (OrientedQuiver G o) :=
  Finite.of_equiv V (vertexEquiv G o)

instance (i j : OrientedQuiver G o) : Finite (i ⟶ j) :=
  Finite.of_subsingleton

/-- An oriented quiver of a finite graph is a finite quiver. The path-algebra API indexes its sums
by `Fintype`, so the instance is recorded here rather than left to each caller. -/
instance [Fintype V] : Fintype (OrientedQuiver G o) :=
  Fintype.ofEquiv V (vertexEquiv G o)

/-- The arrows of an oriented quiver over a fixed pair of vertices form a finite type. Deciding
whether the orientation selects a given dart would need a further decidability hypothesis, and
everything built on path algebras is noncomputable anyway, so the enumeration is taken from the
`Finite` instance. -/
noncomputable instance (i j : OrientedQuiver G o) : Fintype (i ⟶ j) :=
  Fintype.ofFinite _

/-- The oriented-quiver arrow corresponding to a chosen dart. -/
def arrow {i j : V} (h : G.Adj i j) (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    vertex G o i ⟶ vertex G o j :=
  ⟨by simpa only [vertexEquiv_symm_vertex] using h,
    by simpa only [vertexEquiv_symm_vertex] using ho⟩

/-- The arrows of the oriented quiver between two graph vertices are exactly the adjacency proofs
whose dart is selected by the orientation. This is the characteristic description of the quiver
structure, so consumers never need to unfold the `Quiver` instance. -/
def homEquiv (i j : V) :
    (vertex G o i ⟶ vertex G o j) ≃ {h : G.Adj i j // (⟨(i, j), h⟩ : G.Dart) ∈ o} where
  toFun e := ⟨e.1, e.2⟩
  invFun p := arrow G o p.1 p.2
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subtype.ext rfl

/-- The characteristic description of the oriented-quiver arrows reads off the adjacency proof
underlying the arrow of a selected dart. -/
@[simp]
theorem homEquiv_arrow {i j : V} (h : G.Adj i j) (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    homEquiv G o i j (arrow G o h ho) = ⟨h, ho⟩ :=
  Subtype.ext rfl

/-- The characteristic description of the oriented-quiver arrows sends a selected dart back to its
arrow. -/
@[simp]
theorem homEquiv_symm_apply {i j : V} (h : G.Adj i j) (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    (homEquiv G o i j).symm ⟨h, ho⟩ = arrow G o h ho :=
  Subsingleton.elim _ _

/-- Every arrow of the oriented quiver comes from a dart selected by the orientation. -/
theorem exists_eq_arrow {i j : V} (e : vertex G o i ⟶ vertex G o j) :
    ∃ (h : G.Adj i j) (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o), e = arrow G o h ho :=
  ⟨(homEquiv G o i j e).1, (homEquiv G o i j e).2, Subsingleton.elim _ _⟩

/-- There is no arrow from `i` to `j` when the orientation selects no dart from `i` to `j`. This
covers both a nonadjacent pair and an edge oriented the other way. -/
theorem isEmpty_hom {i j : V} (h : ∀ hij : G.Adj i j, (⟨(i, j), hij⟩ : G.Dart) ∉ o) :
    IsEmpty (vertex G o i ⟶ vertex G o j) :=
  ⟨fun e => h (homEquiv G o i j e).1 (homEquiv G o i j e).2⟩

/-- **A sum indexed by the arrows over an unselected dart vanishes**, whatever its terms: the
orientation selects no dart from `i` to `j`, so there is no arrow to sum over. -/
theorem sum_hom_eq_zero_of_forall_notMem {M : Type*} [AddCommMonoid M] {i j : V}
    (h : ∀ hij : G.Adj i j, (⟨(i, j), hij⟩ : G.Dart) ∉ o)
    {F : (vertex G o i ⟶ vertex G o j) → M} : ∑ a, F a = 0 :=
  haveI := isEmpty_hom G o h
  Fintype.sum_empty _

/-- A sum over the vertices of an oriented quiver is a sum over the vertices of the graph. -/
theorem sum_eq_sum_vertex [Fintype V] {M : Type*} [AddCommMonoid M] (F : OrientedQuiver G o → M) :
    ∑ i : OrientedQuiver G o, F i = ∑ w : V, F (vertex G o w) := by
  rw [← Equiv.sum_comp (vertexEquiv G o) F]
  exact Finset.sum_congr rfl fun w _ => by rw [vertexEquiv_apply]

/-- Forgetting the choice of orientation includes the oriented quiver into the doubled quiver. -/
def forget : OrientedQuiver G o ⥤q DoubledQuiver G where
  obj i := DoubledQuiver.vertexEquiv G ((vertexEquiv G o).symm i)
  map e := Quiver.homOfEq (DoubledQuiver.arrow G e.1)
    (DoubledQuiver.vertexEquiv_apply G _).symm
    (DoubledQuiver.vertexEquiv_apply G _).symm

private theorem forget_obj_eq (i : OrientedQuiver G o) :
    (forget G o).obj i = DoubledQuiver.vertexEquiv G ((vertexEquiv G o).symm i) :=
  (rfl)

@[simp]
theorem forget_obj (i : V) :
    (forget G o).obj (vertex G o i) = DoubledQuiver.vertex G i := by
  simp only [forget_obj_eq, vertexEquiv_symm_vertex, DoubledQuiver.vertexEquiv_apply]

@[simp]
theorem forget_arrow {i j : V} (h : G.Adj i j) (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    (forget G o).map (arrow G o h ho) =
      Quiver.homOfEq (DoubledQuiver.arrow G h)
        (forget_obj G o i).symm (forget_obj G o j).symm := by
  apply Subsingleton.elim

end OrientedQuiver

variable (o : Orientation G)

/-- Symmetrifying an oriented graph and forgetting the orientation maps to the doubled quiver. -/
def symmetrifyMap : Symmetrify (OrientedQuiver G o) ⥤q DoubledQuiver G :=
  Symmetrify.lift (OrientedQuiver.forget G o)

@[simp]
theorem symmetrifyMap_obj (i : V) :
    (symmetrifyMap G o).obj (OrientedQuiver.vertex G o i) = DoubledQuiver.vertex G i := by
  exact OrientedQuiver.forget_obj G o i

/-- The comparison sends the positive copy of an oriented arrow to the doubled-quiver arrow of
the selected dart. -/
@[simp]
theorem symmetrifyMap_toPos {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    (symmetrifyMap G o).map (Sum.inl (OrientedQuiver.arrow G o h ho)) =
      Quiver.homOfEq (DoubledQuiver.arrow G h)
        (symmetrifyMap_obj G o i).symm (symmetrifyMap_obj G o j).symm := by
  apply Subsingleton.elim

/-- The comparison sends the negative copy of an oriented arrow to the doubled-quiver arrow of
the reversed dart. -/
@[simp]
theorem symmetrifyMap_toNeg {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    (symmetrifyMap G o).map (Sum.inr (OrientedQuiver.arrow G o h ho)) =
      Quiver.homOfEq (DoubledQuiver.arrow G h.symm)
        (symmetrifyMap_obj G o j).symm (symmetrifyMap_obj G o i).symm := by
  apply Subsingleton.elim

/-- The comparison from a symmetrified orientation to the doubled quiver preserves reversal. -/
instance symmetrifyMapMapReverse : Prefunctor.MapReverse (symmetrifyMap G o) where
  map_reverse' e := Symmetrify.lift_reverse _ e

/-- The inverse comparison sends a doubled arrow to the positive copy when its dart was chosen,
and to the negative copy of the oppositely oriented arrow otherwise. -/
noncomputable def unsymmetrifyMap : DoubledQuiver G ⥤q Symmetrify (OrientedQuiver G o) where
  obj i := OrientedQuiver.vertexEquiv G o ((DoubledQuiver.vertexEquiv G).symm i)
  map {i j} e := by
    let d : G.Dart :=
      ⟨((DoubledQuiver.vertexEquiv G).symm i, (DoubledQuiver.vertexEquiv G).symm j), e.down⟩
    by_cases hd : d ∈ o
    · exact Quiver.homOfEq (Sum.inl (OrientedQuiver.arrow G o d.adj hd))
        (OrientedQuiver.vertexEquiv_apply G o _).symm
        (OrientedQuiver.vertexEquiv_apply G o _).symm
    · exact Quiver.homOfEq (Sum.inr (OrientedQuiver.arrow G o d.adj.symm
          ((o.symm_mem_iff_not_mem d).2 hd)))
        (OrientedQuiver.vertexEquiv_apply G o _).symm
        (OrientedQuiver.vertexEquiv_apply G o _).symm

private theorem unsymmetrifyMap_obj_eq (i : DoubledQuiver G) :
    (unsymmetrifyMap G o).obj i =
      OrientedQuiver.vertexEquiv G o ((DoubledQuiver.vertexEquiv G).symm i) :=
  (rfl)

@[simp]
theorem unsymmetrifyMap_obj (i : V) :
    (unsymmetrifyMap G o).obj (DoubledQuiver.vertex G i) =
      OrientedQuiver.vertex G o i := by
  simp only [unsymmetrifyMap_obj_eq, DoubledQuiver.vertexEquiv_symm_vertex,
    OrientedQuiver.vertexEquiv_apply]
  rfl

/-- The symmetrification of an oriented simple graph is thin, as it has exactly one arrow in each
direction over every graph edge. -/
instance instIsThinSymmetrifyOrientedQuiver :
    Quiver.IsThin (Symmetrify (OrientedQuiver G o)) := fun i j => by
  constructor
  intro e f
  cases e with
  | inl e =>
      cases f with
      | inl f => exact congrArg Sum.inl (Subtype.ext (Subsingleton.elim e.1 f.1))
      | inr f =>
          exfalso
          exact ((o.symm_mem_iff_not_mem
            ⟨((OrientedQuiver.vertexEquiv G o).symm i,
              (OrientedQuiver.vertexEquiv G o).symm j), e.1⟩).1 f.2) e.2
  | inr e =>
      cases f with
      | inl f =>
          exfalso
          exact ((o.symm_mem_iff_not_mem
            ⟨((OrientedQuiver.vertexEquiv G o).symm i,
              (OrientedQuiver.vertexEquiv G o).symm j), f.1⟩).1 e.2) f.2
      | inr f => exact congrArg Sum.inr (Subtype.ext (Subsingleton.elim e.1 f.1))

/-- On a chosen dart, the inverse comparison returns the positive copy of the corresponding
oriented-quiver arrow. -/
@[simp]
theorem unsymmetrifyMap_arrow_of_mem {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    (unsymmetrifyMap G o).map (DoubledQuiver.arrow G h) =
      Quiver.homOfEq (Sum.inl (OrientedQuiver.arrow G o h ho))
        (unsymmetrifyMap_obj G o i).symm (unsymmetrifyMap_obj G o j).symm := by
  apply Subsingleton.elim

/-- On a dart not selected by the orientation, the inverse comparison returns the negative copy
of the oppositely oriented arrow. -/
@[simp]
theorem unsymmetrifyMap_arrow_of_not_mem {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∉ o) :
    (unsymmetrifyMap G o).map (DoubledQuiver.arrow G h) =
      Quiver.homOfEq
        (Sum.inr (OrientedQuiver.arrow G o h.symm
          ((o.symm_mem_iff_not_mem ⟨(i, j), h⟩).2 ho)))
        (unsymmetrifyMap_obj G o i).symm (unsymmetrifyMap_obj G o j).symm := by
  apply Subsingleton.elim

/-- Forgetting after restoring an orientation is the identity doubled-quiver prefunctor. -/
@[simp]
theorem unsymmetrifyMap_comp_symmetrifyMap :
    unsymmetrifyMap G o ⋙q symmetrifyMap G o = Prefunctor.id (DoubledQuiver G) := by
  refine Prefunctor.ext (fun i => ?_) ?_
  · simp only [Prefunctor.comp_obj, unsymmetrifyMap, symmetrifyMap, Symmetrify.lift,
      OrientedQuiver.forget, Prefunctor.id_obj, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply]
  intro i j e
  apply Subsingleton.elim

/-- Restoring the orientation after forgetting it is the identity on the symmetrified oriented
quiver. -/
@[simp]
theorem symmetrifyMap_comp_unsymmetrifyMap :
    symmetrifyMap G o ⋙q unsymmetrifyMap G o =
      Prefunctor.id (Symmetrify (OrientedQuiver G o)) := by
  refine Prefunctor.ext (fun i => ?_) ?_
  · simp only [Prefunctor.comp_obj, unsymmetrifyMap, symmetrifyMap, Symmetrify.lift,
      OrientedQuiver.forget, Prefunctor.id_obj, Equiv.symm_apply_apply]
    exact (OrientedQuiver.vertexEquiv G o).apply_symm_apply i
  intro i j e
  apply Subsingleton.elim

/-- The inverse comparison also preserves arrow reversal. -/
instance unsymmetrifyMapMapReverse : Prefunctor.MapReverse (unsymmetrifyMap G o) where
  map_reverse' _ := Subsingleton.elim _ _

end DoubledQuiver
end TauCeti
