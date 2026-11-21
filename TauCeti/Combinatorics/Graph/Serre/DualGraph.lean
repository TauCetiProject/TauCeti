/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Between
public import TauCeti.Combinatorics.SimpleGraph.Cohomology.Flag
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Group.Indicator
import Mathlib.Tactic.Abel

/-!
# The graph dual to the pattern of a map from a flag complex to a tree

Let `Γ` be a simple graph, `Δ` a tree and `f` a map from the vertices of `Γ` to the vertices of
`Δ`. Extend `f` over the two-skeleton of the flag complex of `Γ`, sending each edge to the
geodesic joining the images of its ends and each triangle to the tripod spanned by the images of
its vertices. The preimage of the midpoints of the edges of `Δ` is a *pattern* in the sense of
Dunwoody: it meets the edge `{a, b}` of `Γ` in `dist (f a) (f b)` points, one for each dart of `Δ`
crossed from `f a` to `f b`, and it meets a triangle in straight arcs joining the points of two
sides which lie over the same dart. Its connected components are *tracks*.

The *dual graph* (`SerreGraph.dualGraph`) has the components of the complement of the pattern as
vertices and the tracks, with a transverse orientation, as darts. Both are described without
points of the realization: a *place* (`SerreGraph.DualPlace`) is a vertex or an edge `{a, b}` of
`Γ` with a vertex `x` of `Δ` between `f a` and `f b`, and two places with the same `x` are
linked when their ends span a vertex, an edge or a triangle of `Γ` and they share an end; a
*crossing* (`SerreGraph.DualDart`) is an edge of `Γ` with a dart of `Δ` crossed along it, and two
crossings of the same dart are linked when their edges are two sides of a triangle. The vertices
and the darts of the dual graph are the classes of places and of crossings
(`SerreGraph.DualPlace.toVertex`, `SerreGraph.DualDart.toDart`). Sending a place to its vertex
`x` and a crossing to its dart defines a morphism from the dual graph to `Δ`
(`SerreGraph.dualGraphHom`).

The definitions make sense for any Serre graph `Δ`. The dual graph is preconnected when `Γ` and
`Δ` are, and connected when moreover `Γ` is nonempty. A *band* (`SerreGraph.IsBandVertex`) is a
component of the complement which contains no vertex of `Γ` and no central region of a triangle;
when `Δ` is acyclic, exactly two darts of the dual graph start at a band, and they lie over
distinct darts of `Δ`: the band is the product of a track with an interval. For instance, a place
strictly inside an edge of `Γ` lying in no triangle lies in a band.

When `Δ` is a tree and the flag complex of `Γ` is connected and has trivial first cohomology with
coefficients in `ℤ/2`, every track separates the complex, so every edge separates the dual graph,
and Dunwoody concludes that the dual graph is a tree. Here the cochain counting the crossings of
the edges of `Γ` with a track is a cocycle, and a primitive of it colours the places so that the
colour changes across the track and nowhere else. Since the tracks of a map to a tree are
two-sided, the signed count of crossings is a cocycle with coefficients in any abelian group, and
trivial first cohomology with coefficients in any nontrivial abelian group, such as `ℤ`, suffices.

## Main definitions

* `TauCeti.SerreGraph.dualGraph`: the graph dual to the pattern of `f`.
* `TauCeti.SerreGraph.DualPlace.toVertex`, `TauCeti.SerreGraph.DualDart.toDart`: the vertex of the
  dual graph containing a place and the dart through a crossing.
* `TauCeti.SerreGraph.dualVertex`: the component of the complement containing a vertex of `Γ`.
* `TauCeti.SerreGraph.dualGraphHom`: the morphism from the dual graph to `Δ`.
* `TauCeti.SerreGraph.IsBandVertex`: a component of the complement containing no vertex of `Γ`
  and meeting no triangle in its central region.

## Main results

* `TauCeti.SerreGraph.dualGraph_preconnected`, `TauCeti.SerreGraph.dualGraph_connected`: the
  dual graph is preconnected when `Γ` and `Δ` are, connected when `Γ` is connected and `Δ`
  preconnected.
* `TauCeti.SerreGraph.IsBandVertex.exists_darts`: when `Δ` is acyclic, a band has exactly two
  darts, over distinct darts of `Δ`.
* `TauCeti.SerreGraph.isBandVertex_toVertex`: a place strictly inside an edge lying in no
  triangle is in a band.
* `TauCeti.SerreGraph.isAcyclic_dualGraph`, `TauCeti.SerreGraph.isTree_dualGraph`: the dual graph
  is acyclic when `Δ` is preconnected and acyclic and the flag complex of `Γ` has trivial first
  cohomology with coefficients in a nontrivial abelian group, and a tree when moreover `Δ` is a
  tree and `Γ` is connected.

## References

* M. J. Dunwoody, *The accessibility of finitely presented groups*, Invent. Math. 81 (1985),
  449–457: §2 (tracks, bands, Proposition 2.3) and the construction of the dual tree in the
  proof of Theorem 5.1.
* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), proof of
  Proposition 2.24.
-/

public section

universe u v w

namespace TauCeti

namespace SerreGraph

variable {V : Type w} (Γ : SimpleGraph V) (Δ : SerreGraph.{u, v}) (f : V → Δ.V)

/-- A *place* of the pattern of `f`: a vertex (`fst = snd`) or an edge `{fst, snd}` of `Γ`
together with a vertex `pt` of `Δ` lying between the images of its ends. When `Δ` is acyclic, it
stands for the part of the vertex or edge sent to the open star of `pt`. -/
@[ext] structure DualPlace where
  /-- The first end. -/
  fst : V
  /-- The second end. -/
  snd : V
  /-- The vertex of `Δ`. -/
  pt : Δ.V
  /-- The two ends are equal or adjacent. -/
  eq_or_adj : fst = snd ∨ Γ.Adj fst snd
  /-- The vertex of `Δ` lies between the images of the ends. -/
  isBetween : Δ.IsBetween (f fst) pt (f snd)

variable {Γ Δ f} in
/-- Two places are *linked* when they have the same vertex of `Δ`, their ends span a vertex, an
edge or a triangle of `Γ` (they are pairwise equal or adjacent), and they share an end. -/
def DualPlace.Linked (p q : DualPlace Γ Δ f) : Prop :=
  p.pt = q.pt ∧ (p.fst = q.fst ∨ Γ.Adj p.fst q.fst) ∧ (p.fst = q.snd ∨ Γ.Adj p.fst q.snd) ∧
    (p.snd = q.fst ∨ Γ.Adj p.snd q.fst) ∧ (p.snd = q.snd ∨ Γ.Adj p.snd q.snd) ∧
    (p.fst = q.fst ∨ p.fst = q.snd ∨ p.snd = q.fst ∨ p.snd = q.snd)

/-- A *crossing* of the pattern of `f`: an oriented edge `(fst, snd)` of `Γ` together with a
dart of `Δ` crossed from the image of `fst` to the image of `snd`. It stands for a point of the
pattern on the edge, with the transverse orientation from `fst` to `snd`. -/
@[ext] structure DualDart where
  /-- The end on the source side. -/
  fst : V
  /-- The end on the target side. -/
  snd : V
  /-- The dart of `Δ`. -/
  dart : Δ.E
  /-- The two ends are adjacent. -/
  adj : Γ.Adj fst snd
  /-- The dart is crossed from the image of `fst` to the image of `snd`. -/
  crosses : Δ.Crosses (f fst) (f snd) dart

variable {Γ Δ f} in
/-- Two crossings are *linked* when they cross the same dart of `Δ` and their edges are equal or
are two sides of a triangle of `Γ`: an arc of the pattern joins the two points. -/
def DualDart.Linked (p q : DualDart Γ Δ f) : Prop :=
  p.dart = q.dart ∧ (p.fst = q.fst ∨ Γ.Adj p.fst q.fst) ∧ (p.snd = q.snd ∨ Γ.Adj p.snd q.snd) ∧
    (p.fst = q.fst ∨ p.snd = q.snd)

variable {Γ Δ f}

/-- Unfold the link between places. -/
theorem DualPlace.linked_iff {p q : DualPlace Γ Δ f} : p.Linked q ↔
    p.pt = q.pt ∧ (p.fst = q.fst ∨ Γ.Adj p.fst q.fst) ∧ (p.fst = q.snd ∨ Γ.Adj p.fst q.snd) ∧
      (p.snd = q.fst ∨ Γ.Adj p.snd q.fst) ∧ (p.snd = q.snd ∨ Γ.Adj p.snd q.snd) ∧
      (p.fst = q.fst ∨ p.fst = q.snd ∨ p.snd = q.fst ∨ p.snd = q.snd) :=
  Iff.rfl

/-- Unfold the link between crossings. -/
theorem DualDart.linked_iff {p q : DualDart Γ Δ f} : p.Linked q ↔
    p.dart = q.dart ∧ (p.fst = q.fst ∨ Γ.Adj p.fst q.fst) ∧
      (p.snd = q.snd ∨ Γ.Adj p.snd q.snd) ∧ (p.fst = q.fst ∨ p.snd = q.snd) :=
  Iff.rfl

/-- The link between places is symmetric. -/
theorem DualPlace.Linked.symm {p q : DualPlace Γ Δ f} (h : p.Linked q) : q.Linked p := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  refine ⟨h₁.symm, h₂.imp Eq.symm .symm, h₄.imp Eq.symm .symm, h₃.imp Eq.symm .symm,
    h₅.imp Eq.symm .symm, ?_⟩
  rcases h₆ with h | h | h | h <;> simp [h]

/-- The link between crossings is symmetric. -/
theorem DualDart.Linked.symm {p q : DualDart Γ Δ f} (h : p.Linked q) : q.Linked p :=
  ⟨h.1.symm, h.2.1.imp Eq.symm .symm, h.2.2.1.imp Eq.symm .symm, h.2.2.2.imp Eq.symm Eq.symm⟩

/-- The link between places is a symmetric relation. -/
instance : Std.Symm (DualPlace.Linked (Γ := Γ) (Δ := Δ) (f := f)) :=
  ⟨fun _ _ => DualPlace.Linked.symm⟩

/-- The link between crossings is a symmetric relation. -/
instance : Std.Symm (DualDart.Linked (Γ := Γ) (Δ := Δ) (f := f)) :=
  ⟨fun _ _ => DualDart.Linked.symm⟩

/-- The place on the source side of a crossing. -/
def DualDart.srcPlace (p : DualDart Γ Δ f) : DualPlace Γ Δ f :=
  ⟨p.fst, p.snd, Δ.src p.dart, .inr p.adj, p.crosses.isBetween_src⟩

@[simp] theorem DualDart.srcPlace_fst (p : DualDart Γ Δ f) : p.srcPlace.fst = p.fst := (rfl)

@[simp] theorem DualDart.srcPlace_snd (p : DualDart Γ Δ f) : p.srcPlace.snd = p.snd := (rfl)

@[simp] theorem DualDart.srcPlace_pt (p : DualDart Γ Δ f) : p.srcPlace.pt = Δ.src p.dart := (rfl)

/-- The crossing with the opposite transverse orientation. -/
def DualDart.reverse (p : DualDart Γ Δ f) : DualDart Γ Δ f :=
  ⟨p.snd, p.fst, Δ.rev p.dart, p.adj.symm, crosses_rev.mpr p.crosses⟩

@[simp] theorem DualDart.reverse_fst (p : DualDart Γ Δ f) : p.reverse.fst = p.snd := (rfl)

@[simp] theorem DualDart.reverse_snd (p : DualDart Γ Δ f) : p.reverse.snd = p.fst := (rfl)

@[simp] theorem DualDart.reverse_dart (p : DualDart Γ Δ f) : p.reverse.dart = Δ.rev p.dart :=
  (rfl)

@[simp] theorem DualDart.reverse_reverse (p : DualDart Γ Δ f) : p.reverse.reverse = p :=
  DualDart.ext rfl rfl (Δ.rev_rev p.dart)

/-- Linked crossings have linked source places. -/
theorem DualDart.Linked.srcPlace {p q : DualDart Γ Δ f} (h : p.Linked q) :
    p.srcPlace.Linked q.srcPlace := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  simp only [DualPlace.linked_iff, srcPlace_fst, srcPlace_snd, srcPlace_pt, h₁, true_and]
  have hp := p.adj
  have hq := q.adj
  rcases h₄ with h | h <;> rw [h] at hp ⊢
  · exact ⟨.inl rfl, .inr hq, .inr hp.symm, h₃, .inl rfl⟩
  · exact ⟨h₂, .inr hp, .inr hq.symm, .inl rfl, by simp⟩

/-- Linked crossings have linked reverses. -/
theorem DualDart.Linked.reverse {p q : DualDart Γ Δ f} (h : p.Linked q) :
    p.reverse.Linked q.reverse :=
  ⟨congrArg Δ.rev h.1, h.2.2.1, h.2.1, h.2.2.2.symm⟩

variable (Γ Δ f)

/-- The graph dual to the pattern of `f`: its vertices are the classes of places, which stand for
the components of the complement of the pattern, and its darts are the classes of crossings,
which stand for the tracks with a transverse orientation. -/
def dualGraph : SerreGraph.{max w u, max w v} where
  V := Quot (DualPlace.Linked (Γ := Γ) (Δ := Δ) (f := f))
  E := Quot (DualDart.Linked (Γ := Γ) (Δ := Δ) (f := f))
  src := Quot.map DualDart.srcPlace fun _ _ h => DualDart.Linked.srcPlace h
  rev := Quot.map DualDart.reverse fun _ _ h => DualDart.Linked.reverse h
  rev_rev := by
    rintro ⟨p⟩
    exact congrArg (Quot.mk _) p.reverse_reverse
  rev_ne := by
    rintro ⟨p⟩ h
    exact Δ.rev_ne p.dart (congrArg (Quot.lift DualDart.dart fun _ _ h => h.1) h)

variable {Γ Δ f}

/-- The vertex of the dual graph containing a place: the class of the place. -/
def DualPlace.toVertex (p : DualPlace Γ Δ f) : (dualGraph Γ Δ f).V :=
  Quot.mk _ p

/-- The dart of the dual graph through a crossing: the class of the crossing. -/
def DualDart.toDart (p : DualDart Γ Δ f) : (dualGraph Γ Δ f).E :=
  Quot.mk _ p

theorem DualPlace.toVertex_surjective :
    Function.Surjective (DualPlace.toVertex (Γ := Γ) (Δ := Δ) (f := f)) :=
  Quot.mk_surjective

theorem DualDart.toDart_surjective :
    Function.Surjective (DualDart.toDart (Γ := Γ) (Δ := Δ) (f := f)) :=
  Quot.mk_surjective

/-- Every vertex of the dual graph is the class of a place. -/
@[elab_as_elim]
theorem dualGraph_vertex_cases {motive : (dualGraph Γ Δ f).V → Prop}
    (place : ∀ p : DualPlace Γ Δ f, motive p.toVertex) (x : (dualGraph Γ Δ f).V) : motive x :=
  Quot.ind place x

/-- Every dart of the dual graph is the class of a crossing. -/
@[elab_as_elim]
theorem dualGraph_dart_cases {motive : (dualGraph Γ Δ f).E → Prop}
    (crossing : ∀ p : DualDart Γ Δ f, motive p.toDart) (e : (dualGraph Γ Δ f).E) : motive e :=
  Quot.ind crossing e

/-- Two places lie in the same vertex of the dual graph exactly when a chain of links joins
them. -/
theorem DualPlace.toVertex_eq_toVertex_iff {p q : DualPlace Γ Δ f} :
    p.toVertex = q.toVertex ↔ Relation.EqvGen DualPlace.Linked p q :=
  Quot.eq

/-- Two crossings lie on the same dart of the dual graph exactly when a chain of links joins
them. -/
theorem DualDart.toDart_eq_toDart_iff {p q : DualDart Γ Δ f} :
    p.toDart = q.toDart ↔ Relation.EqvGen DualDart.Linked p q :=
  Quot.eq

/-- Linked places lie in the same vertex of the dual graph. -/
theorem DualPlace.Linked.toVertex_eq {p q : DualPlace Γ Δ f} (h : p.Linked q) :
    p.toVertex = q.toVertex :=
  Quot.sound h

/-- Linked crossings lie on the same dart of the dual graph. -/
theorem DualDart.Linked.toDart_eq {p q : DualDart Γ Δ f} (h : p.Linked q) :
    p.toDart = q.toDart :=
  Quot.sound h

/-- A property of places which passes along the links between the places of a vertex of the dual
graph holds at every place of the vertex as soon as it holds at one of them. -/
theorem DualPlace.of_toVertex_eq {P : DualPlace Γ Δ f → Prop} {p q : DualPlace Γ Δ f}
    (hP : ∀ ⦃r r' : DualPlace Γ Δ f⦄, r.Linked r' → r.toVertex = p.toVertex → P r → P r')
    (h : p.toVertex = q.toVertex) (hp : P p) : P q := by
  rw [toVertex_eq_toVertex_iff, Relation.eqvGen_eq_reflTransGen] at h
  induction h with
  | refl => exact hp
  | tail hr hl ih =>
    have := toVertex_eq_toVertex_iff.mpr (Relation.reflTransGen_le_eqvGen _ _ _ hr)
    exact hP hl this.symm ih

/-- A property of crossings which passes along the links between the crossings of a dart of the
dual graph holds at every crossing of the dart as soon as it holds at one of them. -/
theorem DualDart.of_toDart_eq {P : DualDart Γ Δ f → Prop} {p q : DualDart Γ Δ f}
    (hP : ∀ ⦃r r' : DualDart Γ Δ f⦄, r.Linked r' → r.toDart = p.toDart → P r → P r')
    (h : p.toDart = q.toDart) (hp : P p) : P q := by
  rw [toDart_eq_toDart_iff, Relation.eqvGen_eq_reflTransGen] at h
  induction h with
  | refl => exact hp
  | tail hr hl ih =>
    have := toDart_eq_toDart_iff.mpr (Relation.reflTransGen_le_eqvGen _ _ _ hr)
    exact hP hl this.symm ih

@[simp] theorem dualGraph_src_toDart (p : DualDart Γ Δ f) :
    (dualGraph Γ Δ f).src p.toDart = p.srcPlace.toVertex := (rfl)

@[simp] theorem dualGraph_rev_toDart (p : DualDart Γ Δ f) :
    (dualGraph Γ Δ f).rev p.toDart = p.reverse.toDart := (rfl)

@[simp] theorem dualGraph_tgt_toDart (p : DualDart Γ Δ f) :
    (dualGraph Γ Δ f).tgt p.toDart = p.reverse.srcPlace.toVertex := (rfl)

variable (Γ Δ f)

/-- The vertex of the dual graph containing a vertex of `Γ`. -/
def dualVertex (a : V) : (dualGraph Γ Δ f).V :=
  DualPlace.toVertex ⟨a, a, f a, .inl rfl, isBetween_self _⟩

/-- The vertex of the dual graph containing `a` is the class of the place `(a, a, f a)`. -/
theorem dualVertex_def (a : V) :
    dualVertex Γ Δ f a = DualPlace.toVertex ⟨a, a, f a, .inl rfl, isBetween_self _⟩ := (rfl)

/-- The morphism from the dual graph to `Δ` which sends the class of a place to its vertex and
that of a crossing to its dart: it sends each track to the edge of `Δ` whose midpoint it lies
over. -/
def dualGraphHom : (dualGraph Γ Δ f).Hom Δ where
  mapV := Quot.lift DualPlace.pt fun _ _ h => h.1
  mapE := Quot.lift DualDart.dart fun _ _ h => h.1
  map_src := by rintro ⟨p⟩; rfl
  map_rev := by rintro ⟨p⟩; rfl

variable {Γ Δ f} in
@[simp] theorem dualGraphHom_mapV_toVertex (p : DualPlace Γ Δ f) :
    (dualGraphHom Γ Δ f).mapV p.toVertex = p.pt := (rfl)

variable {Γ Δ f} in
@[simp] theorem dualGraphHom_mapE_toDart (p : DualDart Γ Δ f) :
    (dualGraphHom Γ Δ f).mapE p.toDart = p.dart := (rfl)

@[simp] theorem dualGraphHom_mapV_dualVertex (a : V) :
    (dualGraphHom Γ Δ f).mapV (dualVertex Γ Δ f a) = f a := (rfl)

/-- A vertex of the dual graph is a *band* when it contains no vertex of `Γ` and no central
region of a triangle: none of its places has its vertex of `Δ` at the image of an end, or between
any two of the images of the vertices of a triangle containing the place (at their median, when
`Δ` is a tree). -/
def IsBandVertex (x : (dualGraph Γ Δ f).V) : Prop :=
  ∀ p : DualPlace Γ Δ f, p.toVertex = x →
    p.pt ≠ f p.fst ∧ p.pt ≠ f p.snd ∧
      ∀ c : V, Γ.Adj p.fst c → Γ.Adj p.snd c → ¬Δ.IsBetween (f p.fst) p.pt (f c) ∨
        ¬Δ.IsBetween (f c) p.pt (f p.snd)

variable {Γ Δ f}

/-- Unfold the band condition. -/
theorem isBandVertex_iff {x : (dualGraph Γ Δ f).V} : IsBandVertex Γ Δ f x ↔
    ∀ p : DualPlace Γ Δ f, p.toVertex = x →
      p.pt ≠ f p.fst ∧ p.pt ≠ f p.snd ∧
        ∀ c : V, Γ.Adj p.fst c → Γ.Adj p.snd c → ¬Δ.IsBetween (f p.fst) p.pt (f c) ∨
          ¬Δ.IsBetween (f c) p.pt (f p.snd) :=
  Iff.rfl

/-- The vertex of the dual graph containing a vertex of `Γ` is not a band. -/
theorem not_isBandVertex_dualVertex (a : V) : ¬IsBandVertex Γ Δ f (dualVertex Γ Δ f a) :=
  fun h => (h _ rfl).1 rfl

/-! ### Connectedness -/

/-- A place whose vertex of `Δ` is not the image of its first end lies on an edge of `Γ`. -/
private theorem DualPlace.adj_of_pt_ne {p : DualPlace Γ Δ f} (h : p.pt ≠ f p.fst) :
    Γ.Adj p.fst p.snd :=
  p.eq_or_adj.resolve_left fun he => h (isBetween_self_iff.mp (he ▸ p.isBetween))

/-- A place is joined in the dual graph to the vertex containing its first end, through the
tracks crossed between the image of that end and the vertex of the place. -/
private theorem nonempty_path_dualVertex_fst (p : DualPlace Γ Δ f) :
    Nonempty ((dualGraph Γ Δ f).Path (dualVertex Γ Δ f p.fst) p.toVertex) := by
  obtain ⟨a, b, x, hab, hx⟩ := p
  induction hn : Δ.dist (f a) x generalizing x with
  | zero =>
    obtain rfl := ((dist_eq_zero_iff hx.nonempty_path_left).mp hn).symm
    have hv : dualVertex Γ Δ f a = DualPlace.toVertex ⟨a, b, f a, hab, hx⟩ :=
      DualPlace.Linked.toVertex_eq ⟨rfl, .inl rfl, hab, .inl rfl, hab, .inl rfl⟩
    exact hv ▸ ⟨.nil⟩
  | succ n ih =>
    have hxa : x ≠ f a := by
      rintro rfl
      simp at hn
    -- The last dart of a shortest path from `f a` to `x` is crossed along the edge.
    obtain ⟨e, he, rfl⟩ := exists_crosses_of_isBetween hx.symm hxa
    have he' := crosses_rev.mpr he
    have hd := he'.dist_tgt
    simp only [tgt_rev, src_rev] at hd
    have hab' := DualPlace.adj_of_pt_ne (p := ⟨a, b, Δ.src e, hab, hx⟩) hxa
    obtain ⟨r⟩ := ih (Δ.tgt e) he.isBetween_tgt.symm (by lia)
    let q : DualDart Γ Δ f := ⟨a, b, Δ.rev e, hab', he'⟩
    -- `Δ.tgt e` is by definition `Δ.src (Δ.rev e)`, the vertex of the source place of `q`.
    have hsrc : (dualGraph Γ Δ f).src q.toDart = DualPlace.toVertex ⟨a, b, Δ.tgt e, hab, _⟩ :=
      dualGraph_src_toDart q
    have htgt : (dualGraph Γ Δ f).tgt q.toDart = DualPlace.toVertex ⟨a, b, Δ.src e, hab, hx⟩ :=
      (dualGraph_tgt_toDart q).trans <| DualPlace.Linked.toVertex_eq
        ⟨by simp [q], .inr hab'.symm, .inl rfl, .inl rfl, .inr hab', .inr (.inl rfl)⟩
    refine ⟨r.comp ?_⟩
    rw [← hsrc, ← htgt]
    exact ((dualGraph Γ Δ f).dart _).toPath

/-- The vertices of the dual graph containing adjacent vertices of `Γ` are joined by a path when
the images of these vertices are. -/
private theorem nonempty_path_dualVertex_of_adj {a b : V} (h : Γ.Adj a b)
    (hab : Nonempty (Δ.Path (f a) (f b))) :
    Nonempty ((dualGraph Γ Δ f).Path (dualVertex Γ Δ f a) (dualVertex Γ Δ f b)) := by
  obtain ⟨r⟩ := nonempty_path_dualVertex_fst (⟨a, b, f b, .inr h, isBetween_right hab⟩ :
    DualPlace Γ Δ f)
  have hv : dualVertex Γ Δ f b = DualPlace.toVertex ⟨a, b, f b, .inr h, isBetween_right hab⟩ :=
    DualPlace.Linked.toVertex_eq
      ⟨rfl, .inr h.symm, .inl rfl, .inr h.symm, .inl rfl, .inr (.inl rfl)⟩
  exact hv ▸ ⟨r⟩

/-- The vertices of the dual graph containing vertices of `Γ` joined by a walk are joined by a
path, when `Δ` is preconnected. -/
private theorem nonempty_path_dualVertex_of_reachable (hΔ : Δ.Preconnected) {a b : V}
    (h : Γ.Reachable a b) :
    Nonempty ((dualGraph Γ Δ f).Path (dualVertex Γ Δ f a) (dualVertex Γ Δ f b)) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact ⟨.nil⟩
  | cons h _ ih =>
    obtain ⟨r⟩ := nonempty_path_dualVertex_of_adj h ((preconnected_iff Δ).mp hΔ _ _)
    obtain ⟨s⟩ := ih
    exact ⟨r.comp s⟩

/-- The graph dual to the pattern of a map from a preconnected graph to a preconnected graph is
preconnected. -/
theorem dualGraph_preconnected (hΔ : Δ.Preconnected) (hΓ : Γ.Preconnected) :
    (dualGraph Γ Δ f).Preconnected := by
  refine (preconnected_iff _).mpr fun x y => ?_
  obtain ⟨p, rfl⟩ := DualPlace.toVertex_surjective x
  obtain ⟨q, rfl⟩ := DualPlace.toVertex_surjective y
  obtain ⟨r⟩ := nonempty_path_dualVertex_fst p
  obtain ⟨s⟩ := nonempty_path_dualVertex_of_reachable hΔ (hΓ p.fst q.fst)
  obtain ⟨t⟩ := nonempty_path_dualVertex_fst q
  exact ⟨r.reverse.comp (s.comp t)⟩

/-- The graph dual to the pattern of a map from a connected graph to a preconnected graph is
connected. -/
theorem dualGraph_connected (hΔ : Δ.Preconnected) (hΓ : Γ.Connected) :
    (dualGraph Γ Δ f).Connected :=
  (connected_iff _).mpr ⟨hΓ.nonempty.map (dualVertex Γ Δ f),
    dualGraph_preconnected hΔ hΓ.preconnected⟩

/-! ### Bands -/

/-- The same place with its two ends exchanged. -/
private def DualPlace.swap (p : DualPlace Γ Δ f) : DualPlace Γ Δ f :=
  ⟨p.snd, p.fst, p.pt, p.eq_or_adj.imp Eq.symm .symm, p.isBetween.symm⟩

private theorem DualPlace.Linked.swap_right {p q : DualPlace Γ Δ f} (h : p.Linked q) :
    p.Linked q.swap := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  refine ⟨h₁, h₃, h₂, h₅, h₄, ?_⟩
  rcases h₆ with h | h | h | h <;> simp [DualPlace.swap, h]

private theorem DualPlace.linked_swap (p : DualPlace Γ Δ f) : p.Linked p.swap :=
  DualPlace.Linked.swap_right
    ⟨rfl, .inl rfl, p.eq_or_adj, p.eq_or_adj.imp Eq.symm .symm, .inl rfl, .inl rfl⟩

/-- A place strictly inside an edge of `Γ` which lies in no triangle is a band: all the places
in its class are places of the same edge over the same vertex of `Δ`. -/
theorem isBandVertex_toVertex {p : DualPlace Γ Δ f} (h₁ : p.pt ≠ f p.fst) (h₂ : p.pt ≠ f p.snd)
    (h : ∀ c : V, Γ.Adj p.fst c → ¬Γ.Adj p.snd c) : IsBandVertex Γ Δ f p.toVertex := by
  -- The places of the class lie over `p.pt`, and their ends are ends of `p`.
  let I (q : DualPlace Γ Δ f) : Prop :=
    q.pt = p.pt ∧ (q.fst = p.fst ∨ q.fst = p.snd) ∧ (q.snd = p.fst ∨ q.snd = p.snd)
  have hne {q : DualPlace Γ Δ f} (hq : I q) : q.fst ≠ q.snd :=
    (DualPlace.adj_of_pt_ne (p := q) (by rcases hq with ⟨hpt, hf | hf, -⟩ <;> rw [hpt, hf] <;>
      assumption)).ne
  have step ⦃q q' : DualPlace Γ Δ f⦄ (hl : q.Linked q') (_ : q.toVertex = p.toVertex)
      (hq : I q) : I q' := by
    have hqq := hne hq
    obtain ⟨hpt, hf, hs⟩ := hq
    obtain ⟨hpt', h₁₁, h₁₂, h₂₁, h₂₂, -⟩ := hl
    have := h q'.fst
    have := h q'.snd
    refine ⟨hpt'.symm.trans hpt, ?_, ?_⟩ <;> grind [SimpleGraph.adj_comm]
  intro q hq
  have hI : I q := DualPlace.of_toVertex_eq step hq.symm ⟨rfl, .inl rfl, .inr rfl⟩
  have hqq := hne hI
  obtain ⟨hpt, hf, hs⟩ := hI
  refine ⟨?_, ?_, fun c hc hc' => (h c ?_ ?_).elim⟩ <;> grind [SimpleGraph.adj_comm]

/-- Over an acyclic graph, a crossing is determined by its source place: there is only one dart
leaving a vertex between two vertices towards the second one. -/
theorem DualDart.srcPlace_injective (hΔ : Δ.IsAcyclic) :
    Function.Injective (DualDart.srcPlace (Γ := Γ) (Δ := Δ) (f := f)) := by
  intro q q' h
  obtain ⟨hc, hd, hs⟩ := DualPlace.ext_iff.mp h
  simp only [srcPlace_fst, srcPlace_snd, srcPlace_pt] at hc hd hs
  have hg := q'.crosses
  rw [← hc, ← hd] at hg
  exact DualDart.ext hc hd (hΔ.eq_of_crosses_of_src_eq q.crosses hg hs)

/-- Let a place `(a, b, src g)` be linked to the source place of a crossing `(c, d, g)` sharing
the end `a` or `b`, with `src g` not the median of the triangle. Then `g` is also crossed from
`f a` to `f b`: the arc of the track through the crossing leaves the triangle through `{a, b}`. -/
private theorem crosses_of_linked (hΔ : Δ.IsAcyclic) {a b c d : V} {g : Δ.E} (hr : Γ.Adj a b)
    (hy : Δ.IsBetween (f a) (Δ.src g) (f b)) (hg : Δ.Crosses (f c) (f d) g)
    (ac : a = c ∨ Γ.Adj a c) (bd : b = d ∨ Γ.Adj b d)
    (hmed : ∀ c' : V, Γ.Adj c c' → Γ.Adj d c' →
      ¬Δ.IsBetween (f c) (Δ.src g) (f c') ∨ ¬Δ.IsBetween (f c') (Δ.src g) (f d))
    (h : a = c ∨ b = d) : Δ.Crosses (f a) (f b) g := by
  rcases h with rfl | rfl
  · rcases bd with rfl | hbd
    · exact hg
    refine (hΔ.crosses_or_crosses hg hy.nonempty_path).resolve_right fun h => ?_
    exact (hmed b hr hbd.symm).elim (· hy) (· h.isBetween_src)
  · rcases ac with rfl | hac
    · exact hg
    refine (hΔ.crosses_or_crosses hg ⟨?_⟩).resolve_left fun h => ?_
    · exact (hg.isBetween_src.nonempty_path_left.some).comp hy.symm.nonempty_path_right.some
    · exact (hmed a hac.symm hr.symm).elim (· h.isBetween_src) (· hy)

/-- A crossing whose source place is linked to an edge place `r` and does not lie at the centre
of a triangle containing its edge is linked to a crossing with source place `r`, or `r` with its
ends exchanged. -/
private theorem exists_linked_of_linked_srcPlace (hΔ : Δ.IsAcyclic) {r : DualPlace Γ Δ f}
    (hr : Γ.Adj r.fst r.snd) {q' : DualDart Γ Δ f} (hl : r.Linked q'.srcPlace)
    (hmed : ∀ c : V, Γ.Adj q'.fst c → Γ.Adj q'.snd c →
      ¬Δ.IsBetween (f q'.fst) (Δ.src q'.dart) (f c) ∨
        ¬Δ.IsBetween (f c) (Δ.src q'.dart) (f q'.snd)) :
    ∃ q : DualDart Γ Δ f, (q.srcPlace = r ∨ q.srcPlace = r.swap) ∧ q.Linked q' := by
  obtain ⟨a, b, y, hab, hy⟩ := r
  obtain ⟨c, d, g, hcd, hg⟩ := q'
  obtain ⟨rfl : y = Δ.src g, ac, ad, bc, bd, hs⟩ := hl
  dsimp only at hr hy ac ad bc bd hs hmed
  -- The shared end decides the orientation of the crossing along `{a, b}`.
  obtain h | h : (a = c ∨ b = d) ∨ (b = c ∨ a = d) := by
    rcases hs with h | h | h | h <;> simp [h]
  · exact ⟨⟨a, b, g, hr, crosses_of_linked hΔ hr hy hg ac bd hmed h⟩, .inl rfl, rfl, ac, bd, h⟩
  · exact ⟨⟨b, a, g, hr.symm, crosses_of_linked hΔ hr.symm hy.symm hg bc ad hmed h⟩, .inr rfl,
      rfl, bc, ad, h⟩

/-- In a band, a crossing whose source place is a place `r'` linked to a place `r` of the band, or
`r'` with its ends exchanged, is linked to a crossing with source place `r` or `r` with its ends
exchanged. -/
private theorem exists_linked_of_isBandVertex (hΔ : Δ.IsAcyclic) {x : (dualGraph Γ Δ f).V}
    (hx : IsBandVertex Γ Δ f x) {r r' : DualPlace Γ Δ f} (hrr' : r.Linked r')
    (hr : r.toVertex = x) {q' : DualDart Γ Δ f} (hq' : q'.srcPlace = r' ∨ q'.srcPlace = r'.swap) :
    ∃ q : DualDart Γ Δ f, (q.srcPlace = r ∨ q.srcPlace = r.swap) ∧ q.Linked q' := by
  have hl : r.Linked q'.srcPlace := by
    rcases hq' with h | h <;> rw [h]
    exacts [hrr', hrr'.swap_right]
  exact exists_linked_of_linked_srcPlace hΔ (DualPlace.adj_of_pt_ne (hx r hr).1) hl
    (hx _ (hl.toVertex_eq.symm.trans hr)).2.2

/-- A band of the pattern of a map to an acyclic graph has exactly two darts, and they lie over
distinct darts of the graph, as do the two sides of the product of a track with an interval. -/
theorem IsBandVertex.exists_darts (hΔ : Δ.IsAcyclic) {x : (dualGraph Γ Δ f).V}
    (hx : IsBandVertex Γ Δ f x) :
    ∃ e₁ e₂ : (dualGraph Γ Δ f).E, (dualGraphHom Γ Δ f).mapE e₁ ≠ (dualGraphHom Γ Δ f).mapE e₂ ∧
      ∀ e : (dualGraph Γ Δ f).E, (dualGraph Γ Δ f).src e = x ↔ e = e₁ ∨ e = e₂ := by
  induction x using dualGraph_vertex_cases with | place p => ?_
  obtain ⟨hpa, hpb, -⟩ := hx p rfl
  have hp := DualPlace.adj_of_pt_ne hpa
  -- The crossings of the edge of `p` over the two darts of `Δ` leaving `p.pt` along the edge.
  obtain ⟨d₁, hd₁, hs₁⟩ := exists_crosses_of_isBetween p.isBetween hpb
  obtain ⟨d₂, hd₂, hs₂⟩ := exists_crosses_of_isBetween p.isBetween.symm hpa
  let q₁ : DualDart Γ Δ f := ⟨p.fst, p.snd, d₁, hp, hd₁⟩
  let q₂ : DualDart Γ Δ f := ⟨p.snd, p.fst, d₂, hp.symm, hd₂⟩
  have hq₁ : q₁.srcPlace = p := DualPlace.ext rfl rfl hs₁
  have hq₂ : q₂.srcPlace = p.swap := DualPlace.ext rfl rfl hs₂
  -- The crossings with source place `r` or `r.swap` lie on the two tracks of `q₁` and `q₂`; this
  -- holds at `p` and passes along the links between the places of the band.
  let N (r : DualPlace Γ Δ f) : Prop := ∀ q : DualDart Γ Δ f, q.srcPlace = r ∨ q.srcPlace = r.swap →
    q.toDart = q₁.toDart ∨ q.toDart = q₂.toDart
  have hN : N p := fun q hq => hq.imp
    (fun h => congrArg _ (DualDart.srcPlace_injective hΔ (h.trans hq₁.symm)))
    (fun h => congrArg _ (DualDart.srcPlace_injective hΔ (h.trans hq₂.symm)))
  have step ⦃r r' : DualPlace Γ Δ f⦄ (hrr' : r.Linked r') (hr : r.toVertex = p.toVertex)
      (hNr : N r) : N r' := fun q' hq' => by
    obtain ⟨q, hq, hqq'⟩ := exists_linked_of_isBandVertex hΔ hx hrr' hr hq'
    rw [← hqq'.toDart_eq]
    exact hNr q hq
  refine ⟨q₁.toDart, q₂.toDart, fun h => ?_, fun e => ⟨fun he => ?_, ?_⟩⟩
  · simp only [dualGraphHom_mapE_toDart, q₁, q₂] at h
    exact hd₁.not_crosses_rev (crosses_rev.mpr (h ▸ hd₂))
  · induction e using dualGraph_dart_cases with | crossing q => ?_
    rw [dualGraph_src_toDart] at he
    exact DualPlace.of_toVertex_eq step he.symm hN q (.inl rfl)
  · rintro (rfl | rfl)
    · exact congrArg DualPlace.toVertex hq₁
    · exact (congrArg DualPlace.toVertex hq₂).trans (DualPlace.linked_swap p).symm.toVertex_eq

/-! ### The dual graph is a tree -/

/-- Two crossings of the same oriented edge of `Γ` lying on the same edge of the dual graph are
equal: an edge of `Γ` crosses each dart of `Δ` at most once, and never a dart and its reverse. -/
private theorem DualDart.eq_of_toGeomEdge_eq {q q' : DualDart Γ Δ f} (hf : q.fst = q'.fst)
    (hs : q.snd = q'.snd)
    (h : (dualGraph Γ Δ f).toGeomEdge q.toDart = (dualGraph Γ Δ f).toGeomEdge q'.toDart) :
    q = q' := by
  have hc := q'.crosses
  rw [← hf, ← hs] at hc
  rcases (dualGraph Γ Δ f).toGeomEdge_eq_toGeomEdge_iff.mp h with h | h <;>
    have hd := congrArg (dualGraphHom Γ Δ f).mapE h <;>
    simp only [dualGraphHom_mapE_toDart, Hom.map_rev] at hd
  · exact DualDart.ext hf hs hd.symm
  · exact (q.crosses.not_crosses_rev (hd ▸ hc)).elim

/-- The edge `(a, b)` of `Γ` has a crossing on the dart `s` of the dual graph, over a dart of `Δ`
crossed from `f a` to `x`: the track of `s` meets the edge between `a` and the region over `x`. -/
private def TrackBefore (s : (dualGraph Γ Δ f).E) (a b : V) (x : Δ.V) : Prop :=
  ∃ q : DualDart Γ Δ f, q.fst = a ∧ q.snd = b ∧ Δ.Crosses (f a) x q.dart ∧ q.toDart = s

/-- The crossing of `(a, b)` on `s` before `x` and the crossing of `(b, a)` on `rev s` before `x`
cannot both exist: the reverse of the second would be the first, crossed after `x`. -/
private theorem not_trackBefore_and_trackBefore {s : (dualGraph Γ Δ f).E} {a b : V} {x : Δ.V} :
    ¬(TrackBefore s a b x ∧ TrackBefore ((dualGraph Γ Δ f).rev s) b a x) := by
  rintro ⟨⟨q, rfl, rfl, hq, rfl⟩, ⟨q', hb, ha, hq', hs⟩⟩
  have hd : q.dart = Δ.rev q'.dart := by
    rw [DualDart.eq_of_toGeomEdge_eq (q' := q'.reverse) ha.symm hb.symm (by
      rw [← dualGraph_rev_toDart, hs, rev_rev]), DualDart.reverse_dart]
  exact hq.not_crosses_right (hd ▸ crosses_rev.mpr hq')

/-- Splitting the edge `(a, b)` at a vertex `x` between `f a` and `f b`: its crossing on `s` lies
before `x`, or its reverse is the crossing of `(b, a)` on `rev s` before `x`. -/
private theorem trackBefore_iff (hΔ : Δ.IsAcyclic) {s : (dualGraph Γ Δ f).E} {a b : V} {x : Δ.V}
    (hx : Δ.IsBetween (f a) x (f b)) : TrackBefore s a b (f b) ↔
      TrackBefore s a b x ∨ TrackBefore ((dualGraph Γ Δ f).rev s) b a x := by
  refine ⟨fun ⟨q, ha, hb, hq, hs⟩ => ?_, ?_⟩
  · refine (hΔ.crosses_or_crosses hq hx.nonempty_path_left).imp (fun h => ⟨q, ha, hb, h, hs⟩)
      fun h => ⟨q.reverse, hb, ha, by simpa [← hb] using h, by rw [← dualGraph_rev_toDart, hs]⟩
  · rintro (⟨q, ha, hb, -, hs⟩ | ⟨q, hb, ha, -, hs⟩)
    · exact ⟨q, ha, hb, ha ▸ hb ▸ q.crosses, hs⟩
    · exact ⟨q.reverse, ha, hb, by simpa [← ha, ← hb] using q.crosses,
        by rw [← dualGraph_rev_toDart, hs, rev_rev]⟩

/-- Along two sides `(a, b)` and `(a, c)` of a triangle of `Γ` (or twice the same side), the same
tracks are met before a vertex `x` between `f a` and both `f b` and `f c`. -/
private theorem TrackBefore.of_isBetween {s : (dualGraph Γ Δ f).E} {a b c : V} {x : Δ.V}
    (h : TrackBefore s a b x) (hac : a = c ∨ Γ.Adj a c) (hbc : b = c ∨ Γ.Adj b c)
    (hx : Δ.IsBetween (f a) x (f c)) : TrackBefore s a c x := by
  obtain ⟨q, rfl, rfl, hq, rfl⟩ := h
  -- The edge `(q.fst, c)` is not a vertex: a dart is crossed from `f q.fst` to `x`.
  have hac : Γ.Adj q.fst c := hac.resolve_left fun h => by
    subst h
    exact not_crosses_self _ _ (isBetween_self_iff.mp hx ▸ hq)
  let q' : DualDart Γ Δ f := ⟨q.fst, c, q.dart, hac, hx.crosses_of_crosses_left hq⟩
  have hl : q.Linked q' := ⟨rfl, .inl rfl, hbc, .inl rfl⟩
  exact ⟨q', rfl, rfl, hq, hl.toDart_eq.symm⟩

/-- Before the target of the dart of a crossing `q`, the edge of `q` meets the tracks it meets
before the source of that dart, and the track of `q`. -/
private theorem trackBefore_tgt_iff (hΔ : Δ.IsAcyclic) (q : DualDart Γ Δ f)
    {s : (dualGraph Γ Δ f).E} : TrackBefore s q.fst q.snd (Δ.tgt q.dart) ↔
      TrackBefore s q.fst q.snd (Δ.src q.dart) ∨ s = q.toDart := by
  -- The dart of `q` is crossed from the image of `q.fst` to its own target.
  have ht : Δ.Crosses (f q.fst) (Δ.tgt q.dart) q.dart :=
    crosses_rev.mp (crosses_rev.mpr q.crosses).crosses_src
  refine ⟨fun ⟨q', ha, hb, hq', hs⟩ => ?_, ?_⟩
  · refine (hΔ.crosses_or_crosses hq' ht.isBetween_src.nonempty_path_left).imp
      (fun h => ⟨q', ha, hb, h, hs⟩) fun h => ?_
    have hd : q'.dart = q.dart := by
      simpa using (hΔ.crosses_iff_mem_darts (Path.isReduced_toPath Δ (Δ.dart q.dart))).mp h
    rw [← hs, DualDart.ext ha hb hd]
  · rintro (⟨q', ha, hb, hq', hs⟩ | rfl)
    · exact ⟨q', ha, hb, ht.isBetween_src.crosses_of_crosses_left hq', hs⟩
    · exact ⟨q, rfl, rfl, ht, rfl⟩

/-- The track of a crossing `q` is not met along its edge before the source of its dart. -/
private theorem not_trackBefore_src (q : DualDart Γ Δ f) :
    ¬TrackBefore q.toDart q.fst q.snd (Δ.src q.dart) := by
  rintro ⟨q', ha, hb, hq', hs⟩
  obtain rfl := DualDart.eq_of_toGeomEdge_eq ha.symm hb.symm (congrArg _ hs.symm)
  exact not_crosses_self _ _ hq'.crosses_src

/-- No track is met along an edge before the image of its first end. -/
private theorem not_trackBefore_self {s : (dualGraph Γ Δ f).E} {a b : V} :
    ¬TrackBefore s a b (f a) :=
  fun ⟨_, _, _, hq, _⟩ => not_crosses_self _ _ hq

section Cochain

variable {A : Type*} [AddCommGroup A]

/-- The signed number of crossings of the edge `(a, b)` with the track of the dart `t` of the dual
graph before `x`: `a₀` for a crossing with the orientation of `t`, `-a₀` for the opposite one.
It is the indicator of the set of darts whose tracks are met, at `t` minus at the reverse of `t`. -/
private noncomputable def trackCount (a₀ : A) (t : (dualGraph Γ Δ f).E) (a b : V) (x : Δ.V) : A :=
  {s | TrackBefore s a b x}.indicator (fun _ => a₀) t -
    {s | TrackBefore s a b x}.indicator (fun _ => a₀) ((dualGraph Γ Δ f).rev t)

variable (a₀ : A) (t : (dualGraph Γ Δ f).E)

/-- Splitting the count of an edge `(a, b)` at a vertex between `f a` and `f b`. -/
private theorem trackCount_eq_sub (hΔ : Δ.IsAcyclic) {a b : V} {x : Δ.V}
    (hx : Δ.IsBetween (f a) x (f b)) :
    trackCount a₀ t a b (f b) = trackCount a₀ t a b x - trackCount a₀ t b a x := by
  -- The tracks met before `f b` are those met before `x` and the reverses of those met along
  -- `(b, a)` before `x`.
  let T : Set (dualGraph Γ Δ f).E := {s | TrackBefore s b a x}
  have h : {s | TrackBefore s a b (f b)} =
      {s | TrackBefore s a b x} ∪ (dualGraph Γ Δ f).rev ⁻¹' T :=
    Set.ext fun _ => trackBefore_iff hΔ hx
  have hd : Disjoint {s | TrackBefore s a b x} ((dualGraph Γ Δ f).rev ⁻¹' T) :=
    Set.disjoint_left.mpr fun _ h₁ h₂ => not_trackBefore_and_trackBefore ⟨h₁, h₂⟩
  have hT (s) : ((dualGraph Γ Δ f).rev ⁻¹' T).indicator (fun _ => a₀) s =
      T.indicator (fun _ => a₀) ((dualGraph Γ Δ f).rev s) :=
    Set.indicator_comp_right (g := fun _ => a₀) _
  simp only [trackCount, h, Set.indicator_union_of_disjoint hd, hT, rev_rev, T]
  abel

/-- Along two sides `(a, b)` and `(a, c)` of a triangle (or twice the same side) the counts before
a vertex between `f a` and both `f b` and `f c` agree. -/
private theorem trackCount_eq_of_isBetween {a b c : V} {x : Δ.V} (hab : a = b ∨ Γ.Adj a b)
    (hac : a = c ∨ Γ.Adj a c) (hbc : b = c ∨ Γ.Adj b c) (hxb : Δ.IsBetween (f a) x (f b))
    (hxc : Δ.IsBetween (f a) x (f c)) : trackCount a₀ t a b x = trackCount a₀ t a c x := by
  have key (s : (dualGraph Γ Δ f).E) : TrackBefore s a b x ↔ TrackBefore s a c x :=
    ⟨fun h => h.of_isBetween hac hbc hxc, fun h => h.of_isBetween hab (hbc.imp Eq.symm .symm) hxb⟩
  simp [trackCount, key]

/-- Crossing the dart of a crossing `q` changes the count along its edge by `a₀` if `q` lies on
`t`, by `-a₀` if it lies on the reverse of `t`, and not at all otherwise. -/
private theorem trackCount_tgt (hΔ : Δ.IsAcyclic) (q : DualDart Γ Δ f) :
    trackCount a₀ t q.fst q.snd (Δ.tgt q.dart) = trackCount a₀ t q.fst q.snd (Δ.src q.dart) +
      (({q.toDart} : Set _).indicator (fun _ => a₀) t -
        ({q.toDart} : Set _).indicator (fun _ => a₀) ((dualGraph Γ Δ f).rev t)) := by
  have h : {s | TrackBefore s q.fst q.snd (Δ.tgt q.dart)} =
      {s | TrackBefore s q.fst q.snd (Δ.src q.dart)} ∪ {q.toDart} :=
    Set.ext fun _ => trackBefore_tgt_iff hΔ q
  have hd : Disjoint {s | TrackBefore s q.fst q.snd (Δ.src q.dart)} {q.toDart} :=
    Set.disjoint_singleton_right.mpr (not_trackBefore_src q)
  simp only [trackCount, h, Set.indicator_union_of_disjoint hd]
  abel

/-- The counts along the edges of `Γ` form a one-cochain of its flag complex: reversing an edge
changes the sign of its count. -/
private theorem trackCount_swap (hΔ : Δ.Preconnected) (hΔ' : Δ.IsAcyclic) (a b : V) :
    trackCount a₀ t b a (f a) = -trackCount a₀ t a b (f b) := by
  have h := trackCount_eq_sub a₀ t hΔ' (isBetween_left ((preconnected_iff Δ).mp hΔ (f a) (f b)))
  -- No track is met along `(a, b)` before `f a`.
  have h0 : trackCount a₀ t a b (f a) = 0 := by simp [trackCount, not_trackBefore_self]
  rw [h, h0, zero_sub, neg_neg]

/-- The cochain of the counts is a cocycle: on a triangle of `Γ`, the counts along two sides add
up to the count along the third side. -/
private theorem trackCount_add (hΔ : Δ.Preconnected) (hΔ' : Δ.IsAcyclic) {a b c : V}
    (hab : Γ.Adj a b) (hbc : Γ.Adj b c) (hac : Γ.Adj a c) :
    trackCount a₀ t a b (f b) + trackCount a₀ t b c (f c) = trackCount a₀ t a c (f c) := by
  -- Split the three sides at the median of the images of the corners.
  have hp := (preconnected_iff Δ).mp hΔ
  obtain ⟨m, ⟨h₁, h₂, h₃⟩, -⟩ := hΔ'.existsUnique_isBetween (hp (f a) (f b)) (hp (f a) (f c))
  simp only [trackCount_eq_sub a₀ t hΔ' h₁, trackCount_eq_sub a₀ t hΔ' h₂,
    trackCount_eq_sub a₀ t hΔ' h₃,
    trackCount_eq_of_isBetween a₀ t (.inr hab) (.inr hac) (.inr hbc) h₁ h₃,
    trackCount_eq_of_isBetween a₀ t (.inr hab.symm) (.inr hbc) (.inr hac) h₁.symm h₂,
    trackCount_eq_of_isBetween a₀ t (.inr hbc.symm) (.inr hac.symm) (.inr hab.symm) h₂.symm
      h₃.symm]
  abel

/-- The colour of a place: the value of `c` at its first end plus the count of its edge before
its vertex of `Δ`. -/
private noncomputable def placeColour (c : V → A) (p : DualPlace Γ Δ f) : A :=
  c p.fst + trackCount a₀ t p.fst p.snd p.pt

/-- When `c` is a primitive of the cochain of the track, exchanging the ends of a place does not
change its colour. -/
private theorem placeColour_swap (hΔ : Δ.IsAcyclic) {c : V → A}
    (hc : ∀ a b, Γ.Adj a b → trackCount a₀ t a b (f b) = c b - c a) (p : DualPlace Γ Δ f) :
    placeColour a₀ t c p.swap = placeColour a₀ t c p := by
  obtain ⟨a, b, x, rfl | hab, hx⟩ := p
  · rfl
  have h := (hc a b hab).symm.trans (trackCount_eq_sub a₀ t hΔ hx)
  rw [placeColour, placeColour, add_comm (c a)]
  exact sub_eq_sub_iff_add_eq_add.mp h

/-- Two places over the same vertex of `Δ` with the same first end and equal or adjacent second
ends have the same colour. -/
private theorem placeColour_eq_of_fst_eq (c : V → A) {p q : DualPlace Γ Δ f} (h₁ : p.fst = q.fst)
    (h₂ : p.pt = q.pt) (h₃ : p.snd = q.snd ∨ Γ.Adj p.snd q.snd) :
    placeColour a₀ t c p = placeColour a₀ t c q := by
  obtain ⟨a, b, x, hab, hx⟩ := p
  dsimp only at h₁ h₂ h₃
  subst h₁ h₂
  rw [placeColour, placeColour,
    trackCount_eq_of_isBetween a₀ t hab q.eq_or_adj h₃ hx q.isBetween]

/-- Linked places have the same colour. -/
private theorem placeColour_eq_of_linked (hΔ : Δ.IsAcyclic) {c : V → A}
    (hc : ∀ a b, Γ.Adj a b → trackCount a₀ t a b (f b) = c b - c a) {p q : DualPlace Γ Δ f}
    (h : p.Linked q) : placeColour a₀ t c p = placeColour a₀ t c q := by
  obtain ⟨hpt, h₁₁, h₁₂, h₂₁, h₂₂, h | h | h | h⟩ := h
  · exact placeColour_eq_of_fst_eq a₀ t c h hpt h₂₂
  · exact (placeColour_eq_of_fst_eq a₀ t c (q := q.swap) h hpt h₂₁).trans
      (placeColour_swap a₀ t hΔ hc q)
  · exact (placeColour_swap a₀ t hΔ hc p).symm.trans
      (placeColour_eq_of_fst_eq a₀ t c (p := p.swap) h hpt h₁₂)
  · exact (placeColour_swap a₀ t hΔ hc p).symm.trans
      ((placeColour_eq_of_fst_eq a₀ t c (p := p.swap) (q := q.swap) h hpt h₁₁).trans
        (placeColour_swap a₀ t hΔ hc q))

/-- Places in the same vertex of the dual graph have the same colour. -/
private theorem placeColour_eq_of_toVertex_eq (hΔ : Δ.IsAcyclic) {c : V → A}
    (hc : ∀ a b, Γ.Adj a b → trackCount a₀ t a b (f b) = c b - c a) {p q : DualPlace Γ Δ f}
    (h : p.toVertex = q.toVertex) : placeColour a₀ t c p = placeColour a₀ t c q :=
  DualPlace.of_toVertex_eq (P := fun r => placeColour a₀ t c p = placeColour a₀ t c r)
    (fun _ _ hl _ hr => hr.trans (placeColour_eq_of_linked a₀ t hΔ hc hl)) h rfl

/-- Across a crossing `q` the colour changes by `a₀` if `q` lies on `t`, by `-a₀` if it lies on
the reverse of `t`, and not at all otherwise. -/
private theorem placeColour_reverse_srcPlace (hΔ : Δ.IsAcyclic) {c : V → A}
    (hc : ∀ a b, Γ.Adj a b → trackCount a₀ t a b (f b) = c b - c a) (q : DualDart Γ Δ f) :
    placeColour a₀ t c q.reverse.srcPlace = placeColour a₀ t c q.srcPlace +
      (({q.toDart} : Set _).indicator (fun _ => a₀) t -
        ({q.toDart} : Set _).indicator (fun _ => a₀) ((dualGraph Γ Δ f).rev t)) := by
  rw [← placeColour_swap a₀ t hΔ hc]
  simp only [placeColour, DualPlace.swap, DualDart.srcPlace_fst, DualDart.srcPlace_snd,
    DualDart.srcPlace_pt, DualDart.reverse_fst, DualDart.reverse_snd, DualDart.reverse_dart,
    src_rev, trackCount_tgt a₀ t hΔ q]
  abel

/-- If the cochain of the track of `t` has a primitive `c`, then every path of the dual graph from
the target of `t` back to its source passes through `t` or its reverse: the colour of the places
changes across the track of `t`, and nowhere else. -/
private theorem mem_darts_of_primitive (hΔ : Δ.IsAcyclic) (ha₀ : a₀ ≠ 0) {c : V → A}
    (hc : ∀ a b, Γ.Adj a b → trackCount a₀ t a b (f b) = c b - c a)
    (P : (dualGraph Γ Δ f).Path ((dualGraph Γ Δ f).tgt t) ((dualGraph Γ Δ f).src t)) :
    t ∈ Path.darts _ P ∨ (dualGraph Γ Δ f).rev t ∈ Path.darts _ P := by
  obtain ⟨q₀, rfl⟩ := DualDart.toDart_surjective t
  -- The vertices whose places have the colour of the source place of `q₀`.
  let R : Set (dualGraph Γ Δ f).V := {v | ∀ p : DualPlace Γ Δ f, p.toVertex = v →
    placeColour a₀ q₀.toDart c p = placeColour a₀ q₀.toDart c q₀.srcPlace}
  have hmem (p : DualPlace Γ Δ f) : p.toVertex ∈ R ↔
      placeColour a₀ q₀.toDart c p = placeColour a₀ q₀.toDart c q₀.srcPlace :=
    ⟨fun h => h p rfl, fun h _ hp => (placeColour_eq_of_toVertex_eq a₀ _ hΔ hc hp).trans h⟩
  -- Leaving the complement of `R`, the path crosses a dart which changes the colour.
  obtain ⟨e, he, hs, ht⟩ := Path.exists_boundary_dart _ P Rᶜ (by
    rw [dualGraph_tgt_toDart, Set.mem_compl_iff, hmem, placeColour_reverse_srcPlace a₀ _ hΔ hc,
      Set.indicator_of_mem (Set.mem_singleton _),
      Set.indicator_of_notMem (Set.notMem_singleton_iff.mpr (rev_ne _ _)), sub_zero]
    simpa using ha₀) (by rw [Set.notMem_compl_iff, dualGraph_src_toDart, hmem])
  suffices e = q₀.toDart ∨ e = (dualGraph Γ Δ f).rev q₀.toDart by
    obtain rfl | rfl := this
    exacts [.inl he, .inr he]
  induction e using dualGraph_dart_cases with | crossing q => ?_
  rw [dualGraph_src_toDart, Set.mem_compl_iff, hmem] at hs
  rw [dualGraph_tgt_toDart, Set.notMem_compl_iff, hmem,
    placeColour_reverse_srcPlace a₀ _ hΔ hc] at ht
  -- Off the track of `q₀`, the colour does not change.
  by_contra! hP
  rw [Set.indicator_of_notMem (Set.notMem_singleton_iff.mpr hP.1.symm),
    Set.indicator_of_notMem (Set.notMem_singleton_iff.mpr hP.2.symm), sub_zero, add_zero] at ht
  exact hs ht

end Cochain

/-- The graph dual to the pattern of a map to a preconnected acyclic graph is acyclic when the flag
complex of `Γ` has trivial first cohomology with coefficients in some nontrivial abelian group `A`
(such as `ℤ/2`, as in Dunwoody, or `ℤ`): every track separates the flag complex, so every
edge of the dual graph separates the dual graph. -/
theorem isAcyclic_dualGraph {A : Type*} [AddCommGroup A] [Nontrivial A] (hΔ : Δ.Preconnected)
    (hΔ' : Δ.IsAcyclic) (hac : Γ.HasTrivialFlagFirstCohomology A) :
    (dualGraph Γ Δ f).IsAcyclic := by
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : A)
  refine (isAcyclic_iff_forall_mem_darts _).mpr fun t P => ?_
  -- The cochain of the track of `t` has a primitive.
  obtain ⟨c, hc⟩ := hac.exists_eq_sub (z := fun a b => trackCount a₀ t a b (f b))
    (fun a b _ => trackCount_swap a₀ t hΔ hΔ' a b)
    fun _ _ _ h₁ h₂ h₃ => trackCount_add a₀ t hΔ hΔ' h₁ h₂ h₃
  exact mem_darts_of_primitive a₀ t hΔ' ha₀ hc P

/-- **The dual graph is a tree** (Dunwoody). If `Δ` is a tree and `Γ` is a connected graph whose
flag complex has trivial first cohomology with coefficients in a nontrivial abelian group `A`, such
as `ℤ/2`, then the graph dual to the pattern of `f` is a tree. -/
theorem isTree_dualGraph {A : Type*} [AddCommGroup A] [Nontrivial A] (hΔ : Δ.IsTree)
    (hΓ : Γ.Connected) (hac : Γ.HasTrivialFlagFirstCohomology A) : (dualGraph Γ Δ f).IsTree := by
  have hΔ' := (Δ.connected_iff.mp hΔ.connected).2
  exact (isTree_iff _).mpr ⟨dualGraph_connected hΔ' hΓ, isAcyclic_dualGraph hΔ' hΔ.isAcyclic hac⟩

end SerreGraph

end TauCeti
