/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Between
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

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
strictly inside an edge of `Γ` lying in no triangle lies in a band. When `Δ` is a tree and the
flag complex of `Γ` is connected and has trivial first cohomology with coefficients in `ℤ/2`,
every track separates the complex and Dunwoody shows that the dual graph is a tree.

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

end SerreGraph

end TauCeti
