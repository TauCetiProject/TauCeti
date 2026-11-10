/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Finite.Sum
public import Mathlib.Logic.Equiv.Bool
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FinCases

/-!
# Unlabelled closed webs

A closed web is a finite oriented trivalent graph together with vertex-free circles.
An interval edge has distinct source and target *ends*, even if both lie at one vertex.

At a trivalent vertex the merge/split orientation singles out one end. Starting the cyclic
order at that end gives a canonical numbering by `Fin 3`: slot zero is the odd end, and slots
one and two follow it in cyclic order. Thus `ClosedWeb.ends` records precisely incidence,
cyclic order and orientation, without choosing an additional basepoint of the cyclic order.
The direction `false` denotes a source end and `true` a target end. A vertex is a merge when
its odd end is a source, and a split when its odd end is a target.

This file supplies incidence fibres, isomorphisms, orientation reversal, mirror reversal,
and disjoint union. Nilvalent webs have no vertices and consist solely of circles; in
particular the empty web and one circle are distinct.

The finite-record model follows Goertz–Marino–Wedrich, *Monoidal 2-categories from foam
evaluation*, arXiv:2602.11120v1, Definition 3.4, distinguishing edge-end occurrences from
vertex-free circles.
-/

public section

namespace TauCeti

universe u v

/-- A finite oriented trivalent graph with cyclic orders and separate vertex-free circles.
The local numbering begins at the unique end of odd orientation. -/
structure ClosedWeb where
  /-- Trivalent vertices. -/
  Vertex : Type u
  /-- Oriented interval edges, including edges with coincident endpoints. -/
  Edge : Type u
  /-- Vertex-free circle components. -/
  Circle : Type u
  /-- There are finitely many vertices. -/
  [finiteVertex : Finite Vertex]
  /-- There are finitely many interval edges. -/
  [finiteEdge : Finite Edge]
  /-- There are finitely many circle components. -/
  [finiteCircle : Finite Circle]
  /-- The three ends at each vertex, in cyclic order starting at the odd end. -/
  ends : Vertex × Fin 3 ≃ Edge × Bool
  /-- Slot one has orientation opposite to the odd end. -/
  orientation_one : ∀ v, (ends (v, 1)).2 = !(ends (v, 0)).2
  /-- Slot two has orientation opposite to the odd end. -/
  orientation_two : ∀ v, (ends (v, 2)).2 = !(ends (v, 0)).2

namespace ClosedWeb

attribute [instance] finiteVertex finiteEdge finiteCircle

variable (W : ClosedWeb.{u})

/-- Interval edge-end occurrences: source and target are distinguished by the Boolean. -/
abbrev End := W.Edge × Bool

/-- The vertex incident to an edge-end occurrence. -/
def incident (d : W.End) : W.Vertex := (W.ends.symm d).1

/-- The source vertex of an oriented interval edge. -/
def source (e : W.Edge) : W.Vertex := W.incident (e, false)

/-- The target vertex of an oriented interval edge. -/
def target (e : W.Edge) : W.Vertex := W.incident (e, true)

/-- A merge has two incoming ends and one outgoing (odd) end. -/
def IsMerge (v : W.Vertex) : Prop := (W.ends (v, 0)).2 = false

/-- A split has one incoming (odd) end and two outgoing ends. -/
def IsSplit (v : W.Vertex) : Prop := (W.ends (v, 0)).2 = true

@[simp] theorem incident_ends (v : W.Vertex) (i : Fin 3) :
    W.incident (W.ends (v, i)) = v := by simp [incident]

/-- Incidence is recovered from the three local slots. -/
theorem incident_eq_iff (d : W.End) (v : W.Vertex) :
    W.incident d = v ↔ ∃ i, W.ends (v, i) = d := by
  constructor
  · intro h
    exact ⟨(W.ends.symm d).2, by simpa [incident] using h ▸ W.ends.apply_symm_apply d⟩
  · rintro ⟨i, rfl⟩
    simp

/-- Each incidence fibre is exactly the three local end occurrences. -/
def incidenceEquiv (v : W.Vertex) : Fin 3 ≃ {d : W.End // W.incident d = v} where
  toFun i := ⟨W.ends (v, i), W.incident_ends v i⟩
  invFun d := (W.ends.symm d.1).2
  left_inv i := by simp
  right_inv d := by
    apply Subtype.ext
    have h : (v, (W.ends.symm d.1).2) = W.ends.symm d.1 :=
      Prod.ext d.2.symm rfl
    exact (congrArg W.ends h).trans (W.ends.apply_symm_apply d.1)

@[simp] theorem incidenceEquiv_apply_coe (v : W.Vertex) (i : Fin 3) :
    (W.incidenceEquiv v i).1 = W.ends (v, i) := (rfl)

@[simp] theorem incidenceEquiv_symm_apply (v : W.Vertex)
    (d : {d : W.End // W.incident d = v}) :
    (W.incidenceEquiv v).symm d = (W.ends.symm d.1).2 := (rfl)

/-- Trivalence counts ends, not edges, so loops contribute twice. -/
@[simp] theorem card_incident (v : W.Vertex) :
    Nat.card {d : W.End // W.incident d = v} = 3 := by
  rw [← Nat.card_congr (W.incidenceEquiv v)]
  simp

/-- Every vertex has one of the two allowed orientation patterns. -/
theorem isMerge_or_isSplit (v : W.Vertex) : W.IsMerge v ∨ W.IsSplit v := by
  cases h : (W.ends (v, 0)).2 <;> simp [IsMerge, IsSplit, h]

@[simp] theorem not_isMerge_iff (v : W.Vertex) : ¬W.IsMerge v ↔ W.IsSplit v := by
  simp [IsMerge, IsSplit]

@[simp] theorem not_isSplit_iff (v : W.Vertex) : ¬W.IsSplit v ↔ W.IsMerge v := by
  simp [IsMerge, IsSplit]

/-- Only slot zero has the distinguished orientation. -/
@[simp] theorem ends_snd_eq_zero_iff (v : W.Vertex) (i : Fin 3) :
    (W.ends (v, i)).2 = (W.ends (v, 0)).2 ↔ i = 0 := by
  fin_cases i <;> simp [W.orientation_one, W.orientation_two]

/-- Cyclic successor of an end at its incident vertex. -/
def rotation : Equiv.Perm W.End :=
  W.ends.symm.trans ((Equiv.prodCongr (Equiv.refl _) (finRotate 3)).trans W.ends)

/-- Cyclic rotation moves to the next slot, rather than reversing the order. -/
@[simp] theorem rotation_ends (v : W.Vertex) (i : Fin 3) :
    W.rotation (W.ends (v, i)) = W.ends (v, finRotate 3 i) := by
  simp [rotation, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map]

/-- Cyclic rotation preserves incidence. -/
@[simp] theorem incident_rotation (d : W.End) : W.incident (W.rotation d) = W.incident d := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.ends.surjective d
  simp

/-- Three cyclic rotations fix every end. -/
@[simp] theorem rotation_rotation_rotation (d : W.End) :
    W.rotation (W.rotation (W.rotation d)) = d := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.ends.surjective d
  fin_cases i <;> simp [finRotate_apply]

/-- No end is fixed by its cyclic successor. -/
theorem rotation_ne (d : W.End) : W.rotation d ≠ d := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.ends.surjective d
  rw [W.rotation_ends, ne_eq, W.ends.injective.eq_iff, Prod.mk.injEq]
  fin_cases i <;> simp [finRotate_apply]

/-- The interval-end count is three times the number of vertices. -/
theorem three_mul_card_vertex : 3 * Nat.card W.Vertex = 2 * Nat.card W.Edge := by
  have h := Nat.card_congr W.ends
  simpa [Nat.card_prod, Nat.mul_comm] using h

/-- A vertex-free web has no interval edges. -/
theorem isEmpty_edge_of_isEmpty_vertex [IsEmpty W.Vertex] : IsEmpty W.Edge :=
  ⟨fun e ↦ isEmptyElim (W.incident (e, false))⟩

/-- Isomorphisms preserve interval orientation, local cyclic order and circle components. -/
@[ext]
structure Iso (V : ClosedWeb.{v}) where
  /-- Transport of vertices. -/
  vertex : W.Vertex ≃ V.Vertex
  /-- Transport of oriented interval edges. -/
  edge : W.Edge ≃ V.Edge
  /-- Transport of vertex-free circles. -/
  circle : W.Circle ≃ V.Circle
  /-- Transport preserves all three local slots. -/
  map_ends : ∀ x, V.ends (vertex x.1, x.2) = (edge (W.ends x).1, (W.ends x).2)

namespace Iso

variable {W : ClosedWeb.{u}} {V : ClosedWeb.{v}}

/-- Identity web isomorphism. -/
def refl (W : ClosedWeb.{u}) : W.Iso W where
  vertex := Equiv.refl _
  edge := Equiv.refl _
  circle := Equiv.refl _
  map_ends _ := rfl

@[simp] theorem refl_vertex (W : ClosedWeb.{u}) : (refl W).vertex = Equiv.refl _ := (rfl)
@[simp] theorem refl_edge (W : ClosedWeb.{u}) : (refl W).edge = Equiv.refl _ := (rfl)
@[simp] theorem refl_circle (W : ClosedWeb.{u}) : (refl W).circle = Equiv.refl _ := (rfl)

/-- Inverse web isomorphism. -/
def symm (f : W.Iso V) : V.Iso W where
  vertex := f.vertex.symm
  edge := f.edge.symm
  circle := f.circle.symm
  map_ends x := by
    have h := f.map_ends (f.vertex.symm x.1, x.2)
    simpa [Prod.map] using
      congrArg (Equiv.prodCongr f.edge.symm (Equiv.refl Bool)) h.symm

@[simp] theorem symm_vertex (f : W.Iso V) : f.symm.vertex = f.vertex.symm := (rfl)
@[simp] theorem symm_edge (f : W.Iso V) : f.symm.edge = f.edge.symm := (rfl)
@[simp] theorem symm_circle (f : W.Iso V) : f.symm.circle = f.circle.symm := (rfl)

/-- Composition of web isomorphisms. -/
def trans {U : ClosedWeb} (f : W.Iso V) (g : V.Iso U) : W.Iso U where
  vertex := f.vertex.trans g.vertex
  edge := f.edge.trans g.edge
  circle := f.circle.trans g.circle
  map_ends x := by
    dsimp only [Equiv.trans_apply]
    rw [g.map_ends (f.vertex x.1, x.2), f.map_ends x]

@[simp] theorem trans_vertex {U : ClosedWeb} (f : W.Iso V) (g : V.Iso U) :
    (f.trans g).vertex = f.vertex.trans g.vertex := (rfl)
@[simp] theorem trans_edge {U : ClosedWeb} (f : W.Iso V) (g : V.Iso U) :
    (f.trans g).edge = f.edge.trans g.edge := (rfl)
@[simp] theorem trans_circle {U : ClosedWeb} (f : W.Iso V) (g : V.Iso U) :
    (f.trans g).circle = f.circle.trans g.circle := (rfl)

/-- Incidence commutes with a web isomorphism. -/
@[simp] theorem map_incident (f : W.Iso V) (d : W.End) :
    V.incident (f.edge d.1, d.2) = f.vertex (W.incident d) := by
  obtain ⟨x, rfl⟩ := W.ends.surjective d
  rw [← f.map_ends]
  simp [incident]

/-- Source vertices commute with a web isomorphism. -/
@[simp] theorem map_source (f : W.Iso V) (e : W.Edge) :
    V.source (f.edge e) = f.vertex (W.source e) := f.map_incident (e, false)

/-- Target vertices commute with a web isomorphism. -/
@[simp] theorem map_target (f : W.Iso V) (e : W.Edge) :
    V.target (f.edge e) = f.vertex (W.target e) := f.map_incident (e, true)

/-- Isomorphisms preserve the merge/split role. -/
@[simp] theorem isMerge_map (f : W.Iso V) (v : W.Vertex) :
    V.IsMerge (f.vertex v) ↔ W.IsMerge v := by
  simp only [IsMerge, f.map_ends (v, 0)]

@[simp] theorem isSplit_map (f : W.Iso V) (v : W.Vertex) :
    V.IsSplit (f.vertex v) ↔ W.IsSplit v := by
  simp only [IsSplit, f.map_ends (v, 0)]

/-- Isomorphisms preserve cyclic successor. -/
@[simp] theorem map_rotation (f : W.Iso V) (d : W.End) :
    V.rotation (f.edge d.1, d.2) = (f.edge (W.rotation d).1, (W.rotation d).2) := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.ends.surjective d
  rw [← f.map_ends (v, i), V.rotation_ends, W.rotation_ends]
  exact f.map_ends (v, finRotate 3 i)

@[simp] theorem refl_trans (f : W.Iso V) : (refl W).trans f = f := by
  cases f
  rfl

@[simp] theorem trans_refl (f : W.Iso V) : f.trans (refl V) = f := by
  cases f
  rfl

@[simp] theorem symm_trans (f : W.Iso V) : f.symm.trans f = refl V := by
  ext <;> simp [symm, trans, refl]

@[simp] theorem trans_symm (f : W.Iso V) : f.trans f.symm = refl W := by
  ext <;> simp [symm, trans, refl]

/-- Composition of web isomorphisms is associative. -/
theorem trans_assoc {U T : ClosedWeb} (f : W.Iso V) (g : V.Iso U) (h : U.Iso T) :
    (f.trans g).trans h = f.trans (g.trans h) := (rfl)

end Iso

/-! The record constructors below are reducible so their finite vertex, edge and circle
carriers compute. This lets incidence maps be used without equality transports of types. -/

/-- Transport all finite incidence data along bijections of vertices, edges and circles. -/
abbrev relabel {V E C : Type v} [Finite V] [Finite E] [Finite C]
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (_c : W.Circle ≃ C) : ClosedWeb.{v} where
  Vertex := V
  Edge := E
  Circle := C
  ends := (Equiv.prodCongr v.symm (Equiv.refl _)).trans
    (W.ends.trans (Equiv.prodCongr e (Equiv.refl _)))
  orientation_one x := W.orientation_one (v.symm x)
  orientation_two x := W.orientation_two (v.symm x)

/-- The canonical isomorphism to a relabelled web. -/
def relabelIso {V E C : Type v} [Finite V] [Finite E] [Finite C]
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) :
    W.Iso (W.relabel v e c) where
  vertex := v
  edge := e
  circle := c
  map_ends x := by
    rcases x with ⟨x, i⟩
    dsimp [relabel]
    simp [Prod.map]

@[simp] theorem relabelIso_vertex {V E C : Type v} [Finite V] [Finite E] [Finite C]
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) :
    (W.relabelIso v e c).vertex = v := (rfl)

@[simp] theorem relabelIso_edge {V E C : Type v} [Finite V] [Finite E] [Finite C]
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) :
    (W.relabelIso v e c).edge = e := (rfl)

@[simp] theorem relabelIso_circle {V E C : Type v} [Finite V] [Finite E] [Finite C]
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) :
    (W.relabelIso v e c).circle = c := (rfl)

/-- Reverse every interval orientation, leaving cyclic orders and circles unchanged. -/
abbrev reverse : ClosedWeb.{u} where
  Vertex := W.Vertex
  Edge := W.Edge
  Circle := W.Circle
  ends := W.ends.trans (Equiv.prodCongr (Equiv.refl _) Equiv.boolNot)
  orientation_one x := by simpa using congrArg Bool.not (W.orientation_one x)
  orientation_two x := by simpa using congrArg Bool.not (W.orientation_two x)

theorem reverse_ends (x : W.Vertex × Fin 3) :
    W.reverse.ends x = ((W.ends x).1, !(W.ends x).2) := rfl

/-- Orientation reversal interchanges source and target incidence. -/
@[simp] theorem reverse_incident (d : W.End) :
    W.reverse.incident d = W.incident (d.1, !d.2) := (rfl)

@[simp] theorem reverse_source (e : W.Edge) : W.reverse.source e = W.target e := (rfl)

@[simp] theorem reverse_target (e : W.Edge) : W.reverse.target e = W.source e := (rfl)

@[simp] theorem reverse_isMerge (v : W.Vertex) : W.reverse.IsMerge v ↔ W.IsSplit v := by
  simp [IsMerge, IsSplit, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map]

@[simp] theorem reverse_isSplit (v : W.Vertex) : W.reverse.IsSplit v ↔ W.IsMerge v := by
  simp [IsMerge, IsSplit, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map]

/-- Orientation reversal is an involution. -/
@[simp] theorem reverse_reverse : W.reverse.reverse = W := by
  cases W
  simp only [reverse]
  congr 1
  apply Equiv.ext
  intro x
  simp [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map]

/-- Reverse cyclic orders, keeping the odd end fixed and interchanging the other two. -/
abbrev mirror : ClosedWeb.{u} where
  Vertex := W.Vertex
  Edge := W.Edge
  Circle := W.Circle
  ends := (Equiv.prodCongr (Equiv.refl _) (Equiv.swap (1 : Fin 3) 2)).trans W.ends
  orientation_one x := by simpa [Equiv.swap_apply_def] using W.orientation_two x
  orientation_two x := by simpa [Equiv.swap_apply_def] using W.orientation_one x

theorem mirror_ends (v : W.Vertex) (i : Fin 3) :
    W.mirror.ends (v, i) = W.ends (v, Equiv.swap (1 : Fin 3) 2 i) := rfl

/-- Mirror reversal does not change incidence. -/
@[simp] theorem mirror_incident (d : W.End) : W.mirror.incident d = W.incident d := (rfl)

@[simp] theorem mirror_isMerge (v : W.Vertex) : W.mirror.IsMerge v ↔ W.IsMerge v := by
  simp [IsMerge, Equiv.swap_apply_def]

@[simp] theorem mirror_isSplit (v : W.Vertex) : W.mirror.IsSplit v ↔ W.IsSplit v := by
  simp [IsSplit, Equiv.swap_apply_def]

/-- Mirror reversal is an involution, not a cyclic rotation of the three ends. -/
@[simp] theorem mirror_mirror : W.mirror.mirror = W := by
  cases W
  simp only [mirror]
  congr 1
  apply Equiv.ext
  rintro ⟨x, i⟩
  simp [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map]

/-- Mirroring changes cyclic successor to cyclic predecessor. -/
theorem mirror_rotation (d : W.End) : W.mirror.rotation d = W.rotation.symm d := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.ends.surjective d
  apply W.rotation.injective
  simp only [Equiv.apply_symm_apply]
  fin_cases i <;>
    simp [rotation, mirror, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
      Equiv.swap_apply_def, finRotate_apply]

/-- Orientation reversal and mirror reversal commute. -/
theorem reverse_mirror : W.reverse.mirror = W.mirror.reverse := rfl

/-- The web consisting of a specified finite set of vertex-free circles. -/
abbrev circles (C : Type u) [Finite C] : ClosedWeb.{u} where
  Vertex := PEmpty
  Edge := PEmpty
  Circle := C
  ends := Equiv.equivOfIsEmpty _ _
  orientation_one x := isEmptyElim x
  orientation_two x := isEmptyElim x

/-- The empty closed web. -/
abbrev empty : ClosedWeb.{u} := circles PEmpty

/-- One vertex-free circle, not the empty web. -/
abbrev circle : ClosedWeb.{u} := circles PUnit

/-- The one-circle web and the empty web are not isomorphic. -/
theorem not_nonempty_iso_circle_empty : ¬Nonempty (circle.{u}.Iso empty.{u}) := by
  rintro ⟨f⟩
  exact PEmpty.elim (f.circle PUnit.unit)

/-- Every vertex-free web is isomorphic to the web of its circles. -/
def circlesIso [IsEmpty W.Vertex] : W.Iso (circles W.Circle) := by
  letI := W.isEmpty_edge_of_isEmpty_vertex
  exact
    { vertex := Equiv.equivOfIsEmpty _ _
      edge := Equiv.equivOfIsEmpty _ _
      circle := Equiv.refl _
      map_ends x := isEmptyElim x.1 }

/-- Disjoint union, retaining each component's cyclic orders and orientations. -/
abbrev sum (V : ClosedWeb.{v}) : ClosedWeb.{max u v} where
  Vertex := W.Vertex ⊕ V.Vertex
  Edge := W.Edge ⊕ V.Edge
  Circle := W.Circle ⊕ V.Circle
  ends := (Equiv.sumProdDistrib _ _ _).trans
    ((Equiv.sumCongr W.ends V.ends).trans (Equiv.sumProdDistrib _ _ _).symm)
  orientation_one x := by
    cases x <;> simp [W.orientation_one, V.orientation_one]
  orientation_two x := by
    cases x <;> simp [W.orientation_two, V.orientation_two]

theorem sum_ends_inl (V : ClosedWeb.{v}) (v : W.Vertex) (i : Fin 3) :
    (W.sum V).ends (Sum.inl v, i) = (Sum.inl (W.ends (v, i)).1, (W.ends (v, i)).2) := rfl

theorem sum_ends_inr (V : ClosedWeb.{v}) (v : V.Vertex) (i : Fin 3) :
    (W.sum V).ends (Sum.inr v, i) = (Sum.inr (V.ends (v, i)).1, (V.ends (v, i)).2) := rfl

/-- Incidence on the left component of a disjoint union. -/
theorem sum_incident_inl (V : ClosedWeb.{v}) (e : W.Edge) (b : Bool) :
    (W.sum V).incident (Sum.inl e, b) = Sum.inl (W.incident (e, b)) := (rfl)

/-- Incidence on the right component of a disjoint union. -/
theorem sum_incident_inr (V : ClosedWeb.{v}) (e : V.Edge) (b : Bool) :
    (W.sum V).incident (Sum.inr e, b) = Sum.inr (V.incident (e, b)) := (rfl)

/-- The disjoint-union left unit isomorphism. -/
def sumEmptyLeft : (empty.{u}.sum W).Iso W where
  vertex := Equiv.emptySum _ _
  edge := Equiv.emptySum _ _
  circle := Equiv.emptySum _ _
  map_ends x := by
    rcases x with ⟨v | v, i⟩
    · exact v.elim
    · rfl

@[simp] theorem sumEmptyLeft_vertex : W.sumEmptyLeft.vertex = Equiv.emptySum _ _ := (rfl)
@[simp] theorem sumEmptyLeft_edge : W.sumEmptyLeft.edge = Equiv.emptySum _ _ := (rfl)
@[simp] theorem sumEmptyLeft_circle : W.sumEmptyLeft.circle = Equiv.emptySum _ _ := (rfl)

/-- The disjoint-union right unit isomorphism. -/
def sumEmptyRight : (W.sum empty.{u}).Iso W where
  vertex := Equiv.sumEmpty _ _
  edge := Equiv.sumEmpty _ _
  circle := Equiv.sumEmpty _ _
  map_ends x := by
    rcases x with ⟨v | v, i⟩
    · rfl
    · exact v.elim

@[simp] theorem sumEmptyRight_vertex : W.sumEmptyRight.vertex = Equiv.sumEmpty _ _ := (rfl)
@[simp] theorem sumEmptyRight_edge : W.sumEmptyRight.edge = Equiv.sumEmpty _ _ := (rfl)
@[simp] theorem sumEmptyRight_circle : W.sumEmptyRight.circle = Equiv.sumEmpty _ _ := (rfl)

/-- The disjoint-union associativity isomorphism. -/
def sumAssoc (V : ClosedWeb.{v}) (U : ClosedWeb) :
    ((W.sum V).sum U).Iso (W.sum (V.sum U)) where
  vertex := Equiv.sumAssoc _ _ _
  edge := Equiv.sumAssoc _ _ _
  circle := Equiv.sumAssoc _ _ _
  map_ends x := by rcases x with ⟨(v | v) | v, i⟩ <;> rfl

@[simp] theorem sumAssoc_vertex (V : ClosedWeb.{v}) (U : ClosedWeb) :
    (W.sumAssoc V U).vertex = Equiv.sumAssoc _ _ _ := (rfl)
@[simp] theorem sumAssoc_edge (V : ClosedWeb.{v}) (U : ClosedWeb) :
    (W.sumAssoc V U).edge = Equiv.sumAssoc _ _ _ := (rfl)
@[simp] theorem sumAssoc_circle (V : ClosedWeb.{v}) (U : ClosedWeb) :
    (W.sumAssoc V U).circle = Equiv.sumAssoc _ _ _ := (rfl)

/-- Exchange the two disjoint components without reversing any local order. -/
def sumComm (V : ClosedWeb.{v}) : (W.sum V).Iso (V.sum W) where
  vertex := Equiv.sumComm _ _
  edge := Equiv.sumComm _ _
  circle := Equiv.sumComm _ _
  map_ends x := by rcases x with ⟨v | v, i⟩ <;> rfl

@[simp] theorem sumComm_vertex (V : ClosedWeb.{v}) :
    (W.sumComm V).vertex = Equiv.sumComm _ _ := (rfl)
@[simp] theorem sumComm_edge (V : ClosedWeb.{v}) :
    (W.sumComm V).edge = Equiv.sumComm _ _ := (rfl)
@[simp] theorem sumComm_circle (V : ClosedWeb.{v}) :
    (W.sumComm V).circle = Equiv.sumComm _ _ := (rfl)

namespace Iso

variable {W : ClosedWeb.{u}} {V : ClosedWeb.{v}}

/-- Reverse both webs in an isomorphism. -/
def reverse (f : W.Iso V) : W.reverse.Iso V.reverse where
  vertex := f.vertex
  edge := f.edge
  circle := f.circle
  map_ends x := by
    rw [ClosedWeb.reverse_ends, f.map_ends]
    rfl

@[simp] theorem reverse_vertex (f : W.Iso V) : f.reverse.vertex = f.vertex := (rfl)
@[simp] theorem reverse_edge (f : W.Iso V) : f.reverse.edge = f.edge := (rfl)
@[simp] theorem reverse_circle (f : W.Iso V) : f.reverse.circle = f.circle := (rfl)

/-- Mirror both webs in an isomorphism. -/
def mirror (f : W.Iso V) : W.mirror.Iso V.mirror where
  vertex := f.vertex
  edge := f.edge
  circle := f.circle
  map_ends x := by
    rcases x with ⟨v, i⟩
    exact f.map_ends (v, Equiv.swap (1 : Fin 3) 2 i)

@[simp] theorem mirror_vertex (f : W.Iso V) : f.mirror.vertex = f.vertex := (rfl)
@[simp] theorem mirror_edge (f : W.Iso V) : f.mirror.edge = f.edge := (rfl)
@[simp] theorem mirror_circle (f : W.Iso V) : f.mirror.circle = f.circle := (rfl)

/-- Disjoint union transports isomorphisms on both components. -/
def sum {W' V' : ClosedWeb} (f : W.Iso V) (g : W'.Iso V') :
    (W.sum W').Iso (V.sum V') where
  vertex := Equiv.sumCongr f.vertex g.vertex
  edge := Equiv.sumCongr f.edge g.edge
  circle := Equiv.sumCongr f.circle g.circle
  map_ends x := by
    rcases x with ⟨v | v, i⟩
    · exact congrArg (fun d ↦ ((Sum.inl d.1 : V.Edge ⊕ V'.Edge), d.2))
        (f.map_ends (v, i))
    · exact congrArg (fun d ↦ ((Sum.inr d.1 : V.Edge ⊕ V'.Edge), d.2))
        (g.map_ends (v, i))

@[simp] theorem sum_vertex {W' V' : ClosedWeb} (f : W.Iso V) (g : W'.Iso V') :
    (f.sum g).vertex = Equiv.sumCongr f.vertex g.vertex := (rfl)
@[simp] theorem sum_edge {W' V' : ClosedWeb} (f : W.Iso V) (g : W'.Iso V') :
    (f.sum g).edge = Equiv.sumCongr f.edge g.edge := (rfl)
@[simp] theorem sum_circle {W' V' : ClosedWeb} (f : W.Iso V) (g : W'.Iso V') :
    (f.sum g).circle = Equiv.sumCongr f.circle g.circle := (rfl)

end Iso

/-- The oriented theta web, with one merge and one split and no vertex-free circles.
Edge zero runs from the merge to the split; the other two edges run back. -/
abbrev theta : ClosedWeb where
  Vertex := Bool
  Edge := Fin 3
  Circle := PEmpty
  ends := (Equiv.prodComm _ _).trans
    (Equiv.prodCongrRight fun i : Fin 3 ↦ if i = 0 then Equiv.refl Bool else Equiv.boolNot)
  orientation_one _ := rfl
  orientation_two _ := rfl

@[simp] theorem theta_isMerge (v : Bool) : theta.IsMerge v ↔ v = false := Iff.rfl

@[simp] theorem theta_isSplit (v : Bool) : theta.IsSplit v ↔ v = true := Iff.rfl

end ClosedWeb
end TauCeti
