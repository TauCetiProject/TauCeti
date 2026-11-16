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
For the compatible surface rotation, use the stored cyclic order at split vertices and
its inverse at merge vertices. Planarity of this rotation system is a separate condition,
not imposed by this record; higher-genus structures are allowed.

This file supplies incidence fibres, isomorphisms, orientation reversal, mirror reversal,
and disjoint union. Nilvalent webs have no vertices and consist solely of circles; in
particular the empty web and one circle are distinct.

The finite-record model adapts the incidence data of Goertz–Marino–Wedrich, *Monoidal
2-categories from foam evaluation*, arXiv:2602.11120v1, Definition 3.4, distinguishing
edge-end occurrences from vertex-free circles and leaving planarity as a separate condition.
-/

public section

namespace TauCeti

universe u v

/-- A finite oriented trivalent graph with cyclic orders and separate vertex-free circles.
The local numbering begins at the unique end of odd orientation. The compatible surface
rotation uses the stored cyclic order at splits and its inverse at merges. Planarity of
that rotation system is a separate condition, not part of this record. -/
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
attribute [simp] orientation_one orientation_two

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

theorem incident_def (d : W.End) : W.incident d = (W.ends.symm d).1 := (rfl)

theorem source_def (e : W.Edge) : W.source e = W.incident (e, false) := (rfl)

theorem target_def (e : W.Edge) : W.target e = W.incident (e, true) := (rfl)

theorem isMerge_def (v : W.Vertex) : W.IsMerge v ↔ (W.ends (v, 0)).2 = false := Iff.rfl

theorem isSplit_def (v : W.Vertex) : W.IsSplit v ↔ (W.ends (v, 0)).2 = true := Iff.rfl

instance : DecidablePred W.IsMerge := fun v ↦
  inferInstanceAs (Decidable ((W.ends (v, 0)).2 = false))

instance : DecidablePred W.IsSplit := fun v ↦
  inferInstanceAs (Decidable ((W.ends (v, 0)).2 = true))

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
@[simp] theorem ends_snd_eq_ends_zero_snd_iff (v : W.Vertex) (i : Fin 3) :
    (W.ends (v, i)).2 = (W.ends (v, 0)).2 ↔ i = 0 := by
  fin_cases i <;> simp [W.orientation_one, W.orientation_two]

/-- Stored cyclic successor of an end at its incident vertex, before the merge inversion
used for compatible surface rotation. -/
def cyclicSucc : Equiv.Perm W.End :=
  W.ends.symm.trans ((Equiv.prodCongr (Equiv.refl _) (finRotate 3)).trans W.ends)

theorem cyclicSucc_def : W.cyclicSucc =
    W.ends.symm.trans ((Equiv.prodCongr (Equiv.refl _) (finRotate 3)).trans W.ends) := (rfl)

/-- Cyclic successor moves to the next slot, rather than reversing the order. -/
@[simp] theorem cyclicSucc_ends (v : W.Vertex) (i : Fin 3) :
    W.cyclicSucc (W.ends (v, i)) = W.ends (v, finRotate 3 i) := by
  simp [cyclicSucc, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map]

/-- Cyclic successor preserves incidence. -/
@[simp] theorem incident_cyclicSucc (d : W.End) : W.incident (W.cyclicSucc d) = W.incident d := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.ends.surjective d
  simp

@[simp] theorem cyclicSucc_symm_ends (v : W.Vertex) (i : Fin 3) :
    W.cyclicSucc.symm (W.ends (v, i)) = W.ends (v, (finRotate 3).symm i) := by
  apply W.cyclicSucc.injective
  simp

@[simp] theorem incident_cyclicSucc_symm (d : W.End) :
    W.incident (W.cyclicSucc.symm d) = W.incident d := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.ends.surjective d
  simp

/-- Three cyclic successors fix every end. -/
@[simp] theorem cyclicSucc_cyclicSucc_cyclicSucc (d : W.End) :
    W.cyclicSucc (W.cyclicSucc (W.cyclicSucc d)) = d := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.ends.surjective d
  fin_cases i <;> simp [finRotate_apply]

/-- No end is fixed by its cyclic successor. -/
theorem cyclicSucc_ne_self (d : W.End) : W.cyclicSucc d ≠ d := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.ends.surjective d
  rw [W.cyclicSucc_ends, ne_eq, W.ends.injective.eq_iff, Prod.mk.injEq]
  fin_cases i <;> simp [finRotate_apply]

/-- Cyclic predecessor is the square of cyclic successor. -/
theorem cyclicSucc_symm_apply (d : W.End) :
    W.cyclicSucc.symm d = W.cyclicSucc (W.cyclicSucc d) := by
  apply W.cyclicSucc.injective
  simp

/-- Three cyclic predecessors fix every end. -/
@[simp] theorem cyclicSucc_symm_cyclicSucc_symm_cyclicSucc_symm (d : W.End) :
    W.cyclicSucc.symm (W.cyclicSucc.symm (W.cyclicSucc.symm d)) = d := by
  simp only [cyclicSucc_symm_apply, cyclicSucc_cyclicSucc_cyclicSucc]

/-- No end is fixed by its cyclic predecessor. -/
theorem cyclicSucc_symm_ne_self (d : W.End) : W.cyclicSucc.symm d ≠ d := by
  intro h
  exact W.cyclicSucc_ne_self d (by simpa using (congrArg W.cyclicSucc h).symm)

/-- The interval-end count is three times the number of vertices. -/
theorem three_mul_card_vertex_eq_two_mul_card_edge :
    3 * Nat.card W.Vertex = 2 * Nat.card W.Edge := by
  have h := Nat.card_congr W.ends
  simpa [Nat.card_prod, Nat.mul_comm] using h

/-- A vertex-free web has no interval edges. -/
instance isEmpty_edge_of_isEmpty_vertex [IsEmpty W.Vertex] : IsEmpty W.Edge :=
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

@[simp] theorem symm_symm (f : W.Iso V) : f.symm.symm = f := by
  ext <;> rfl

@[simp] theorem refl_symm : (refl W).symm = refl W := by
  ext <;> rfl

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

/-- Inversion reverses the order of composition. -/
@[simp] theorem symm_trans {U : ClosedWeb} (f : W.Iso V) (g : V.Iso U) :
    (f.trans g).symm = g.symm.trans f.symm := by
  ext <;> rfl

/-- Isomorphisms transport each local end slot. -/
@[simp] theorem map_ends_apply (f : W.Iso V) (v : W.Vertex) (i : Fin 3) :
    V.ends (f.vertex v, i) = (f.edge (W.ends (v, i)).1, (W.ends (v, i)).2) :=
  f.map_ends (v, i)

/-- Isomorphisms transport the inverse local-slot assignment. -/
@[simp] theorem map_ends_symm (f : W.Iso V) (e : W.Edge) (b : Bool) :
    V.ends.symm (f.edge e, b) =
      (f.vertex (W.ends.symm (e, b)).1, (W.ends.symm (e, b)).2) := by
  apply V.ends.injective
  simp

/-- Incidence commutes with a web isomorphism. -/
@[simp] theorem map_incident (f : W.Iso V) (e : W.Edge) (b : Bool) :
    V.incident (f.edge e, b) = f.vertex (W.incident (e, b)) := by
  obtain ⟨⟨v, i⟩, h⟩ := W.ends.surjective (e, b)
  have hw := W.incident_ends v i
  rw [h] at hw
  have hv := V.incident_ends (f.vertex v) i
  rw [f.map_ends (v, i), h] at hv
  rw [hw]
  exact hv

/-- Source vertices commute with a web isomorphism. -/
@[simp] theorem map_source (f : W.Iso V) (e : W.Edge) :
    V.source (f.edge e) = f.vertex (W.source e) := f.map_incident e false

/-- Target vertices commute with a web isomorphism. -/
@[simp] theorem map_target (f : W.Iso V) (e : W.Edge) :
    V.target (f.edge e) = f.vertex (W.target e) := f.map_incident e true

/-- Isomorphisms preserve the merge/split role. -/
@[simp] theorem isMerge_vertex (f : W.Iso V) (v : W.Vertex) :
    V.IsMerge (f.vertex v) ↔ W.IsMerge v := by
  simp only [IsMerge, f.map_ends (v, 0)]

@[simp] theorem isSplit_vertex (f : W.Iso V) (v : W.Vertex) :
    V.IsSplit (f.vertex v) ↔ W.IsSplit v := by
  simp only [IsSplit, f.map_ends (v, 0)]

/-- Isomorphisms preserve cyclic successor. -/
@[simp] theorem map_cyclicSucc (f : W.Iso V) (e : W.Edge) (b : Bool) :
    V.cyclicSucc (f.edge e, b) = (f.edge (W.cyclicSucc (e, b)).1, (W.cyclicSucc (e, b)).2) := by
  obtain ⟨⟨v, i⟩, h⟩ := W.ends.surjective (e, b)
  have hr := V.cyclicSucc_ends (f.vertex v) i
  rw [f.map_ends (v, i), f.map_ends (v, finRotate 3 i), ← W.cyclicSucc_ends, h] at hr
  exact hr

/-- Isomorphisms preserve cyclic predecessor. -/
@[simp] theorem map_cyclicSucc_symm (f : W.Iso V) (e : W.Edge) (b : Bool) :
    V.cyclicSucc.symm (f.edge e, b) =
      (f.edge (W.cyclicSucc.symm (e, b)).1, (W.cyclicSucc.symm (e, b)).2) := by
  obtain ⟨⟨v, i⟩, h⟩ := W.ends.surjective (e, b)
  have hr := V.cyclicSucc_symm_ends (f.vertex v) i
  rw [f.map_ends (v, i), f.map_ends (v, (finRotate 3).symm i),
    ← W.cyclicSucc_symm_ends, h] at hr
  exact hr

@[simp] theorem refl_trans (f : W.Iso V) : (refl W).trans f = f := by
  cases f
  rfl

@[simp] theorem trans_refl (f : W.Iso V) : f.trans (refl V) = f := by
  cases f
  rfl

@[simp] theorem symm_trans_self (f : W.Iso V) : f.symm.trans f = refl V := by
  ext <;> simp [symm, trans, refl]

@[simp] theorem self_trans_symm (f : W.Iso V) : f.trans f.symm = refl W := by
  ext <;> simp [symm, trans, refl]

/-- Composition of web isomorphisms is associative. -/
theorem trans_assoc {U T : ClosedWeb} (f : W.Iso V) (g : V.Iso U) (h : U.Iso T) :
    (f.trans g).trans h = f.trans (g.trans h) := (rfl)

end Iso

/-! The record constructors below are reducible so their finite vertex, edge and circle
carriers compute. This lets incidence maps be used without equality transports of types.
Their characteristic ends equations are explicit rewrite lemmas, not simp lemmas: generic
`Equiv` simp rules already reduce their left-hand sides, so `simpNF` rejects those annotations. -/

/-- Transport all finite incidence data along bijections of vertices, edges and circles. -/
abbrev relabel {V E C : Type v}
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) : ClosedWeb.{v} where
  Vertex := V
  Edge := E
  Circle := C
  finiteVertex := .of_equiv _ v
  finiteEdge := .of_equiv _ e
  finiteCircle := .of_equiv _ c
  ends := (Equiv.prodCongr v.symm (Equiv.refl _)).trans
    (W.ends.trans (Equiv.prodCongr e (Equiv.refl _)))
  orientation_one x := W.orientation_one (v.symm x)
  orientation_two x := W.orientation_two (v.symm x)

/-- The canonical isomorphism to a relabelled web. -/
def relabelIso {V E C : Type v}
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) :
    W.Iso (W.relabel v e c) where
  vertex := v
  edge := e
  circle := c
  map_ends x := by
    rcases x with ⟨x, i⟩
    dsimp [relabel]
    simp [Prod.map]

@[simp] theorem relabelIso_vertex {V E C : Type v}
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) :
    (W.relabelIso v e c).vertex = v := (rfl)

@[simp] theorem relabelIso_edge {V E C : Type v}
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) :
    (W.relabelIso v e c).edge = e := (rfl)

@[simp] theorem relabelIso_circle {V E C : Type v}
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) :
    (W.relabelIso v e c).circle = c := (rfl)

theorem relabel_ends_apply {V E C : Type v}
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) (x : V × Fin 3) :
    (W.relabel v e c).ends x =
      (e (W.ends (v.symm x.1, x.2)).1, (W.ends (v.symm x.1, x.2)).2) := (rfl)

@[simp] theorem incident_relabel {V E C : Type v}
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) (d : E × Bool) :
    (W.relabel v e c).incident d = v (W.incident (e.symm d.1, d.2)) := by
  simpa using (W.relabelIso v e c).map_incident (e.symm d.1) d.2

@[simp] theorem source_relabel {V E C : Type v}
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) (a : E) :
    (W.relabel v e c).source a = v (W.source (e.symm a)) := by
  rw [source_def, incident_relabel, source_def]

@[simp] theorem target_relabel {V E C : Type v}
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) (a : E) :
    (W.relabel v e c).target a = v (W.target (e.symm a)) := by
  rw [target_def, incident_relabel, target_def]

@[simp] theorem isMerge_relabel {V E C : Type v}
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) (a : V) :
    (W.relabel v e c).IsMerge a ↔ W.IsMerge (v.symm a) := by
  simpa using (W.relabelIso v e c).isMerge_vertex (v.symm a)

@[simp] theorem isSplit_relabel {V E C : Type v}
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) (a : V) :
    (W.relabel v e c).IsSplit a ↔ W.IsSplit (v.symm a) := by
  simpa using (W.relabelIso v e c).isSplit_vertex (v.symm a)

@[simp] theorem cyclicSucc_relabel_apply {V E C : Type v}
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) (d : E × Bool) :
    (W.relabel v e c).cyclicSucc d =
      (e (W.cyclicSucc (e.symm d.1, d.2)).1, (W.cyclicSucc (e.symm d.1, d.2)).2) := by
  simpa using (W.relabelIso v e c).map_cyclicSucc (e.symm d.1) d.2

-- Inverse-constructor simp lemmas use no_index on carrier types so their keys also match
-- terms produced by cyclicSucc_mirror, regardless of reduced constructor projections.
@[simp] theorem cyclicSucc_symm_relabel_apply {V E C : Type v}
    (v : W.Vertex ≃ V) (e : W.Edge ≃ E) (c : W.Circle ≃ C) (d : E × Bool) :
    (W.relabel v e c).cyclicSucc.symm
        (α := no_index (E × Bool)) (β := no_index (E × Bool)) d =
      (e (W.cyclicSucc.symm (e.symm d.1, d.2)).1,
        (W.cyclicSucc.symm (e.symm d.1, d.2)).2) := by
  simpa using (W.relabelIso v e c).map_cyclicSucc_symm (e.symm d.1) d.2

/-- Reverse every interval orientation, leaving cyclic orders and circles unchanged. -/
abbrev reverse : ClosedWeb.{u} where
  Vertex := W.Vertex
  Edge := W.Edge
  Circle := W.Circle
  ends := W.ends.trans (Equiv.prodCongr (Equiv.refl _) Equiv.boolNot)
  orientation_one x := by simp
  orientation_two x := by simp

theorem reverse_ends_apply (x : W.Vertex × Fin 3) :
    W.reverse.ends x = ((W.ends x).1, !(W.ends x).2) := (rfl)

/-- Orientation reversal interchanges source and target incidence. -/
@[simp] theorem incident_reverse (d : W.End) :
    W.reverse.incident d = W.incident (d.1, !d.2) := by
  obtain ⟨x, rfl⟩ := W.reverse.ends.surjective d
  rw [W.reverse.incident_ends, reverse_ends_apply]
  simp [incident]

@[simp] theorem source_reverse (e : W.Edge) : W.reverse.source e = W.target e := by
  simp [source, target]

@[simp] theorem target_reverse (e : W.Edge) : W.reverse.target e = W.source e := by
  simp [source, target]

@[simp] theorem isMerge_reverse (v : W.Vertex) : W.reverse.IsMerge v ↔ W.IsSplit v := by
  rw [IsMerge, reverse_ends_apply]
  simp [IsSplit]

@[simp] theorem isSplit_reverse (v : W.Vertex) : W.reverse.IsSplit v ↔ W.IsMerge v := by
  rw [IsSplit, reverse_ends_apply]
  simp [IsMerge]

/-- Reversing orientations conjugates cyclic successor by exchange of the two edge ends. -/
@[simp] theorem cyclicSucc_reverse_apply (d : W.End) :
    W.reverse.cyclicSucc d =
      ((W.cyclicSucc (d.1, !d.2)).1, !(W.cyclicSucc (d.1, !d.2)).2) := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.reverse.ends.surjective d
  rw [W.reverse.cyclicSucc_ends, reverse_ends_apply, reverse_ends_apply]
  simp

@[simp] theorem cyclicSucc_symm_reverse_apply (d : W.End) :
    W.reverse.cyclicSucc.symm (α := no_index W.End) (β := no_index W.End) d =
      ((W.cyclicSucc.symm (d.1, !d.2)).1, !(W.cyclicSucc.symm (d.1, !d.2)).2) := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.reverse.ends.surjective d
  rw [W.reverse.cyclicSucc_symm_ends, reverse_ends_apply, reverse_ends_apply]
  simp

/-- Orientation reversal is an involution. -/
@[simp] theorem reverse_reverse : W.reverse.reverse = W := by
  have h : W.reverse.reverse.ends = W.ends := by
    apply Equiv.ext
    intro x
    rw [reverse_ends_apply, reverse_ends_apply]
    simp
  cases W
  simp only [reverse]
  congr 1

/-- Reverse cyclic orders, keeping the odd end fixed and interchanging the other two. -/
abbrev mirror : ClosedWeb.{u} where
  Vertex := W.Vertex
  Edge := W.Edge
  Circle := W.Circle
  ends := (Equiv.prodCongr (Equiv.refl _) (Equiv.swap (1 : Fin 3) 2)).trans W.ends
  orientation_one x := by simp [Equiv.swap_apply_def]
  orientation_two x := by simp [Equiv.swap_apply_def]

theorem mirror_ends_apply (v : W.Vertex) (i : Fin 3) :
    W.mirror.ends (v, i) = W.ends (v, Equiv.swap (1 : Fin 3) 2 i) := (rfl)

/-- Mirror reversal does not change incidence. -/
@[simp] theorem incident_mirror (d : W.End) : W.mirror.incident d = W.incident d := by
  obtain ⟨⟨v, i⟩, rfl⟩ := W.mirror.ends.surjective d
  rw [W.mirror.incident_ends, mirror_ends_apply, W.incident_ends]

@[simp] theorem source_mirror (e : W.Edge) : W.mirror.source e = W.source e := by
  simp [source]

@[simp] theorem target_mirror (e : W.Edge) : W.mirror.target e = W.target e := by
  simp [target]

@[simp] theorem isMerge_mirror (v : W.Vertex) : W.mirror.IsMerge v ↔ W.IsMerge v := by
  rw [IsMerge, mirror_ends_apply]
  simp [IsMerge, Equiv.swap_apply_def]

@[simp] theorem isSplit_mirror (v : W.Vertex) : W.mirror.IsSplit v ↔ W.IsSplit v := by
  rw [IsSplit, mirror_ends_apply]
  simp [IsSplit, Equiv.swap_apply_def]

/-- Mirror reversal is an involution, not a cyclic rotation of the three ends. -/
@[simp] theorem mirror_mirror : W.mirror.mirror = W := by
  have h : W.mirror.mirror.ends = W.ends := by
    apply Equiv.ext
    rintro ⟨v, i⟩
    rw [mirror_ends_apply, mirror_ends_apply]
    simp
  cases W
  simp only [mirror]
  congr 1

/-- Mirroring changes cyclic successor to cyclic predecessor. -/
@[simp] theorem cyclicSucc_mirror : W.mirror.cyclicSucc = W.cyclicSucc.symm := by
  apply Equiv.ext
  intro d
  obtain ⟨⟨v, i⟩, rfl⟩ := W.mirror.ends.surjective d
  apply W.cyclicSucc.injective
  rw [Equiv.apply_symm_apply, W.mirror.cyclicSucc_ends]
  fin_cases i <;> simp [Equiv.swap_apply_def, finRotate_apply]

/-- Orientation reversal and mirror reversal commute. -/
theorem mirror_reverse : W.reverse.mirror = W.mirror.reverse := rfl

/-- The web consisting of a specified finite set of vertex-free circles. -/
abbrev circles (C : Type u) [Finite C] : ClosedWeb.{u} where
  Vertex := PEmpty
  Edge := PEmpty
  Circle := C
  ends := Equiv.equivOfIsEmpty _ _
  orientation_one x := isEmptyElim x
  orientation_two x := isEmptyElim x

/-- Orientation reversal fixes every vertex-free web. -/
theorem reverse_of_isEmpty_vertex [IsEmpty W.Vertex] : W.reverse = W := by
  have h : W.reverse.ends = W.ends := Equiv.ext fun x ↦ isEmptyElim x.1
  cases W
  simp only [reverse]
  congr 1

/-- Mirror reversal fixes every vertex-free web. -/
theorem mirror_of_isEmpty_vertex [IsEmpty W.Vertex] : W.mirror = W := by
  have h : W.mirror.ends = W.ends := Equiv.ext fun x ↦ isEmptyElim x.1
  cases W
  simp only [mirror]
  congr 1

@[simp] theorem reverse_circles (C : Type u) [Finite C] :
    (circles C).reverse = circles C := (circles C).reverse_of_isEmpty_vertex

@[simp] theorem mirror_circles (C : Type u) [Finite C] :
    (circles C).mirror = circles C := (circles C).mirror_of_isEmpty_vertex

/-- The empty closed web. -/
abbrev empty : ClosedWeb.{u} := circles PEmpty

/-- One vertex-free circle, not the empty web. -/
abbrev circle : ClosedWeb.{u} := circles PUnit

/-- The one-circle web and the empty web are not isomorphic. -/
theorem not_nonempty_iso_circle_empty : ¬Nonempty (circle.{u}.Iso empty.{v}) := by
  rintro ⟨f⟩
  exact PEmpty.elim (f.circle PUnit.unit)

/-- Every vertex-free web is isomorphic to the web of its circles. -/
def circlesIso [IsEmpty W.Vertex] : W.Iso (circles W.Circle) where
  vertex := Equiv.equivOfIsEmpty _ _
  edge := Equiv.equivOfIsEmpty _ _
  circle := Equiv.refl _
  map_ends x := isEmptyElim x.1

@[simp] theorem circlesIso_vertex [IsEmpty W.Vertex] :
    W.circlesIso.vertex = Equiv.equivOfIsEmpty _ _ := (rfl)

@[simp] theorem circlesIso_edge [IsEmpty W.Vertex] :
    W.circlesIso.edge = Equiv.equivOfIsEmpty _ _ := (rfl)

@[simp] theorem circlesIso_circle [IsEmpty W.Vertex] :
    W.circlesIso.circle = Equiv.refl _ := (rfl)

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

theorem sum_ends_apply_inl (V : ClosedWeb.{v}) (v : W.Vertex) (i : Fin 3) :
    (W.sum V).ends (Sum.inl v, i) = (Sum.inl (W.ends (v, i)).1, (W.ends (v, i)).2) := (rfl)

theorem sum_ends_apply_inr (V : ClosedWeb.{v}) (v : V.Vertex) (i : Fin 3) :
    (W.sum V).ends (Sum.inr v, i) = (Sum.inr (V.ends (v, i)).1, (V.ends (v, i)).2) := (rfl)

/-- Incidence on the left component of a disjoint union. -/
@[simp] theorem incident_sum_inl (V : ClosedWeb.{v}) (e : W.Edge) (b : Bool) :
    (W.sum V).incident ((Sum.inl e, b) : (W.Edge ⊕ V.Edge) × Bool) =
      Sum.inl (W.incident (e, b)) := by
  obtain ⟨⟨v, i⟩, h⟩ := W.ends.surjective (e, b)
  have hv : W.incident (e, b) = v := by rw [← h, incident_ends]
  have hi := (W.sum V).incident_ends (Sum.inl v) i
  rw [sum_ends_apply_inl, h] at hi
  rw [hv]
  exact hi

/-- Incidence on the right component of a disjoint union. -/
@[simp] theorem incident_sum_inr (V : ClosedWeb.{v}) (e : V.Edge) (b : Bool) :
    (W.sum V).incident ((Sum.inr e, b) : (W.Edge ⊕ V.Edge) × Bool) =
      Sum.inr (V.incident (e, b)) := by
  obtain ⟨⟨v, i⟩, h⟩ := V.ends.surjective (e, b)
  have hv : V.incident (e, b) = v := by rw [← h, incident_ends]
  have hi := (W.sum V).incident_ends (Sum.inr v) i
  rw [sum_ends_apply_inr, h] at hi
  rw [hv]
  exact hi

@[simp] theorem source_sum_inl (V : ClosedWeb.{v}) (e : W.Edge) :
    (W.sum V).source (Sum.inl e) = Sum.inl (W.source e) := by
  simp only [source]
  rw [incident_sum_inl]

@[simp] theorem source_sum_inr (V : ClosedWeb.{v}) (e : V.Edge) :
    (W.sum V).source (Sum.inr e) = Sum.inr (V.source e) := by
  simp only [source]
  rw [incident_sum_inr]

@[simp] theorem target_sum_inl (V : ClosedWeb.{v}) (e : W.Edge) :
    (W.sum V).target (Sum.inl e) = Sum.inl (W.target e) := by
  simp only [target]
  rw [incident_sum_inl]

@[simp] theorem target_sum_inr (V : ClosedWeb.{v}) (e : V.Edge) :
    (W.sum V).target (Sum.inr e) = Sum.inr (V.target e) := by
  simp only [target]
  rw [incident_sum_inr]

@[simp] theorem isMerge_sum_inl (V : ClosedWeb.{v}) (v : W.Vertex) :
    (W.sum V).IsMerge (Sum.inl v) ↔ W.IsMerge v := by simp [IsMerge]

@[simp] theorem isMerge_sum_inr (V : ClosedWeb.{v}) (v : V.Vertex) :
    (W.sum V).IsMerge (Sum.inr v) ↔ V.IsMerge v := by simp [IsMerge]

@[simp] theorem isSplit_sum_inl (V : ClosedWeb.{v}) (v : W.Vertex) :
    (W.sum V).IsSplit (Sum.inl v) ↔ W.IsSplit v := by simp [IsSplit]

@[simp] theorem isSplit_sum_inr (V : ClosedWeb.{v}) (v : V.Vertex) :
    (W.sum V).IsSplit (Sum.inr v) ↔ V.IsSplit v := by simp [IsSplit]

@[simp] theorem cyclicSucc_sum_apply_inl (V : ClosedWeb.{v}) (e : W.Edge) (b : Bool) :
    (W.sum V).cyclicSucc ((Sum.inl e, b) : (W.Edge ⊕ V.Edge) × Bool) =
      (Sum.inl (W.cyclicSucc (e, b)).1, (W.cyclicSucc (e, b)).2) := by
  obtain ⟨⟨v, i⟩, h⟩ := W.ends.surjective (e, b)
  have hr := (W.sum V).cyclicSucc_ends (Sum.inl v) i
  rw [sum_ends_apply_inl, sum_ends_apply_inl, ← W.cyclicSucc_ends, h] at hr
  exact hr

@[simp] theorem cyclicSucc_sum_apply_inr (V : ClosedWeb.{v}) (e : V.Edge) (b : Bool) :
    (W.sum V).cyclicSucc ((Sum.inr e, b) : (W.Edge ⊕ V.Edge) × Bool) =
      (Sum.inr (V.cyclicSucc (e, b)).1, (V.cyclicSucc (e, b)).2) := by
  obtain ⟨⟨v, i⟩, h⟩ := V.ends.surjective (e, b)
  have hr := (W.sum V).cyclicSucc_ends (Sum.inr v) i
  rw [sum_ends_apply_inr, sum_ends_apply_inr, ← V.cyclicSucc_ends, h] at hr
  exact hr

@[simp] theorem cyclicSucc_symm_sum_apply_inl (V : ClosedWeb.{v}) (e : W.Edge) (b : Bool) :
    (W.sum V).cyclicSucc.symm
        (α := no_index ((W.Edge ⊕ V.Edge) × Bool))
        (β := no_index ((W.Edge ⊕ V.Edge) × Bool))
        ((Sum.inl e, b) : (W.Edge ⊕ V.Edge) × Bool) =
      (Sum.inl (W.cyclicSucc.symm (e, b)).1, (W.cyclicSucc.symm (e, b)).2) := by
  obtain ⟨⟨v, i⟩, h⟩ := W.ends.surjective (e, b)
  have hr := (W.sum V).cyclicSucc_symm_ends (Sum.inl v) i
  rw [sum_ends_apply_inl, sum_ends_apply_inl, ← W.cyclicSucc_symm_ends, h] at hr
  exact hr

@[simp] theorem cyclicSucc_symm_sum_apply_inr (V : ClosedWeb.{v}) (e : V.Edge) (b : Bool) :
    (W.sum V).cyclicSucc.symm
        (α := no_index ((W.Edge ⊕ V.Edge) × Bool))
        (β := no_index ((W.Edge ⊕ V.Edge) × Bool))
        ((Sum.inr e, b) : (W.Edge ⊕ V.Edge) × Bool) =
      (Sum.inr (V.cyclicSucc.symm (e, b)).1, (V.cyclicSucc.symm (e, b)).2) := by
  obtain ⟨⟨v, i⟩, h⟩ := V.ends.surjective (e, b)
  have hr := (W.sum V).cyclicSucc_symm_ends (Sum.inr v) i
  rw [sum_ends_apply_inr, sum_ends_apply_inr, ← V.cyclicSucc_symm_ends, h] at hr
  exact hr

@[simp] theorem reverse_sum (V : ClosedWeb.{v}) :
    (W.sum V).reverse = W.reverse.sum V.reverse := by
  have h : (W.sum V).reverse.ends = (W.reverse.sum V.reverse).ends := by
    apply Equiv.ext
    rintro ⟨v | v, i⟩
    · rw [reverse_ends_apply, sum_ends_apply_inl, sum_ends_apply_inl, reverse_ends_apply]
    · rw [reverse_ends_apply, sum_ends_apply_inr, sum_ends_apply_inr, reverse_ends_apply]
  cases W
  cases V
  simp only [reverse, sum]
  congr 1

@[simp] theorem mirror_sum (V : ClosedWeb.{v}) :
    (W.sum V).mirror = W.mirror.sum V.mirror := by
  have h : (W.sum V).mirror.ends = (W.mirror.sum V.mirror).ends := by
    apply Equiv.ext
    rintro ⟨v | v, i⟩
    · rw [mirror_ends_apply, sum_ends_apply_inl, sum_ends_apply_inl, mirror_ends_apply]
    · rw [mirror_ends_apply, sum_ends_apply_inr, sum_ends_apply_inr, mirror_ends_apply]
  cases W
  cases V
  simp only [mirror, sum]
  congr 1

/-- The disjoint-union left unit isomorphism. -/
def emptySum : (empty.{v}.sum W).Iso W where
  vertex := Equiv.emptySum _ _
  edge := Equiv.emptySum _ _
  circle := Equiv.emptySum _ _
  map_ends x := by
    rcases x with ⟨v | v, i⟩
    · exact v.elim
    · rw [Equiv.emptySum_apply_inr, sum_ends_apply_inr]
      simp

@[simp] theorem emptySum_vertex : W.emptySum.vertex = Equiv.emptySum _ _ := (rfl)
@[simp] theorem emptySum_edge : W.emptySum.edge = Equiv.emptySum _ _ := (rfl)
@[simp] theorem emptySum_circle : W.emptySum.circle = Equiv.emptySum _ _ := (rfl)

/-- The disjoint-union right unit isomorphism. -/
def sumEmpty : (W.sum empty.{v}).Iso W where
  vertex := Equiv.sumEmpty _ _
  edge := Equiv.sumEmpty _ _
  circle := Equiv.sumEmpty _ _
  map_ends x := by
    rcases x with ⟨v | v, i⟩
    · rw [Equiv.sumEmpty_apply_inl, sum_ends_apply_inl]
      simp
    · exact v.elim

@[simp] theorem sumEmpty_vertex : W.sumEmpty.vertex = Equiv.sumEmpty _ _ := (rfl)
@[simp] theorem sumEmpty_edge : W.sumEmpty.edge = Equiv.sumEmpty _ _ := (rfl)
@[simp] theorem sumEmpty_circle : W.sumEmpty.circle = Equiv.sumEmpty _ _ := (rfl)

/-- The disjoint-union associativity isomorphism. -/
def sumAssoc (V : ClosedWeb.{v}) (U : ClosedWeb) :
    ((W.sum V).sum U).Iso (W.sum (V.sum U)) where
  vertex := Equiv.sumAssoc _ _ _
  edge := Equiv.sumAssoc _ _ _
  circle := Equiv.sumAssoc _ _ _
  map_ends x := by
    rcases x with ⟨(v | v) | v, i⟩
    · rw [Equiv.sumAssoc_apply_inl_inl, sum_ends_apply_inl, sum_ends_apply_inl, sum_ends_apply_inl]
      simp
    · rw [Equiv.sumAssoc_apply_inl_inr, sum_ends_apply_inr, sum_ends_apply_inl, sum_ends_apply_inl,
        sum_ends_apply_inr]
      simp
    · rw [Equiv.sumAssoc_apply_inr, sum_ends_apply_inr, sum_ends_apply_inr, sum_ends_apply_inr]
      simp

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
  map_ends x := by
    rcases x with ⟨v | v, i⟩
    · simp only [Equiv.sumComm_apply, Sum.swap_inl]
      rw [sum_ends_apply_inr, sum_ends_apply_inl]
      rfl
    · simp only [Equiv.sumComm_apply, Sum.swap_inr]
      rw [sum_ends_apply_inl, sum_ends_apply_inr]
      rfl

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
    rw [ClosedWeb.reverse_ends_apply, ClosedWeb.reverse_ends_apply, f.map_ends x]

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
    · simp only [Equiv.sumCongr_apply, Sum.map_inl]
      rw [sum_ends_apply_inl, sum_ends_apply_inl, f.map_ends (v, i)]
      rfl
    · simp only [Equiv.sumCongr_apply, Sum.map_inr]
      rw [sum_ends_apply_inr, sum_ends_apply_inr, g.map_ends (v, i)]
      rfl

@[simp] theorem sum_vertex {W' V' : ClosedWeb} (f : W.Iso V) (g : W'.Iso V') :
    (f.sum g).vertex = Equiv.sumCongr f.vertex g.vertex := (rfl)
@[simp] theorem sum_edge {W' V' : ClosedWeb} (f : W.Iso V) (g : W'.Iso V') :
    (f.sum g).edge = Equiv.sumCongr f.edge g.edge := (rfl)
@[simp] theorem sum_circle {W' V' : ClosedWeb} (f : W.Iso V) (g : W'.Iso V') :
    (f.sum g).circle = Equiv.sumCongr f.circle g.circle := (rfl)

end Iso

/-- The compatibly planar oriented theta web, with one merge, one split and no vertex-free
circles. Both vertices order the edges as zero, one, two; the compatible surface rotation
inverts this order at the merge. Edge zero runs from the merge to the split; the other two
edges run back. -/
abbrev theta : ClosedWeb where
  Vertex := Bool
  Edge := Fin 3
  Circle := PEmpty
  ends := (Equiv.prodComm _ _).trans
    (Equiv.prodCongrRight fun i : Fin 3 ↦ if i = 0 then Equiv.refl Bool else Equiv.boolNot)
  orientation_one _ := rfl
  orientation_two _ := rfl

theorem theta_ends_apply (v : Bool) (i : Fin 3) :
    theta.ends (v, i) = (i, if i = 0 then v else !v) := by
  simp [theta, Equiv.prodCongrRight, Equiv.prodComm_apply]
  split <;> rfl

@[simp] theorem incident_theta (d : theta.End) :
    theta.incident d = if d.1 = 0 then d.2 else !d.2 := by
  rcases d with ⟨e, b⟩
  have h := theta.incident_ends (if e = 0 then b else !b) e
  rw [theta_ends_apply] at h
  by_cases he : e = 0 <;> simpa [he] using h

@[simp] theorem source_theta (e : Fin 3) : theta.source e = !decide (e = 0) := by
  rw [source_def, incident_theta]
  by_cases h : e = 0 <;> simp [h]

@[simp] theorem target_theta (e : Fin 3) : theta.target e = decide (e = 0) := by
  rw [target_def, incident_theta]
  by_cases h : e = 0 <;> simp [h]

@[simp] theorem cyclicSucc_theta_apply (d : theta.End) :
    theta.cyclicSucc d = (finRotate 3 d.1, if d.1 = 1 then d.2 else !d.2) := by
  rcases d with ⟨e, b⟩
  have h := theta.cyclicSucc_ends (theta.incident (e, b)) e
  rw [theta_ends_apply, theta_ends_apply, incident_theta] at h
  fin_cases e <;> simpa [finRotate_apply] using h

@[simp] theorem cyclicSucc_symm_theta_apply (d : theta.End) :
    theta.cyclicSucc.symm
        (α := no_index (Fin 3 × Bool)) (β := no_index (Fin 3 × Bool)) d =
      ((finRotate 3).symm d.1, if d.1 = 2 then d.2 else !d.2) := by
  apply theta.cyclicSucc.injective
  rcases d with ⟨e, b⟩
  fin_cases e <;> cases b <;>
    simp only [cyclicSucc_theta_apply, Equiv.apply_symm_apply] <;> decide

@[simp] theorem isMerge_theta (v : Bool) : theta.IsMerge v ↔ v = false := by
  rw [IsMerge, theta_ends_apply]
  simp

@[simp] theorem isSplit_theta (v : Bool) : theta.IsSplit v ↔ v = true := by
  rw [IsSplit, theta_ends_apply]
  simp

end ClosedWeb
end TauCeti
