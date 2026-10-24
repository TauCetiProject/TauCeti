/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Components
public import TauCeti.Data.Fintype.Fiber
public import TauCeti.GroupTheory.Perm.Basic

/-! # Labelled components of oriented PD-codes

`OrientedPDCode.Component` consists of the outgoing traversal classes and a separate finite
set of crossing-free circle labels. Its cardinality is the native component count. The
constructor `componentOfOutgoing` assigns an outgoing half-edge to its component, independently
of the point chosen along that traversal.

`componentEquiv` transports these components along an equivalence of outgoing traversals and
an explicit bijection of crossing-free labels. It preserves identities and composition;
`relabelComponentEquiv` and `mirrorComponentEquiv` apply it to the native diagram operations.

`CrossinglessLabeling` decorates the crossing-free labels by the prescribed orientation
multiset. Such labellings exist and any two differ by a permutation, so choosing labels does
not lose multiplicities or distinguish circles with equal orientation artificially.

The component traversal follows M. Mastin, *Links and Planar Diagram Codes*, Definitions 2–3.
No planarity hypothesis is needed for these component constructions.
-/

public section

noncomputable section

namespace TauCeti.OrientedPDCode

open Equiv Equiv.Perm

variable {n m r : ℕ}

/-- The components meeting a crossing, represented by outgoing traversal classes. -/
abbrev CrossingComponent (D : OrientedPDCode n) :=
  Quotient (SameCycle.setoid D.componentPermOutgoing)

/-- The link components, including individually labelled crossing-free circles. -/
abbrev Component (D : OrientedPDCode n) :=
  D.CrossingComponent ⊕ Fin D.crossinglessComponentCount

/-- The component containing an outgoing half-edge. -/
def componentOfOutgoing (D : OrientedPDCode n)
    (h : {h : Fin (4 * n) // D.orientation h = true}) : D.Component :=
  Sum.inl (Quotient.mk _ h)

/-- Two outgoing half-edges represent the same component exactly when traversal joins them. -/
@[simp] theorem componentOfOutgoing_eq_iff (D : OrientedPDCode n)
    (h k : {h : Fin (4 * n) // D.orientation h = true}) :
    D.componentOfOutgoing h = D.componentOfOutgoing k ↔
      D.componentPermOutgoing.SameCycle h k := by
  simp [componentOfOutgoing, Quotient.eq, SameCycle.setoid]

-- Not simp: the native outgoing-traversal simp lemma expands the argument first.
/-- Traversing to the next outgoing half-edge does not change the component. -/
theorem componentOfOutgoing_componentPermOutgoing (D : OrientedPDCode n)
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    D.componentOfOutgoing (D.componentPermOutgoing h) = D.componentOfOutgoing h := by
  rw [componentOfOutgoing_eq_iff]
  exact sameCycle_apply_left.mpr (SameCycle.refl _ _)

/-- The number of crossing-bearing component classes is the native crossing-component count. -/
@[simp] theorem card_crossingComponent (D : OrientedPDCode n) :
    Nat.card D.CrossingComponent = D.toPDCode.crossingComponentCount := by
  rw [← orbitCount_def, orbitCount_componentPermOutgoing]

-- Not simp: the native sum-cardinality lemmas already expand the left-hand side.
/-- The labelled component carrier has exactly the native number of components. -/
theorem card_component (D : OrientedPDCode n) :
    Nat.card D.Component = D.toPDCode.componentCount := by
  simp [Component, PDCode.componentCount_eq]

/-- Every component either contains an outgoing half-edge or is a crossing-free label. -/
theorem component_cases (D : OrientedPDCode n) (c : D.Component) :
    (∃ h, D.componentOfOutgoing h = c) ∨ (∃ i, Sum.inr i = c) := by
  rcases c with c | i
  · obtain ⟨h, rfl⟩ := Quotient.mk_surjective c
    exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

/-- Transport components by an equivalence of outgoing traversals and a chosen bijection of
crossing-free labels. The latter is data, not just equality of component counts. -/
def componentEquiv (D : OrientedPDCode n) (E : OrientedPDCode m)
    (e : {h : Fin (4 * n) // D.orientation h = true} ≃
      {h : Fin (4 * m) // E.orientation h = true})
    (he : E.componentPermOutgoing = e.permCongr D.componentPermOutgoing)
    (isolated : Fin D.crossinglessComponentCount ≃ Fin E.crossinglessComponentCount) :
    D.Component ≃ E.Component :=
  Equiv.sumCongr (sameCycleQuotientCongr e he) isolated

/-- Component transport sends a represented component to the transported representative. -/
@[simp] theorem componentEquiv_componentOfOutgoing (D : OrientedPDCode n) (E : OrientedPDCode m)
    (e : {h : Fin (4 * n) // D.orientation h = true} ≃
      {h : Fin (4 * m) // E.orientation h = true})
    (he : E.componentPermOutgoing = e.permCongr D.componentPermOutgoing)
    (isolated : Fin D.crossinglessComponentCount ≃ Fin E.crossinglessComponentCount)
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    D.componentEquiv E e he isolated (D.componentOfOutgoing h) =
      E.componentOfOutgoing (e h) := by
  simp only [componentEquiv, componentOfOutgoing, Equiv.sumCongr_apply, Sum.map_inl,
    sameCycleQuotientCongr_mk]

/-- Component transport acts on crossing-free circles by the supplied bijection. -/
@[simp] theorem componentEquiv_inr (D : OrientedPDCode n) (E : OrientedPDCode m)
    (e : {h : Fin (4 * n) // D.orientation h = true} ≃
      {h : Fin (4 * m) // E.orientation h = true})
    (he : E.componentPermOutgoing = e.permCongr D.componentPermOutgoing)
    (isolated : Fin D.crossinglessComponentCount ≃ Fin E.crossinglessComponentCount)
    (i : Fin D.crossinglessComponentCount) :
    D.componentEquiv E e he isolated (Sum.inr i) = Sum.inr (isolated i) := (rfl)

/-- Identity traversal and label bijections induce identity component transport. -/
@[simp] theorem componentEquiv_refl (D : OrientedPDCode n) :
    D.componentEquiv D (Equiv.refl _) (by ext h; simp) (Equiv.refl _) = Equiv.refl _ := by
  rw [componentEquiv, sameCycleQuotientCongr_refl, Equiv.sumCongr_refl]

/-- Component transport respects composition, including the chosen crossing-free labels. -/
theorem componentEquiv_trans (D : OrientedPDCode n) (E : OrientedPDCode m)
    (F : OrientedPDCode r)
    (e : {h : Fin (4 * n) // D.orientation h = true} ≃
      {h : Fin (4 * m) // E.orientation h = true})
    (f : {h : Fin (4 * m) // E.orientation h = true} ≃
      {h : Fin (4 * r) // F.orientation h = true})
    (he : E.componentPermOutgoing = e.permCongr D.componentPermOutgoing)
    (hf : F.componentPermOutgoing = f.permCongr E.componentPermOutgoing)
    (i : Fin D.crossinglessComponentCount ≃ Fin E.crossinglessComponentCount)
    (j : Fin E.crossinglessComponentCount ≃ Fin F.crossinglessComponentCount) :
    (D.componentEquiv E e he i).trans (E.componentEquiv F f hf j) =
      D.componentEquiv F (e.trans f) (by ext h; simp [hf, he]) (i.trans j) := by
  simp only [componentEquiv, Equiv.sumCongr_trans, sameCycleQuotientCongr_trans]

/-- Native relabelling transports components and keeps the crossing-free labels fixed. -/
def relabelComponentEquiv (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    D.Component ≃ (D.relabel half cross).Component :=
  D.componentEquiv _ (D.relabelOutgoingEquiv half cross)
    (D.componentPermOutgoing_relabel half cross) (finCongr (by simp))

/-- Relabelling transports the component of an outgoing half-edge to that of its image. -/
@[simp] theorem relabelComponentEquiv_componentOfOutgoing (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m)
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    D.relabelComponentEquiv half cross (D.componentOfOutgoing h) =
      (D.relabel half cross).componentOfOutgoing (D.relabelOutgoingEquiv half cross h) := by
  exact D.componentEquiv_componentOfOutgoing _ _ _ _ h

/-- Relabelling fixes each crossing-free component label. -/
@[simp] theorem relabelComponentEquiv_inr (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m)
    (i : Fin D.crossinglessComponentCount) :
    D.relabelComponentEquiv half cross (Sum.inr i) =
      Sum.inr (Fin.cast (by simp) i) := (rfl)

/-- Native mirroring preserves component representatives and crossing-free labels. -/
def mirrorComponentEquiv (D : OrientedPDCode n) : D.Component ≃ D.mirror.Component :=
  D.componentEquiv _ D.mirrorOutgoingEquiv D.componentPermOutgoing_mirror (finCongr (by simp))

/-- Mirroring transports the component of each outgoing half-edge. -/
@[simp] theorem mirrorComponentEquiv_componentOfOutgoing (D : OrientedPDCode n)
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    D.mirrorComponentEquiv (D.componentOfOutgoing h) =
      D.mirror.componentOfOutgoing (D.mirrorOutgoingEquiv h) := by
  exact D.componentEquiv_componentOfOutgoing _ _ _ _ h

/-- Mirroring fixes each crossing-free component label. -/
@[simp] theorem mirrorComponentEquiv_inr (D : OrientedPDCode n)
    (i : Fin D.crossinglessComponentCount) :
    D.mirrorComponentEquiv (Sum.inr i) = Sum.inr (Fin.cast (by simp) i) := (rfl)

/-- A labelling of the crossing-free circles by orientations with the prescribed multiset.
Repeated orientations still occupy distinct labels. -/
abbrev CrossinglessLabeling (D : OrientedPDCode n) :=
  {o : Fin D.crossinglessComponentCount → Bool //
    Finset.univ.val.map o = D.crossinglessComponents}

namespace CrossinglessLabeling

/-- Crossing-free circles admit orientation labels, including when there are no such circles. -/
instance (D : OrientedPDCode n) : Nonempty D.CrossinglessLabeling := by
  obtain ⟨o, ho⟩ := exists_map_univ_eq (X := Fin D.crossinglessComponentCount)
    D.crossinglessComponents (by simp)
  exact ⟨⟨o, ho⟩⟩

/-- Reindex the crossing-free labels, keeping their orientation multiset unchanged. -/
def reindex {D : OrientedPDCode n} (o : D.CrossinglessLabeling)
    (e : Equiv.Perm (Fin D.crossinglessComponentCount)) : D.CrossinglessLabeling :=
  ⟨o.val ∘ e, by
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
    exact o.property⟩

/-- The reindexed orientation at a label is the old orientation at its image. -/
@[simp] theorem reindex_apply {D : OrientedPDCode n} (o : D.CrossinglessLabeling)
    (e : Equiv.Perm (Fin D.crossinglessComponentCount))
    (i : Fin D.crossinglessComponentCount) :
    (o.reindex e).val i = o.val (e i) := (rfl)

/-- Reindexing by the identity changes no orientation labels. -/
@[simp] theorem reindex_refl {D : OrientedPDCode n} (o : D.CrossinglessLabeling) :
    o.reindex (Equiv.refl _) = o := by
  apply Subtype.ext
  rfl

/-- Reindexing composes contravariantly, as precomposition of the orientation function. -/
theorem reindex_trans {D : OrientedPDCode n} (o : D.CrossinglessLabeling)
    (e f : Equiv.Perm (Fin D.crossinglessComponentCount)) :
    o.reindex (e.trans f) = (o.reindex f).reindex e := by
  apply Subtype.ext
  rfl

/-- The number of labels of a given orientation is its multiplicity in the native multiset. -/
@[simp] theorem occCount_val {D : OrientedPDCode n} (o : D.CrossinglessLabeling) (b : Bool) :
    Function.occCount o.val b = D.crossinglessComponents.count b := by
  rw [occCount_eq_count_map_univ, o.property]

/-- Any two choices of orientation labels differ by a permutation of the individual circles. -/
theorem exists_reindex_eq {D : OrientedPDCode n} (o p : D.CrossinglessLabeling) :
    ∃ e : Equiv.Perm (Fin D.crossinglessComponentCount), p.reindex e = o := by
  obtain ⟨e, he⟩ := exists_perm_of_map_univ_eq (o.property.trans p.property.symm)
  exact ⟨e, Subtype.ext he⟩

end CrossinglessLabeling

end TauCeti.OrientedPDCode
