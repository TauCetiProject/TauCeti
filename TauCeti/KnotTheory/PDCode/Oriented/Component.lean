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
`crossingComponentOfHalfEdge` also accepts incoming half-edges, is invariant under arc pairing and
passing straight through a crossing, and identifies two half-edges exactly when `componentPerm`
connects one to the other or to its opposite crossing slot (`crossingComponentOfHalfEdge_eq_iff`).

`componentEquiv` transports these components along an equivalence of outgoing traversals and
an explicit bijection of crossing-free labels. It preserves identities and composition;
`relabelComponentEquiv` and `mirrorComponentEquiv` apply it to the native diagram operations.

`CrossinglessLabeling` decorates the crossing-free labels by the prescribed orientation
multiset. Such labellings exist and any two differ by a permutation, so choosing labels does
not lose multiplicities or distinguish circles with equal orientation artificially.

Conversely, every unoriented `PDCode` admits an orientation: arc pairing induces a fixed-point-free
involution `TauCeti.PDCode.componentCycleReversal` on the directed `componentPerm` orbits, so
choosing one orbit from each reversal pair (`TauCeti.PDCode.orient`) and supplying a `Multiset Bool`
of crossing-free circle orientations constructs an `OrientedPDCode`
(`TauCeti.PDCode.exists_orientedPDCode_of_card_eq`, `TauCeti.PDCode.exists_orientedPDCode`).

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

/-- The component of an outgoing half-edge is its traversal class in the crossing-bearing
summand. -/
theorem componentOfOutgoing_def (D : OrientedPDCode n)
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    D.componentOfOutgoing h = Sum.inl (Quotient.mk _ h) := (rfl)

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

section HalfEdge

variable (D : OrientedPDCode n)

/-- The crossing-bearing component containing a half-edge, irrespective of its direction.
An incoming half-edge is represented by the outgoing half-edge at the other end of its arc. -/
def crossingComponentOfHalfEdge (h : Fin (4 * n)) : D.CrossingComponent :=
  if hh : D.orientation h = true then ⟦⟨h, hh⟩⟧
  else ⟦⟨D.edgePair.val h, by simpa using hh⟩⟧

/-- An outgoing half-edge represents its own crossing-bearing component. -/
@[simp] theorem crossingComponentOfHalfEdge_of_outgoing (h : Fin (4 * n))
    (hh : D.orientation h = true) :
    D.crossingComponentOfHalfEdge h = ⟦⟨h, hh⟩⟧ := by
  simp [crossingComponentOfHalfEdge, hh]

/-- An incoming half-edge is represented by the outgoing end of its arc. -/
@[simp] theorem crossingComponentOfHalfEdge_of_incoming (h : Fin (4 * n))
    (hh : D.orientation h = false) :
    D.crossingComponentOfHalfEdge h =
      ⟦⟨D.edgePair.val h, by simp [hh]⟩⟧ := by
  simp [crossingComponentOfHalfEdge, hh]

/-- The arbitrary-half-edge assignment agrees with the outgoing component constructor. -/
@[simp] theorem inl_crossingComponentOfHalfEdge
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    Sum.inl (D.crossingComponentOfHalfEdge h) = D.componentOfOutgoing h := by
  simp [crossingComponentOfHalfEdge, h.property, componentOfOutgoing]

/-- The two ends of an arc belong to the same crossing-bearing component. -/
@[simp] theorem crossingComponentOfHalfEdge_edgePair (h : Fin (4 * n)) :
    D.crossingComponentOfHalfEdge (D.edgePair.val h) = D.crossingComponentOfHalfEdge h := by
  cases hh : D.orientation h <;> simp [crossingComponentOfHalfEdge, hh]

/-- Passing straight through a crossing does not change the link component. -/
@[simp] theorem crossingComponentOfHalfEdge_crossingTurn (h : Fin (4 * n)) :
    D.crossingComponentOfHalfEdge (D.crossingTurn h) = D.crossingComponentOfHalfEdge h := by
  cases hh : D.orientation h with
  | false =>
    have he : D.orientation (D.edgePair.val h) = true := by simp [hh]
    rw [crossingComponentOfHalfEdge_of_outgoing D _ (by simp [hh])]
    have ht := sameCycle_apply_left.mpr
      (SameCycle.refl D.componentPermOutgoing ⟨D.edgePair.val h, he⟩)
    have hv : D.componentPermOutgoing ⟨D.edgePair.val h, he⟩ =
        ⟨D.crossingTurn h, by simp [hh]⟩ := by
      apply Subtype.ext
      simp
    rw [hv] at ht
    exact (Quotient.sound ht).trans (by simp [crossingComponentOfHalfEdge, hh])
  | true =>
    have he : D.orientation (D.edgePair.val (D.crossingTurn h)) = true := by simp [hh]
    have ht := sameCycle_apply_left.mpr
      (SameCycle.refl D.componentPermOutgoing ⟨D.edgePair.val (D.crossingTurn h), he⟩)
    have hv : D.componentPermOutgoing ⟨D.edgePair.val (D.crossingTurn h), he⟩ =
        ⟨h, hh⟩ := by
      apply Subtype.ext
      simp
    rw [hv] at ht
    rw [crossingComponentOfHalfEdge_of_outgoing D h hh]
    exact (by simp [crossingComponentOfHalfEdge, hh] :
      D.crossingComponentOfHalfEdge (D.crossingTurn h) =
        ⟦⟨D.edgePair.val (D.crossingTurn h), he⟩⟧).trans (Quotient.sound ht.symm)

/-- Two half-edges in the same directed `componentPerm` orbit have the same orientation. -/
theorem orientation_eq_of_sameCycle_componentPerm {x y : Fin (4 * n)}
    (h : D.toPDCode.componentPerm.SameCycle x y) :
    D.orientation x = D.orientation y := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Perm.mul_apply, D.orientation_componentPerm, ih]

private theorem crossingComponentOfHalfEdge_eq_iff_of_outgoing {x y : Fin (4 * n)}
    (hx : D.orientation x = true) (hy : D.orientation y = true) :
    D.crossingComponentOfHalfEdge x = D.crossingComponentOfHalfEdge y ↔
      D.toPDCode.componentPerm.SameCycle x y ∨
        D.toPDCode.componentPerm.SameCycle x (D.crossingTurn y) := by
  have hnot : ¬ D.toPDCode.componentPerm.SameCycle x (D.crossingTurn y) := fun h ↦ by
    have ho := D.orientation_eq_of_sameCycle_componentPerm h
    simp [hx, hy] at ho
  have hsub : D.componentPermOutgoing =
      D.toPDCode.componentPerm.subtypePerm (fun h ↦ by simp only [orientation_componentPerm]) := by
    ext h
    simp
  rw [← Sum.inl_injective.eq_iff, D.inl_crossingComponentOfHalfEdge ⟨x, hx⟩,
    D.inl_crossingComponentOfHalfEdge ⟨y, hy⟩, D.componentOfOutgoing_eq_iff, hsub,
    or_iff_left hnot]
  exact sameCycle_subtypePerm

private theorem crossingComponentOfHalfEdge_eq_iff_of_left_outgoing {x : Fin (4 * n)}
    (hx : D.orientation x = true) (y : Fin (4 * n)) :
    D.crossingComponentOfHalfEdge x = D.crossingComponentOfHalfEdge y ↔
      D.toPDCode.componentPerm.SameCycle x y ∨
        D.toPDCode.componentPerm.SameCycle x (D.crossingTurn y) := by
  cases hy : D.orientation y
  · have hy' : D.orientation (D.crossingTurn y) = true := by simp [hy]
    rw [← D.crossingComponentOfHalfEdge_crossingTurn y,
      D.crossingComponentOfHalfEdge_eq_iff_of_outgoing hx hy', D.crossingTurn_apply_apply, or_comm]
  · exact D.crossingComponentOfHalfEdge_eq_iff_of_outgoing hx hy

/-- Two half-edges belong to the same crossing-bearing component iff `componentPerm` connects `x`
either to `y` (same direction) or to `D.crossingTurn y` (opposite direction). -/
theorem crossingComponentOfHalfEdge_eq_iff (x y : Fin (4 * n)) :
    D.crossingComponentOfHalfEdge x = D.crossingComponentOfHalfEdge y ↔
      D.toPDCode.componentPerm.SameCycle x y ∨
        D.toPDCode.componentPerm.SameCycle x (D.crossingTurn y) := by
  cases hx : D.orientation x
  · have hx' : D.orientation (D.crossingTurn x) = true := by simp [hx]
    rw [← D.crossingComponentOfHalfEdge_crossingTurn x,
      D.crossingComponentOfHalfEdge_eq_iff_of_left_outgoing hx' y,
      ← D.toPDCode.sameCycle_componentPerm_crossingTurn_iff (x := D.crossingTurn x) (y := y),
      D.crossingTurn_apply_apply, D.toPDCode.sameCycle_componentPerm_crossingTurn_iff, or_comm]
  · exact D.crossingComponentOfHalfEdge_eq_iff_of_left_outgoing hx y

end HalfEdge

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
  Equiv.sumCongr (e.sameCycleQuotientCongr he) isolated

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

/-- Inverting component transport reverses both traversal and crossing-free label bijections. -/
@[simp] theorem componentEquiv_symm (D : OrientedPDCode n) (E : OrientedPDCode m)
    (e : {h : Fin (4 * n) // D.orientation h = true} ≃
      {h : Fin (4 * m) // E.orientation h = true})
    (he : E.componentPermOutgoing = e.permCongr D.componentPermOutgoing)
    (isolated : Fin D.crossinglessComponentCount ≃ Fin E.crossinglessComponentCount) :
    (D.componentEquiv E e he isolated).symm =
      E.componentEquiv D e.symm (by ext h; simp [he]) isolated.symm := by
  simp only [componentEquiv, Equiv.sumCongr_symm, sameCycleQuotientCongr_symm]

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
  obtain ⟨o, ho⟩ := D.crossinglessComponents.exists_map_univ_eq
    (X := Fin D.crossinglessComponentCount) (by simp)
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
  rw [Function.occCount_eq_count_map_univ, o.property]

/-- Any two choices of orientation labels differ by a permutation of the individual circles. -/
theorem exists_reindex_eq {D : OrientedPDCode n} (o p : D.CrossinglessLabeling) :
    ∃ e : Equiv.Perm (Fin D.crossinglessComponentCount), p.reindex e = o := by
  obtain ⟨e, he⟩ := Function.exists_perm_of_map_univ_eq (o.property.trans p.property.symm)
  exact ⟨e, Subtype.ext he⟩

end CrossinglessLabeling

end TauCeti.OrientedPDCode

end

namespace TauCeti.PDCode

open Equiv Equiv.Perm

variable {n : ℕ}

/-! ### Orientability of arbitrary PD-codes -/

/-- Identify the `SameCycle` quotient of `D.crossingTurn * D.edgePair.val` with that of
`D.componentPerm`, whose body is not exposed across modules. -/
private def componentOrbitEquiv (D : PDCode n) :
    Quotient (SameCycle.setoid (D.crossingTurn * D.edgePair.val)) ≃
      Quotient (SameCycle.setoid D.componentPerm) :=
  Quotient.congr (Equiv.refl _) fun _ _ ↦ by
    rw [componentPerm_def]
    exact Iff.rfl

private theorem componentOrbitEquiv_mk (D : PDCode n) (x : Fin (4 * n)) :
    D.componentOrbitEquiv ⟦x⟧ = ⟦x⟧ :=
  rfl

private theorem componentOrbitEquiv_symm_mk (D : PDCode n) (x : Fin (4 * n)) :
    D.componentOrbitEquiv.symm ⟦x⟧ = ⟦x⟧ :=
  (Equiv.symm_apply_eq _).mpr rfl

/-- **Reversal of directed component orbits**: following the other end of an arc carries each
directed traversal orbit of `D.componentPerm` to the opposite traversal of the same component. -/
noncomputable def componentCycleReversal (D : PDCode n) :
    Perm (Quotient (SameCycle.setoid D.componentPerm)) :=
  D.componentOrbitEquiv.permCongr
    (D.isPerfectMatching_crossingTurn.involutive.cycleReversal D.edgePair.apply_apply)

/-- Reversal sends the directed orbit of a half-edge to that of the other end of its arc. -/
@[simp] theorem componentCycleReversal_mk (D : PDCode n) (x : Fin (4 * n)) :
    D.componentCycleReversal ⟦x⟧ = ⟦D.edgePair.val x⟧ :=
  -- Term proof: `rw` rejects `D.edgePair.val` before unfolding `PerfectMatching` at implicit
  -- transparency, as in `TauCeti.PDCode.stateCycleReversal_mk`.
  (Equiv.permCongr_apply _ _ _).trans <|
    (congrArg _ ((congrArg _ (D.componentOrbitEquiv_symm_mk x)).trans
      (Function.Involutive.cycleReversal_mk _ _ x))).trans (D.componentOrbitEquiv_mk _)

/-- Reversal also sends the directed orbit of a half-edge to that of its opposite crossing slot. -/
theorem componentCycleReversal_mk_eq_crossingTurn (D : PDCode n) (x : Fin (4 * n)) :
    D.componentCycleReversal ⟦x⟧ = ⟦D.crossingTurn x⟧ := by
  rw [componentCycleReversal_mk]
  apply Quotient.sound
  have h : D.componentPerm (D.edgePair.val x) = D.crossingTurn x :=
    (D.componentPerm_apply (D.edgePair.val x)).trans
      (congrArg D.crossingTurn (D.edgePair.apply_apply x))
  exact ⟨(1 : ℕ), by rw [zpow_natCast, pow_one]; exact h⟩

/-- Reversal of directed component orbits is a fixed-point-free involution. -/
theorem isPerfectMatching_componentCycleReversal (D : PDCode n) :
    IsPerfectMatching D.componentCycleReversal :=
  PerfectMatching.isPerfectMatching_permCongr _
    (D.isPerfectMatching_crossingTurn.isPerfectMatching_cycleReversal D.edgePair.prop)

/-- Endow an unoriented `PDCode` with an orientation from a reversal-antisymmetric `Bool` choice on
its directed `componentPerm` orbits and a `Multiset Bool` of crossing-free circle orientations. -/
def orient (D : PDCode n) (o : Quotient (SameCycle.setoid D.componentPerm) → Bool)
    (ho : ∀ q, o (D.componentCycleReversal q) = !o q) (l : Multiset Bool)
    (hl : l.card = D.crossinglessComponentCount) : OrientedPDCode n where
  toPDCode := D
  orientation x := o ⟦x⟧
  orientation_edgePair x := by
    simpa only [componentCycleReversal_mk] using ho ⟦x⟧
  orientation_oppositeCrossingSlot i slot := by
    rw [← D.crossing_apply, ← D.crossingTurn_crossing, ← componentCycleReversal_mk_eq_crossingTurn]
    exact ho _
  crossinglessComponents := l
  card_crossinglessComponents := hl

/-- Forgetting the orientation constructed by `orient` recovers `D`. -/
@[simp] theorem toPDCode_orient (D : PDCode n)
    (o : Quotient (SameCycle.setoid D.componentPerm) → Bool)
    (ho : ∀ q, o (D.componentCycleReversal q) = !o q) (l : Multiset Bool)
    (hl : l.card = D.crossinglessComponentCount) :
    (D.orient o ho l hl).toPDCode = D := (rfl)

/-- The half-edge orientation of `D.orient` evaluates the chosen orbit function on `⟦x⟧`. -/
@[simp] theorem orient_orientation (D : PDCode n)
    (o : Quotient (SameCycle.setoid D.componentPerm) → Bool)
    (ho : ∀ q, o (D.componentCycleReversal q) = !o q) (l : Multiset Bool)
    (hl : l.card = D.crossinglessComponentCount) (x : Fin (4 * n)) :
    (D.orient o ho l hl).orientation x = o ⟦x⟧ := (rfl)

/-- `D.orient` records the supplied crossing-free circle orientations. -/
@[simp] theorem orient_crossinglessComponents (D : PDCode n)
    (o : Quotient (SameCycle.setoid D.componentPerm) → Bool)
    (ho : ∀ q, o (D.componentCycleReversal q) = !o q) (l : Multiset Bool)
    (hl : l.card = D.crossinglessComponentCount) :
    (D.orient o ho l hl).crossinglessComponents = l := (rfl)

/-- **Every `PDCode` admits an orientation** with any prescribed `Multiset Bool` of orientations on
its crossing-free circles. -/
theorem exists_orientedPDCode_of_card_eq (D : PDCode n) (l : Multiset Bool)
    (hl : l.card = D.crossinglessComponentCount) :
    ∃ E : OrientedPDCode n, E.toPDCode = D ∧ E.crossinglessComponents = l := by
  classical
  let e := Fintype.equivFin (Quotient (SameCycle.setoid D.componentPerm))
  obtain ⟨hinv, hne⟩ := isPerfectMatching_iff.mp D.isPerfectMatching_componentCycleReversal
  have ho : ∀ q, decide (e (D.componentCycleReversal q) <
      e (D.componentCycleReversal (D.componentCycleReversal q))) =
        !decide (e q < e (D.componentCycleReversal q)) := fun q ↦ by
    rw [hinv q]
    have hneq : (e (D.componentCycleReversal q) : ℕ) ≠ e q :=
      Fin.val_ne_of_ne (e.injective.ne (hne q))
    cases hlt : decide (e q < e (D.componentCycleReversal q)) <;>
      simp only [Fin.lt_def, decide_eq_true_iff, decide_eq_false_iff_not,
        Bool.not_false, Bool.not_true] at hlt ⊢ <;> omega
  exact ⟨D.orient (fun q ↦ decide (e q < e (D.componentCycleReversal q))) ho l hl, rfl, rfl⟩

/-- **Every `PDCode` admits an orientation.** -/
theorem exists_orientedPDCode (D : PDCode n) : ∃ E : OrientedPDCode n, E.toPDCode = D := by
  obtain ⟨E, hE, -⟩ := D.exists_orientedPDCode_of_card_eq
    (Multiset.replicate D.crossinglessComponentCount true) (Multiset.card_replicate _ _)
  exact ⟨E, hE⟩

end TauCeti.PDCode
