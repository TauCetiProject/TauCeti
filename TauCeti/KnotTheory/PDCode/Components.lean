/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Basic
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic
import TauCeti.Data.Fintype.Fiber
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.SumCongr

/-! # Components of PD-codes

The arcs of a PD-code and the local strands at its crossings determine a permutation of the
half-edge labels. Its outgoing restriction has one orbit per component meeting a crossing.
Crossing-free components remain an explicit field of `PDCode`.

The orbits of `componentPermOutgoing` correspond to the crossing-bearing components; the
unrestricted `componentPerm` preserves orientation and therefore has separate incoming and
outgoing orbits for each such component.

Quotienting by the undirected step relation `PDCode.ComponentStep` yields the unoriented
crossing-bearing components `PDCode.UnorientedCrossingComponent` and total unoriented components
`PDCode.UnorientedComponent`. Choosing an orientation bit on each unoriented component constructs
an `OrientedPDCode` via `PDCode.orient`, showing every `PDCode` admits an orientation
(`PDCode.exists_orientedPDCode_toPDCode_eq`) and every `OrientedPDCode` arises in this way
(`PDCode.exists_orient_eq`).

The traversal follows M. Mastin, *Links and Planar Diagram Codes*, Definitions 2–3.
-/

public section
namespace TauCeti
open Equiv Equiv.Perm
namespace PDCode
variable {n : ℕ}

/-- The permutation induced by moving to the opposite slot at each crossing. -/
def crossingTurn (D : PDCode n) : Equiv.Perm (Fin (4 * n)) :=
  D.halfEdge.permCongr
    ((PDCode.crossingSlotEquiv n).permCongr
      (Equiv.prodCongr (Equiv.refl (Fin n)) PDCode.oppositeCrossingSlot))

/-- The defining equation for the crossing traversal permutation. -/
theorem crossingTurn_def (D : PDCode n) :
    D.crossingTurn = D.halfEdge.permCongr
      ((crossingSlotEquiv n).permCongr
        (Equiv.prodCongr (Equiv.refl _) oppositeCrossingSlot)) := (rfl)

/-- The component traversal moves across an arc and then through a crossing. -/
def componentPerm (D : PDCode n) : Equiv.Perm (Fin (4 * n)) :=
  D.crossingTurn * D.edgePair.val

/-- The defining equation of component traversal. -/
theorem componentPerm_def (D : PDCode n) : D.componentPerm = D.crossingTurn * D.edgePair.val :=
  (rfl)

/-- Traversal pairs the arc first, then takes the opposite crossing slot. -/
@[simp] theorem componentPerm_apply (D : PDCode n) (h : Fin (4 * n)) :
    D.componentPerm h = D.crossingTurn (D.edgePair.val h) := by
  simp [componentPerm, Equiv.Perm.mul_def]

/-- Crossing turns take a crossing slot to its opposite slot. -/
@[simp] theorem crossingTurn_crossing (D : PDCode n) (i : Fin n) (slot : Fin 4) :
    D.crossingTurn (D.halfEdge (PDCode.crossingSlotEquiv n (i, slot))) =
      D.crossing i (oppositeCrossingSlot slot) := by
  simp [crossingTurn]

/-- The crossing turn is an involution. -/
@[simp] theorem crossingTurn_apply_apply (D : PDCode n) (h : Fin (4 * n)) :
    D.crossingTurn (D.crossingTurn h) = h := by
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective h
  obtain ⟨⟨i, slot⟩, rfl⟩ := (PDCode.crossingSlotEquiv n).surjective x
  simp [crossingTurn]

/-- Mirroring preserves the opposite-slot permutation. -/
@[simp] theorem crossingTurn_mirror (D : PDCode n) : D.mirror.crossingTurn = D.crossingTurn := by
  simp [crossingTurn]

/-- Mirroring preserves component traversal. -/
@[simp] theorem componentPerm_mirror (D : PDCode n) :
    D.mirror.componentPerm = D.componentPerm := by
  simp [componentPerm]

/-- Relabelling conjugates the opposite-slot permutation by the half-edge relabelling. -/
@[simp] theorem crossingTurn_relabel {m : ℕ} (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) :
    (D.relabel half cross).crossingTurn = half.permCongr D.crossingTurn := by
  ext h
  obtain ⟨x, rfl⟩ := half.surjective h
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective x
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
  have he : half (D.halfEdge (crossingSlotEquiv n (i, slot))) =
      (D.relabel half cross).halfEdge (crossingSlotEquiv m (cross i, slot)) := by
    rw [← D.crossing_apply, ← (D.relabel half cross).crossing_apply]
    simpa only [Equiv.symm_apply_apply] using (D.crossing_relabel half cross (cross i) slot).symm
  rw [he, crossingTurn_crossing, crossing_relabel]
  simp

/-- On a code `D'` with one crossing more than `D`, whose first `n` crossings keep the half-edges
of `D` and whose last crossing takes the four new half-edge positions, the crossing turn is that
of `D` together with the opposite-slot permutation of the new crossing. -/
theorem crossingTurn_eq_permCongr_sumCongr {D : PDCode n} {D' : PDCode (n + 1)}
    (hD : D'.halfEdge = (halfEdgeSuccEquiv n).permCongr (Perm.sumCongr D.halfEdge 1)) :
    D'.crossingTurn =
      (halfEdgeSuccEquiv n).permCongr (Perm.sumCongr D.crossingTurn oppositeCrossingSlot) :=
  eq_permCongr_sumCongr_of_halfEdge_eq hD (fun _ => oppositeCrossingSlot)
    D.crossingTurn_crossing D'.crossingTurn_crossing

/-- Relabelling conjugates component traversal by the half-edge relabelling. -/
@[simp] theorem componentPerm_relabel {m : ℕ} (D : PDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.relabel half cross).componentPerm = half.permCongr D.componentPerm := by
  simp [componentPerm]

/-- The number of crossing-bearing components, each represented by two directed traversal orbits.
The outgoing restriction records the directed traversal on the positively oriented
half-edges. -/
noncomputable def crossingComponentCount (D : PDCode n) : ℕ :=
  orbitCount D.componentPerm / 2

/-- Crossing traversal is a perfect matching of the half-edge labels. -/
theorem isPerfectMatching_crossingTurn (D : PDCode n) :
    IsPerfectMatching D.crossingTurn := by
  refine isPerfectMatching_iff.mpr ⟨D.crossingTurn_apply_apply, ?_⟩
  intro h hh
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective h
  obtain ⟨⟨i, slot⟩, rfl⟩ := (PDCode.crossingSlotEquiv n).surjective x
  rw [crossingTurn_crossing, crossing_apply, D.halfEdge.apply_eq_iff_eq,
    (crossingSlotEquiv n).apply_eq_iff_eq, Prod.mk.injEq] at hh
  exact Fin.oppositeCrossingSlot_ne _ hh.2

/-- The directed crossing traversal orbits come in pairs. -/
theorem even_orbitCount_componentPerm (D : PDCode n) :
    Even (orbitCount D.componentPerm) :=
  (D.isPerfectMatching_crossingTurn).even_orbitCount_mul D.edgePair.prop

/-- The number of crossing-bearing components is half the number of directed traversal orbits. -/
theorem crossingComponentCount_def (D : PDCode n) :
    D.crossingComponentCount = orbitCount D.componentPerm / 2 := (rfl)

/-- A code with a crossing has at least one crossing-bearing component. -/
theorem crossingComponentCount_pos (D : PDCode n) (hn : n ≠ 0) :
    0 < D.crossingComponentCount := by
  have hpos : 0 < orbitCount D.componentPerm := by
    let _ : Nonempty (Fin (4 * n)) := ⟨⟨0, by omega⟩⟩
    exact Equiv.Perm.orbitCount_pos D.componentPerm
  obtain ⟨k, hk⟩ := D.even_orbitCount_componentPerm
  rw [crossingComponentCount_def, hk]
  omega

/-- A code with no crossing visits has no crossing-bearing components. -/
@[simp] theorem crossingComponentCount_eq_zero (D : PDCode 0) :
    D.crossingComponentCount = 0 := by
  have h := Equiv.Perm.orbitCount_le_card D.componentPerm
  simp at h
  simp [crossingComponentCount, h]

/-- Mirroring preserves the number of crossing-bearing components. -/
@[simp] theorem crossingComponentCount_mirror (D : PDCode n) :
    D.mirror.crossingComponentCount = D.crossingComponentCount := by
  simp [crossingComponentCount]

/-- Relabelling preserves the number of crossing-bearing components. -/
@[simp] theorem crossingComponentCount_relabel {m : ℕ} (D : PDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.relabel half cross).crossingComponentCount = D.crossingComponentCount := by
  simp [crossingComponentCount]

/-- The total number of components, including crossing-free circles. -/
noncomputable abbrev componentCount (D : PDCode n) : ℕ :=
  D.crossingComponentCount + D.crossinglessComponentCount

/-- The total component count is the sum of crossing-bearing and crossing-free components. -/
theorem componentCount_eq (D : PDCode n) :
    D.componentCount = D.crossingComponentCount + D.crossinglessComponentCount := rfl

/-- Twice the total component count is the number of directed traversal orbits plus twice the
crossing-free circle count. -/
theorem two_mul_componentCount (D : PDCode n) :
    2 * D.componentCount = orbitCount D.componentPerm + 2 * D.crossinglessComponentCount := by
  obtain ⟨k, hk⟩ := D.even_orbitCount_componentPerm
  rw [componentCount_eq, crossingComponentCount_def, hk]
  omega

/-- A code with a nonzero crossing count has at least one component. -/
theorem componentCount_pos (D : PDCode n) (hn : n ≠ 0) : 0 < D.componentCount := by
  rw [componentCount_eq]
  exact Nat.lt_of_lt_of_le (D.crossingComponentCount_pos hn)
    (Nat.le_add_right _ _)

/-- Mirroring preserves the total number of components. -/
@[simp] theorem componentCount_mirror (D : PDCode n) :
    D.mirror.componentCount = D.componentCount := by
  simp [componentCount]

/-- Relabelling preserves the total number of components. -/
@[simp] theorem componentCount_relabel {m : ℕ} (D : PDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.relabel half cross).componentCount = D.componentCount := by
  simp [componentCount]

/-- Following a strand of the kink through its crossing passes to the opposite slot. -/
@[simp] theorem kink_crossingTurn (i : Fin 1) (t : Fin 4) :
    kink.crossingTurn (crossingSlotEquiv 1 (i, t))
      = crossingSlotEquiv 1 (i, oppositeCrossingSlot t) := by
  have h := kink.crossingTurn_crossing i t
  rw [kink_halfEdge] at h
  simpa using h

/-- Traversing the kink alternates its arcs with the passage to the opposite slot. -/
private theorem kink_componentPerm : kink.componentPerm = (crossingSlotEquiv 1).permCongr
    (Equiv.prodCongrRight fun _ : Fin 1 ↦ oppositeCrossingSlot * slotSmoothing true) := by
  refine Equiv.ext fun h ↦ ?_
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv 1).surjective h
  rw [componentPerm_apply, kink_edgePair_apply, kink_crossingTurn]
  simp [Equiv.Perm.mul_apply]

/-- **The kink is a diagram of a knot**: it has a single component. -/
theorem crossingComponentCount_kink : kink.crossingComponentCount = 1 := by
  have h : orbitCount kink.componentPerm = 2 := by
    rw [kink_componentPerm, Equiv.orbitCount_permCongr, orbitCount_prodCongrRight_const,
      orbitCount_oppositeCrossingSlot_mul_slotSmoothing]
    simp
  rw [crossingComponentCount_def, h]

/-! ### Unoriented components and orienting a PD-code -/

/-- The relation joining a half-edge `x` to the other end `D.edgePair.val x` of its arc and to the
opposite slot `D.crossingTurn x` across its crossing. Its equivalence classes are the unoriented
components of `D` that meet a crossing. -/
abbrev ComponentStep (D : PDCode n) (x y : Fin (4 * n)) : Prop :=
  y = D.edgePair.val x ∨ y = D.crossingTurn x

/-- Two half-edges lie on the same unoriented component of `D` exactly when the second lies on the
directed traversal orbit of the first, or on that of the other end of its arc. -/
theorem eqvGen_componentStep_iff (D : PDCode n) {x y : Fin (4 * n)} :
    Relation.EqvGen D.ComponentStep x y ↔
      D.componentPerm.SameCycle x y ∨ D.componentPerm.SameCycle (D.edgePair.val x) y := by
  rw [componentPerm_def]
  exact D.isPerfectMatching_crossingTurn.involutive.eqvGen_iff_sameCycle D.edgePair.prop.involutive

/-- Lying on the same unoriented component of `D` is decidable. -/
instance (D : PDCode n) : DecidableRel (Relation.EqvGen D.ComponentStep) :=
  fun _ _ ↦ decidable_of_iff _ D.eqvGen_componentStep_iff.symm

/-- The unoriented link components of `D` that meet at least one crossing. -/
abbrev UnorientedCrossingComponent (D : PDCode n) : Type :=
  Quotient (Relation.EqvGen.setoid D.ComponentStep)

instance (D : PDCode n) : DecidableEq D.UnorientedCrossingComponent :=
  @Quotient.decidableEq _ _ (inferInstanceAs (DecidableRel (Relation.EqvGen D.ComponentStep)))

instance (D : PDCode n) : Fintype D.UnorientedCrossingComponent :=
  @Quotient.fintype _ _ _ (inferInstanceAs (DecidableRel (Relation.EqvGen D.ComponentStep)))

namespace UnorientedCrossingComponent

variable {D : PDCode n}

/-- Two half-edges represent the same unoriented crossing-bearing component if and only if the
second lies on the directed traversal orbit of the first, or on that of the other end of its arc. -/
theorem mk_eq_mk_iff {x y : Fin (4 * n)} :
    (⟦x⟧ : D.UnorientedCrossingComponent) = ⟦y⟧ ↔
      D.componentPerm.SameCycle x y ∨ D.componentPerm.SameCycle (D.edgePair.val x) y :=
  Quotient.eq.trans D.eqvGen_componentStep_iff

/-- Paired arc ends belong to the same unoriented crossing-bearing component. -/
@[simp] theorem mk_edgePair (x : Fin (4 * n)) :
    (⟦D.edgePair.val x⟧ : D.UnorientedCrossingComponent) = ⟦x⟧ :=
  Quotient.sound (.symm _ _ (.rel _ _ (.inl rfl)))

/-- Opposite crossing slots belong to the same unoriented crossing-bearing component. -/
@[simp] theorem mk_crossingTurn (x : Fin (4 * n)) :
    (⟦D.crossingTurn x⟧ : D.UnorientedCrossingComponent) = ⟦x⟧ :=
  Quotient.sound (.symm _ _ (.rel _ _ (.inr rfl)))

end UnorientedCrossingComponent

/-- All unoriented link components of `D`: the components meeting a crossing together with one
explicit label for each crossing-free circle. -/
abbrev UnorientedComponent (D : PDCode n) : Type :=
  D.UnorientedCrossingComponent ⊕ Fin D.crossinglessComponentCount

/-- Each unoriented crossing-bearing component carries two directed traversal orbits. -/
theorem two_mul_card_unorientedCrossingComponent (D : PDCode n) :
    2 * Fintype.card D.UnorientedCrossingComponent = orbitCount D.componentPerm := by
  rw [componentPerm_def, Fintype.card_eq_nat_card]
  exact D.isPerfectMatching_crossingTurn.two_mul_card_quotient_eqvGen D.edgePair.prop

/-- There are `D.crossingComponentCount` unoriented crossing-bearing components. -/
@[simp] theorem card_unorientedCrossingComponent (D : PDCode n) :
    Fintype.card D.UnorientedCrossingComponent = D.crossingComponentCount := by
  have h := D.two_mul_card_unorientedCrossingComponent
  rw [crossingComponentCount_def]
  omega

/-- There are `D.componentCount` unoriented components in total. -/
theorem card_unorientedComponent (D : PDCode n) :
    Fintype.card D.UnorientedComponent = D.componentCount := by
  simp [UnorientedComponent, componentCount_eq]

/-- Identify the orbits of `D.crossingTurn * D.edgePair.val` with those of `D.componentPerm`. -/
private def componentOrbitEquiv (D : PDCode n) :
    Quotient (SameCycle.setoid (D.crossingTurn * D.edgePair.val)) ≃
      Quotient (SameCycle.setoid D.componentPerm) :=
  Quotient.congr (Equiv.refl _) fun _ _ ↦ by rw [componentPerm_def]; rfl

private theorem componentOrbitEquiv_mk (D : PDCode n) (x : Fin (4 * n)) :
    D.componentOrbitEquiv ⟦x⟧ = ⟦x⟧ :=
  rfl

private theorem componentOrbitEquiv_symm_mk (D : PDCode n) (x : Fin (4 * n)) :
    D.componentOrbitEquiv.symm ⟦x⟧ = ⟦x⟧ :=
  (Equiv.symm_apply_eq _).mpr rfl

/-- Reversal of the directed component traversal orbits of `D`, sending the orbit of a half-edge to
that of the opposite end of its arc. -/
def componentCycleReversal (D : PDCode n) :
    Perm (Quotient (SameCycle.setoid D.componentPerm)) :=
  D.componentOrbitEquiv.permCongr
    (D.isPerfectMatching_crossingTurn.involutive.cycleReversal D.edgePair.apply_apply)

/-- Reversal sends the directed component orbit of `x` to that of `D.edgePair.val x`. -/
@[simp] theorem componentCycleReversal_mk (D : PDCode n) (x : Fin (4 * n)) :
    D.componentCycleReversal ⟦x⟧ = ⟦D.edgePair.val x⟧ :=
  (Equiv.permCongr_apply _ _ _).trans <|
    (congrArg _ ((congrArg _ (D.componentOrbitEquiv_symm_mk x)).trans
      (Function.Involutive.cycleReversal_mk _ _ x))).trans (D.componentOrbitEquiv_mk _)

/-- Reversal of directed component orbits is a fixed-point-free involution. -/
theorem isPerfectMatching_componentCycleReversal (D : PDCode n) :
    IsPerfectMatching D.componentCycleReversal :=
  PerfectMatching.isPerfectMatching_permCongr _
    (D.isPerfectMatching_crossingTurn.isPerfectMatching_cycleReversal D.edgePair.prop)

/-- Projection from directed traversal orbits to unoriented crossing-bearing components. -/
def unorientedCrossingComponentOfOrbit (D : PDCode n) :
    Quotient (SameCycle.setoid D.componentPerm) → D.UnorientedCrossingComponent :=
  Quotient.lift (fun x ↦ ⟦x⟧) fun _ _ h ↦ Quotient.sound (D.eqvGen_componentStep_iff.mpr (.inl h))

/-- The unoriented component of the directed traversal orbit of `x` is the class of `x`. -/
@[simp] theorem unorientedCrossingComponentOfOrbit_mk (D : PDCode n) (x : Fin (4 * n)) :
    D.unorientedCrossingComponentOfOrbit ⟦x⟧ = ⟦x⟧ :=
  (rfl)

/-- Opposite directed traversal orbits project to the same unoriented component. -/
@[simp] theorem unorientedCrossingComponentOfOrbit_componentCycleReversal (D : PDCode n)
    (q : Quotient (SameCycle.setoid D.componentPerm)) :
    D.unorientedCrossingComponentOfOrbit (D.componentCycleReversal q) =
      D.unorientedCrossingComponentOfOrbit q := by
  induction q using Quotient.ind with | _ x => simp

/-- Two directed traversal orbits lie over the same unoriented component if and only if they are
equal or reverse to each other. -/
theorem unorientedCrossingComponentOfOrbit_eq_iff (D : PDCode n)
    {q₁ q₂ : Quotient (SameCycle.setoid D.componentPerm)} :
    D.unorientedCrossingComponentOfOrbit q₁ = D.unorientedCrossingComponentOfOrbit q₂ ↔
      q₁ = q₂ ∨ D.componentCycleReversal q₁ = q₂ :=
  Quotient.inductionOn₂ q₁ q₂ fun x y ↦
    UnorientedCrossingComponent.mk_eq_mk_iff.trans <|
      or_congr (Quotient.eq (r := SameCycle.setoid D.componentPerm)).symm <|
        (Quotient.eq (r := SameCycle.setoid D.componentPerm)).symm.trans <|
          Iff.of_eq (congrArg (· = ⟦y⟧) (D.componentCycleReversal_mk x).symm)

private theorem unorientedCrossingComponentOfOrbit_surjective (D : PDCode n) :
    Function.Surjective D.unorientedCrossingComponentOfOrbit := by
  intro C
  induction C using Quotient.ind with | _ x => exact ⟨⟦x⟧, rfl⟩

private noncomputable def orientOrbitRep (D : PDCode n)
    (C : D.UnorientedCrossingComponent) : Quotient (SameCycle.setoid D.componentPerm) :=
  (D.unorientedCrossingComponentOfOrbit_surjective C).choose

private theorem unorientedCrossingComponentOfOrbit_orientOrbitRep (D : PDCode n)
    (C : D.UnorientedCrossingComponent) :
    D.unorientedCrossingComponentOfOrbit (D.orientOrbitRep C) = C :=
  (D.unorientedCrossingComponentOfOrbit_surjective C).choose_spec

private noncomputable def orientOrbitDir (D : PDCode n) (choice : D.UnorientedComponent → Bool)
    (q : Quotient (SameCycle.setoid D.componentPerm)) : Bool :=
  open Classical in
  if q = D.orientOrbitRep (D.unorientedCrossingComponentOfOrbit q) then
    choice (.inl (D.unorientedCrossingComponentOfOrbit q))
  else !choice (.inl (D.unorientedCrossingComponentOfOrbit q))

private theorem orientOrbitDir_componentCycleReversal (D : PDCode n)
    (choice : D.UnorientedComponent → Bool)
    (q : Quotient (SameCycle.setoid D.componentPerm)) :
    D.orientOrbitDir choice (D.componentCycleReversal q) = !D.orientOrbitDir choice q := by
  have hpm := isPerfectMatching_iff.mp D.isPerfectMatching_componentCycleReversal
  have hC := D.unorientedCrossingComponentOfOrbit_componentCycleReversal q
  have hne : D.componentCycleReversal q ≠ q := hpm.2 q
  have hpair : D.orientOrbitRep (D.unorientedCrossingComponentOfOrbit q) = q ∨
      D.componentCycleReversal (D.orientOrbitRep (D.unorientedCrossingComponentOfOrbit q)) = q :=
    D.unorientedCrossingComponentOfOrbit_eq_iff.mp
      (D.unorientedCrossingComponentOfOrbit_orientOrbitRep _)
  dsimp only [orientOrbitDir]
  split_ifs with h₁ h₂ h₃
  · rw [hC] at h₁
    exact absurd (h₁.trans h₂.symm) hne
  · simp [hC]
  · rw [hC]
  · rw [hC] at h₁
    rcases hpair with h | h
    · exact absurd h.symm h₃
    · exact absurd ((congrArg D.componentCycleReversal h).symm.trans (hpm.1 _)) h₁

private noncomputable def orientHalfEdge (D : PDCode n) (choice : D.UnorientedComponent → Bool) :
    { ori : Fin (4 * n) → Bool //
      (∀ h, ori (D.edgePair.val h) = !ori h) ∧
        ∀ i slot,
          ori (D.halfEdge (crossingSlotEquiv n (i, oppositeCrossingSlot slot))) =
            !ori (D.halfEdge (crossingSlotEquiv n (i, slot))) } := by
  refine ⟨fun h ↦ D.orientOrbitDir choice ⟦h⟧, fun h ↦ ?_, fun i slot ↦ ?_⟩
  · dsimp only
    rw [← D.componentCycleReversal_mk h, orientOrbitDir_componentCycleReversal]
  · dsimp only
    have hturn (h : Fin (4 * n)) :
        (⟦D.crossingTurn h⟧ : Quotient (SameCycle.setoid D.componentPerm)) =
          ⟦D.edgePair.val h⟧ := by
      have hstep : D.componentPerm (D.edgePair.val h) = D.crossingTurn h := by
        rw [componentPerm_apply, D.edgePair.apply_apply]
      rw [← hstep]
      exact Quotient.sound (sameCycle_apply_left.mpr (SameCycle.refl _ _))
    have hslot : D.halfEdge (crossingSlotEquiv n (i, oppositeCrossingSlot slot)) =
        D.crossingTurn (D.halfEdge (crossingSlotEquiv n (i, slot))) := by
      rw [crossingTurn_crossing, crossing_apply]
    rw [hslot, hturn, ← D.componentCycleReversal_mk, orientOrbitDir_componentCycleReversal]

/-- **Orienting a PD-code.** Given a Boolean orientation choice on every unoriented component of
`D` — choosing one of the two traversal directions on each crossing-bearing component and retaining
the explicit Boolean label `choice (.inr i)` on each crossing-free circle `i` — construct the
corresponding `OrientedPDCode`. -/
noncomputable def orient (D : PDCode n) (choice : D.UnorientedComponent → Bool) :
    OrientedPDCode n where
  toPDCode := D
  orientation := (D.orientHalfEdge choice).val
  orientation_edgePair := (D.orientHalfEdge choice).property.1
  orientation_oppositeCrossingSlot := (D.orientHalfEdge choice).property.2
  crossinglessComponents := Finset.univ.val.map (choice ∘ Sum.inr)
  card_crossinglessComponents := by simp

/-- Orienting a code leaves the underlying unoriented code unchanged. -/
@[simp] theorem toPDCode_orient (D : PDCode n) (choice : D.UnorientedComponent → Bool) :
    (D.orient choice).toPDCode = D :=
  (rfl)

/-- Orienting a code records the supplied Boolean labels on its crossing-free circles. -/
@[simp] theorem crossinglessComponents_orient (D : PDCode n)
    (choice : D.UnorientedComponent → Bool) :
    (D.orient choice).crossinglessComponents = Finset.univ.val.map (choice ∘ Sum.inr) :=
  (rfl)

/-- Two orientation choices give a half-edge `h` the same direction if and only if they agree on
the unoriented component `⟦h⟧` of `h`. -/
theorem orientation_orient_eq_iff (D : PDCode n)
    (choice₁ choice₂ : D.UnorientedComponent → Bool) (h : Fin (4 * n)) :
    (D.orient choice₁).orientation h = (D.orient choice₂).orientation h ↔
      choice₁ (.inl ⟦h⟧) = choice₂ (.inl ⟦h⟧) := by
  simp only [orient, orientHalfEdge, orientOrbitDir, unorientedCrossingComponentOfOrbit_mk]
  split_ifs <;> simp

/-- Two orientation choices agreeing on `⟦h⟧` assign the same direction to `h`. -/
theorem orientation_orient_of_eq (D : PDCode n)
    {choice₁ choice₂ : D.UnorientedComponent → Bool} {h : Fin (4 * n)}
    (hc : choice₁ (.inl ⟦h⟧) = choice₂ (.inl ⟦h⟧)) :
    (D.orient choice₁).orientation h = (D.orient choice₂).orientation h :=
  (D.orientation_orient_eq_iff choice₁ choice₂ h).mpr hc

/-- Two orientation choices opposite on `⟦h⟧` assign opposite directions to `h`. -/
theorem orientation_orient_of_eq_not (D : PDCode n)
    {choice₁ choice₂ : D.UnorientedComponent → Bool} {h : Fin (4 * n)}
    (hc : choice₁ (.inl ⟦h⟧) = !choice₂ (.inl ⟦h⟧)) :
    (D.orient choice₁).orientation h = !(D.orient choice₂).orientation h := by
  simp only [orient, orientHalfEdge, orientOrbitDir, unorientedCrossingComponentOfOrbit_mk, hc]
  split_ifs <;> simp

/-- Negating every component's orientation choice reverses the resulting oriented PD-code. -/
@[simp] theorem orient_not (D : PDCode n) (choice : D.UnorientedComponent → Bool) :
    (D.orient fun c ↦ !choice c) = (D.orient choice).reverse := by
  apply OrientedPDCode.ext
  · simp
  · funext h
    simpa using D.orientation_orient_of_eq_not (choice₁ := fun c ↦ !choice c) rfl
  · simp [Function.comp_def]

/-- Every unoriented PD-code admits an orientation. -/
theorem exists_orientedPDCode_toPDCode_eq (D : PDCode n) :
    ∃ E : OrientedPDCode n, E.toPDCode = D :=
  ⟨D.orient fun _ ↦ true, rfl⟩

end PDCode

namespace OrientedPDCode

/-- The crossing turn reverses the orientation of a half-edge. -/
@[simp] theorem orientation_crossingTurn (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.orientation (D.crossingTurn h) = !D.orientation h := by
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective h
  obtain ⟨i, slot, rfl⟩ := (PDCode.crossingSlotEquiv n).surjective x
  simp [PDCode.crossingTurn, Prod.map, D.orientation_oppositeCrossingSlot]

/-- The component traversal preserves the orientation of a half-edge. -/
theorem orientation_componentPerm (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.orientation (D.toPDCode.componentPerm h) = D.orientation h := by
  rw [PDCode.componentPerm_apply, orientation_crossingTurn, D.orientation_edgePair, Bool.not_not]

/-- Half-edges on the same directed traversal orbit of `componentPerm` have the same orientation. -/
theorem orientation_eq_of_sameCycle_componentPerm (D : OrientedPDCode n) {x y : Fin (4 * n)}
    (h : D.toPDCode.componentPerm.SameCycle x y) : D.orientation x = D.orientation y :=
  h.apply_eq_of_apply_eq D.orientation_componentPerm

/-- The component traversal permutation restricted to half-edges pointing away from crossings. -/
noncomputable def componentPermOutgoing (D : OrientedPDCode n) :
    Equiv.Perm {h : Fin (4 * n) // D.orientation h = true} :=
    D.toPDCode.componentPerm.subtypePerm (fun h => by
      simp only [orientation_componentPerm])

/-- There are two outgoing half-edges at every crossing. -/
theorem card_outgoingHalfEdges (D : OrientedPDCode n) :
    Fintype.card {h : Fin (4 * n) // D.orientation h = true} = 2 * n := by
  classical
  let p := fun h ↦ D.orientation h = true
  let e : {h // p h} ≃ {h // ¬p h} :=
    D.edgePair.val.subtypeEquiv (fun h ↦ by simp [p])
  have h := Fintype.card_congr (Equiv.sumCompl p)
  have he := Fintype.card_congr e
  rw [Fintype.card_sum, Fintype.card_fin] at h
  dsimp [p] at h he
  omega

/-- The identity on half-edge labels identifies outgoing half-edges before and after mirroring. -/
def mirrorOutgoingEquiv (D : OrientedPDCode n) :
    {h : Fin (4 * n) // D.orientation h = true} ≃
      {h : Fin (4 * n) // D.mirror.orientation h = true} :=
  (Equiv.refl _).subtypeEquiv fun _ => by simp

/-- The outgoing mirror equivalence preserves the underlying half-edge label. -/
@[simp] theorem mirrorOutgoingEquiv_apply (D : OrientedPDCode n)
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    (D.mirrorOutgoingEquiv h).val = h := by
  simp [mirrorOutgoingEquiv, Equiv.subtypeEquiv]

/-- The inverse outgoing mirror equivalence preserves the underlying half-edge label. -/
@[simp] theorem mirrorOutgoingEquiv_symm_apply (D : OrientedPDCode n)
    (h : {h : Fin (4 * n) // D.mirror.orientation h = true}) :
    (D.mirrorOutgoingEquiv.symm h).val = h := by
  simp [mirrorOutgoingEquiv, Equiv.subtypeEquiv]

/-- Mirroring transports the outgoing traversal along the outgoing half-edge equivalence. -/
@[simp] theorem componentPermOutgoing_mirror (D : OrientedPDCode n) :
    D.mirror.componentPermOutgoing =
      D.mirrorOutgoingEquiv.permCongr D.componentPermOutgoing := by
  apply Equiv.ext
  intro h
  apply Subtype.ext
  simp [mirrorOutgoingEquiv, componentPermOutgoing, Equiv.subtypeEquiv]

/-- Arc pairing identifies outgoing half-edges with outgoing half-edges after reversal. -/
def reverseOutgoingEquiv (D : OrientedPDCode n) :
    {h : Fin (4 * n) // D.orientation h = true} ≃
      {h : Fin (4 * n) // D.reverse.orientation h = true} :=
  D.edgePair.val.subtypeEquiv fun _ => by simp

/-- The outgoing reversal equivalence acts by arc pairing on half-edge labels. -/
@[simp] theorem reverseOutgoingEquiv_apply (D : OrientedPDCode n)
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    (D.reverseOutgoingEquiv h).val = D.edgePair.val h := by
  simp [reverseOutgoingEquiv, Equiv.subtypeEquiv]

/-- The inverse outgoing reversal equivalence acts by arc pairing. -/
@[simp] theorem reverseOutgoingEquiv_symm_apply (D : OrientedPDCode n)
    (h : {h : Fin (4 * n) // D.reverse.orientation h = true}) :
    (D.reverseOutgoingEquiv.symm h).val = D.edgePair.val h := by
  apply D.edgePair.val.injective
  simp [reverseOutgoingEquiv, Equiv.subtypeEquiv, D.edgePair.apply_apply]

/-- Inverse outgoing traversal has the same half-edge value as inverse unrestricted traversal. -/
@[simp] theorem componentPermOutgoing_symm_apply_val (D : OrientedPDCode n)
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    (D.componentPermOutgoing.symm h).val = D.toPDCode.componentPerm.symm h := by
  apply D.toPDCode.componentPerm.injective
  have hx := congrArg Subtype.val (D.componentPermOutgoing.apply_symm_apply h)
  simp only [componentPermOutgoing, Equiv.Perm.subtypePerm_apply] at hx
  rw [Equiv.apply_symm_apply]
  exact hx

/-- Reversal transports inverse outgoing traversal along the arc-pairing equivalence. -/
@[simp] theorem componentPermOutgoing_reverse (D : OrientedPDCode n) :
    D.reverse.componentPermOutgoing =
      D.reverseOutgoingEquiv.permCongr D.componentPermOutgoing⁻¹ := by
  apply Equiv.ext
  intro h
  obtain ⟨h, rfl⟩ := D.reverseOutgoingEquiv.surjective h
  apply Subtype.ext
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  simp only [componentPermOutgoing, Equiv.Perm.subtypePerm_apply, reverse_toPDCode]
  simp only [reverseOutgoingEquiv_apply]
  rw [PDCode.componentPerm_apply, D.edgePair.apply_apply]
  apply D.edgePair.val.injective
  rw [D.edgePair.apply_apply]
  have hbase : D.edgePair.val (D.crossingTurn h) =
      D.toPDCode.componentPerm.symm h := by
    apply D.toPDCode.componentPerm.injective
    simp [PDCode.componentPerm_apply, PDCode.crossingTurn_apply_apply]
  exact hbase.trans (componentPermOutgoing_symm_apply_val D h).symm

/-- Outgoing traversal has the same half-edge value as unrestricted traversal. -/
@[simp] theorem componentPermOutgoing_apply (D : OrientedPDCode n)
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    D.componentPermOutgoing h = ⟨D.toPDCode.componentPerm h, by
      exact (orientation_componentPerm D h).trans h.property⟩ := by
  simp only [componentPermOutgoing, Equiv.Perm.subtypePerm_apply]

/-- Counting outgoing traversal orbits gives the crossing-bearing component count. -/
@[simp] theorem orbitCount_componentPermOutgoing (D : OrientedPDCode n) :
    orbitCount D.componentPermOutgoing = D.toPDCode.crossingComponentCount := by
  classical
  let p := fun h => D.orientation h = true
  let incoming := D.toPDCode.componentPerm.subtypePerm (p := fun h => ¬p h)
    (fun h => by simp only [p, orientation_componentPerm])
  let e : {h // p h} ≃ {h // ¬p h} :=
    D.edgePair.val.subtypeEquiv (fun h => by simp [p])
  -- Arc pairing exchanges outgoing and incoming traversal, reversing its direction.
  have he : e.permCongr D.componentPermOutgoing = incoming⁻¹ := by
    apply Equiv.ext
    intro h
    obtain ⟨h, rfl⟩ := e.surjective h
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    apply incoming.injective
    apply Subtype.ext
    simp [e, incoming, Equiv.subtypeEquiv, componentPermOutgoing,
      PDCode.componentPerm_apply, PDCode.crossingTurn_apply_apply]
  -- Splitting by orientation accounts for every unrestricted orbit, including fixed points.
  have hsplit : D.toPDCode.componentPerm =
      (Equiv.sumCompl p).permCongr (Equiv.Perm.sumCongr D.componentPermOutgoing incoming) := by
    ext h
    by_cases hh : p h <;>
      simp [Equiv.permCongr_apply, Equiv.sumCompl_symm_apply_of_pos,
        Equiv.sumCompl_symm_apply_of_neg, hh, incoming, componentPermOutgoing]
  have hcount : orbitCount incoming = orbitCount D.componentPermOutgoing := by
    simpa using (congrArg orbitCount he).symm
  simp only [PDCode.crossingComponentCount]
  rw [hsplit, Equiv.orbitCount_permCongr,
    Equiv.Perm.orbitCount_sumCongr, hcount]
  omega

/-- Relabelling restricts to an equivalence of outgoing half-edges. -/
def relabelOutgoingEquiv {m : ℕ} (D : OrientedPDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) :
    {h : Fin (4 * n) // D.orientation h = true} ≃
      {h : Fin (4 * m) // (D.relabel half cross).orientation h = true} :=
  half.subtypeEquiv (fun h => by simp)

/-- The outgoing relabelling equivalence acts by the original half-edge permutation. -/
@[simp] theorem relabelOutgoingEquiv_apply {m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m)
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    (D.relabelOutgoingEquiv half cross h).val = half h := by
  simp [relabelOutgoingEquiv, Equiv.subtypeEquiv]

/-- The inverse outgoing relabelling equivalence acts by the inverse permutation. -/
@[simp] theorem relabelOutgoingEquiv_symm_apply {m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m)
    (h : {h : Fin (4 * m) // (D.relabel half cross).orientation h = true}) :
    ((D.relabelOutgoingEquiv half cross).symm h).val = half.symm h.val := by
  simp [relabelOutgoingEquiv, Equiv.subtypeEquiv]

/-- Relabelling transports outgoing traversal along the outgoing half-edge equivalence. -/
@[simp] theorem componentPermOutgoing_relabel {m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.relabel half cross).componentPermOutgoing =
      (D.relabelOutgoingEquiv half cross).permCongr D.componentPermOutgoing := by
  ext h
  simp [relabelOutgoingEquiv, Equiv.subtypeEquiv, PDCode.componentPerm_relabel]

end OrientedPDCode

namespace PDCode

variable {n : ℕ}

/-- Every `OrientedPDCode` with underlying unoriented code `D` arises as `D.orient choice` for
some component-wise orientation `choice`. -/
theorem exists_orient_eq {D : PDCode n} (E : OrientedPDCode n) (hE : E.toPDCode = D) :
    ∃ choice : D.UnorientedComponent → Bool, D.orient choice = E := by
  subst hE
  classical
  obtain ⟨o, ho⟩ := E.crossinglessComponents.exists_map_univ_eq
    (X := Fin E.crossinglessComponentCount) (by simp)
  let orbitOri : Quotient (SameCycle.setoid E.toPDCode.componentPerm) → Bool :=
    Quotient.lift E.orientation fun _ _ h ↦ E.orientation_eq_of_sameCycle_componentPerm h
  let choice : E.toPDCode.UnorientedComponent → Bool :=
    Sum.elim (fun C ↦ orbitOri (E.toPDCode.orientOrbitRep C)) o
  refine ⟨choice, ?_⟩
  apply OrientedPDCode.ext
  · rfl
  · funext h
    simp only [orient, orientHalfEdge, orientOrbitDir, unorientedCrossingComponentOfOrbit_mk,
      choice, Sum.elim_inl]
    split_ifs with hq
    · rw [← hq]
      rfl
    · have hpair : E.toPDCode.orientOrbitRep ⟦h⟧ = ⟦h⟧ ∨
          E.toPDCode.componentCycleReversal (E.toPDCode.orientOrbitRep ⟦h⟧) = ⟦h⟧ :=
        E.toPDCode.unorientedCrossingComponentOfOrbit_eq_iff.mp
          (E.toPDCode.unorientedCrossingComponentOfOrbit_orientOrbitRep ⟦h⟧)
      rcases hpair with h1 | h1
      · exact absurd h1.symm hq
      · have hinv :=
          (isPerfectMatching_iff.mp E.toPDCode.isPerfectMatching_componentCycleReversal).1
        have h2 : E.toPDCode.orientOrbitRep ⟦h⟧ = E.toPDCode.componentCycleReversal ⟦h⟧ :=
          (hinv _).symm.trans (congrArg E.toPDCode.componentCycleReversal h1)
        rw [h2, componentCycleReversal_mk]
        simp only [orbitOri, Quotient.lift_mk, E.orientation_edgePair, Bool.not_not]
  · simpa [choice] using ho

end PDCode
end TauCeti
