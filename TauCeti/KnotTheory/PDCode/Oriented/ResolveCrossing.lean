/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.NegOnePow
public import TauCeti.KnotTheory.PDCode.Oriented.Component
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Seifert
public import TauCeti.KnotTheory.PDCode.VertexResolution
import TauCeti.GroupTheory.Perm.SwapFactors

/-!
# Orienting resolutions, component counts, and crossing changes of PD-codes

Resolving one crossing `c` of an oriented PD-code `D` produces two unoriented resolutions,
`D.toPDCode.resolveCrossing c true` and `D.toPDCode.resolveCrossing c false`. Only the coherent
smoothing — the one selected by `TauCeti.OrientedPDCode.seifertState` at `c` — joins incoming
strands to outgoing ones and therefore inherits the half-edge directions of `D`
(`TauCeti.OrientedPDCode.resolveCrossingSeifert`), while retaining explicit Boolean orientation
labels for any newly detached crossing-free circles. The other smoothing merges strands of opposite
local directions; orienting it requires choosing a direction on each of its unoriented components
(`TauCeti.PDCode.orient`), again keeping explicit Boolean labels on its crossing-free circles.

Whether the two smoothings merge or split the link components of `D` depends only on whether the
two strands meeting at `c` belong to the same component of `D`:

* if the two strands lie on different components, both smoothings merge those two components into
  one, so both resolutions have `c - 1` components
  (`TauCeti.OrientedPDCode.componentCount_resolveCrossing_add_one_of_ne`);
* if the two strands lie on the same component, the coherent smoothing splits that component in two
  (`c + 1` components, `TauCeti.OrientedPDCode.componentCount_resolveCrossing_seifertState_of_eq`)
  whereas the incoherent smoothing reconnects it into a single component (`c` components,
  `TauCeti.OrientedPDCode.componentCount_resolveCrossing_not_seifertState_of_eq`), so the two
  component counts are `{c, c + 1}`.

No planarity hypothesis is required for any of these constructions or component counts.

This file also defines the single-crossing change `TauCeti.PDCode.changeCrossing` and its oriented
lift `TauCeti.OrientedPDCode.changeCrossing`, together with the involutive `A`/`B` state bijection
`TauCeti.PDCode.changeCrossingStateEquiv` that complements the state at the changed crossing. Both
the number of `B`-smoothed crossings and the number `n₋` of negative crossings change parity by
one, while the smoothed diagrams and their circle counts are preserved.

## Main definitions

* `TauCeti.PDCode.UnorientedCrossingComponent`, `TauCeti.PDCode.UnorientedComponent`: the
  unoriented link components of a `PDCode`.
* `TauCeti.PDCode.orient`: orient a `PDCode` from a Boolean direction choice on each component,
  retaining explicit Boolean labels on the crossing-free circles.
* `TauCeti.OrientedPDCode.resolveCrossingSeifert`: the coherent smoothing of an oriented code at a
  crossing, inheriting its half-edge directions and adding explicit Boolean labels for the detached
  circles.
* `TauCeti.OrientedPDCode.resolveCrossingOriented`: orient either resolution of a crossing, using
  the inherited orientation on the coherent smoothing and a chosen component orientation on the
  other.
* `TauCeti.PDCode.changeCrossing`, `TauCeti.OrientedPDCode.changeCrossing`: switch the over- and
  under-strands at a single crossing, with state bijection
  `TauCeti.PDCode.changeCrossingStateEquiv`.

## Main results

* `TauCeti.OrientedPDCode.componentCount_resolveCrossing_add_one_of_ne`: when the strands at `c`
  lie on different components, both resolutions have one component fewer than `D`.
* `TauCeti.OrientedPDCode.componentCount_resolveCrossing_seifertState_of_eq`,
  `TauCeti.OrientedPDCode.componentCount_resolveCrossing_not_seifertState_of_eq`: when the strands
  at `c` lie on the same component, the coherent resolution has `c + 1` components and the
  incoherent resolution has `c` components.
* `TauCeti.OrientedPDCode.componentCount_resolveCrossing_dichotomy`: the combined component-count
  alternatives `{c - 1, c - 1}` or `{c, c + 1}` for the `A`- and `B`-resolutions.
* `TauCeti.PDCode.stateLoopCount_changeCrossing_changeCrossingStateEquiv`,
  `TauCeti.OrientedPDCode.negOnePow_negativeCrossingCount_changeCrossing`: the `A`/`B` state
  bijection preserves state circle counts and flips both the `B`-count parity and the `n₋` parity.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.4.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1 and
  Chapter 3.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm Finset

namespace PDCode

variable {n : ℕ}

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
  induction q using Quotient.ind with | _ x =>
    rw [componentCycleReversal_mk, unorientedCrossingComponentOfOrbit_mk,
      unorientedCrossingComponentOfOrbit_mk]
    exact Quotient.sound (Relation.EqvGen.symm (r := D.ComponentStep) _ _
      (Relation.EqvGen.rel _ _ (.inl rfl)))

/-- Two directed traversal orbits lie over the same unoriented component if and only if they are
equal or reverse to each other. -/
theorem unorientedCrossingComponentOfOrbit_eq_iff (D : PDCode n)
    {q₁ q₂ : Quotient (SameCycle.setoid D.componentPerm)} :
    D.unorientedCrossingComponentOfOrbit q₁ = D.unorientedCrossingComponentOfOrbit q₂ ↔
      q₁ = q₂ ∨ D.componentCycleReversal q₁ = q₂ := by
  induction q₁ using Quotient.ind with | _ x =>
    induction q₂ using Quotient.ind with | _ y =>
      rw [unorientedCrossingComponentOfOrbit_mk, unorientedCrossingComponentOfOrbit_mk,
        componentCycleReversal_mk, Quotient.eq]
      change Relation.EqvGen D.ComponentStep x y ↔ _
      rw [D.eqvGen_componentStep_iff, Quotient.eq, Quotient.eq]
      rfl

private theorem unorientedCrossingComponentOfOrbit_surjective (D : PDCode n) :
    Function.Surjective D.unorientedCrossingComponentOfOrbit := by
  intro C
  induction C using Quotient.ind with | _ x => exact ⟨⟦x⟧, rfl⟩

private noncomputable def orientHalfEdge (D : PDCode n) (choice : D.UnorientedComponent → Bool) :
    { ori : Fin (4 * n) → Bool //
      (∀ h, ori (D.edgePair.val h) = !ori h) ∧
        ∀ i slot,
          ori (D.halfEdge (crossingSlotEquiv n (i, oppositeCrossingSlot slot))) =
            !ori (D.halfEdge (crossingSlotEquiv n (i, slot))) } := by
  classical
  let rep : D.UnorientedCrossingComponent → Quotient (SameCycle.setoid D.componentPerm) :=
    fun C ↦ (D.unorientedCrossingComponentOfOrbit_surjective C).choose
  have hrep (C : D.UnorientedCrossingComponent) :
      D.unorientedCrossingComponentOfOrbit (rep C) = C :=
    (D.unorientedCrossingComponentOfOrbit_surjective C).choose_spec
  let orbitDir : Quotient (SameCycle.setoid D.componentPerm) → Bool := fun q ↦
    bif decide (q = rep (D.unorientedCrossingComponentOfOrbit q)) then
      choice (.inl (D.unorientedCrossingComponentOfOrbit q))
    else !choice (.inl (D.unorientedCrossingComponentOfOrbit q))
  have hpm := isPerfectMatching_iff.mp D.isPerfectMatching_componentCycleReversal
  have horbitDir (q : Quotient (SameCycle.setoid D.componentPerm)) :
      orbitDir (D.componentCycleReversal q) = !orbitDir q := by
    have hC := D.unorientedCrossingComponentOfOrbit_componentCycleReversal q
    have hne : D.componentCycleReversal q ≠ q := hpm.2 q
    have hpair : rep (D.unorientedCrossingComponentOfOrbit q) = q ∨
        D.componentCycleReversal (rep (D.unorientedCrossingComponentOfOrbit q)) = q :=
      D.unorientedCrossingComponentOfOrbit_eq_iff.mp (hrep _)
    by_cases hq : q = rep (D.unorientedCrossingComponentOfOrbit q)
    · have hτ : D.componentCycleReversal q ≠
          rep (D.unorientedCrossingComponentOfOrbit (D.componentCycleReversal q)) := by
        rw [hC, ← hq]
        exact hne
      dsimp only [orbitDir]
      rw [decide_eq_false hτ, decide_eq_true hq, Bool.cond_false, Bool.cond_true, hC]
    · have hτ : D.componentCycleReversal q =
          rep (D.unorientedCrossingComponentOfOrbit (D.componentCycleReversal q)) := by
        rw [hC]
        rcases hpair with h | h
        · exact absurd h.symm hq
        · exact (congrArg D.componentCycleReversal h).symm.trans (hpm.1 _)
      dsimp only [orbitDir]
      rw [decide_eq_true hτ, decide_eq_false hq, Bool.cond_true, Bool.cond_false, hC, Bool.not_not]
  refine ⟨fun h ↦ orbitDir ⟦h⟧, fun h ↦ ?_, fun i slot ↦ ?_⟩
  · dsimp only
    rw [← D.componentCycleReversal_mk h, horbitDir]
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
    rw [hslot, hturn, ← D.componentCycleReversal_mk, horbitDir]

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

/-- The explicit crossing-free circle labelling retained by `D.orient choice`. -/
noncomputable def orientCrossinglessLabeling (D : PDCode n)
    (choice : D.UnorientedComponent → Bool) : (D.orient choice).CrossinglessLabeling :=
  ⟨choice ∘ Sum.inr ∘ finCongr (by simp), by
    rw [← Function.comp_assoc, ← Multiset.map_map, Multiset.map_univ_val_equiv]
    exact (D.crossinglessComponents_orient choice).symm⟩

/-- Applying `orientCrossinglessLabeling` reads the supplied Boolean choice on `.inr i`. -/
@[simp] theorem orientCrossinglessLabeling_apply (D : PDCode n)
    (choice : D.UnorientedComponent → Bool)
    (i : Fin (D.orient choice).crossinglessComponentCount) :
    (D.orientCrossinglessLabeling choice).val i = choice (.inr (finCongr (by simp) i)) :=
  (rfl)

/-- Every unoriented PD-code admits an orientation. -/
theorem exists_orientedPDCode_toPDCode_eq (D : PDCode n) :
    ∃ E : OrientedPDCode n, E.toPDCode = D :=
  ⟨D.orient fun _ ↦ true, rfl⟩

/-! ### Crossing changes and the A/B state bijection -/

/-- **Crossing change.** Switch the over- and under-strands at crossing `c`, leaving all other
crossings, all arcs, and all crossing-free circles unchanged. -/
def changeCrossing (D : PDCode n) (c : Fin n) : PDCode n where
  halfEdge := D.halfEdge
  edgePair := D.edgePair
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := Function.update D.overPair c (!D.overPair c)

/-- Changing a crossing preserves the half-edge enumeration. -/
@[simp] theorem changeCrossing_halfEdge (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).halfEdge = D.halfEdge := (rfl)

/-- Changing a crossing preserves the arc pairing. -/
@[simp] theorem changeCrossing_edgePair (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).edgePair = D.edgePair := (rfl)

/-- Changing a crossing preserves the number of crossing-free circles. -/
@[simp] theorem changeCrossing_crossinglessComponentCount (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).crossinglessComponentCount = D.crossinglessComponentCount := (rfl)

/-- Changing crossing `c` complements `overPair` at `c`. -/
@[simp] theorem changeCrossing_overPair_self (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).overPair c = !D.overPair c := by
  simp [changeCrossing]

/-- Changing crossing `c` leaves `overPair` unchanged at every other crossing. -/
@[simp] theorem changeCrossing_overPair_of_ne (D : PDCode n) {c i : Fin n} (hi : i ≠ c) :
    (D.changeCrossing c).overPair i = D.overPair i := by
  simp [changeCrossing, hi]

/-- Changing a crossing preserves the half-edges at every crossing slot. -/
theorem crossing_changeCrossing (D : PDCode n) (c i : Fin n) (k : Fin 4) :
    (D.changeCrossing c).crossing i k = D.crossing i k := by
  rw [crossing_apply, crossing_apply, changeCrossing_halfEdge]

/-- Changing the same crossing twice recovers the original PD-code. -/
@[simp] theorem changeCrossing_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).changeCrossing c = D := by
  ext : 1
  · rfl
  · rfl
  · rfl
  · funext i
    by_cases hi : i = c
    · subst hi
      simp
    · simp [hi]

/-- Changing a crossing preserves the opposite-slot involution `crossingTurn`. -/
@[simp] theorem crossingTurn_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).crossingTurn = D.crossingTurn := by
  rw [crossingTurn_def, crossingTurn_def, changeCrossing_halfEdge]

/-- Changing a crossing preserves the directed component traversal permutation. -/
@[simp] theorem componentPerm_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).componentPerm = D.componentPerm := by
  rw [componentPerm_def, componentPerm_def, crossingTurn_changeCrossing, changeCrossing_edgePair]

/-- Changing a crossing preserves the number of crossing-bearing components. -/
@[simp] theorem crossingComponentCount_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).crossingComponentCount = D.crossingComponentCount := by
  rw [crossingComponentCount_def, crossingComponentCount_def, componentPerm_changeCrossing]

/-- Changing a crossing preserves the total number of link components. -/
@[simp] theorem componentCount_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).componentCount = D.componentCount := by
  rw [componentCount_eq, componentCount_eq, crossingComponentCount_changeCrossing,
    changeCrossing_crossinglessComponentCount]

/-- Changing a crossing preserves the cyclic crossing rotation. -/
@[simp] theorem crossingRotation_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).crossingRotation = D.crossingRotation := by
  rw [crossingRotation_def, crossingRotation_def, changeCrossing_halfEdge]

/-- Changing a crossing preserves the face permutation. -/
@[simp] theorem facePerm_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).facePerm = D.facePerm := by
  rw [facePerm_def, facePerm_def, changeCrossing_edgePair, crossingRotation_changeCrossing]

/-- Changing a crossing preserves the underlying ribbon-graph permutation triple. -/
@[simp] theorem toPermutationTriple_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).toPermutationTriple = D.toPermutationTriple := by
  apply PermutationTriple.ext_of_two <;> simp

/-- Changing a crossing preserves planarity. -/
@[simp] theorem isPlanar_changeCrossing (D : PDCode n) (c : Fin n) :
    (D.changeCrossing c).IsPlanar ↔ D.IsPlanar := by
  rw [isPlanar_def, isPlanar_def, toPermutationTriple_changeCrossing]

/-- **The `A`/`B` state bijection of a crossing change**: exchange the `A`- and `B`-smoothings at
crossing `c` while leaving the state unchanged at every other crossing. -/
def changeCrossingStateEquiv (c : Fin n) : Perm (Fin n → Bool) where
  toFun s := Function.update s c (!s c)
  invFun s := Function.update s c (!s c)
  left_inv s := by
    funext i
    by_cases hi : i = c
    · subst hi; simp
    · simp [hi]
  right_inv s := by
    funext i
    by_cases hi : i = c
    · subst hi; simp
    · simp [hi]

/-- At the changed crossing `c`, `changeCrossingStateEquiv` complements the state value. -/
@[simp] theorem changeCrossingStateEquiv_apply_self (c : Fin n) (s : Fin n → Bool) :
    changeCrossingStateEquiv c s c = !s c := by
  simp [changeCrossingStateEquiv]

/-- Away from `c`, `changeCrossingStateEquiv` leaves the state value unchanged. -/
@[simp] theorem changeCrossingStateEquiv_apply_of_ne {c i : Fin n} (hi : i ≠ c)
    (s : Fin n → Bool) :
    changeCrossingStateEquiv c s i = s i := by
  simp [changeCrossingStateEquiv, hi]

/-- `changeCrossingStateEquiv` is its own inverse. -/
@[simp] theorem changeCrossingStateEquiv_symm (c : Fin n) :
    (changeCrossingStateEquiv c).symm = changeCrossingStateEquiv c := (rfl)

/-- Complementing the state at `c` selects the same local smoothings in `D.changeCrossing c` as the
original state selects in `D`. -/
@[simp] theorem smoothingChoice_changeCrossing_changeCrossingStateEquiv (D : PDCode n) (c : Fin n)
    (s : Fin n → Bool) :
    (D.changeCrossing c).smoothingChoice (changeCrossingStateEquiv c s) = D.smoothingChoice s := by
  funext i
  by_cases hi : i = c
  · subst hi
    cases hs : s i <;> simp [hs]
  · cases hs : s i <;> simp [hs, hi]

/-- The `A`/`B` state bijection preserves the smoothed traversal permutation. -/
@[simp] theorem statePerm_changeCrossing_changeCrossingStateEquiv (D : PDCode n) (c : Fin n)
    (s : Fin n → Bool) :
    (D.changeCrossing c).statePerm (changeCrossingStateEquiv c s) = D.statePerm s := by
  simp [statePerm_def, smoothingTurn_def]

/-- The `A`/`B` state bijection preserves the number of circles in every state. -/
@[simp] theorem stateLoopCount_changeCrossing_changeCrossingStateEquiv (D : PDCode n) (c : Fin n)
    (s : Fin n → Bool) :
    (D.changeCrossing c).stateLoopCount (changeCrossingStateEquiv c s) = D.stateLoopCount s := by
  simp [stateLoopCount_def]

/-- Complementing a state at `c` flips the sign `(-1) ^ |S|` of the `B`-smoothing count. -/
theorem negOnePow_card_false_changeCrossingStateEquiv (c : Fin n) (s : Fin n → Bool) :
    (#{i | changeCrossingStateEquiv c s i = false} : ℤ).negOnePow =
      -(#{i | s i = false} : ℤ).negOnePow := by
  apply Int.negOnePow_eq_neg_of_odd_sub
  have hcompl : ∀ j ∈ ({c}ᶜ : Finset (Fin n)),
      (if changeCrossingStateEquiv c s j = false then (1 : ℤ) else 0) =
        if s j = false then 1 else 0 :=
    fun j hj ↦ by rw [changeCrossingStateEquiv_apply_of_ne (by simpa using hj)]
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter, Fintype.sum_eq_add_sum_compl c,
    Fintype.sum_eq_add_sum_compl c (fun i ↦ if s i = false then (1 : ℤ) else 0),
    Finset.sum_congr rfl hcompl, add_sub_add_right_eq_sub, changeCrossingStateEquiv_apply_self]
  cases s c
  · exact ⟨-1, by decide⟩
  · exact ⟨0, by decide⟩

end PDCode

namespace OrientedPDCode

variable {n : ℕ}

/-! ### Oriented crossing changes -/

/-- **Oriented crossing change.** Switch the over- and under-strands at crossing `c` while keeping
every half-edge direction and every crossing-free component orientation unchanged. -/
def changeCrossing (D : OrientedPDCode n) (c : Fin n) : OrientedPDCode n where
  toPDCode := D.toPDCode.changeCrossing c
  orientation := D.orientation
  orientation_edgePair := D.orientation_edgePair
  orientation_oppositeCrossingSlot := D.orientation_oppositeCrossingSlot
  crossinglessComponents := D.crossinglessComponents
  card_crossinglessComponents := D.card_crossinglessComponents

/-- Forgetting orientation commutes with `changeCrossing`. -/
@[simp] theorem toPDCode_changeCrossing (D : OrientedPDCode n) (c : Fin n) :
    (D.changeCrossing c).toPDCode = D.toPDCode.changeCrossing c := (rfl)

/-- Changing an oriented crossing keeps all half-edge directions unchanged. -/
@[simp] theorem orientation_changeCrossing (D : OrientedPDCode n) (c : Fin n) :
    (D.changeCrossing c).orientation = D.orientation := (rfl)

/-- Changing an oriented crossing keeps the crossing-free component orientations unchanged. -/
@[simp] theorem crossinglessComponents_changeCrossing (D : OrientedPDCode n) (c : Fin n) :
    (D.changeCrossing c).crossinglessComponents = D.crossinglessComponents := (rfl)

/-- Changing the same oriented crossing twice recovers the original oriented PD-code. -/
@[simp] theorem changeCrossing_changeCrossing (D : OrientedPDCode n) (c : Fin n) :
    (D.changeCrossing c).changeCrossing c = D := by
  ext <;> simp

/-- Changing crossing `c` negates its crossing sign. -/
@[simp] theorem crossingSign_changeCrossing_self (D : OrientedPDCode n) (c : Fin n) :
    (D.changeCrossing c).crossingSign c = -D.crossingSign c := by
  rw [crossingSign_def, crossingSign_def]
  simp only [toPDCode_changeCrossing, PDCode.crossing_changeCrossing, orientation_changeCrossing,
    PDCode.changeCrossing_overPair_self]
  cases Bool.xor (D.orientation (D.crossing c 0)) (D.orientation (D.crossing c 1)) <;>
    cases D.overPair c <;> decide

/-- Changing crossing `c` preserves the sign of every other crossing. -/
@[simp] theorem crossingSign_changeCrossing_of_ne (D : OrientedPDCode n) {c i : Fin n}
    (hi : i ≠ c) :
    (D.changeCrossing c).crossingSign i = D.crossingSign i := by
  rw [crossingSign_def, crossingSign_def]
  simp [hi]

/-- Changing a single crossing flips the parity sign `(-1) ^ n₋` of the negative crossing count. -/
theorem negOnePow_negativeCrossingCount_changeCrossing (D : OrientedPDCode n) (c : Fin n) :
    ((D.changeCrossing c).negativeCrossingCount : ℤ).negOnePow =
      -(D.negativeCrossingCount : ℤ).negOnePow := by
  apply Int.negOnePow_eq_neg_of_odd_sub
  have hcompl : ∀ j ∈ ({c}ᶜ : Finset (Fin n)),
      (if (D.changeCrossing c).crossingSign j = -1 then (1 : ℤ) else 0) =
        if D.crossingSign j = -1 then 1 else 0 :=
    fun j hj ↦ by rw [D.crossingSign_changeCrossing_of_ne (by simpa using hj)]
  rw [negativeCrossingCount_def, negativeCrossingCount_def, Finset.natCast_card_filter,
    Finset.natCast_card_filter, Fintype.sum_eq_add_sum_compl c,
    Fintype.sum_eq_add_sum_compl c (fun i ↦ if D.crossingSign i = -1 then (1 : ℤ) else 0),
    Finset.sum_congr rfl hcompl, add_sub_add_right_eq_sub, crossingSign_changeCrossing_self]
  rcases D.crossingSign_eq_one_or_neg_one c with hc | hc <;> rw [hc]
  · exact ⟨0, by decide⟩
  · exact ⟨-1, by decide⟩

/-! ### Oriented smoothings of a crossing -/

section Smoothings

variable (D : OrientedPDCode (n + 1)) (c : Fin (n + 1))

/-- **The coherent oriented smoothing** of `D` at crossing `c`: the resolution selected by
`D.seifertState c`, inheriting the half-edge directions of `D` at all remaining crossings and
recording explicit Boolean orientation labels `detached` on the circles detached at `c`. -/
def resolveCrossingSeifert
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool) :
    OrientedPDCode n where
  toPDCode := D.toPDCode.resolveCrossing c (D.seifertState c)
  orientation y := D.orientation
    (D.crossing (c.succAbove ((PDCode.crossingSlotEquiv n).symm y).1)
      ((PDCode.crossingSlotEquiv n).symm y).2)
  orientation_edgePair := D.toPDCode.orientation_resolveCrossing_edgePair c (D.seifertState c)
    D.orientation_edgePair fun k ↦ by
      have hturn : D.crossing c
          (PDCode.slotSmoothing
            (bif D.seifertState c then D.overPair c else !D.overPair c) k) =
          D.smoothingTurn (D.smoothingChoice D.seifertState) (D.crossing c k) := by
        rw [PDCode.crossing_apply (slot := k), PDCode.smoothingTurn_crossing]
        congr 2
        cases hs : D.seifertState c <;> simp [hs]
      rw [hturn, D.orientation_smoothingTurn_seifertState]
  orientation_oppositeCrossingSlot i slot := by
    simp only [PDCode.resolveCrossing_halfEdge, Perm.one_apply, Equiv.symm_apply_apply,
      PDCode.crossing_apply]
    exact D.orientation_oppositeCrossingSlot (c.succAbove i) slot
  crossinglessComponents := D.crossinglessComponents + Finset.univ.val.map detached
  card_crossinglessComponents := by simp

/-- The underlying unoriented PD-code of `resolveCrossingSeifert` is the coherent resolution. -/
@[simp] theorem toPDCode_resolveCrossingSeifert
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool) :
    (D.resolveCrossingSeifert c detached).toPDCode =
      D.toPDCode.resolveCrossing c (D.seifertState c) :=
  (rfl)

/-- Half-edges of `resolveCrossingSeifert` inherit their orientation from `D`. -/
@[simp] theorem orientation_resolveCrossingSeifert
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool)
    (i : Fin n) (k : Fin 4) :
    (D.resolveCrossingSeifert c detached).orientation (PDCode.crossingSlotEquiv n (i, k)) =
      D.orientation (D.crossing (c.succAbove i) k) := by
  simp [resolveCrossingSeifert]

/-- The crossing-free circle orientations of `resolveCrossingSeifert` append `detached` to those of
`D`. -/
@[simp] theorem crossinglessComponents_resolveCrossingSeifert
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool) :
    (D.resolveCrossingSeifert c detached).crossinglessComponents =
      D.crossinglessComponents + Finset.univ.val.map detached :=
  (rfl)

/-- Every remaining crossing keeps its crossing sign in the coherent smoothing. -/
@[simp] theorem crossingSign_resolveCrossingSeifert
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool) (i : Fin n) :
    (D.resolveCrossingSeifert c detached).crossingSign i = D.crossingSign (c.succAbove i) := by
  rw [crossingSign_def, crossingSign_def]
  simp

/-- Combine a crossing-free circle labelling of `D` with the explicit Boolean orientation labels of
the detached circles to obtain a crossing-free labelling of
`D.resolveCrossingSeifert c detached`. -/
def resolveCrossingSeifertCrossinglessLabeling (o : D.CrossinglessLabeling)
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool) :
    (D.resolveCrossingSeifert c detached).CrossinglessLabeling :=
  let e : Fin (D.resolveCrossingSeifert c detached).crossinglessComponentCount ≃
      Fin D.crossinglessComponentCount ⊕
        Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) :=
    (finCongr (by simp)).trans finSumFinEquiv.symm
  ⟨Sum.elim o.val detached ∘ e, by
    ext b
    rw [crossinglessComponents_resolveCrossingSeifert, Multiset.count_add, ← o.occCount_val b,
      ← Function.occCount_eq_count_map_univ, ← Function.occCount_eq_count_map_univ,
      Function.occCount_eq_sum, Function.occCount_eq_sum, Function.occCount_eq_sum]
    simp only [Function.comp_apply]
    rw [e.sum_comp (fun x ↦ if Sum.elim o.val detached x = b then 1 else 0), Fintype.sum_sum_type]
    rfl⟩

/-- **Orienting either resolution of a crossing.** On the coherent smoothing `t = D.seifertState c`,
inherit the orientation of `D` and use `detached` on the newly detached circles; on the other
smoothing `t = !D.seifertState c`, orient the resolved code using `choice`. -/
noncomputable def resolveCrossingOriented (t : Bool)
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool)
    (choice : (D.toPDCode.resolveCrossing c (!D.seifertState c)).UnorientedComponent → Bool) :
    OrientedPDCode n :=
  if t = D.seifertState c then
    D.resolveCrossingSeifert c detached
  else
    (D.toPDCode.resolveCrossing c (!D.seifertState c)).orient choice

/-- Forgetting orientation after `resolveCrossingOriented` recovers `PDCode.resolveCrossing`. -/
@[simp] theorem toPDCode_resolveCrossingOriented (t : Bool)
    (detached : Fin (D.toPDCode.detachedCircleCount c (D.seifertState c)) → Bool)
    (choice : (D.toPDCode.resolveCrossing c (!D.seifertState c)).UnorientedComponent → Bool) :
    (D.resolveCrossingOriented c t detached choice).toPDCode = D.toPDCode.resolveCrossing c t := by
  rw [resolveCrossingOriented]
  split_ifs with ht
  · rw [ht, toPDCode_resolveCrossingSeifert]
  · have hnot : t = !D.seifertState c := by
      revert ht; generalize D.seifertState c = s; cases t <;> cases s <;> decide
    rw [PDCode.toPDCode_orient, hnot]

end Smoothings

/-! ### Component-count alternatives for `resolveCrossing` -/

section ComponentCount

private theorem orientation_eq_of_sameCycle (D : OrientedPDCode n)
    {τ : Perm (Fin (4 * n))} (hτ : ∀ x, D.orientation (τ x) = D.orientation x)
    {x y : Fin (4 * n)} (h : τ.SameCycle x y) : D.orientation x = D.orientation y := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Perm.mul_apply, hτ, ih]

/-- Half-edges on the same directed traversal orbit of `componentPerm` have the same orientation. -/
theorem orientation_eq_of_sameCycle_componentPerm (D : OrientedPDCode n) {x y : Fin (4 * n)}
    (h : D.toPDCode.componentPerm.SameCycle x y) : D.orientation x = D.orientation y :=
  D.orientation_eq_of_sameCycle D.orientation_componentPerm h

private theorem componentPermOutgoing_eq_subtypePerm (D : OrientedPDCode n) :
    D.componentPermOutgoing =
      D.toPDCode.componentPerm.subtypePerm (fun _ ↦ by simp only [orientation_componentPerm]) := by
  ext h
  simp

/-- Pairing both endpoints of an arc preserves whether they share a `componentPerm`-cycle. -/
private theorem sameCycle_componentPerm_edgePair_iff (D : OrientedPDCode n) {x y : Fin (4 * n)} :
    D.toPDCode.componentPerm.SameCycle (D.edgePair.val x) (D.edgePair.val y) ↔
      D.toPDCode.componentPerm.SameCycle x y := by
  rw [PDCode.componentPerm_def]
  exact D.toPDCode.isPerfectMatching_crossingTurn.involutive.sameCycle_apply_apply_iff
    D.edgePair.prop.involutive

/-- Two half-edges of the same orientation lie in one `componentPerm`-cycle if and only if they
belong to the same crossing-bearing component of `D`. -/
theorem sameCycle_componentPerm_iff_crossingComponentOfHalfEdge_eq (D : OrientedPDCode n)
    {x y : Fin (4 * n)} (hxy : D.orientation x = D.orientation y) :
    D.toPDCode.componentPerm.SameCycle x y ↔
      D.crossingComponentOfHalfEdge x = D.crossingComponentOfHalfEdge y := by
  cases hx : D.orientation x with
  | false =>
    have hy : D.orientation y = false := hxy.symm.trans hx
    rw [crossingComponentOfHalfEdge_of_incoming D x hx,
      crossingComponentOfHalfEdge_of_incoming D y hy, Quotient.eq]
    change _ ↔ D.componentPermOutgoing.SameCycle _ _
    rw [componentPermOutgoing_eq_subtypePerm, sameCycle_subtypePerm,
      sameCycle_componentPerm_edgePair_iff]
  | true =>
    have hy : D.orientation y = true := hxy.symm.trans hx
    rw [crossingComponentOfHalfEdge_of_outgoing D x hx,
      crossingComponentOfHalfEdge_of_outgoing D y hy, Quotient.eq]
    change _ ↔ D.componentPermOutgoing.SameCycle _ _
    rw [componentPermOutgoing_eq_subtypePerm, sameCycle_subtypePerm]

variable (D : OrientedPDCode (n + 1)) (c : Fin (n + 1))

/-- Under either local smoothing, the partners of slots `0` and `2` are slots `1` and `3`. -/
private theorem slotSmoothing_zero_and_two (b : Bool) :
    (PDCode.slotSmoothing b 0 = 1 ∨ PDCode.slotSmoothing b 0 = 3) ∧
      (PDCode.slotSmoothing b 2 = 1 ∨ PDCode.slotSmoothing b 2 = 3) := by
  cases b <;> simp only [PDCode.slotSmoothing_true, PDCode.slotSmoothing_false] <;> decide

private theorem crossingComponentOfHalfEdge_crossing_two :
    D.crossingComponentOfHalfEdge (D.crossing c 2) =
      D.crossingComponentOfHalfEdge (D.crossing c 0) := by
  have ht : D.crossing c 2 = D.crossingTurn (D.crossing c 0) := by
    rw [PDCode.crossing_apply (D := D.toPDCode) c 0, PDCode.crossingTurn_crossing,
      show PDCode.oppositeCrossingSlot 0 = 2 by rw [PDCode.oppositeCrossingSlot_apply]; decide]
  rw [ht, crossingComponentOfHalfEdge_crossingTurn]

/-- Both `slotSmoothing b 0` and `slotSmoothing b 2` lie on the `1`-`3` strand at `c`, so their
half-edges belong to the component of `D.crossing c 1`. -/
private theorem crossingComponentOfHalfEdge_slotSmoothing_zero_and_two (b : Bool) :
    D.crossingComponentOfHalfEdge (D.crossing c (PDCode.slotSmoothing b 0)) =
        D.crossingComponentOfHalfEdge (D.crossing c 1) ∧
      D.crossingComponentOfHalfEdge (D.crossing c (PDCode.slotSmoothing b 2)) =
        D.crossingComponentOfHalfEdge (D.crossing c 1) := by
  have h3 : D.crossingComponentOfHalfEdge (D.crossing c 3) =
      D.crossingComponentOfHalfEdge (D.crossing c 1) := by
    have ht : D.crossing c 3 = D.crossingTurn (D.crossing c 1) := by
      rw [PDCode.crossing_apply (D := D.toPDCode) c 1, PDCode.crossingTurn_crossing,
        show PDCode.oppositeCrossingSlot 1 = 3 by rw [PDCode.oppositeCrossingSlot_apply]; decide]
    rw [ht, crossingComponentOfHalfEdge_crossingTurn]
  obtain ⟨h0, h2⟩ := slotSmoothing_zero_and_two b
  refine ⟨?_, ?_⟩
  · rcases h0 with h0 | h0
    · rw [h0]
    · rw [h0]; exact h3
  · rcases h2 with h2 | h2
    · rw [h2]
    · rw [h2]; exact h3

/-- At slot level, the non-Seifert smoothing preserves the orientation of all four slots. -/
private theorem slotSmoothing_not_xor_orientation_all (p q : Bool) (k : Fin 4) :
    ![p, q, !p, !q] (PDCode.slotSmoothing (!Bool.xor p q) k) = ![p, q, !p, !q] k := by
  cases p <;> cases q <;> revert k <;>
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      PDCode.slotSmoothing_true, PDCode.slotSmoothing_false] <;> decide

/-- At crossing `c`, the local smoothing opposite to `D.seifertState c` joins half-edges of equal
orientation. -/
private theorem orientation_crossing_slotSmoothing_not_seifertState (k : Fin 4) :
    D.orientation
        (D.crossing c (PDCode.slotSmoothing
          (bif !D.seifertState c then D.overPair c else !D.overPair c) k)) =
      D.orientation (D.crossing c k) := by
  have hb : (bif !D.seifertState c then D.overPair c else !D.overPair c) =
      !Bool.xor (D.orientation (D.crossing c 0)) (D.orientation (D.crossing c 1)) := by
    have hS := D.smoothingChoice_seifertState c
    cases hs : D.seifertState c
    · rw [D.smoothingChoice_of_false hs] at hS
      simpa [hs] using congrArg Bool.not hS
    · rw [D.smoothingChoice_of_true hs] at hS
      simpa [hs] using congrArg Bool.not hS
  rw [hb, D.orientation_crossing_eq c _, D.orientation_crossing_eq c k]
  exact slotSmoothing_not_xor_orientation_all _ _ k

/-- When the two strands at `c` belong to different components, `D` has at least two components. -/
theorem two_le_componentCount_of_crossingComponentOfHalfEdge_ne
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) ≠
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    2 ≤ D.componentCount := by
  have : Nontrivial D.CrossingComponent := ⟨_, _, hc⟩
  let _ := Fintype.ofFinite D.CrossingComponent
  have hcard : 1 < Nat.card D.CrossingComponent := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  rw [card_crossingComponent] at hcard
  rw [PDCode.componentCount_eq]
  omega

open Classical in
/-- Orbit-count step for the coherent smoothing at `c`. -/
private theorem orbitCount_resolveCrossingTurn_seifertState :
    orbitCount
        (D.toPDCode.resolveCrossingTurn c (D.seifertState c) * D.edgePair.val) +
        (if D.crossingComponentOfHalfEdge (D.crossing c 0) =
            D.crossingComponentOfHalfEdge (D.crossing c 1) then 0 else 2) =
      orbitCount D.toPDCode.componentPerm +
        (if D.crossingComponentOfHalfEdge (D.crossing c 0) =
            D.crossingComponentOfHalfEdge (D.crossing c 1) then 2 else 0) := by
  set b := bif D.seifertState c then D.overPair c else !D.overPair c
  set a₁ := D.crossing c 0
  set b₁ := D.crossing c (PDCode.slotSmoothing b 2)
  set a₂ := D.crossing c 2
  set b₂ := D.crossing c (PDCode.slotSmoothing b 0)
  set σ := D.toPDCode.componentPerm
  have hfac : D.toPDCode.resolveCrossingTurn c (D.seifertState c) * D.edgePair.val =
      swap a₁ b₁ * (swap a₂ b₂ * σ) := by
    rw [PDCode.resolveCrossingTurn_eq_swap_mul_swap_mul_crossingTurn, mul_assoc, mul_assoc,
      ← PDCode.componentPerm_def]
  obtain ⟨hs0, hs2⟩ := slotSmoothing_zero_and_two b
  have ha₁b₁ : a₁ ≠ b₁ := fun h ↦ by
    have hk := (D.toPDCode.crossing_eq_crossing_iff.mp h).2
    rcases hs2 with hs2 | hs2 <;> omega
  have ha₂b₂ : a₂ ≠ b₂ := fun h ↦ by
    have hk := (D.toPDCode.crossing_eq_crossing_iff.mp h).2
    rcases hs0 with hs0 | hs0 <;> omega
  have hSori (k : Fin 4) :
      D.orientation (D.crossing c (PDCode.slotSmoothing b k)) =
        !D.orientation (D.crossing c k) := by
    have hturn : D.crossing c (PDCode.slotSmoothing b k) =
        D.smoothingTurn (D.smoothingChoice D.seifertState) (D.crossing c k) := by
      rw [PDCode.crossing_apply (slot := k), PDCode.smoothingTurn_crossing]
      congr 2
      cases hs : D.seifertState c <;> simp [b, hs]
    rw [hturn, D.orientation_smoothingTurn_seifertState]
  have hoa₂ : D.orientation a₂ = !D.orientation a₁ :=
    D.orientation_crossing_of_add_two_eq c (by decide)
  have hob₁ : D.orientation a₁ = D.orientation b₁ := by
    rw [show b₁ = _ from rfl, hSori 2, hoa₂, Bool.not_not]
  have hob₂ : D.orientation a₂ = D.orientation b₂ := by
    rw [show b₂ = _ from rfl, hSori 0, hoa₂]
  have hcomp := D.crossingComponentOfHalfEdge_slotSmoothing_zero_and_two c b
  have hca₂ : D.crossingComponentOfHalfEdge a₂ = D.crossingComponentOfHalfEdge a₁ :=
    D.crossingComponentOfHalfEdge_crossing_two c
  -- `swap a₂ b₂ * σ` preserves orientation and has the same relation on `{a₁, b₁}` as `σ`.
  have hori' (h : Fin (4 * (n + 1))) : D.orientation ((swap a₂ b₂ * σ) h) = D.orientation h := by
    rw [Perm.mul_apply, Equiv.apply_swap_eq_self hob₂, D.orientation_componentPerm]
  have hsc₁₂ : (swap a₂ b₂ * σ).SameCycle a₁ b₁ ↔ σ.SameCycle a₁ b₁ := by
    constructor
    · intro h
      rcases h.sameCycle_or_of_swap_mul with h | ⟨h1, _⟩
      · exact h
      · exfalso
        have ho : D.orientation a₁ = D.orientation a₂ :=
          h1.elim D.orientation_eq_of_sameCycle_componentPerm fun h' ↦
            (D.orientation_eq_of_sameCycle_componentPerm h').trans hob₂.symm
        rw [hoa₂] at ho
        cases D.orientation a₁ <;> simp at ho
    · intro h
      have h' : (swap a₂ b₂ * (swap a₂ b₂ * σ)).SameCycle a₁ b₁ := by rwa [swap_mul_self_mul]
      rcases h'.sameCycle_or_of_swap_mul with h' | ⟨h1, _⟩
      · exact h'
      · exfalso
        have ho : D.orientation a₁ = D.orientation a₂ :=
          h1.elim (D.orientation_eq_of_sameCycle hori') fun h2 ↦
            (D.orientation_eq_of_sameCycle hori' h2).trans hob₂.symm
        rw [hoa₂] at ho
        cases D.orientation a₁ <;> simp at ho
  rw [hfac]
  by_cases hc : D.crossingComponentOfHalfEdge a₁ = D.crossingComponentOfHalfEdge (D.crossing c 1)
  · have hc₁ : σ.SameCycle a₁ b₁ :=
      (D.sameCycle_componentPerm_iff_crossingComponentOfHalfEdge_eq hob₁).mpr
        (hc.trans hcomp.2.symm)
    have hc₂ : σ.SameCycle a₂ b₂ :=
      (D.sameCycle_componentPerm_iff_crossingComponentOfHalfEdge_eq hob₂).mpr
        (hca₂.trans (hc.trans hcomp.1.symm))
    simp only [hc, ↓reduceIte]
    rw [orbitCount_swap_mul_of_sameCycle ha₁b₁ (hsc₁₂.mpr hc₁),
      orbitCount_swap_mul_of_sameCycle ha₂b₂ hc₂]
  · have hc₁ : ¬σ.SameCycle a₁ b₁ := fun h ↦ hc <|
      ((D.sameCycle_componentPerm_iff_crossingComponentOfHalfEdge_eq hob₁).mp h).trans hcomp.2
    have hc₂ : ¬σ.SameCycle a₂ b₂ := fun h ↦ hc <|
      hca₂.symm.trans <|
        ((D.sameCycle_componentPerm_iff_crossingComponentOfHalfEdge_eq hob₂).mp h).trans hcomp.1
    have hstep₁ := orbitCount_swap_mul_add_one_of_not_sameCycle (hsc₁₂.not.mpr hc₁)
    have hstep₂ := orbitCount_swap_mul_add_one_of_not_sameCycle hc₂
    simp only [hc, ↓reduceIte]
    omega

open Classical in
/-- Orbit-count step for the incoherent smoothing at `c`. -/
private theorem orbitCount_resolveCrossingTurn_not_seifertState :
    orbitCount
        (D.toPDCode.resolveCrossingTurn c (!D.seifertState c) * D.edgePair.val) +
        (if D.crossingComponentOfHalfEdge (D.crossing c 0) =
            D.crossingComponentOfHalfEdge (D.crossing c 1) then 0 else 2) =
      orbitCount D.toPDCode.componentPerm := by
  set b := bif !D.seifertState c then D.overPair c else !D.overPair c
  set a₁ := D.crossing c 0
  set b₁ := D.crossing c (PDCode.slotSmoothing b 2)
  set a₂ := D.crossing c 2
  set b₂ := D.crossing c (PDCode.slotSmoothing b 0)
  set σ := D.toPDCode.componentPerm
  have hfac : D.toPDCode.resolveCrossingTurn c (!D.seifertState c) * D.edgePair.val =
      swap a₁ b₁ * (swap a₂ b₂ * σ) := by
    rw [PDCode.resolveCrossingTurn_eq_swap_mul_swap_mul_crossingTurn, mul_assoc, mul_assoc,
      ← PDCode.componentPerm_def]
  obtain ⟨_, hs2⟩ := slotSmoothing_zero_and_two b
  have ha₁b₁ : a₁ ≠ b₁ := fun h ↦ by
    have hk := (D.toPDCode.crossing_eq_crossing_iff.mp h).2
    rcases hs2 with hs2 | hs2 <;> omega
  have hSori (k : Fin 4) :
      D.orientation (D.crossing c (PDCode.slotSmoothing b k)) = D.orientation (D.crossing c k) :=
    D.orientation_crossing_slotSmoothing_not_seifertState c k
  have hoa₂ : D.orientation a₂ = !D.orientation a₁ :=
    D.orientation_crossing_of_add_two_eq c (by decide)
  have hob₁ : D.orientation b₁ = D.orientation a₂ := hSori 2
  have hob₂ : D.orientation b₂ = D.orientation a₁ := hSori 0
  have hcomp := D.crossingComponentOfHalfEdge_slotSmoothing_zero_and_two c b
  have hca₂ : D.crossingComponentOfHalfEdge a₂ = D.crossingComponentOfHalfEdge a₁ :=
    D.crossingComponentOfHalfEdge_crossing_two c
  -- `a₂` and `b₂` have opposite orientations, so the first swap always merges their cycles.
  have hnot₂ : ¬σ.SameCycle a₂ b₂ := fun h ↦ by
    have ho := D.orientation_eq_of_sameCycle_componentPerm h
    rw [hob₂, hoa₂] at ho
    cases D.orientation a₁ <;> simp at ho
  have hstep₂ := orbitCount_swap_mul_add_one_of_not_sameCycle hnot₂
  have hab₂ : (swap a₂ b₂ * σ).SameCycle a₂ b₂ :=
    sameCycle_swap_mul_of_mem_periodicPts_of_not_sameCycle (σ.injective.mem_periodicPts b₂) hnot₂
  rw [hfac]
  by_cases hc : D.crossingComponentOfHalfEdge a₁ = D.crossingComponentOfHalfEdge (D.crossing c 1)
  · have hc₁₂ : σ.SameCycle a₁ b₂ :=
      (D.sameCycle_componentPerm_iff_crossingComponentOfHalfEdge_eq hob₂.symm).mpr
        (hc.trans hcomp.1.symm)
    have hc₂₁ : σ.SameCycle a₂ b₁ :=
      (D.sameCycle_componentPerm_iff_crossingComponentOfHalfEdge_eq hob₁.symm).mpr
        (hca₂.trans (hc.trans hcomp.2.symm))
    have hsc₁ : (swap a₂ b₂ * σ).SameCycle a₁ b₁ :=
      (hab₂.swap_mul_of_sameCycle hc₁₂).trans
        (hab₂.symm.trans (hab₂.swap_mul_of_sameCycle hc₂₁))
    simp only [hc, ↓reduceIte]
    rw [orbitCount_swap_mul_of_sameCycle ha₁b₁ hsc₁]
    omega
  · have hnot₁ : ¬(swap a₂ b₂ * σ).SameCycle a₁ b₁ := by
      intro h
      rcases h.sameCycle_or_of_swap_mul with h | ⟨h1, _⟩
      · have ho := D.orientation_eq_of_sameCycle_componentPerm h
        rw [hob₁, hoa₂] at ho
        cases D.orientation a₁ <;> simp at ho
      · rcases h1 with h1 | h1
        · have ho := D.orientation_eq_of_sameCycle_componentPerm h1
          rw [hoa₂] at ho
          cases D.orientation a₁ <;> simp at ho
        · exact hc <|
            ((D.sameCycle_componentPerm_iff_crossingComponentOfHalfEdge_eq hob₂.symm).mp h1).trans
              hcomp.1
    have hstep₁ := orbitCount_swap_mul_add_one_of_not_sameCycle hnot₁
    simp only [hc, ↓reduceIte]
    omega

/-- **Different-component resolution.** If the two strands at `c` lie on different components of
`D`, then both smoothings of `c` merge those two components and therefore have one component fewer
than `D`. -/
theorem componentCount_resolveCrossing_add_one_of_ne
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) ≠
      D.crossingComponentOfHalfEdge (D.crossing c 1)) (t : Bool) :
    (D.toPDCode.resolveCrossing c t).componentCount + 1 = D.componentCount := by
  have htwo := D.toPDCode.two_mul_componentCount_resolveCrossing c t
  obtain ⟨r, hr⟩ := D.toPDCode.even_orbitCount_componentPerm
  have hD : 2 * D.componentCount =
      orbitCount D.toPDCode.componentPerm + 2 * D.crossinglessComponentCount := by
    rw [PDCode.componentCount_eq, PDCode.crossingComponentCount_def, hr]
    omega
  by_cases ht : t = D.seifertState c
  · subst ht
    have hs := D.orbitCount_resolveCrossingTurn_seifertState c
    simp only [hc, ↓reduceIte] at hs
    omega
  · have hnot : t = !D.seifertState c := by
      revert ht; generalize D.seifertState c = s; cases t <;> cases s <;> decide
    subst hnot
    have hs := D.orbitCount_resolveCrossingTurn_not_seifertState c
    simp only [hc, ↓reduceIte] at hs
    omega

/-- Subtracted form of `componentCount_resolveCrossing_add_one_of_ne`: both smoothings at a
crossing between two distinct components have `D.componentCount - 1` components. -/
theorem componentCount_resolveCrossing_of_ne
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) ≠
      D.crossingComponentOfHalfEdge (D.crossing c 1)) (t : Bool) :
    (D.toPDCode.resolveCrossing c t).componentCount = D.componentCount - 1 := by
  have h := D.componentCount_resolveCrossing_add_one_of_ne c hc t
  omega

/-- **Same-component coherent resolution.** If the two strands at `c` belong to the same component
of `D`, then the coherent smoothing `D.seifertState c` splits that component in two, giving
`D.componentCount + 1` components. -/
theorem componentCount_resolveCrossing_seifertState_of_eq
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (D.seifertState c)).componentCount = D.componentCount + 1 := by
  have htwo := D.toPDCode.two_mul_componentCount_resolveCrossing c (D.seifertState c)
  obtain ⟨r, hr⟩ := D.toPDCode.even_orbitCount_componentPerm
  have hD : 2 * D.componentCount =
      orbitCount D.toPDCode.componentPerm + 2 * D.crossinglessComponentCount := by
    rw [PDCode.componentCount_eq, PDCode.crossingComponentCount_def, hr]
    omega
  have hs := D.orbitCount_resolveCrossingTurn_seifertState c
  simp only [hc, ↓reduceIte] at hs
  omega

/-- **Same-component incoherent resolution.** If the two strands at `c` belong to the same
component of `D`, then the incoherent smoothing `!D.seifertState c` reconnects that component into
one component, preserving `D.componentCount`. -/
theorem componentCount_resolveCrossing_not_seifertState_of_eq
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (!D.seifertState c)).componentCount = D.componentCount := by
  have htwo := D.toPDCode.two_mul_componentCount_resolveCrossing c (!D.seifertState c)
  obtain ⟨r, hr⟩ := D.toPDCode.even_orbitCount_componentPerm
  have hD : 2 * D.componentCount =
      orbitCount D.toPDCode.componentPerm + 2 * D.crossinglessComponentCount := by
    rw [PDCode.componentCount_eq, PDCode.crossingComponentCount_def, hr]
    omega
  have hs := D.orbitCount_resolveCrossingTurn_not_seifertState c
  simp only [hc, ↓reduceIte] at hs
  omega

/-- At a self-crossing of one component, the `A`- and `B`-resolutions have component counts
`{c + 1, c}` (in the order determined by `D.seifertState c`). -/
theorem componentCount_resolveCrossing_true_and_false_of_eq
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    ((D.toPDCode.resolveCrossing c true).componentCount = D.componentCount + 1 ∧
        (D.toPDCode.resolveCrossing c false).componentCount = D.componentCount) ∨
      ((D.toPDCode.resolveCrossing c true).componentCount = D.componentCount ∧
        (D.toPDCode.resolveCrossing c false).componentCount = D.componentCount + 1) := by
  have hS := D.componentCount_resolveCrossing_seifertState_of_eq c hc
  have hN := D.componentCount_resolveCrossing_not_seifertState_of_eq c hc
  cases hs : D.seifertState c
  · rw [hs] at hS hN
    exact .inr ⟨by simpa using hN, hS⟩
  · rw [hs] at hS hN
    exact .inl ⟨hS, by simpa using hN⟩

/-- **Component-count dichotomy for `resolveCrossing`.** At any crossing `c` of an oriented PD-code
`D` with `m = D.componentCount` components, either both resolutions have `m - 1` components (when
`c` joins two distinct components), or their component counts are `{m + 1, m}` (when `c` is a
self-crossing of one component). -/
theorem componentCount_resolveCrossing_dichotomy :
    ((D.toPDCode.resolveCrossing c true).componentCount + 1 = D.componentCount ∧
        (D.toPDCode.resolveCrossing c false).componentCount + 1 = D.componentCount) ∨
      ((D.toPDCode.resolveCrossing c true).componentCount = D.componentCount + 1 ∧
          (D.toPDCode.resolveCrossing c false).componentCount = D.componentCount) ∨
        ((D.toPDCode.resolveCrossing c true).componentCount = D.componentCount ∧
          (D.toPDCode.resolveCrossing c false).componentCount = D.componentCount + 1) := by
  by_cases hc : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)
  · exact .inr (D.componentCount_resolveCrossing_true_and_false_of_eq c hc)
  · exact .inl ⟨D.componentCount_resolveCrossing_add_one_of_ne c hc true,
      D.componentCount_resolveCrossing_add_one_of_ne c hc false⟩

end ComponentCount

end OrientedPDCode

end TauCeti
