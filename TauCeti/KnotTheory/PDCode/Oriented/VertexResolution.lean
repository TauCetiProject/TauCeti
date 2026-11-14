/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Oriented.Component
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Seifert
public import TauCeti.KnotTheory.PDCode.VertexResolution
import TauCeti.GroupTheory.Perm.SwapFactors

/-!
# Orientations and component counts of crossing resolutions

Resolving one crossing `c` of an oriented PD-code `D` with `n + 1` crossings produces the two
`n`-crossing codes `D.toPDCode.resolveCrossing c true` and `D.toPDCode.resolveCrossing c false`.
At the coherent smoothing `t = D.seifertState c`, the local smoothing joins incoming half-edges to
outgoing ones, so the orientations of `D` away from `c` descend directly to an oriented code
`TauCeti.OrientedPDCode.resolveCrossingCoherent D c` keeping the crossing signs of the remaining
crossings. At the opposite smoothing `!D.seifertState c`, strands are reversed along part of a
component, so the resolved diagram must be reoriented; more generally, every unoriented `PDCode`
admits a canonical choice of component orientations (`TauCeti.PDCode.orient`), because each
undirected component splits into two opposite directed orbits of `componentPerm`. Combining the two
gives `TauCeti.OrientedPDCode.resolveCrossingOriented D c t` for both `t : Bool`.

Comparing `TauCeti.PDCode.two_mul_componentCount_resolveCrossing` with `D.componentCount` through
the transposition step lemmas of `TauCeti.GroupTheory.Perm.SwapFactors` determines the component
counts of the two resolutions without any planarity assumption:

* When the two strands at `c` belong to **different** link components of `D`, both resolutions merge
  those two components into one, so both have `D.componentCount - 1` components
  (`TauCeti.OrientedPDCode.componentCount_resolveCrossing_add_one_of_ne`).
* When the two strands at `c` belong to the **same** link component of `D`, the coherent smoothing
  `D.seifertState c` splits that component in two (`D.componentCount + 1` components,
  `TauCeti.OrientedPDCode.componentCount_resolveCrossing_seifertState_of_eq`), whereas the other
  smoothing `!D.seifertState c` reconnects the component to itself (`D.componentCount` components,
  `TauCeti.OrientedPDCode.componentCount_resolveCrossing_not_seifertState_of_eq`). Consequently
  the unordered pair of component counts of the `A`- and `B`-resolutions is
  `{D.componentCount, D.componentCount + 1}`
  (`TauCeti.OrientedPDCode.componentCount_resolveCrossing_true_and_false_of_eq`).

## Main definitions

* `TauCeti.PDCode.orient`: equip every component of an unoriented PD-code with a consistent
  orientation.
* `TauCeti.OrientedPDCode.resolveCrossingCoherent`: resolve crossing `c` in the coherent direction
  `D.seifertState c`, inheriting half-edge orientations and crossing signs from `D`.
* `TauCeti.OrientedPDCode.resolveCrossingOriented`: orient either resolution `t : Bool` of
  crossing `c`, agreeing with `resolveCrossingCoherent` at `t = D.seifertState c`.

## Main results

* `TauCeti.PDCode.toPDCode_orient` and `TauCeti.PDCode.exists_toPDCode_eq`: every PD-code underlies
  an oriented PD-code.
* `TauCeti.OrientedPDCode.crossingSign_resolveCrossingCoherent`: coherent resolution preserves the
  crossing signs of the remaining crossings.
* `TauCeti.OrientedPDCode.componentCount_resolveCrossing_add_one_of_ne`: at a crossing between two
  different components, both smoothings have `c - 1` components.
* `TauCeti.OrientedPDCode.componentCount_resolveCrossing_seifertState_of_eq`,
  `TauCeti.OrientedPDCode.componentCount_resolveCrossing_not_seifertState_of_eq`, and
  `TauCeti.OrientedPDCode.componentCount_resolveCrossing_true_and_false_of_eq`: at a self-crossing
  of a component, the two smoothings have `c + 1` and `c` components.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapters 1–3.
* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §§2–3.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PDCode

variable {n : ℕ}

/-! ### Orienting an arbitrary PD-code -/

/-- The undirected step relation joining each half-edge to its arc partner and to its opposite
crossing-slot partner. -/
private abbrev UndirectedComponentStep (P : PDCode n) (x y : Fin (4 * n)) : Prop :=
  y = P.edgePair.val x ∨ y = P.crossingTurn x

/-- A chosen representative half-edge in the undirected component of `x`. -/
private noncomputable def undirectedComponentRep (P : PDCode n) (x : Fin (4 * n)) : Fin (4 * n) :=
  (⟦x⟧ : Quotient (Relation.EqvGen.setoid P.UndirectedComponentStep)).out

private theorem undirectedComponentRep_edgePair (P : PDCode n) (x : Fin (4 * n)) :
    P.undirectedComponentRep (P.edgePair.val x) = P.undirectedComponentRep x :=
  congrArg Quotient.out (Quotient.sound (.symm _ _ (.rel _ _ (Or.inl rfl))))

private theorem undirectedComponentRep_crossingTurn (P : PDCode n) (x : Fin (4 * n)) :
    P.undirectedComponentRep (P.crossingTurn x) = P.undirectedComponentRep x :=
  congrArg Quotient.out (Quotient.sound (.symm _ _ (.rel _ _ (Or.inr rfl))))

private theorem sameCycle_undirectedComponentRep_or (P : PDCode n) (x : Fin (4 * n)) :
    P.componentPerm.SameCycle (P.undirectedComponentRep x) x ∨
      P.componentPerm.SameCycle (P.edgePair.val (P.undirectedComponentRep x)) x := by
  have hout : Relation.EqvGen P.UndirectedComponentStep (P.undirectedComponentRep x) x :=
    Quotient.exact (Quotient.out_eq (⟦x⟧ : Quotient (Relation.EqvGen.setoid _)))
  rw [P.componentPerm_def]
  exact (P.isPerfectMatching_crossingTurn.involutive.eqvGen_iff_sameCycle
    P.edgePair.prop.involutive).mp hout

private theorem not_sameCycle_undirectedComponentRep_and (P : PDCode n) (x : Fin (4 * n)) :
    ¬(P.componentPerm.SameCycle (P.undirectedComponentRep x) x ∧
      P.componentPerm.SameCycle (P.edgePair.val (P.undirectedComponentRep x)) x) := by
  rintro ⟨h₁, h₂⟩
  have h := h₁.trans h₂.symm
  rw [P.componentPerm_def] at h
  exact P.isPerfectMatching_crossingTurn.not_sameCycle_self_apply P.edgePair.prop _ h

private theorem sameCycle_undirectedComponentRep_edgePair_iff (P : PDCode n) (x : Fin (4 * n)) :
    P.componentPerm.SameCycle (P.undirectedComponentRep x) (P.edgePair.val x) ↔
      ¬P.componentPerm.SameCycle (P.undirectedComponentRep x) x := by
  have hrev : P.componentPerm.SameCycle (P.undirectedComponentRep x) (P.edgePair.val x) ↔
      P.componentPerm.SameCycle (P.edgePair.val (P.undirectedComponentRep x)) x := by
    rw [P.componentPerm_def,
      ← P.isPerfectMatching_crossingTurn.involutive.sameCycle_apply_apply_iff
        P.edgePair.prop.involutive,
      P.edgePair.apply_apply]
  have hor := P.sameCycle_undirectedComponentRep_or x
  have hand := P.not_sameCycle_undirectedComponentRep_and x
  tauto

private theorem sameCycle_undirectedComponentRep_crossingTurn_iff (P : PDCode n)
    (x : Fin (4 * n)) :
    P.componentPerm.SameCycle (P.undirectedComponentRep x) (P.crossingTurn x) ↔
      ¬P.componentPerm.SameCycle (P.undirectedComponentRep x) x := by
  have hturn : P.crossingTurn x = P.componentPerm (P.edgePair.val x) := by
    simp [P.edgePair.apply_apply]
  rw [hturn, sameCycle_apply_right]
  exact P.sameCycle_undirectedComponentRep_edgePair_iff x

/-- Equip an arbitrary unoriented PD-code `P` with a consistent orientation on every component:
each undirected crossing-bearing component splits into two opposite directed orbits of
`P.componentPerm`, one of which is selected as outgoing, and crossing-free circles are oriented by
`true`. -/
noncomputable def orient (P : PDCode n) : OrientedPDCode n where
  toPDCode := P
  orientation h :=
    @decide (P.componentPerm.SameCycle (P.undirectedComponentRep h) h) (Classical.dec _)
  orientation_edgePair h := by
    classical
    simp only [undirectedComponentRep_edgePair]
    by_cases hc : P.componentPerm.SameCycle (P.undirectedComponentRep h) h
    · have hnc := (P.sameCycle_undirectedComponentRep_edgePair_iff h).not.mpr (not_not.mpr hc)
      simp [hc, hnc]
    · have hc' := (P.sameCycle_undirectedComponentRep_edgePair_iff h).mpr hc
      simp [hc, hc']
  orientation_oppositeCrossingSlot i slot := by
    classical
    have hslot : P.halfEdge (crossingSlotEquiv n (i, oppositeCrossingSlot slot)) =
        P.crossingTurn (P.halfEdge (crossingSlotEquiv n (i, slot))) := by
      rw [P.crossingTurn_crossing, P.crossing_apply]
    set h := P.halfEdge (crossingSlotEquiv n (i, slot))
    rw [hslot, undirectedComponentRep_crossingTurn]
    by_cases hc : P.componentPerm.SameCycle (P.undirectedComponentRep h) h
    · have hnc := (P.sameCycle_undirectedComponentRep_crossingTurn_iff h).not.mpr (not_not.mpr hc)
      simp [hc, hnc]
    · have hc' := (P.sameCycle_undirectedComponentRep_crossingTurn_iff h).mpr hc
      simp [hc, hc']
  crossinglessComponents := Multiset.replicate P.crossinglessComponentCount true
  card_crossinglessComponents := Multiset.card_replicate _ _

/-- Forgetting the chosen orientation of `P.orient` recovers `P`. -/
@[simp] theorem toPDCode_orient (P : PDCode n) : P.orient.toPDCode = P := (rfl)

/-- `P.orient` labels every crossing-free circle by `true`. -/
@[simp] theorem crossinglessComponents_orient (P : PDCode n) :
    P.orient.crossinglessComponents = Multiset.replicate P.crossinglessComponentCount true := (rfl)

/-- Every unoriented PD-code admits at least one compatible orientation. -/
theorem exists_toPDCode_eq (P : PDCode n) : ∃ D : OrientedPDCode n, D.toPDCode = P :=
  ⟨P.orient, rfl⟩

end PDCode

namespace OrientedPDCode

variable {n : ℕ} (D : OrientedPDCode (n + 1)) (c : Fin (n + 1))

/-! ### Coherent and general oriented vertex resolutions -/

/-- No fifth slot can avoid two disjoint local-smoothing pairs on `Fin 4`. -/
private theorem slotSmoothing_exhaust (b : Bool) (l₁ l₂ l₃ : Fin 4)
    (hl₂₁ : l₂ ≠ l₁) (hl₂S₁ : l₂ ≠ PDCode.slotSmoothing b l₁)
    (hl₃₁ : l₃ ≠ l₁) (hl₃S₁ : l₃ ≠ PDCode.slotSmoothing b l₁)
    (hl₃₂ : l₃ ≠ l₂) (hl₃S₂ : l₃ ≠ PDCode.slotSmoothing b l₂) : False := by
  have hs₁₁ := Fin.val_ne_of_ne (PDCode.slotSmoothing_ne b l₁)
  have hs₂₂ := Fin.val_ne_of_ne (PDCode.slotSmoothing_ne b l₂)
  have hs₂₁ : (PDCode.slotSmoothing b l₂).val ≠ l₁.val := Fin.val_ne_of_ne fun h ↦
    hl₂S₁ (by rw [← h, PDCode.slotSmoothing_apply_apply])
  have hs₂s₁ : (PDCode.slotSmoothing b l₂).val ≠ (PDCode.slotSmoothing b l₁).val :=
    Fin.val_ne_of_ne ((PDCode.slotSmoothing b).injective.ne hl₂₁)
  have := Fin.val_ne_of_ne hl₂₁
  have := Fin.val_ne_of_ne hl₂S₁
  have := Fin.val_ne_of_ne hl₃₁
  have := Fin.val_ne_of_ne hl₃S₁
  have := Fin.val_ne_of_ne hl₃₂
  have := Fin.val_ne_of_ne hl₃S₂
  omega

/-- At crossing `c`, the local smoothing selected by `D.seifertState c` reverses orientation. -/
private theorem orientation_crossing_slotSmoothing_seifertState (k : Fin 4) :
    D.orientation (D.crossing c
      (PDCode.slotSmoothing
        (bif D.seifertState c then D.overPair c else !D.overPair c) k)) =
      !D.orientation (D.crossing c k) := by
  have hchoice : (bif D.seifertState c then D.overPair c else !D.overPair c) =
      D.smoothingChoice D.seifertState c := by
    cases hs : D.seifertState c <;> simp [hs]
  rw [hchoice, ← D.toPDCode.smoothingTurn_crossing, ← PDCode.crossing_apply,
    D.orientation_smoothingTurn_seifertState]

/-- The half-edge orientation on `Fin (4 * n)` inherited from the crossings of `D` other than
`c`. -/
private def coherentOrientation (x : Fin (4 * n)) : Bool :=
  D.orientation (D.crossing (c.succAbove ((PDCode.crossingSlotEquiv n).symm x).1)
    ((PDCode.crossingSlotEquiv n).symm x).2)

private theorem coherentOrientation_crossingSlotEquiv (i : Fin n) (k : Fin 4) :
    D.coherentOrientation c (PDCode.crossingSlotEquiv n (i, k)) =
      D.orientation (D.crossing (c.succAbove i) k) := by
  simp [coherentOrientation]

/-- Every half-edge of `D` occupies a slot of some crossing. -/
private theorem exists_crossing_eq (h : Fin (4 * (n + 1))) :
    ∃ (j : Fin (n + 1)) (l : Fin 4), h = D.crossing j l := by
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective h
  obtain ⟨⟨j, l⟩, rfl⟩ := (PDCode.crossingSlotEquiv (n + 1)).surjective x
  exact ⟨j, l, (D.crossing_apply j l).symm⟩

/-- Following `D.edgePair` and `slotSmoothing b` from a crossing `c.succAbove i ≠ c` through `c`
twice cannot land at `c` a third time. -/
private theorem crossing_ne_of_slotSmoothing_twice {b : Bool} {i : Fin n} {k l₁ l₂ l₃ : Fin 4}
    {j₃ : Fin (n + 1)}
    (h₁ : D.edgePair.val (D.crossing (c.succAbove i) k) = D.crossing c l₁)
    (h₂ : D.edgePair.val (D.crossing c (PDCode.slotSmoothing b l₁)) = D.crossing c l₂)
    (h₃ : D.edgePair.val (D.crossing c (PDCode.slotSmoothing b l₂)) = D.crossing j₃ l₃) :
    j₃ ≠ c := by
  intro hj₃c
  subst j₃
  have hl₂₁ : l₂ ≠ l₁ := fun h ↦ by
    have := D.edgePair.val.injective (h₁.trans (h ▸ h₂.symm))
    exact c.succAbove_ne i (D.toPDCode.crossing_eq_crossing_iff.mp this).1
  have hl₂S₁ : l₂ ≠ PDCode.slotSmoothing b l₁ := fun h ↦
    D.edgePair.apply_ne _ (h ▸ h₂)
  have hl₃₁ : l₃ ≠ l₁ := fun h ↦ by
    have := (D.edgePair.apply_eq_of_apply_eq h₁).symm.trans
      (D.edgePair.apply_eq_of_apply_eq (h ▸ h₃))
    exact c.succAbove_ne i (D.toPDCode.crossing_eq_crossing_iff.mp this).1
  have hl₃S₁ : l₃ ≠ PDCode.slotSmoothing b l₁ := fun h ↦ by
    have : D.crossing c (PDCode.slotSmoothing b l₂) = D.crossing c l₂ := by
      rw [← D.edgePair.apply_apply (D.crossing c (PDCode.slotSmoothing b l₂)), h₃, h, h₂]
    exact PDCode.slotSmoothing_ne b l₂ (D.toPDCode.crossing_eq_crossing_iff.mp this).2
  have hl₃₂ : l₃ ≠ l₂ := fun h ↦ by
    have := D.edgePair.val.injective (h₂.trans (h ▸ h₃).symm)
    exact hl₂₁ ((PDCode.slotSmoothing_apply_apply b l₁ ▸
      PDCode.slotSmoothing_apply_apply b l₂ ▸
      congrArg (PDCode.slotSmoothing b)
        (D.toPDCode.crossing_eq_crossing_iff.mp this).2).symm)
  have hl₃S₂ : l₃ ≠ PDCode.slotSmoothing b l₂ := fun h ↦
    D.edgePair.apply_ne _ (h ▸ h₃)
  exact slotSmoothing_exhaust b l₁ l₂ l₃ hl₂₁ hl₂S₁ hl₃₁ hl₃S₁ hl₃₂ hl₃S₂

/-- Every arc of the coherent resolution `D.toPDCode.resolveCrossing c (D.seifertState c)` joins
half-edges of opposite `D`-orientations, whether it avoids `c` or traverses `c` once or twice. -/
private theorem coherentOrientation_edgePair (x : Fin (4 * n)) :
    D.coherentOrientation c
        ((D.toPDCode.resolveCrossing c (D.seifertState c)).edgePair.val x) =
      !D.coherentOrientation c x := by
  obtain ⟨⟨i, k⟩, rfl⟩ := (PDCode.crossingSlotEquiv n).surjective x
  set t := D.seifertState c
  set b := bif t then D.overPair c else !D.overPair c
  obtain ⟨j₁, l₁, h₁⟩ := D.exists_crossing_eq (D.edgePair.val (D.crossing (c.succAbove i) k))
  by_cases hj₁ : j₁ = c
  · subst j₁
    obtain ⟨j₂, l₂, h₂⟩ := D.exists_crossing_eq
      (D.edgePair.val (D.crossing c (PDCode.slotSmoothing b l₁)))
    by_cases hj₂ : j₂ = c
    · subst j₂
      obtain ⟨j₃, l₃, h₃⟩ := D.exists_crossing_eq
        (D.edgePair.val (D.crossing c (PDCode.slotSmoothing b l₂)))
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq
        (D.crossing_ne_of_slotSmoothing_twice c h₁ h₂ h₃)
      rw [D.toPDCode.resolveCrossing_edgePair_val_of_edgePair_val_eq_crossing_twice c t h₁ h₂ h₃,
        coherentOrientation_crossingSlotEquiv, coherentOrientation_crossingSlotEquiv,
        ← h₃, D.orientation_edgePair, D.orientation_crossing_slotSmoothing_seifertState c l₂,
        ← h₂, D.orientation_edgePair, D.orientation_crossing_slotSmoothing_seifertState c l₁,
        ← h₁, D.orientation_edgePair]
      simp
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hj₂
      rw [D.toPDCode.resolveCrossing_edgePair_val_of_edgePair_val_eq_crossing c t h₁ h₂,
        coherentOrientation_crossingSlotEquiv, coherentOrientation_crossingSlotEquiv,
        ← h₂, D.orientation_edgePair, D.orientation_crossing_slotSmoothing_seifertState c l₁,
        ← h₁, D.orientation_edgePair]
      simp
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hj₁
    rw [D.toPDCode.resolveCrossing_edgePair_val_of_edgePair_val_eq c t h₁,
      coherentOrientation_crossingSlotEquiv, coherentOrientation_crossingSlotEquiv,
      ← h₁, D.orientation_edgePair]

/-- **Coherent resolution of an oriented crossing.** Resolving crossing `c` in its Seifert direction
`D.seifertState c` preserves the orientations of all remaining half-edges and crossings, and adjoins
any detached circles with orientation `true`. -/
noncomputable def resolveCrossingCoherent : OrientedPDCode n where
  toPDCode := D.toPDCode.resolveCrossing c (D.seifertState c)
  orientation := D.coherentOrientation c
  orientation_edgePair := D.coherentOrientation_edgePair c
  orientation_oppositeCrossingSlot i slot := by
    simp only [PDCode.resolveCrossing_halfEdge, Perm.one_apply,
      coherentOrientation_crossingSlotEquiv, PDCode.crossing_apply,
      D.orientation_oppositeCrossingSlot]
  crossinglessComponents := D.crossinglessComponents +
    Multiset.replicate (D.toPDCode.detachedCircleCount c (D.seifertState c)) true
  card_crossinglessComponents := by simp

/-- Forgetting orientation on `D.resolveCrossingCoherent c` gives the Seifert resolution of `c`. -/
@[simp] theorem toPDCode_resolveCrossingCoherent :
    (D.resolveCrossingCoherent c).toPDCode =
      D.toPDCode.resolveCrossing c (D.seifertState c) := (rfl)

/-- Coherent resolution keeps the crossing-free circles of `D` and adjoins any detached circles
oriented by `true`. -/
@[simp] theorem crossinglessComponents_resolveCrossingCoherent :
    (D.resolveCrossingCoherent c).crossinglessComponents = D.crossinglessComponents +
      Multiset.replicate (D.toPDCode.detachedCircleCount c (D.seifertState c)) true := (rfl)

/-- Slot `k` of crossing `i` in `D.resolveCrossingCoherent c` keeps the orientation of slot `k` of
crossing `c.succAbove i` in `D`. -/
@[simp] theorem orientation_resolveCrossingCoherent (i : Fin n) (k : Fin 4) :
    (D.resolveCrossingCoherent c).orientation (PDCode.crossingSlotEquiv n (i, k)) =
      D.orientation (D.crossing (c.succAbove i) k) :=
  D.coherentOrientation_crossingSlotEquiv c i k

/-- **Coherent resolution preserves every remaining crossing sign.** -/
@[simp] theorem crossingSign_resolveCrossingCoherent (i : Fin n) :
    (D.resolveCrossingCoherent c).crossingSign i = D.crossingSign (c.succAbove i) := by
  simp [crossingSign_def]

/-- Coherent resolution restricts the Seifert state to the remaining crossings. -/
@[simp] theorem seifertState_resolveCrossingCoherent (i : Fin n) :
    (D.resolveCrossingCoherent c).seifertState i = D.seifertState (c.succAbove i) := by
  rw [Bool.eq_iff_iff]
  simp

/-- **Oriented crossing resolution in either direction.** At `t = D.seifertState c` this is the
coherent resolution `TauCeti.OrientedPDCode.resolveCrossingCoherent`; at the other smoothing it
equips `D.toPDCode.resolveCrossing c t` with a reorientation via `TauCeti.PDCode.orient`. -/
noncomputable def resolveCrossingOriented (t : Bool) : OrientedPDCode n where
  toPDCode := D.toPDCode.resolveCrossing c t
  orientation := if t = D.seifertState c then D.coherentOrientation c
    else (D.toPDCode.resolveCrossing c t).orient.orientation
  orientation_edgePair h := by
    split_ifs with ht
    · subst ht
      exact D.coherentOrientation_edgePair c h
    · exact (D.toPDCode.resolveCrossing c t).orient.orientation_edgePair h
  orientation_oppositeCrossingSlot i slot := by
    split_ifs with ht
    · subst ht
      exact (D.resolveCrossingCoherent c).orientation_oppositeCrossingSlot i slot
    · exact (D.toPDCode.resolveCrossing c t).orient.orientation_oppositeCrossingSlot i slot
  crossinglessComponents := D.crossinglessComponents +
    Multiset.replicate (D.toPDCode.detachedCircleCount c t) true
  card_crossinglessComponents := by simp

/-- Forgetting orientation on `D.resolveCrossingOriented c t` recovers
`D.toPDCode.resolveCrossing c t`. -/
@[simp] theorem toPDCode_resolveCrossingOriented (t : Bool) :
    (D.resolveCrossingOriented c t).toPDCode = D.toPDCode.resolveCrossing c t := (rfl)

/-- `D.resolveCrossingOriented c t` keeps the crossing-free circles of `D` and adjoins any detached
circles oriented by `true`. -/
@[simp] theorem crossinglessComponents_resolveCrossingOriented (t : Bool) :
    (D.resolveCrossingOriented c t).crossinglessComponents = D.crossinglessComponents +
      Multiset.replicate (D.toPDCode.detachedCircleCount c t) true := (rfl)

/-- At `t = D.seifertState c`, `resolveCrossingOriented` agrees with `resolveCrossingCoherent`. -/
@[simp] theorem resolveCrossingOriented_seifertState :
    D.resolveCrossingOriented c (D.seifertState c) = D.resolveCrossingCoherent c := by
  apply OrientedPDCode.ext
  · rfl
  · simp [resolveCrossingOriented, resolveCrossingCoherent]
  · rfl

/-! ### Component-count alternatives for crossing resolutions -/

/-- The outgoing slot (`0` or `2`) on the `0`–`2` local strand at a crossing, given the orientation
at slot `0`. -/
private def outSlotEven (a : Bool) : Fin 4 := bif a then 0 else 2

/-- The outgoing slot (`1` or `3`) on the `1`–`3` local strand at a crossing, given the orientation
at slot `1`. -/
private def outSlotOdd (b : Bool) : Fin 4 := bif b then 1 else 3

private theorem slotSmoothing_xor_mul_oppositeCrossingSlot (a b : Bool) :
    PDCode.slotSmoothing (Bool.xor a b) * PDCode.oppositeCrossingSlot =
      Equiv.swap (outSlotEven a) (outSlotOdd b) *
        Equiv.swap (PDCode.oppositeCrossingSlot (outSlotEven a))
          (PDCode.oppositeCrossingSlot (outSlotOdd b)) := by
  ext k
  cases a <;> cases b <;>
    simp only [outSlotEven, outSlotOdd, Bool.xor_false, Bool.xor_true, Bool.not_false,
      Bool.not_true, Bool.cond_false, Bool.cond_true, PDCode.slotSmoothing_true,
      PDCode.slotSmoothing_false, PDCode.oppositeCrossingSlot_eq_swap_mul_swap, Perm.mul_apply,
      swap_apply_def] <;>
    revert k <;> decide

private theorem slotSmoothing_not_xor_mul_oppositeCrossingSlot (a b : Bool) :
    PDCode.slotSmoothing (!Bool.xor a b) * PDCode.oppositeCrossingSlot =
      Equiv.swap (outSlotOdd b) (PDCode.oppositeCrossingSlot (outSlotEven a)) *
        Equiv.swap (outSlotEven a) (PDCode.oppositeCrossingSlot (outSlotOdd b)) := by
  ext k
  cases a <;> cases b <;>
    simp only [outSlotEven, outSlotOdd, Bool.xor_false, Bool.xor_true, Bool.not_false,
      Bool.not_true, Bool.cond_false, Bool.cond_true, PDCode.slotSmoothing_true,
      PDCode.slotSmoothing_false, PDCode.oppositeCrossingSlot_eq_swap_mul_swap, Perm.mul_apply,
      swap_apply_def] <;>
    revert k <;> decide

private theorem outSlotEven_ne_outSlotOdd (a b : Bool) : outSlotEven a ≠ outSlotOdd b := by
  revert a b
  decide

private theorem orientation_crossing_outSlotEven :
    D.orientation (D.crossing c (outSlotEven (D.orientation (D.crossing c 0)))) = true := by
  cases ho : D.orientation (D.crossing c 0)
  · rw [outSlotEven, Bool.cond_false,
      D.orientation_crossing_of_add_two_eq c (s := 0) (t := 2) rfl, ho, Bool.not_false]
  · rw [outSlotEven, Bool.cond_true, ho]

private theorem orientation_crossing_outSlotOdd :
    D.orientation (D.crossing c (outSlotOdd (D.orientation (D.crossing c 1)))) = true := by
  cases ho : D.orientation (D.crossing c 1)
  · rw [outSlotOdd, Bool.cond_false,
      D.orientation_crossing_of_add_two_eq c (s := 1) (t := 3) rfl, ho, Bool.not_false]
  · rw [outSlotOdd, Bool.cond_true, ho]

private theorem crossingComponentOfHalfEdge_outSlotEven :
    D.crossingComponentOfHalfEdge (D.crossing c (outSlotEven (D.orientation (D.crossing c 0)))) =
      D.crossingComponentOfHalfEdge (D.crossing c 0) := by
  cases ho : D.orientation (D.crossing c 0)
  · have h2 : D.crossing c 2 = D.crossingTurn (D.crossing c 0) := by
      rw [D.crossing_apply c 0, D.crossingTurn_crossing, PDCode.oppositeCrossingSlot_apply]
      rfl
    rw [outSlotEven, Bool.cond_false, h2, D.crossingComponentOfHalfEdge_crossingTurn]
  · rw [outSlotEven, Bool.cond_true]

private theorem crossingComponentOfHalfEdge_outSlotOdd :
    D.crossingComponentOfHalfEdge (D.crossing c (outSlotOdd (D.orientation (D.crossing c 1)))) =
      D.crossingComponentOfHalfEdge (D.crossing c 1) := by
  cases ho : D.orientation (D.crossing c 1)
  · have h3 : D.crossing c 3 = D.crossingTurn (D.crossing c 1) := by
      rw [D.crossing_apply c 1, D.crossingTurn_crossing, PDCode.oppositeCrossingSlot_apply]
      rfl
    rw [outSlotOdd, Bool.cond_false, h3, D.crossingComponentOfHalfEdge_crossingTurn]
  · rw [outSlotOdd, Bool.cond_true]

/-- Two half-edges in the same directed orbit of `D.toPDCode.componentPerm` have the same
orientation. -/
private theorem orientation_eq_of_sameCycle_componentPerm {x y : Fin (4 * (n + 1))}
    (h : D.toPDCode.componentPerm.SameCycle x y) : D.orientation x = D.orientation y := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Perm.mul_apply, D.orientation_componentPerm, ih]

/-- Two half-edges of opposite orientations cannot share a directed orbit of `componentPerm`. -/
private theorem not_sameCycle_componentPerm_of_orientation {x y : Fin (4 * (n + 1))}
    (hx : D.orientation x = true) (hy : D.orientation y = false) :
    ¬D.toPDCode.componentPerm.SameCycle x y := fun h ↦ by
  have := D.orientation_eq_of_sameCycle_componentPerm h
  simp [hx, hy] at this

/-- Two outgoing half-edges share a `componentPerm` orbit iff their `crossingTurn` partners do. -/
private theorem sameCycle_componentPerm_crossingTurn_iff {u₀ u₁ : Fin (4 * (n + 1))} :
    D.toPDCode.componentPerm.SameCycle (D.crossingTurn u₀) (D.crossingTurn u₁) ↔
      D.toPDCode.componentPerm.SameCycle u₀ u₁ := by
  have ht (u : Fin (4 * (n + 1))) :
      D.crossingTurn u = D.toPDCode.componentPerm (D.edgePair.val u) := by
    simp [D.edgePair.apply_apply]
  rw [ht u₀, ht u₁, sameCycle_apply_left, sameCycle_apply_right, PDCode.componentPerm_def]
  exact D.toPDCode.isPerfectMatching_crossingTurn.involutive.sameCycle_apply_apply_iff
    D.edgePair.prop.involutive

/-- A transposition of two incoming half-edges does not alter `componentPerm` orbits on outgoing
half-edges. -/
private theorem sameCycle_swap_incoming_mul_componentPerm_iff
    {v₀ v₁ u₀ u₁ : Fin (4 * (n + 1))}
    (hv₀ : D.orientation v₀ = false) (hv₁ : D.orientation v₁ = false)
    (hu₀ : D.orientation u₀ = true) :
    (Equiv.swap v₀ v₁ * D.toPDCode.componentPerm).SameCycle u₀ u₁ ↔
      D.toPDCode.componentPerm.SameCycle u₀ u₁ := by
  have hpow (k : ℕ) :
      ((Equiv.swap v₀ v₁ * D.toPDCode.componentPerm) ^ k) u₀ =
        (D.toPDCode.componentPerm ^ k) u₀ := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk_or : D.orientation ((D.toPDCode.componentPerm ^ (k + 1)) u₀) = true := by
        have hsc : D.toPDCode.componentPerm.SameCycle u₀
            ((D.toPDCode.componentPerm ^ (k + 1)) u₀) :=
          ⟨((k + 1 : ℕ) : ℤ), by rw [zpow_natCast]⟩
        exact (D.orientation_eq_of_sameCycle_componentPerm hsc).symm.trans hu₀
      have hne₀ : D.toPDCode.componentPerm ((D.toPDCode.componentPerm ^ k) u₀) ≠ v₀ := by
        intro h
        rw [← Perm.mul_apply, ← pow_succ'] at h
        simp [h, hv₀] at hk_or
      have hne₁ : D.toPDCode.componentPerm ((D.toPDCode.componentPerm ^ k) u₀) ≠ v₁ := by
        intro h
        rw [← Perm.mul_apply, ← pow_succ'] at h
        simp [h, hv₁] at hk_or
      rw [pow_succ', Perm.mul_apply, ih, Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne hne₀ hne₁, pow_succ', Perm.mul_apply]
  constructor <;> intro h
  · obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    exact ⟨(k : ℤ), by rw [zpow_natCast, hpow k]⟩
  · obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    exact ⟨(k : ℤ), by rw [zpow_natCast, hpow k]⟩

private theorem sameCycle_componentPermOutgoing_iff
    (h k : {x : Fin (4 * (n + 1)) // D.orientation x = true}) :
    D.componentPermOutgoing.SameCycle h k ↔ D.toPDCode.componentPerm.SameCycle h.val k.val := by
  have hpow (m : ℕ) : ((D.componentPermOutgoing ^ m) h).val =
      (D.toPDCode.componentPerm ^ m) h.val := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Perm.mul_apply, componentPermOutgoing_apply, Subtype.coe_mk, ih, pow_succ',
        Perm.mul_apply]
  constructor <;> intro hs
  · obtain ⟨m, rfl⟩ := hs.exists_nat_pow_eq
    exact ⟨(m : ℤ), by rw [zpow_natCast, ← hpow m]⟩
  · obtain ⟨m, hm⟩ := hs.exists_nat_pow_eq
    exact ⟨(m : ℤ), Subtype.ext (by rw [zpow_natCast, hpow m, hm])⟩

/-- The two strands at crossing `c` lie on the same component iff their outgoing half-edges lie in
the same `componentPerm` orbit. -/
private theorem crossingComponentOfHalfEdge_zero_eq_one_iff :
    D.crossingComponentOfHalfEdge (D.crossing c 0) =
        D.crossingComponentOfHalfEdge (D.crossing c 1) ↔
      D.toPDCode.componentPerm.SameCycle
        (D.crossing c (outSlotEven (D.orientation (D.crossing c 0))))
        (D.crossing c (outSlotOdd (D.orientation (D.crossing c 1)))) := by
  rw [← D.crossingComponentOfHalfEdge_outSlotEven c, ← D.crossingComponentOfHalfEdge_outSlotOdd c,
    D.crossingComponentOfHalfEdge_of_outgoing _ (D.orientation_crossing_outSlotEven c),
    D.crossingComponentOfHalfEdge_of_outgoing _ (D.orientation_crossing_outSlotOdd c),
    Quotient.eq]
  exact D.sameCycle_componentPermOutgoing_iff _ _

/-- At crossing `j`, `resolvedTurn c t * crossingTurn` acts on slot `k` by
`slotSmoothing * oppositeCrossingSlot` when `j = c` and fixes the half-edge when `j ≠ c`. -/
private theorem resolvedTurn_mul_crossingTurn_crossing (t : Bool) (j : Fin (n + 1)) (k : Fin 4) :
    (D.toPDCode.resolvedTurn c t * D.toPDCode.crossingTurn) (D.crossing j k) =
      if j = c then
        D.crossing c ((PDCode.slotSmoothing (bif t then D.overPair c else !D.overPair c) *
          PDCode.oppositeCrossingSlot) k)
      else D.crossing j k := by
  split_ifs with hj
  · subst j
    simp [Perm.mul_apply, PDCode.crossing_apply]
  · simp [Perm.mul_apply, PDCode.crossing_apply, hj]

private theorem crossing_swap_apply (j : Fin (n + 1)) (s₁ s₂ k : Fin 4) :
    Equiv.swap (D.crossing j s₁) (D.crossing j s₂) (D.crossing j k) =
      D.crossing j (Equiv.swap s₁ s₂ k) := by
  simp only [swap_apply_def, D.toPDCode.crossing_eq_crossing_iff, true_and]
  split_ifs <;> rfl

/-- At `t = D.seifertState c`, `resolvedTurn * edgePair` differs from `componentPerm` by swapping
the two outgoing half-edges at `c` and swapping the two incoming half-edges at `c`. -/
private theorem resolvedTurn_seifertState_mul_edgePair_eq :
    D.toPDCode.resolvedTurn c (D.seifertState c) * D.edgePair.val =
      Equiv.swap (D.crossing c (outSlotEven (D.orientation (D.crossing c 0))))
          (D.crossing c (outSlotOdd (D.orientation (D.crossing c 1)))) *
        (Equiv.swap (D.crossingTurn (D.crossing c (outSlotEven (D.orientation (D.crossing c 0)))))
            (D.crossingTurn (D.crossing c (outSlotOdd (D.orientation (D.crossing c 1))))) *
          D.toPDCode.componentPerm) := by
  have hturn : D.toPDCode.resolvedTurn c (D.seifertState c) * D.toPDCode.crossingTurn =
      Equiv.swap (D.crossing c (outSlotEven (D.orientation (D.crossing c 0))))
          (D.crossing c (outSlotOdd (D.orientation (D.crossing c 1)))) *
        Equiv.swap (D.crossingTurn (D.crossing c (outSlotEven (D.orientation (D.crossing c 0)))))
          (D.crossingTurn (D.crossing c (outSlotOdd (D.orientation (D.crossing c 1))))) := by
    have hchoice : (bif D.seifertState c then D.overPair c else !D.overPair c) =
        Bool.xor (D.orientation (D.crossing c 0)) (D.orientation (D.crossing c 1)) := by
      rw [← D.smoothingChoice_seifertState c]
      cases hs : D.seifertState c <;> simp [hs]
    have hct (s : Fin 4) : D.crossingTurn (D.crossing c s) =
        D.crossing c (PDCode.oppositeCrossingSlot s) := by
      rw [PDCode.crossing_apply, PDCode.crossingTurn_crossing]
    ext h
    obtain ⟨j, k, rfl⟩ := D.exists_crossing_eq h
    rw [D.resolvedTurn_mul_crossingTurn_crossing c, hchoice,
      slotSmoothing_xor_mul_oppositeCrossingSlot]
    simp only [hct]
    split_ifs with hj
    · subst j
      simp only [Perm.mul_apply]
      rw [D.crossing_swap_apply, D.crossing_swap_apply]
    · have hne (s : Fin 4) : D.crossing j k ≠ D.crossing c s := fun h ↦
        hj (D.toPDCode.crossing_eq_crossing_iff.mp h).1
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (hne _) (hne _),
        swap_apply_of_ne_of_ne (hne _) (hne _)]
  calc D.toPDCode.resolvedTurn c (D.seifertState c) * D.edgePair.val
      = (D.toPDCode.resolvedTurn c (D.seifertState c) * D.toPDCode.crossingTurn) *
          D.toPDCode.componentPerm := by
        ext h
        simp [Perm.mul_apply, PDCode.componentPerm_apply]
    _ = _ := by rw [hturn, mul_assoc]

/-- At `t = !D.seifertState c`, `resolvedTurn * edgePair` differs from `componentPerm` by two
outgoing-to-incoming transpositions at `c`. -/
private theorem resolvedTurn_not_seifertState_mul_edgePair_eq :
    D.toPDCode.resolvedTurn c (!D.seifertState c) * D.edgePair.val =
      Equiv.swap (D.crossing c (outSlotOdd (D.orientation (D.crossing c 1))))
          (D.crossingTurn (D.crossing c (outSlotEven (D.orientation (D.crossing c 0))))) *
        (Equiv.swap (D.crossing c (outSlotEven (D.orientation (D.crossing c 0))))
            (D.crossingTurn (D.crossing c (outSlotOdd (D.orientation (D.crossing c 1))))) *
          D.toPDCode.componentPerm) := by
  have hturn : D.toPDCode.resolvedTurn c (!D.seifertState c) * D.toPDCode.crossingTurn =
      Equiv.swap (D.crossing c (outSlotOdd (D.orientation (D.crossing c 1))))
          (D.crossingTurn (D.crossing c (outSlotEven (D.orientation (D.crossing c 0))))) *
        Equiv.swap (D.crossing c (outSlotEven (D.orientation (D.crossing c 0))))
          (D.crossingTurn (D.crossing c (outSlotOdd (D.orientation (D.crossing c 1))))) := by
    have hchoice : (bif !D.seifertState c then D.overPair c else !D.overPair c) =
        !Bool.xor (D.orientation (D.crossing c 0)) (D.orientation (D.crossing c 1)) := by
      rw [← D.smoothingChoice_seifertState c]
      cases hs : D.seifertState c <;> simp [hs]
    have hct (s : Fin 4) : D.crossingTurn (D.crossing c s) =
        D.crossing c (PDCode.oppositeCrossingSlot s) := by
      rw [PDCode.crossing_apply, PDCode.crossingTurn_crossing]
    ext h
    obtain ⟨j, k, rfl⟩ := D.exists_crossing_eq h
    rw [D.resolvedTurn_mul_crossingTurn_crossing c, hchoice,
      slotSmoothing_not_xor_mul_oppositeCrossingSlot]
    simp only [hct]
    split_ifs with hj
    · subst j
      simp only [Perm.mul_apply]
      rw [D.crossing_swap_apply, D.crossing_swap_apply]
    · have hne (s : Fin 4) : D.crossing j k ≠ D.crossing c s := fun h ↦
        hj (D.toPDCode.crossing_eq_crossing_iff.mp h).1
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (hne _) (hne _),
        swap_apply_of_ne_of_ne (hne _) (hne _)]
  calc D.toPDCode.resolvedTurn c (!D.seifertState c) * D.edgePair.val
      = (D.toPDCode.resolvedTurn c (!D.seifertState c) * D.toPDCode.crossingTurn) *
          D.toPDCode.componentPerm := by
        ext h
        simp [Perm.mul_apply, PDCode.componentPerm_apply]
    _ = _ := by rw [hturn, mul_assoc]

/-- **Coherent resolution of a self-crossing splits the component.** When the two strands at `c`
belong to the same component of `D`, smoothing `c` by `D.seifertState c` increases the number of
components by one. -/
theorem componentCount_resolveCrossing_seifertState_of_eq
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (D.seifertState c)).componentCount = D.componentCount + 1 := by
  have hu : D.toPDCode.componentPerm.SameCycle
      (D.crossing c (outSlotEven (D.orientation (D.crossing c 0))))
      (D.crossing c (outSlotOdd (D.orientation (D.crossing c 1)))) :=
    (D.crossingComponentOfHalfEdge_zero_eq_one_iff c).mp hc
  set u₀ := D.crossing c (outSlotEven (D.orientation (D.crossing c 0)))
  set u₁ := D.crossing c (outSlotOdd (D.orientation (D.crossing c 1)))
  have hu₀ : D.orientation u₀ = true := D.orientation_crossing_outSlotEven c
  have hu₁ : D.orientation u₁ = true := D.orientation_crossing_outSlotOdd c
  have hv₀ : D.orientation (D.crossingTurn u₀) = false := by simp [hu₀]
  have hv₁ : D.orientation (D.crossingTurn u₁) = false := by simp [hu₁]
  have hu_ne : u₀ ≠ u₁ := fun h ↦
    outSlotEven_ne_outSlotOdd _ _ (D.toPDCode.crossing_eq_crossing_iff.mp h).2
  have hv_ne : D.crossingTurn u₀ ≠ D.crossingTurn u₁ := D.toPDCode.crossingTurn.injective.ne hu_ne
  have hv : D.toPDCode.componentPerm.SameCycle (D.crossingTurn u₀) (D.crossingTurn u₁) :=
    D.sameCycle_componentPerm_crossingTurn_iff.mpr hu
  have hu' : (Equiv.swap (D.crossingTurn u₀) (D.crossingTurn u₁) *
      D.toPDCode.componentPerm).SameCycle u₀ u₁ :=
    (D.sameCycle_swap_incoming_mul_componentPerm_iff hv₀ hv₁ hu₀).mpr hu
  have htwo := D.toPDCode.two_mul_componentCount_resolveCrossing c (D.seifertState c)
  rw [D.resolvedTurn_seifertState_mul_edgePair_eq c,
    orbitCount_swap_mul_of_sameCycle hu_ne hu',
    orbitCount_swap_mul_of_sameCycle hv_ne hv] at htwo
  obtain ⟨r, hr⟩ := D.toPDCode.even_orbitCount_componentPerm
  rw [D.toPDCode.componentCount_eq, D.toPDCode.crossingComponentCount_def]
  omega

/-- **Non-coherent resolution of a self-crossing keeps the component count.** When the two strands
at `c` belong to the same component of `D`, smoothing `c` by `!D.seifertState c` reconnects that
component into one component again. -/
theorem componentCount_resolveCrossing_not_seifertState_of_eq
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (!D.seifertState c)).componentCount = D.componentCount := by
  have hu : D.toPDCode.componentPerm.SameCycle
      (D.crossing c (outSlotEven (D.orientation (D.crossing c 0))))
      (D.crossing c (outSlotOdd (D.orientation (D.crossing c 1)))) :=
    (D.crossingComponentOfHalfEdge_zero_eq_one_iff c).mp hc
  set u₀ := D.crossing c (outSlotEven (D.orientation (D.crossing c 0)))
  set u₁ := D.crossing c (outSlotOdd (D.orientation (D.crossing c 1)))
  have hu₀ : D.orientation u₀ = true := D.orientation_crossing_outSlotEven c
  have hu₁ : D.orientation u₁ = true := D.orientation_crossing_outSlotOdd c
  have hv₀ : D.orientation (D.crossingTurn u₀) = false := by simp [hu₀]
  have hv₁ : D.orientation (D.crossingTurn u₁) = false := by simp [hu₁]
  have hnot₁ : ¬D.toPDCode.componentPerm.SameCycle u₀ (D.crossingTurn u₁) :=
    D.not_sameCycle_componentPerm_of_orientation hu₀ hv₁
  have hm₁ : (Equiv.swap u₀ (D.crossingTurn u₁) * D.toPDCode.componentPerm).SameCycle
      u₀ (D.crossingTurn u₁) :=
    sameCycle_swap_mul_of_mem_periodicPts_of_not_sameCycle
      (D.toPDCode.componentPerm.injective.mem_periodicPts _) hnot₁
  have hv : D.toPDCode.componentPerm.SameCycle (D.crossingTurn u₀) (D.crossingTurn u₁) :=
    D.sameCycle_componentPerm_crossingTurn_iff.mpr hu
  have hm₂ : (Equiv.swap u₀ (D.crossingTurn u₁) * D.toPDCode.componentPerm).SameCycle
      u₁ (D.crossingTurn u₀) :=
    (hm₁.swap_mul_of_sameCycle hu.symm).trans (hm₁.trans (hm₁.swap_mul_of_sameCycle hv.symm))
  have hne₂ : u₁ ≠ D.crossingTurn u₀ := fun h ↦ by
    have := congrArg D.orientation h
    simp [hu₁, hv₀] at this
  have hstep₁ := orbitCount_swap_mul_add_one_of_not_sameCycle hnot₁
  have hstep₂ := orbitCount_swap_mul_of_sameCycle hne₂ hm₂
  have htwo := D.toPDCode.two_mul_componentCount_resolveCrossing c (!D.seifertState c)
  rw [D.resolvedTurn_not_seifertState_mul_edgePair_eq c, hstep₂] at htwo
  obtain ⟨r, hr⟩ := D.toPDCode.even_orbitCount_componentPerm
  rw [D.toPDCode.componentCount_eq, D.toPDCode.crossingComponentCount_def]
  omega

/-- **At a self-crossing, the `A`- and `B`-resolutions have component counts `c` and `c + 1`.** -/
theorem componentCount_resolveCrossing_true_and_false_of_eq
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    ((D.toPDCode.resolveCrossing c true).componentCount = D.componentCount ∧
        (D.toPDCode.resolveCrossing c false).componentCount = D.componentCount + 1) ∨
      ((D.toPDCode.resolveCrossing c true).componentCount = D.componentCount + 1 ∧
        (D.toPDCode.resolveCrossing c false).componentCount = D.componentCount) := by
  have hs := D.componentCount_resolveCrossing_seifertState_of_eq c hc
  have hns := D.componentCount_resolveCrossing_not_seifertState_of_eq c hc
  cases h : D.seifertState c
  · rw [h] at hs hns
    exact Or.inl ⟨hns, hs⟩
  · rw [h] at hs hns
    exact Or.inr ⟨hs, hns⟩

private theorem componentCount_resolveCrossing_seifertState_add_one_of_ne
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) ≠
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (D.seifertState c)).componentCount + 1 = D.componentCount := by
  have hnu : ¬D.toPDCode.componentPerm.SameCycle
      (D.crossing c (outSlotEven (D.orientation (D.crossing c 0))))
      (D.crossing c (outSlotOdd (D.orientation (D.crossing c 1)))) :=
    fun h ↦ hc ((D.crossingComponentOfHalfEdge_zero_eq_one_iff c).mpr h)
  set u₀ := D.crossing c (outSlotEven (D.orientation (D.crossing c 0)))
  set u₁ := D.crossing c (outSlotOdd (D.orientation (D.crossing c 1)))
  have hu₀ : D.orientation u₀ = true := D.orientation_crossing_outSlotEven c
  have hu₁ : D.orientation u₁ = true := D.orientation_crossing_outSlotOdd c
  have hv₀ : D.orientation (D.crossingTurn u₀) = false := by simp [hu₀]
  have hv₁ : D.orientation (D.crossingTurn u₁) = false := by simp [hu₁]
  have hnv : ¬D.toPDCode.componentPerm.SameCycle (D.crossingTurn u₀) (D.crossingTurn u₁) :=
    D.sameCycle_componentPerm_crossingTurn_iff.not.mpr hnu
  have hnu' : ¬(Equiv.swap (D.crossingTurn u₀) (D.crossingTurn u₁) *
      D.toPDCode.componentPerm).SameCycle u₀ u₁ :=
    (D.sameCycle_swap_incoming_mul_componentPerm_iff hv₀ hv₁ hu₀).not.mpr hnu
  have hstep₁ := orbitCount_swap_mul_add_one_of_not_sameCycle hnv
  have hstep₂ := orbitCount_swap_mul_add_one_of_not_sameCycle hnu'
  have horb : orbitCount (D.toPDCode.resolvedTurn c (D.seifertState c) * D.edgePair.val) + 2 =
      orbitCount D.toPDCode.componentPerm := by
    rw [D.resolvedTurn_seifertState_mul_edgePair_eq c]
    dsimp only [u₀, u₁] at hstep₁ hstep₂
    omega
  have htwo := D.toPDCode.two_mul_componentCount_resolveCrossing c (D.seifertState c)
  obtain ⟨r, hr⟩ := D.toPDCode.even_orbitCount_componentPerm
  rw [D.toPDCode.componentCount_eq, D.toPDCode.crossingComponentCount_def]
  omega

private theorem componentCount_resolveCrossing_not_seifertState_add_one_of_ne
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) ≠
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (!D.seifertState c)).componentCount + 1 = D.componentCount := by
  have hnu : ¬D.toPDCode.componentPerm.SameCycle
      (D.crossing c (outSlotEven (D.orientation (D.crossing c 0))))
      (D.crossing c (outSlotOdd (D.orientation (D.crossing c 1)))) :=
    fun h ↦ hc ((D.crossingComponentOfHalfEdge_zero_eq_one_iff c).mpr h)
  set u₀ := D.crossing c (outSlotEven (D.orientation (D.crossing c 0)))
  set u₁ := D.crossing c (outSlotOdd (D.orientation (D.crossing c 1)))
  have hu₀ : D.orientation u₀ = true := D.orientation_crossing_outSlotEven c
  have hu₁ : D.orientation u₁ = true := D.orientation_crossing_outSlotOdd c
  have hv₀ : D.orientation (D.crossingTurn u₀) = false := by simp [hu₀]
  have hv₁ : D.orientation (D.crossingTurn u₁) = false := by simp [hu₁]
  have hnot₁ : ¬D.toPDCode.componentPerm.SameCycle u₀ (D.crossingTurn u₁) :=
    D.not_sameCycle_componentPerm_of_orientation hu₀ hv₁
  have hnot₂ : ¬(Equiv.swap u₀ (D.crossingTurn u₁) * D.toPDCode.componentPerm).SameCycle
      u₁ (D.crossingTurn u₀) := by
    intro hm
    rcases hm.sameCycle_or_of_swap_mul with h1 | ⟨h2, -⟩
    · exact D.not_sameCycle_componentPerm_of_orientation hu₁ hv₀ h1
    · rcases h2 with h2a | h2b
      · exact hnu h2a.symm
      · exact D.not_sameCycle_componentPerm_of_orientation hu₁ hv₁ h2b
  have hstep₁ := orbitCount_swap_mul_add_one_of_not_sameCycle hnot₁
  have hstep₂ := orbitCount_swap_mul_add_one_of_not_sameCycle hnot₂
  have horb : orbitCount (D.toPDCode.resolvedTurn c (!D.seifertState c) * D.edgePair.val) + 2 =
      orbitCount D.toPDCode.componentPerm := by
    rw [D.resolvedTurn_not_seifertState_mul_edgePair_eq c]
    dsimp only [u₀, u₁] at hstep₁ hstep₂
    omega
  have htwo := D.toPDCode.two_mul_componentCount_resolveCrossing c (!D.seifertState c)
  obtain ⟨r, hr⟩ := D.toPDCode.even_orbitCount_componentPerm
  rw [D.toPDCode.componentCount_eq, D.toPDCode.crossingComponentCount_def]
  omega

/-- **Resolving a crossing between two different components merges them**, so both the `A`- and
`B`-resolutions have `D.componentCount - 1` components. -/
theorem componentCount_resolveCrossing_add_one_of_ne
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) ≠
      D.crossingComponentOfHalfEdge (D.crossing c 1)) (t : Bool) :
    (D.toPDCode.resolveCrossing c t).componentCount + 1 = D.componentCount := by
  by_cases ht : t = D.seifertState c
  · subst ht
    exact D.componentCount_resolveCrossing_seifertState_add_one_of_ne c hc
  · have ht' : t = !D.seifertState c := by
      revert ht
      generalize D.seifertState c = s
      cases t <;> cases s <;> decide
    subst ht'
    exact D.componentCount_resolveCrossing_not_seifertState_add_one_of_ne c hc

/-- Subtracted form of `TauCeti.OrientedPDCode.componentCount_resolveCrossing_add_one_of_ne`. -/
theorem componentCount_resolveCrossing_of_ne
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) ≠
      D.crossingComponentOfHalfEdge (D.crossing c 1)) (t : Bool) :
    (D.toPDCode.resolveCrossing c t).componentCount = D.componentCount - 1 := by
  have h := D.componentCount_resolveCrossing_add_one_of_ne c hc t
  omega

end OrientedPDCode

end TauCeti
