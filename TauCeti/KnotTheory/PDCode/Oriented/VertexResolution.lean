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
`TauCeti.OrientedPDCode.resolveCrossingCoherent` keeping the crossing signs of the remaining
crossings, with explicit orientation data supplied for any newly detached crossing-free circles. At
the opposite smoothing `!D.seifertState c`, strands are reversed along part of a component, so the
resolved diagram must be reoriented; every unoriented `PDCode` admits a consistent choice of
component orientations (`TauCeti.PDCode.orient`), because each undirected component splits into two
opposite directed orbits of `componentPerm`. Combining the two gives
`TauCeti.OrientedPDCode.resolveCrossingOriented` for both `t : Bool`.

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
  (`OrientedPDCode.componentCount_resolveCrossing_eq_and_eq_add_one_or_eq_add_one_and_eq_of_eq`).

## Main definitions

* `TauCeti.OrientedPDCode.resolveCrossingCoherent`: resolve crossing `c` in the coherent direction
  `D.seifertState c`, inheriting half-edge orientations and crossing signs from `D` and equipping
  any detached crossing-free circles with prescribed orientations.
* `TauCeti.OrientedPDCode.resolveCrossingOriented`: orient either resolution `t : Bool` of
  crossing `c` with prescribed orientations on detached crossing-free circles, agreeing with
  `resolveCrossingCoherent` at `t = D.seifertState c`.

## Main results

* `TauCeti.OrientedPDCode.crossingSign_resolveCrossingCoherent`,
  `TauCeti.OrientedPDCode.writhe_resolveCrossingCoherent`,
  `TauCeti.OrientedPDCode.mirror_resolveCrossingCoherent`, and
  `TauCeti.OrientedPDCode.reverse_resolveCrossingCoherent`: coherent resolution preserves the
  crossing signs of the remaining crossings, shifts writhe by `-D.crossingSign c`, and commutes
  with mirroring and orientation reversal.
* `TauCeti.OrientedPDCode.componentCount_resolveCrossing_add_one_of_ne`: at a crossing between two
  different components, both smoothings have `D.componentCount - 1` components.
* `TauCeti.OrientedPDCode.componentCount_resolveCrossing_seifertState_of_eq`,
  `TauCeti.OrientedPDCode.componentCount_resolveCrossing_not_seifertState_of_eq`, and
  `OrientedPDCode.componentCount_resolveCrossing_eq_and_eq_add_one_or_eq_add_one_and_eq_of_eq`:
  at a self-crossing of a component, the two smoothings have `D.componentCount + 1` and
  `D.componentCount` components.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapters 1–3.
* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §§2–3.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

namespace OrientedPDCode

variable {n : ℕ} (D : OrientedPDCode (n + 1)) (c : Fin (n + 1))

/-! ### Coherent and general oriented vertex resolutions -/

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
        (D.toPDCode.crossing_ne_of_slotSmoothing_twice c h₁ h₂ h₃)
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
any newly detached crossing-free circles with the prescribed orientations `detached`. -/
def resolveCrossingCoherent (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c)) :
    OrientedPDCode n where
  toPDCode := D.toPDCode.resolveCrossing c (D.seifertState c)
  orientation := D.coherentOrientation c
  orientation_edgePair := D.coherentOrientation_edgePair c
  orientation_oppositeCrossingSlot i slot := by
    simp only [PDCode.resolveCrossing_halfEdge, Perm.one_apply,
      coherentOrientation_crossingSlotEquiv, PDCode.crossing_apply,
      D.orientation_oppositeCrossingSlot]
  crossinglessComponents := D.crossinglessComponents + detached
  card_crossinglessComponents := by simp [hdetached]

/-- Forgetting orientation on `D.resolveCrossingCoherent c detached hdetached` gives the Seifert
resolution of `c`. -/
@[simp] theorem toPDCode_resolveCrossingCoherent (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c)) :
    (D.resolveCrossingCoherent c detached hdetached).toPDCode =
      D.toPDCode.resolveCrossing c (D.seifertState c) := (rfl)

/-- Coherent resolution keeps the crossing-free circles of `D` and adjoins `detached`. -/
@[simp] theorem crossinglessComponents_resolveCrossingCoherent (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c)) :
    (D.resolveCrossingCoherent c detached hdetached).crossinglessComponents =
      D.crossinglessComponents + detached := (rfl)

/-- Slot `k` of crossing `i` in `D.resolveCrossingCoherent c detached hdetached` keeps the
orientation of slot `k` of crossing `c.succAbove i` in `D`. -/
@[simp] theorem orientation_resolveCrossingCoherent (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c))
    (i : Fin n) (k : Fin 4) :
    (D.resolveCrossingCoherent c detached hdetached).orientation
        (PDCode.crossingSlotEquiv n (i, k)) =
      D.orientation (D.crossing (c.succAbove i) k) :=
  D.coherentOrientation_crossingSlotEquiv c i k

/-- **Coherent resolution preserves every remaining crossing sign.** -/
@[simp] theorem crossingSign_resolveCrossingCoherent (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c)) (i : Fin n) :
    (D.resolveCrossingCoherent c detached hdetached).crossingSign i =
      D.crossingSign (c.succAbove i) := by
  simp [crossingSign_def]

/-- Coherent resolution restricts the Seifert state to the remaining crossings. -/
@[simp] theorem seifertState_resolveCrossingCoherent (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c)) (i : Fin n) :
    (D.resolveCrossingCoherent c detached hdetached).seifertState i =
      D.seifertState (c.succAbove i) := by
  rw [Bool.eq_iff_iff]
  simp

/-- Coherent resolution subtracts the sign of the resolved crossing `c` from the writhe. -/
theorem writhe_resolveCrossingCoherent (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c)) :
    (D.resolveCrossingCoherent c detached hdetached).writhe = D.writhe - D.crossingSign c := by
  rw [writhe_def, writhe_def, Fin.sum_univ_succAbove _ c]
  simp

/-- Coherent resolution of a positive crossing decreases `positiveCrossingCount` by one. -/
theorem positiveCrossingCount_resolveCrossingCoherent_add_one_of_eq_one (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c))
    (hc : D.crossingSign c = 1) :
    (D.resolveCrossingCoherent c detached hdetached).positiveCrossingCount + 1 =
      D.positiveCrossingCount := by
  set R := D.resolveCrossingCoherent c detached hdetached
  have hw : R.writhe = D.writhe - D.crossingSign c :=
    D.writhe_resolveCrossingCoherent c detached hdetached
  have := D.writhe_eq_positiveCrossingCount_sub_negativeCrossingCount
  have := R.writhe_eq_positiveCrossingCount_sub_negativeCrossingCount
  have := D.positiveCrossingCount_add_negativeCrossingCount
  have := R.positiveCrossingCount_add_negativeCrossingCount
  omega

/-- Coherent resolution of a negative crossing preserves `positiveCrossingCount`. -/
theorem positiveCrossingCount_resolveCrossingCoherent_of_eq_neg_one (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c))
    (hc : D.crossingSign c = -1) :
    (D.resolveCrossingCoherent c detached hdetached).positiveCrossingCount =
      D.positiveCrossingCount := by
  set R := D.resolveCrossingCoherent c detached hdetached
  have hw : R.writhe = D.writhe - D.crossingSign c :=
    D.writhe_resolveCrossingCoherent c detached hdetached
  have := D.writhe_eq_positiveCrossingCount_sub_negativeCrossingCount
  have := R.writhe_eq_positiveCrossingCount_sub_negativeCrossingCount
  have := D.positiveCrossingCount_add_negativeCrossingCount
  have := R.positiveCrossingCount_add_negativeCrossingCount
  omega

/-- Coherent resolution of a positive crossing preserves `negativeCrossingCount`. -/
theorem negativeCrossingCount_resolveCrossingCoherent_of_eq_one (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c))
    (hc : D.crossingSign c = 1) :
    (D.resolveCrossingCoherent c detached hdetached).negativeCrossingCount =
      D.negativeCrossingCount := by
  have := D.positiveCrossingCount_resolveCrossingCoherent_add_one_of_eq_one c detached hdetached hc
  have := D.positiveCrossingCount_add_negativeCrossingCount
  have := (D.resolveCrossingCoherent c detached
    hdetached).positiveCrossingCount_add_negativeCrossingCount
  omega

/-- Coherent resolution of a negative crossing decreases `negativeCrossingCount` by one. -/
theorem negativeCrossingCount_resolveCrossingCoherent_add_one_of_eq_neg_one
    (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c))
    (hc : D.crossingSign c = -1) :
    (D.resolveCrossingCoherent c detached hdetached).negativeCrossingCount + 1 =
      D.negativeCrossingCount := by
  have := D.positiveCrossingCount_resolveCrossingCoherent_of_eq_neg_one c detached hdetached hc
  have := D.positiveCrossingCount_add_negativeCrossingCount
  have := (D.resolveCrossingCoherent c detached
    hdetached).positiveCrossingCount_add_negativeCrossingCount
  omega

/-- Mirroring commutes with coherent crossing resolution. -/
@[simp] theorem mirror_resolveCrossingCoherent (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c)) :
    (D.resolveCrossingCoherent c detached hdetached).mirror =
      D.mirror.resolveCrossingCoherent c detached (by simpa using hdetached) := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    obtain ⟨⟨i, k⟩, rfl⟩ := (PDCode.crossingSlotEquiv n).surjective x
    simp
  · simp

/-- Reversing component orientations commutes with coherent crossing resolution, reversing the
orientations of any detached crossing-free circles. -/
@[simp] theorem reverse_resolveCrossingCoherent (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c)) :
    (D.resolveCrossingCoherent c detached hdetached).reverse =
      D.reverse.resolveCrossingCoherent c (detached.map (!·)) (by simpa using hdetached) := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    obtain ⟨⟨i, k⟩, rfl⟩ := (PDCode.crossingSlotEquiv n).surjective x
    simp
  · simp

/-- **Oriented crossing resolution in either direction.** At `t = D.seifertState c` this is the
coherent resolution `TauCeti.OrientedPDCode.resolveCrossingCoherent`; at the other smoothing it
equips `D.toPDCode.resolveCrossing c t` with a reorientation via `TauCeti.PDCode.orient`. Newly
detached crossing-free circles receive the prescribed orientations `detached`. -/
noncomputable def resolveCrossingOriented (t : Bool) (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c t) : OrientedPDCode n :=
  if ht : t = D.seifertState c then
    D.resolveCrossingCoherent c detached (ht ▸ hdetached)
  else
    (D.toPDCode.resolveCrossing c t).orient (D.crossinglessComponents + detached) (by
      simp [hdetached])

/-- Forgetting orientation on `D.resolveCrossingOriented c t detached hdetached` recovers
`D.toPDCode.resolveCrossing c t`. -/
@[simp] theorem toPDCode_resolveCrossingOriented (t : Bool) (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c t) :
    (D.resolveCrossingOriented c t detached hdetached).toPDCode =
      D.toPDCode.resolveCrossing c t := by
  unfold resolveCrossingOriented
  split_ifs with ht <;> simp [ht]

/-- `D.resolveCrossingOriented c t detached hdetached` keeps the crossing-free circles of `D` and
adjoins `detached`. -/
@[simp] theorem crossinglessComponents_resolveCrossingOriented (t : Bool) (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c t) :
    (D.resolveCrossingOriented c t detached hdetached).crossinglessComponents =
      D.crossinglessComponents + detached := by
  unfold resolveCrossingOriented
  split_ifs <;> simp

/-- At `t = D.seifertState c`, `resolveCrossingOriented` agrees with `resolveCrossingCoherent`. -/
@[simp] theorem resolveCrossingOriented_seifertState (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c)) :
    D.resolveCrossingOriented c (D.seifertState c) detached hdetached =
      D.resolveCrossingCoherent c detached hdetached := by
  simp [resolveCrossingOriented]

/-! ### Component-count alternatives for crossing resolutions -/

/-- The outgoing slot (`s` or its opposite slot) on the strand passing through slot `s`, given the
orientation `a` at slot `s`. -/
private def outSlot (s : Fin 4) (a : Bool) : Fin 4 :=
  bif a then s else PDCode.oppositeCrossingSlot s

/-- The outgoing half-edge at crossing `c` on the strand passing through slot `s`. -/
private def outgoingHalfEdge (s : Fin 4) : Fin (4 * (n + 1)) :=
  D.crossing c (outSlot s (D.orientation (D.crossing c s)))

private theorem slotSmoothing_xor_mul_oppositeCrossingSlot (a b : Bool) :
    PDCode.slotSmoothing (Bool.xor a b) * PDCode.oppositeCrossingSlot =
      Equiv.swap (outSlot 0 a) (outSlot 1 b) *
        Equiv.swap (PDCode.oppositeCrossingSlot (outSlot 0 a))
          (PDCode.oppositeCrossingSlot (outSlot 1 b)) := by
  ext k
  cases a <;> cases b <;>
    simp only [outSlot, Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Bool.cond_false, Bool.cond_true, PDCode.slotSmoothing_true, PDCode.slotSmoothing_false,
      PDCode.oppositeCrossingSlot_eq_swap_mul_swap, Perm.mul_apply, swap_apply_def] <;>
    revert k <;> decide

private theorem slotSmoothing_not_xor_mul_oppositeCrossingSlot (a b : Bool) :
    PDCode.slotSmoothing (!Bool.xor a b) * PDCode.oppositeCrossingSlot =
      Equiv.swap (outSlot 1 b) (PDCode.oppositeCrossingSlot (outSlot 0 a)) *
        Equiv.swap (outSlot 0 a) (PDCode.oppositeCrossingSlot (outSlot 1 b)) := by
  ext k
  cases a <;> cases b <;>
    simp only [outSlot, Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Bool.cond_false, Bool.cond_true, PDCode.slotSmoothing_true, PDCode.slotSmoothing_false,
      PDCode.oppositeCrossingSlot_eq_swap_mul_swap, Perm.mul_apply, swap_apply_def] <;>
    revert k <;> decide

private theorem outSlot_zero_ne_one (a b : Bool) : outSlot 0 a ≠ outSlot 1 b := by
  cases a <;> cases b <;>
    simp only [outSlot, Bool.cond_false, Bool.cond_true, PDCode.oppositeCrossingSlot_apply] <;>
    decide

private theorem outgoingHalfEdge_zero_ne_one :
    D.outgoingHalfEdge c 0 ≠ D.outgoingHalfEdge c 1 := fun h ↦
  outSlot_zero_ne_one _ _ (D.toPDCode.crossing_eq_crossing_iff.mp h).2

private theorem orientation_outgoingHalfEdge (s : Fin 4) :
    D.orientation (D.outgoingHalfEdge c s) = true := by
  cases ho : D.orientation (D.crossing c s)
  · rw [outgoingHalfEdge, ho, outSlot, Bool.cond_false, PDCode.crossing_apply,
      D.orientation_oppositeCrossingSlot]
    simpa [PDCode.crossing_apply] using ho
  · rw [outgoingHalfEdge, ho, outSlot, Bool.cond_true, ho]

private theorem crossingComponentOfHalfEdge_outgoingHalfEdge (s : Fin 4) :
    D.crossingComponentOfHalfEdge (D.outgoingHalfEdge c s) =
      D.crossingComponentOfHalfEdge (D.crossing c s) := by
  cases ho : D.orientation (D.crossing c s)
  · have hct : D.crossing c (PDCode.oppositeCrossingSlot s) =
        D.crossingTurn (D.crossing c s) := by
      simp [PDCode.crossing_apply]
    rw [outgoingHalfEdge, ho, outSlot, Bool.cond_false, hct,
      D.crossingComponentOfHalfEdge_crossingTurn]
  · rw [outgoingHalfEdge, ho, outSlot, Bool.cond_true]

/-- Two half-edges in the same directed orbit of `D.toPDCode.componentPerm` have the same
orientation. -/
private theorem orientation_eq_of_sameCycle_componentPerm {x y : Fin (4 * (n + 1))}
    (h : D.toPDCode.componentPerm.SameCycle x y) : D.orientation x = D.orientation y :=
  h.apply_eq_of_apply_eq D.orientation_componentPerm

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
  have hor (z : Fin (4 * (n + 1))) :
      D.orientation ((Equiv.swap v₀ v₁ * D.toPDCode.componentPerm) z) = D.orientation z := by
    rw [Perm.mul_apply, ← D.orientation_componentPerm z, swap_apply_def]
    split_ifs with h₁ h₂
    · rw [h₁, hv₀, hv₁]
    · rw [h₂, hv₀, hv₁]
    · rfl
  refine ⟨fun h ↦ h.sameCycle_or_of_swap_mul.resolve_right ?_, fun h ↦ ?_⟩
  · rintro ⟨h₀ | h₁, -⟩
    · exact D.not_sameCycle_componentPerm_of_orientation hu₀ hv₀ h₀
    · exact D.not_sameCycle_componentPerm_of_orientation hu₀ hv₁ h₁
  · rw [← Equiv.swap_mul_self_mul v₀ v₁ D.toPDCode.componentPerm] at h
    refine h.sameCycle_or_of_swap_mul.resolve_right ?_
    rintro ⟨h₀ | h₁, -⟩
    · exact absurd (h₀.apply_eq_of_apply_eq hor) (by simp [hu₀, hv₀])
    · exact absurd (h₁.apply_eq_of_apply_eq hor) (by simp [hu₀, hv₁])

/-- Swapping an outgoing half-edge `u₀` with an incoming half-edge `D.crossingTurn u₁` puts
`u₁` and `D.crossingTurn u₀` in the same cycle iff `u₀` and `u₁` already share a `componentPerm`
cycle. -/
private theorem sameCycle_swap_outgoing_incoming_mul_componentPerm_iff
    {u₀ u₁ : Fin (4 * (n + 1))}
    (hu₀ : D.orientation u₀ = true) (hu₁ : D.orientation u₁ = true) :
    (Equiv.swap u₀ (D.crossingTurn u₁) * D.toPDCode.componentPerm).SameCycle
        u₁ (D.crossingTurn u₀) ↔
      D.toPDCode.componentPerm.SameCycle u₀ u₁ := by
  have hv₀ : D.orientation (D.crossingTurn u₀) = false := by simp [hu₀]
  have hv₁ : D.orientation (D.crossingTurn u₁) = false := by simp [hu₁]
  refine ⟨fun hm ↦ ?_, fun hu ↦ ?_⟩
  · rcases hm.sameCycle_or_of_swap_mul with h₁ | ⟨h₂ | h₂, -⟩
    · exact absurd h₁ (D.not_sameCycle_componentPerm_of_orientation hu₁ hv₀)
    · exact h₂.symm
    · exact absurd h₂ (D.not_sameCycle_componentPerm_of_orientation hu₁ hv₁)
  · have hnot : ¬D.toPDCode.componentPerm.SameCycle u₀ (D.crossingTurn u₁) :=
      D.not_sameCycle_componentPerm_of_orientation hu₀ hv₁
    have hm₁ : (Equiv.swap u₀ (D.crossingTurn u₁) * D.toPDCode.componentPerm).SameCycle
        u₀ (D.crossingTurn u₁) :=
      sameCycle_swap_mul_of_mem_periodicPts_of_not_sameCycle
        (D.toPDCode.componentPerm.injective.mem_periodicPts _) hnot
    have hv : D.toPDCode.componentPerm.SameCycle (D.crossingTurn u₀) (D.crossingTurn u₁) :=
      D.sameCycle_componentPerm_crossingTurn_iff.mpr hu
    exact (hm₁.swap_mul_of_sameCycle hu.symm).trans
      (hm₁.trans (hm₁.swap_mul_of_sameCycle hv.symm))

/-- The two strands at crossing `c` lie on the same component iff their outgoing half-edges lie in
the same `componentPerm` orbit. -/
private theorem crossingComponentOfHalfEdge_zero_eq_one_iff :
    D.crossingComponentOfHalfEdge (D.crossing c 0) =
        D.crossingComponentOfHalfEdge (D.crossing c 1) ↔
      D.toPDCode.componentPerm.SameCycle (D.outgoingHalfEdge c 0) (D.outgoingHalfEdge c 1) := by
  have hsub : D.componentPermOutgoing =
      D.toPDCode.componentPerm.subtypePerm (fun h ↦ by rw [orientation_componentPerm]) := by
    ext x
    simp
  rw [← D.crossingComponentOfHalfEdge_outgoingHalfEdge c 0,
    ← D.crossingComponentOfHalfEdge_outgoingHalfEdge c 1,
    D.crossingComponentOfHalfEdge_of_outgoing _ (D.orientation_outgoingHalfEdge c 0),
    D.crossingComponentOfHalfEdge_of_outgoing _ (D.orientation_outgoingHalfEdge c 1)]
  simp only [Quotient.eq, SameCycle.setoid]
  rw [hsub, sameCycle_subtypePerm]

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

private theorem resolvedTurn_mul_edgePair_eq_of_slotSmoothing_mul_eq (t : Bool)
    (s₁ s₂ t₁ t₂ : Fin 4)
    (hslot : PDCode.slotSmoothing (bif t then D.overPair c else !D.overPair c) *
        PDCode.oppositeCrossingSlot =
      Equiv.swap s₁ s₂ * Equiv.swap t₁ t₂) :
    D.toPDCode.resolvedTurn c t * D.edgePair.val =
      Equiv.swap (D.crossing c s₁) (D.crossing c s₂) *
        (Equiv.swap (D.crossing c t₁) (D.crossing c t₂) * D.toPDCode.componentPerm) := by
  have hturn : D.toPDCode.resolvedTurn c t * D.toPDCode.crossingTurn =
      Equiv.swap (D.crossing c s₁) (D.crossing c s₂) *
        Equiv.swap (D.crossing c t₁) (D.crossing c t₂) := by
    ext h
    obtain ⟨j, k, rfl⟩ := D.exists_crossing_eq h
    rw [D.resolvedTurn_mul_crossingTurn_crossing c, hslot]
    split_ifs with hj
    · subst j
      simp only [Perm.mul_apply]
      rw [D.crossing_swap_apply, D.crossing_swap_apply]
    · have hne (s : Fin 4) : D.crossing j k ≠ D.crossing c s := fun h ↦
        hj (D.toPDCode.crossing_eq_crossing_iff.mp h).1
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (hne _) (hne _),
        swap_apply_of_ne_of_ne (hne _) (hne _)]
  calc D.toPDCode.resolvedTurn c t * D.edgePair.val
      = (D.toPDCode.resolvedTurn c t * D.toPDCode.crossingTurn) *
          D.toPDCode.componentPerm := by
        ext h
        simp [Perm.mul_apply, PDCode.componentPerm_apply]
    _ = _ := by rw [hturn, mul_assoc]

/-- At `t = D.seifertState c`, `resolvedTurn * edgePair` differs from `componentPerm` by swapping
the two outgoing half-edges at `c` and swapping the two incoming half-edges at `c`. -/
private theorem resolvedTurn_seifertState_mul_edgePair_eq :
    D.toPDCode.resolvedTurn c (D.seifertState c) * D.edgePair.val =
      Equiv.swap (D.outgoingHalfEdge c 0) (D.outgoingHalfEdge c 1) *
        (Equiv.swap (D.crossingTurn (D.outgoingHalfEdge c 0))
            (D.crossingTurn (D.outgoingHalfEdge c 1)) *
          D.toPDCode.componentPerm) := by
  have hchoice : (bif D.seifertState c then D.overPair c else !D.overPair c) =
      Bool.xor (D.orientation (D.crossing c 0)) (D.orientation (D.crossing c 1)) := by
    rw [← D.smoothingChoice_seifertState c]
    cases hs : D.seifertState c <;> simp [hs]
  have hct (s : Fin 4) : D.crossingTurn (D.crossing c s) =
      D.crossing c (PDCode.oppositeCrossingSlot s) := by
    rw [PDCode.crossing_apply, PDCode.crossingTurn_crossing]
  simp only [outgoingHalfEdge, hct]
  exact D.resolvedTurn_mul_edgePair_eq_of_slotSmoothing_mul_eq c _ _ _ _ _
    (by rw [hchoice, slotSmoothing_xor_mul_oppositeCrossingSlot])

/-- At `t = !D.seifertState c`, `resolvedTurn * edgePair` differs from `componentPerm` by two
outgoing-to-incoming transpositions at `c`. -/
private theorem resolvedTurn_not_seifertState_mul_edgePair_eq :
    D.toPDCode.resolvedTurn c (!D.seifertState c) * D.edgePair.val =
      Equiv.swap (D.outgoingHalfEdge c 1) (D.crossingTurn (D.outgoingHalfEdge c 0)) *
        (Equiv.swap (D.outgoingHalfEdge c 0) (D.crossingTurn (D.outgoingHalfEdge c 1)) *
          D.toPDCode.componentPerm) := by
  have hchoice : (bif !D.seifertState c then D.overPair c else !D.overPair c) =
      !Bool.xor (D.orientation (D.crossing c 0)) (D.orientation (D.crossing c 1)) := by
    rw [← D.smoothingChoice_seifertState c]
    cases hs : D.seifertState c <;> simp [hs]
  have hct (s : Fin 4) : D.crossingTurn (D.crossing c s) =
      D.crossing c (PDCode.oppositeCrossingSlot s) := by
    rw [PDCode.crossing_apply, PDCode.crossingTurn_crossing]
  simp only [outgoingHalfEdge, hct]
  exact D.resolvedTurn_mul_edgePair_eq_of_slotSmoothing_mul_eq c _ _ _ _ _
    (by rw [hchoice, slotSmoothing_not_xor_mul_oppositeCrossingSlot])

/-- Convert an orbit-count shift on `resolvedTurn * edgePair` into a component-count shift on
`resolveCrossing`. -/
private theorem componentCount_resolveCrossing_eq_of_orbitCount (t : Bool) {a b : ℕ}
    (h : orbitCount (D.toPDCode.resolvedTurn c t * D.edgePair.val) + 2 * a =
      orbitCount D.toPDCode.componentPerm + 2 * b) :
    (D.toPDCode.resolveCrossing c t).componentCount + a = D.componentCount + b := by
  have htwo := D.toPDCode.two_mul_componentCount_resolveCrossing c t
  obtain ⟨r, hr⟩ := D.toPDCode.even_orbitCount_componentPerm
  rw [D.toPDCode.componentCount_eq, D.toPDCode.crossingComponentCount_def]
  omega

/-- **Coherent resolution of a self-crossing splits the component.** When the two strands at `c`
belong to the same component of `D`, smoothing `c` by `D.seifertState c` increases the number of
components by one. -/
theorem componentCount_resolveCrossing_seifertState_of_eq
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (D.seifertState c)).componentCount = D.componentCount + 1 := by
  have hu := (D.crossingComponentOfHalfEdge_zero_eq_one_iff c).mp hc
  have hu₀ := D.orientation_outgoingHalfEdge c 0
  have hu₁ := D.orientation_outgoingHalfEdge c 1
  have hv₀ : D.orientation (D.crossingTurn (D.outgoingHalfEdge c 0)) = false := by simp [hu₀]
  have hv₁ : D.orientation (D.crossingTurn (D.outgoingHalfEdge c 1)) = false := by simp [hu₁]
  have hu_ne := D.outgoingHalfEdge_zero_ne_one c
  have hv_ne := D.toPDCode.crossingTurn.injective.ne hu_ne
  have hv := D.sameCycle_componentPerm_crossingTurn_iff.mpr hu
  have hu' := (D.sameCycle_swap_incoming_mul_componentPerm_iff hv₀ hv₁ hu₀).mpr hu
  simpa using D.componentCount_resolveCrossing_eq_of_orbitCount c (D.seifertState c)
    (a := 0) (b := 1) (by
      rw [D.resolvedTurn_seifertState_mul_edgePair_eq c,
        orbitCount_swap_mul_of_sameCycle hu_ne hu',
        orbitCount_swap_mul_of_sameCycle hv_ne hv])

/-- **Non-coherent resolution of a self-crossing keeps the component count.** When the two strands
at `c` belong to the same component of `D`, smoothing `c` by `!D.seifertState c` reconnects that
component into one component again. -/
theorem componentCount_resolveCrossing_not_seifertState_of_eq
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (!D.seifertState c)).componentCount = D.componentCount := by
  have hu := (D.crossingComponentOfHalfEdge_zero_eq_one_iff c).mp hc
  have hu₀ := D.orientation_outgoingHalfEdge c 0
  have hu₁ := D.orientation_outgoingHalfEdge c 1
  have hv₀ : D.orientation (D.crossingTurn (D.outgoingHalfEdge c 0)) = false := by simp [hu₀]
  have hv₁ : D.orientation (D.crossingTurn (D.outgoingHalfEdge c 1)) = false := by simp [hu₁]
  have hnot₁ := D.not_sameCycle_componentPerm_of_orientation hu₀ hv₁
  have hm₂ := (D.sameCycle_swap_outgoing_incoming_mul_componentPerm_iff hu₀ hu₁).mpr hu
  have hne₂ : D.outgoingHalfEdge c 1 ≠ D.crossingTurn (D.outgoingHalfEdge c 0) :=
    fun h ↦ by simpa [hu₁, hv₀] using congrArg D.orientation h
  have hstep₁ := orbitCount_swap_mul_add_one_of_not_sameCycle hnot₁
  have hstep₂ := orbitCount_swap_mul_of_sameCycle hne₂ hm₂
  simpa using D.componentCount_resolveCrossing_eq_of_orbitCount c (!D.seifertState c)
    (a := 0) (b := 0) (by
      rw [D.resolvedTurn_not_seifertState_mul_edgePair_eq c, hstep₂]
      omega)

/-- **At a self-crossing, the `A`- and `B`-resolutions have component counts `D.componentCount` and
`D.componentCount + 1` in some order** (with `D.componentCount + 1` at `D.seifertState c`). -/
theorem componentCount_resolveCrossing_eq_and_eq_add_one_or_eq_add_one_and_eq_of_eq
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
  have hnu := (D.crossingComponentOfHalfEdge_zero_eq_one_iff c).not.mp hc
  have hu₀ := D.orientation_outgoingHalfEdge c 0
  have hu₁ := D.orientation_outgoingHalfEdge c 1
  have hv₀ : D.orientation (D.crossingTurn (D.outgoingHalfEdge c 0)) = false := by simp [hu₀]
  have hv₁ : D.orientation (D.crossingTurn (D.outgoingHalfEdge c 1)) = false := by simp [hu₁]
  have hnv := D.sameCycle_componentPerm_crossingTurn_iff.not.mpr hnu
  have hnu' := (D.sameCycle_swap_incoming_mul_componentPerm_iff hv₀ hv₁ hu₀).not.mpr hnu
  have hstep₁ := orbitCount_swap_mul_add_one_of_not_sameCycle hnv
  have hstep₂ := orbitCount_swap_mul_add_one_of_not_sameCycle hnu'
  simpa using D.componentCount_resolveCrossing_eq_of_orbitCount c (D.seifertState c)
    (a := 1) (b := 0) (by
      rw [D.resolvedTurn_seifertState_mul_edgePair_eq c]
      omega)

private theorem componentCount_resolveCrossing_not_seifertState_add_one_of_ne
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) ≠
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (!D.seifertState c)).componentCount + 1 = D.componentCount := by
  have hnu := (D.crossingComponentOfHalfEdge_zero_eq_one_iff c).not.mp hc
  have hu₀ := D.orientation_outgoingHalfEdge c 0
  have hu₁ := D.orientation_outgoingHalfEdge c 1
  have hv₁ : D.orientation (D.crossingTurn (D.outgoingHalfEdge c 1)) = false := by simp [hu₁]
  have hnot₁ := D.not_sameCycle_componentPerm_of_orientation hu₀ hv₁
  have hnot₂ := (D.sameCycle_swap_outgoing_incoming_mul_componentPerm_iff hu₀ hu₁).not.mpr hnu
  have hstep₁ := orbitCount_swap_mul_add_one_of_not_sameCycle hnot₁
  have hstep₂ := orbitCount_swap_mul_add_one_of_not_sameCycle hnot₂
  simpa using D.componentCount_resolveCrossing_eq_of_orbitCount c (!D.seifertState c)
    (a := 1) (b := 0) (by
      rw [D.resolvedTurn_not_seifertState_mul_edgePair_eq c]
      omega)

/-- **Resolving a crossing between two different components merges them**, so both the `A`- and
`B`-resolutions have `D.componentCount - 1` components. -/
theorem componentCount_resolveCrossing_add_one_of_ne
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) ≠
      D.crossingComponentOfHalfEdge (D.crossing c 1)) (t : Bool) :
    (D.toPDCode.resolveCrossing c t).componentCount + 1 = D.componentCount := by
  by_cases ht : t = D.seifertState c
  · subst ht
    exact D.componentCount_resolveCrossing_seifertState_add_one_of_ne c hc
  · obtain rfl := Bool.eq_not_of_ne ht
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
