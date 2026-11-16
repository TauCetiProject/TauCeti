/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Oriented.Component
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Seifert
public import TauCeti.KnotTheory.PDCode.VertexResolution

/-!
# Resolving crossings of oriented PD-codes

At a crossing `c` of an oriented code `D`, the Seifert smoothing `D.seifertState c` joins incoming
half-edges to outgoing ones, so the resolution `D.toPDCode.resolveCrossing c (D.seifertState c)`
inherits the half-edge orientations of `D` (`TauCeti.OrientedPDCode.coherentResolveCrossing`) once
the newly detached crossing-free circles are oriented. Every remaining crossing `i` keeps the sign
of `c.succAbove i`.

Comparing `TauCeti.OrientedPDCode.crossingComponentOfHalfEdge` with `componentPerm` orbits
(`TauCeti.OrientedPDCode.crossingComponentOfHalfEdge_eq_iff`) yields the oriented component-count
dichotomy at `c`:

* if the two local strands at `c` belong to distinct link components, both the `A`- and
  `B`-smoothings merge those two components into one (`c - 1` components each);
* if `c` is a self-crossing of one link component, the Seifert smoothing splits that component
  (`c + 1` components) and the opposite smoothing leaves `c` components.

## Main definitions

* `TauCeti.OrientedPDCode.coherentResolveCrossing`: the Seifert resolution at `c`, inheriting the
  orientation of `D` on all remaining half-edges.

## Main results

* `TauCeti.OrientedPDCode.crossingSign_coherentResolveCrossing`,
  `TauCeti.OrientedPDCode.writhe_coherentResolveCrossing`,
  `TauCeti.OrientedPDCode.positiveCrossingCount_coherentResolveCrossing`, and
  `TauCeti.OrientedPDCode.negativeCrossingCount_coherentResolveCrossing`: crossing signs, writhe,
  and positive/negative crossing counts of the oriented smoothing.
* `TauCeti.OrientedPDCode.componentCount_resolveCrossing_add_one_of_crossingComponentOfHalfEdge_ne`,
  `TauCeti.OrientedPDCode.componentCount_resolveCrossing_seifertState`, and
  `TauCeti.OrientedPDCode.componentCount_resolveCrossing_not_seifertState`: component counts of
  smoothings of two-component crossings and self-crossings.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapters 1-3.
* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.4.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §3.1.
-/

public section

namespace TauCeti

namespace OrientedPDCode

private theorem smoothingChoice_eq_bif {m : ℕ} (E : PDCode m) (s : Fin m → Bool) (i : Fin m) :
    E.smoothingChoice s i = (bif s i then E.overPair i else !E.overPair i) := by
  cases hs : s i <;> simp [hs]

/-! ### Coherent orientation of the Seifert smoothing at one crossing -/

section CoherentResolveCrossing

variable {n : ℕ} (D : OrientedPDCode (n + 1)) (c : Fin (n + 1)) (l : Multiset Bool)
  (hl : l.card = D.toPDCode.detachedCircleCount c (D.seifertState c))

/-- **The coherently oriented smoothing at a crossing `c`**: resolving `c` by `D.seifertState c`
joins incoming half-edges to outgoing ones, so every remaining half-edge keeps its orientation in
`D`, while `l` supplies orientations for any newly detached crossing-free circles. -/
def coherentResolveCrossing : OrientedPDCode n where
  toPDCode := D.toPDCode.resolveCrossing c (D.seifertState c)
  orientation y := D.orientation (D.toPDCode.resolveCrossingHalfEdge c y)
  orientation_edgePair y := by
    refine D.toPDCode.apply_resolveCrossingHalfEdge_edgePair_val c (D.seifertState c)
      D.orientation_edgePair (fun k ↦ ?_) y
    have h := D.orientation_smoothingTurn_seifertState (D.crossing c k)
    rwa [PDCode.crossing_apply, PDCode.smoothingTurn_crossing, ← PDCode.crossing_apply,
      smoothingChoice_eq_bif] at h
  orientation_oppositeCrossingSlot i slot := by
    simp [PDCode.resolveCrossingHalfEdge_crossingSlotEquiv, D.orientation_oppositeCrossingSlot]
  crossinglessComponents := D.crossinglessComponents + l
  card_crossinglessComponents := by
    simp [hl]

/-- The underlying code of `coherentResolveCrossing` is the Seifert resolution at `c`. -/
@[simp] theorem toPDCode_coherentResolveCrossing :
    (D.coherentResolveCrossing c l hl).toPDCode =
      D.toPDCode.resolveCrossing c (D.seifertState c) := (rfl)

/-- Each half-edge of `coherentResolveCrossing` inherits its orientation from `D`. -/
@[simp] theorem coherentResolveCrossing_orientation (y : Fin (4 * n)) :
    (D.coherentResolveCrossing c l hl).orientation y =
      D.orientation (D.toPDCode.resolveCrossingHalfEdge c y) := (rfl)

/-- `coherentResolveCrossing` appends the detached-circle orientations `l` to those of `D`. -/
@[simp] theorem coherentResolveCrossing_crossinglessComponents :
    (D.coherentResolveCrossing c l hl).crossinglessComponents = D.crossinglessComponents + l :=
  (rfl)

/-- Every remaining crossing `i` of `coherentResolveCrossing` keeps the sign of `c.succAbove i`. -/
@[simp] theorem crossingSign_coherentResolveCrossing (i : Fin n) :
    (D.coherentResolveCrossing c l hl).crossingSign i = D.crossingSign (c.succAbove i) := by
  simp [crossingSign_def]

/-- Resolving `c` coherently removes `D.crossingSign c` from the writhe. -/
theorem writhe_coherentResolveCrossing :
    (D.coherentResolveCrossing c l hl).writhe + D.crossingSign c = D.writhe := by
  rw [writhe_def, D.writhe_def, Fin.sum_univ_succAbove _ c]
  simp [add_comm]

/-- Positive crossing count of `D` in terms of `coherentResolveCrossing` and `D.crossingSign c`. -/
theorem positiveCrossingCount_coherentResolveCrossing :
    D.positiveCrossingCount =
      (D.coherentResolveCrossing c l hl).positiveCrossingCount +
        if D.crossingSign c = 1 then 1 else 0 := by
  rw [positiveCrossingCount_def, positiveCrossingCount_def, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_succAbove _ c]
  simp_rw [crossingSign_coherentResolveCrossing]
  exact add_comm _ _

/-- Negative crossing count of `D` in terms of `coherentResolveCrossing` and `D.crossingSign c`. -/
theorem negativeCrossingCount_coherentResolveCrossing :
    D.negativeCrossingCount =
      (D.coherentResolveCrossing c l hl).negativeCrossingCount +
        if D.crossingSign c = -1 then 1 else 0 := by
  rw [negativeCrossingCount_def, negativeCrossingCount_def, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_succAbove _ c]
  simp_rw [crossingSign_coherentResolveCrossing]
  exact add_comm _ _

end CoherentResolveCrossing

/-! ### Oriented link components and component counts of smoothings -/

section ComponentCount

variable {n : ℕ} (D : OrientedPDCode (n + 1)) (c : Fin (n + 1))

/-- **Two-component crossing.** If slots `0` and `1` of crossing `c` lie on distinct link
components, then both the `A`- and `B`-smoothings merge those two components and have
`D.componentCount - 1` components. -/
theorem componentCount_resolveCrossing_add_one_of_crossingComponentOfHalfEdge_ne
    (h : D.crossingComponentOfHalfEdge (D.crossing c 0) ≠
      D.crossingComponentOfHalfEdge (D.crossing c 1)) (t : Bool) :
    (D.toPDCode.resolveCrossing c t).componentCount + 1 = D.componentCount := by
  rw [Ne, D.crossingComponentOfHalfEdge_eq_iff, D.toPDCode.crossingTurn_crossing_one c, not_or] at h
  exact D.toPDCode.componentCount_resolveCrossing_add_one_of_not_sameCycle c t h.1 h.2

/-- If slots `0` and `1` of crossing `c` lie on the same link component, then the Seifert smoothing
`D.seifertState c` splits that component (`D.componentCount + 1` components) and the opposite
smoothing `!D.seifertState c` leaves `D.componentCount` components. -/
private theorem componentCount_resolveCrossing_seifertState_and_not
    (h : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (D.seifertState c)).componentCount = D.componentCount + 1 ∧
      (D.toPDCode.resolveCrossing c (!D.seifertState c)).componentCount = D.componentCount := by
  have ht₁ : D.crossingTurn (D.crossing c 1) = D.crossing c 3 :=
    D.toPDCode.crossingTurn_crossing_one c
  have hsc := D.smoothingChoice_seifertState c
  rw [D.crossingComponentOfHalfEdge_eq_iff, ht₁] at h
  rcases h with h₁ | h₃
  · have ho := D.orientation_eq_of_sameCycle_componentPerm h₁
    have hseif : D.seifertState c = !D.overPair c := by
      rw [ho, Bool.xor_self, smoothingChoice_eq_bif] at hsc
      cases hs : D.seifertState c <;> cases ho' : D.overPair c <;> simp [hs, ho'] at hsc ⊢
    rw [hseif, Bool.not_not]
    exact D.toPDCode.componentCount_resolveCrossing_of_sameCycle_zero_one c h₁
  · have ho := D.orientation_eq_of_sameCycle_componentPerm h₃
    have h31 : D.orientation (D.crossing c 3) = !D.orientation (D.crossing c 1) := by
      rw [← ht₁, D.orientation_crossingTurn]
    have hseif : D.seifertState c = D.overPair c := by
      rw [ho, h31] at hsc
      have hxor : Bool.xor (!D.orientation (D.crossing c 1)) (D.orientation (D.crossing c 1)) =
          true := by
        cases D.orientation (D.crossing c 1) <;> decide
      rw [hxor, smoothingChoice_eq_bif] at hsc
      cases hs : D.seifertState c <;> cases ho' : D.overPair c <;> simp [hs, ho'] at hsc ⊢
    rw [hseif]
    exact D.toPDCode.componentCount_resolveCrossing_of_sameCycle_zero_three c h₃

/-- **Self-crossing (Seifert smoothing).** If slots `0` and `1` of crossing `c` lie on the same
link component, then the Seifert smoothing `D.seifertState c` splits that component and has
`D.componentCount + 1` components. -/
theorem componentCount_resolveCrossing_seifertState
    (h : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (D.seifertState c)).componentCount = D.componentCount + 1 :=
  (D.componentCount_resolveCrossing_seifertState_and_not c h).1

/-- **Self-crossing (non-Seifert smoothing).** If slots `0` and `1` of crossing `c` lie on the same
link component, then the opposite smoothing `!D.seifertState c` has `D.componentCount`
components. -/
theorem componentCount_resolveCrossing_not_seifertState
    (h : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (!D.seifertState c)).componentCount = D.componentCount :=
  (D.componentCount_resolveCrossing_seifertState_and_not c h).2

end ComponentCount

end OrientedPDCode

end TauCeti
