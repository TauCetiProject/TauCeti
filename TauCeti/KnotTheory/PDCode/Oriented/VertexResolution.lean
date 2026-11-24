/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Oriented.Component
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Seifert
public import TauCeti.KnotTheory.PDCode.VertexResolution.Components

/-!
# Orientations and component counts of crossing resolutions

Resolving one crossing `c` of an oriented PD-code `D` with `n + 1` crossings produces the two
`n`-crossing codes `D.toPDCode.resolveCrossing c true` and `D.toPDCode.resolveCrossing c false`.
At the coherent smoothing `t = D.seifertState c`, the local smoothing joins incoming half-edges to
outgoing ones, so pulling back `D.orientation` along `TauCeti.PDCode.resolveCrossingHalfEdge` via
`TauCeti.PDCode.apply_resolveCrossingHalfEdge_edgePair_val` descends directly to an oriented code
`TauCeti.OrientedPDCode.resolveCrossingCoherent` keeping the crossing signs of the remaining
crossings, with explicit orientation data supplied for any newly detached crossing-free circles. At
the opposite smoothing `!D.seifertState c`, strands are reversed along part of a component, so the
resolved diagram must be reoriented; every unoriented `PDCode` admits a consistent choice of
component orientations (`TauCeti.PDCode.orient`), because each undirected component splits into two
opposite directed orbits of `componentPerm`. Combining the two gives
`TauCeti.OrientedPDCode.resolveCrossingOriented` for both `t : Bool`.

Combining `TauCeti.OrientedPDCode.crossingComponentOfHalfEdge_eq_iff` with the unoriented
component-count theorems of `TauCeti.KnotTheory.PDCode.VertexResolution.Components` determines the
component counts of the two resolutions without any planarity assumption:

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

/-- **Coherent resolution of an oriented crossing.** Resolving crossing `c` in its Seifert direction
`D.seifertState c` preserves the orientations of all remaining half-edges and crossings, and adjoins
any newly detached crossing-free circles with the prescribed orientations `detached`. -/
def resolveCrossingCoherent (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c)) :
    OrientedPDCode n where
  toPDCode := D.toPDCode.resolveCrossing c (D.seifertState c)
  orientation y := D.orientation (D.toPDCode.resolveCrossingHalfEdge c y)
  orientation_edgePair y := by
    refine D.toPDCode.apply_resolveCrossingHalfEdge_edgePair_val c (D.seifertState c)
      D.orientation_edgePair (fun k ↦ ?_) y
    have h := D.orientation_smoothingTurn_seifertState (D.crossing c k)
    rwa [PDCode.crossing_apply, PDCode.smoothingTurn_crossing, ← PDCode.crossing_apply,
      PDCode.smoothingChoice_def] at h
  orientation_oppositeCrossingSlot i slot := by
    simp [PDCode.resolveCrossingHalfEdge_crossingSlotEquiv, D.orientation_oppositeCrossingSlot]
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

-- Not `@[simp]`: `orientation_resolveCrossingCoherent` normalizes crossing-slot evaluations.
/-- Each half-edge of `D.resolveCrossingCoherent c detached hdetached` inherits the orientation of
its image under `TauCeti.PDCode.resolveCrossingHalfEdge`. -/
theorem resolveCrossingCoherent_orientation (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c))
    (y : Fin (4 * n)) :
    (D.resolveCrossingCoherent c detached hdetached).orientation y =
      D.orientation (D.toPDCode.resolveCrossingHalfEdge c y) := (rfl)

/-- Slot `k` of crossing `i` in `D.resolveCrossingCoherent c detached hdetached` keeps the
orientation of slot `k` of crossing `c.succAbove i` in `D`. -/
@[simp] theorem orientation_resolveCrossingCoherent (detached : Multiset Bool)
    (hdetached : detached.card = D.toPDCode.detachedCircleCount c (D.seifertState c))
    (i : Fin n) (k : Fin 4) :
    (D.resolveCrossingCoherent c detached hdetached).orientation
        (PDCode.crossingSlotEquiv n (i, k)) =
      D.orientation (D.crossing (c.succAbove i) k) := by
  simp [resolveCrossingCoherent_orientation]

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

private theorem componentCount_resolveCrossing_seifertState_and_not_of_eq
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (D.seifertState c)).componentCount = D.componentCount + 1 ∧
      (D.toPDCode.resolveCrossing c (!D.seifertState c)).componentCount = D.componentCount := by
  have ht₁ : D.crossingTurn (D.crossing c 1) = D.crossing c 3 :=
    D.toPDCode.crossingTurn_crossing_one c
  have hsc := D.smoothingChoice_seifertState c
  rw [D.crossingComponentOfHalfEdge_eq_iff, ht₁] at hc
  rcases hc with h₁ | h₃
  · have ho := D.orientation_eq_of_sameCycle_componentPerm h₁
    have hseif : D.seifertState c = !D.overPair c := by
      rw [ho, Bool.xor_self, PDCode.smoothingChoice_def] at hsc
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
      rw [hxor, PDCode.smoothingChoice_def] at hsc
      cases hs : D.seifertState c <;> cases ho' : D.overPair c <;> simp [hs, ho'] at hsc ⊢
    rw [hseif]
    exact D.toPDCode.componentCount_resolveCrossing_of_sameCycle_zero_three c h₃

/-- **Coherent resolution of a self-crossing splits the component.** When the two strands at `c`
belong to the same component of `D`, smoothing `c` by `D.seifertState c` increases the number of
components by one. -/
theorem componentCount_resolveCrossing_seifertState_of_eq
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (D.seifertState c)).componentCount = D.componentCount + 1 :=
  (D.componentCount_resolveCrossing_seifertState_and_not_of_eq c hc).left

/-- **Non-coherent resolution of a self-crossing keeps the component count.** When the two strands
at `c` belong to the same component of `D`, smoothing `c` by `!D.seifertState c` reconnects that
component into one component again. -/
theorem componentCount_resolveCrossing_not_seifertState_of_eq
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) =
      D.crossingComponentOfHalfEdge (D.crossing c 1)) :
    (D.toPDCode.resolveCrossing c (!D.seifertState c)).componentCount = D.componentCount :=
  (D.componentCount_resolveCrossing_seifertState_and_not_of_eq c hc).right

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

/-- **Resolving a crossing between two different components merges them**, so both the `A`- and
`B`-resolutions have `D.componentCount - 1` components. -/
theorem componentCount_resolveCrossing_add_one_of_ne
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) ≠
      D.crossingComponentOfHalfEdge (D.crossing c 1)) (t : Bool) :
    (D.toPDCode.resolveCrossing c t).componentCount + 1 = D.componentCount := by
  rw [Ne, D.crossingComponentOfHalfEdge_eq_iff, D.toPDCode.crossingTurn_crossing_one c,
    not_or] at hc
  exact D.toPDCode.componentCount_resolveCrossing_add_one_of_not_sameCycle c t hc.left hc.right

/-- Subtracted form of `TauCeti.OrientedPDCode.componentCount_resolveCrossing_add_one_of_ne`. -/
theorem componentCount_resolveCrossing_of_ne
    (hc : D.crossingComponentOfHalfEdge (D.crossing c 0) ≠
      D.crossingComponentOfHalfEdge (D.crossing c 1)) (t : Bool) :
    (D.toPDCode.resolveCrossing c t).componentCount = D.componentCount - 1 := by
  have h := D.componentCount_resolveCrossing_add_one_of_ne c hc t
  omega

end OrientedPDCode

end TauCeti
