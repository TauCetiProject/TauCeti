/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Basic

/-!
# Orientation-preserving reconnection of diagram arcs

Two arc ends with opposite directions can be joined while keeping every half-edge's
direction. This lifts `PDCode.reconnect` to oriented codes and supplies the oriented
smoothing in the Jones skein relation. Reconnection leaves the crossings and writhe unchanged.

Reference: W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 3,
Proposition 3.7 (oriented smoothing).
-/

public section

namespace TauCeti.OrientedPDCode

variable {n : ℕ}

/-- Join two oppositely directed arc ends, preserving all half-edge directions and
crossing-free components. The ends may belong to the same arc. -/
def reconnect (D : OrientedPDCode n) (p q : Fin (4 * n))
    (h : D.orientation p = !D.orientation q) : OrientedPDCode n where
  toPDCode := D.toPDCode.reconnect p q
  orientation := D.orientation
  orientation_edgePair := by
    have hs (x) : D.orientation (Equiv.swap (D.edgePair.val p) q x) = D.orientation x := by
      by_cases hx : x = D.edgePair.val p
      · subst x
        simp [h]
      by_cases hxq : x = q
      · subst x
        simp [h]
      simp [Equiv.swap_apply_of_ne_of_ne hx hxq]
    intro x
    rw [PDCode.reconnect_edgePair_val, Equiv.permCongr_apply, Equiv.symm_swap,
      hs, D.orientation_edgePair, hs]
  orientation_oppositeCrossingSlot := by simp
  crossinglessComponents := D.crossinglessComponents
  card_crossinglessComponents := by simp

variable (D : OrientedPDCode n) (p q : Fin (4 * n))
  (h : D.orientation p = !D.orientation q)

/-- Forgetting orientation gives the existing arc reconnection. -/
@[simp] theorem reconnect_toPDCode :
    (D.reconnect p q h).toPDCode = D.toPDCode.reconnect p q := (rfl)

/-- Reconnection retains the directions of all half-edges. -/
@[simp] theorem reconnect_orientation (x : Fin (4 * n)) :
    (D.reconnect p q h).orientation x = D.orientation x := (rfl)

/-- Reconnection retains the oriented crossing-free components. -/
@[simp] theorem reconnect_crossinglessComponents :
    (D.reconnect p q h).crossinglessComponents = D.crossinglessComponents := (rfl)

/-- Reconnection preserves each crossing sign. -/
@[simp] theorem crossingSign_reconnect (i : Fin n) :
    (D.reconnect p q h).crossingSign i = D.crossingSign i := by
  simp [crossingSign_def, PDCode.crossing_apply]

/-- Reconnection preserves the writhe. -/
@[simp] theorem writhe_reconnect : (D.reconnect p q h).writhe = D.writhe := by
  simp [writhe_def]

end TauCeti.OrientedPDCode
