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
  orientation_edgePair x := by
    rw [PDCode.reconnect_edgePair]
    exact D.edgePair.not_apply_reconnect_val D.orientation_edgePair (by rw [h, Bool.not_not]) x
  orientation_oppositeCrossingSlot := by simp
  crossinglessComponents := D.crossinglessComponents
  card_crossinglessComponents := by simp

variable (D : OrientedPDCode n) (p q : Fin (4 * n))
  (h : D.orientation p = !D.orientation q)

/-- Forgetting orientation gives the existing arc reconnection. -/
@[simp] theorem toPDCode_reconnect :
    (D.reconnect p q h).toPDCode = D.toPDCode.reconnect p q := (rfl)

/-- Reconnection retains the directions of all half-edges. -/
@[simp] theorem orientation_reconnect (x : Fin (4 * n)) :
    (D.reconnect p q h).orientation x = D.orientation x := (rfl)

/-- Reconnection retains the oriented crossing-free components. -/
@[simp] theorem crossinglessComponents_reconnect :
    (D.reconnect p q h).crossinglessComponents = D.crossinglessComponents := (rfl)

/-- Reconnecting the two ends of one arc leaves the oriented code unchanged. -/
@[simp] theorem reconnect_partner
    (h : D.orientation p = !D.orientation (D.edgePair.val p)) :
    D.reconnect p (D.edgePair.val p) h = D := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    simp
  · simp

/-- Reconnection preserves each crossing sign. -/
@[simp] theorem crossingSign_reconnect (i : Fin n) :
    (D.reconnect p q h).crossingSign i = D.crossingSign i := by
  simp [crossingSign_def, PDCode.crossing_apply]

/-- Reconnection preserves the writhe. -/
@[simp] theorem writhe_reconnect : (D.reconnect p q h).writhe = D.writhe := by
  simp [writhe_def]

/-- Reflecting a reconnection reconnects the reflected code. -/
@[simp] theorem mirror_reconnect :
    (D.reconnect p q h).mirror = D.mirror.reconnect p q (by simpa using h) := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    simp
  · simp

/-- Reversing a reconnection reconnects the reversed code. -/
@[simp] theorem reverse_reconnect :
    (D.reconnect p q h).reverse = D.reverse.reconnect p q (by simp [h]) := by
  apply OrientedPDCode.ext
  · simp
  · funext x
    simp
  · simp

end TauCeti.OrientedPDCode
