/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.FreeCancellation.Basic
public import TauCeti.KnotTheory.BraidWord.DoubleCrossing

/-!
# Crossing data for free cancellation in braid closures

An inverse pair inserted at the top of a braid word contributes a Reidemeister-II clasp to its
closure.  This file records the local crossing data needed by the eventual diagrammatic
identification: old crossings retain their signs, and the two new crossings have opposite signs
and opposite over-pair indicators.  The existing `DoubleCrossing` API supplies the two internal
arcs; the remaining closure theorem must match the external arcs with a `PDCode.insertClasp` and
prove its face condition.

The pair is appended so its crossing names are the final two `Fin` indices.  This is the numbering
used by `PDCode.insertClasp`, and lets later proofs compare old blocks by `Fin.castAdd 2`.
-/

public section
namespace TauCeti
namespace BraidWord

open BraidGroup PDCode

variable {n : ℕ}

/-- The sign of an old crossing is unchanged when an inverse pair is appended. -/
theorem crossingSign_closure_append_freeCancel_old (v : BraidWord n) (i : Fin (n - 1))
    (ε : ℤˣ) (j : Fin v.length) :
    (closure (v ++ [(i, ε), (i, -ε)])).crossingSign
        (Fin.cast (by simp [List.length_append]) (Fin.castAdd 2 j)) =
      v.closure.crossingSign j := by
  rw [crossingSign_closure, crossingSign_closure]
  simp [List.getElem_append_left j.isLt]

/-- The first crossing of an appended inverse pair has the sign of its letter. -/
theorem crossingSign_closure_append_freeCancel_first (v : BraidWord n) (i : Fin (n - 1))
    (ε : ℤˣ) :
    (closure (v ++ [(i, ε), (i, -ε)])).crossingSign
        ⟨v.length, by simp [List.length_append]⟩ = ε := by
  rw [crossingSign_closure]
  simp [List.getElem_append_right]

/-- The second crossing of an appended inverse pair has the opposite sign. -/
theorem crossingSign_closure_append_freeCancel_second (v : BraidWord n) (i : Fin (n - 1))
    (ε : ℤˣ) :
    (closure (v ++ [(i, ε), (i, -ε)])).crossingSign
        ⟨v.length + 1, by simp [List.length_append]⟩ = -ε := by
  rw [crossingSign_closure]
  simp [List.getElem_append_right]

/-- Opposite appended letters produce opposite over-pair indicators at the two new crossings. -/
theorem overPair_closure_append_freeCancel_second_eq_not_first
    (v : BraidWord n) (i : Fin (n - 1))
    (ε : ℤˣ) :
    (closure (v ++ [(i, ε), (i, -ε)])).overPair
        ⟨v.length + 1, by simp [List.length_append]⟩ =
      !(closure (v ++ [(i, ε), (i, -ε)])).overPair
        ⟨v.length, by simp [List.length_append]⟩ := by
  rw [overPair_closure, overPair_closure]
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

end BraidWord
end TauCeti
