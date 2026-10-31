/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.Equivalence
public import TauCeti.KnotTheory.BraidWord.SeifertMatrix.Basic
import TauCeti.KnotTheory.BraidWord.FreeCancellation.SeifertMatrix
import TauCeti.KnotTheory.BraidWord.SeifertMatrix.BraidRelation

/-!
# Words of the same braid have Seifert matrices with the same signatures

Two braid words represent the same braid exactly when they are connected by Artin relations and
free cancellation of inverse pairs. An Artin relation changes the Seifert matrix
`TauCeti.BraidWord.seifertMatrix` of the closure by a congruence
(`TauCeti.BraidWord.tristramLevineSignature_seifertMatrix_eq_of_artinStep`), and a free insertion or
deletion by an elementary enlargement or a zero row and column
(`TauCeti.BraidWord.FreeCancelStep.tristramLevineSignature_seifertMatrix_eq`). None of these changes
the Tristram–Levine signatures, so they depend only on the braid.

## Main results

* `TauCeti.BraidWord.WordEquiv.tristramLevineSignature_seifertMatrix_eq` and
  `TauCeti.BraidWord.tristramLevineSignature_seifertMatrix_eq_of_toBraid_eq`: words representing the
  same braid have Seifert matrices with the same Tristram–Levine signatures.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 6
  (Seifert matrices) and Chapter 8 (the signature).
-/

public section

namespace TauCeti

open KnotTheory

namespace BraidWord

variable {n : ℕ} {w w' : BraidWord n}

/-- Braid words connected by Artin relations and free cancellation have Seifert matrices with the
same Tristram–Levine signatures. -/
theorem WordEquiv.tristramLevineSignature_seifertMatrix_eq (h : WordEquiv w w') (ω : ℂ) :
    tristramLevineSignature (w.seifertMatrix.map ((↑) : ℤ → ℝ)) ω =
      tristramLevineSignature (w'.seifertMatrix.map ((↑) : ℤ → ℝ)) ω :=
  WordEquiv.induction (fun h ↦ tristramLevineSignature_seifertMatrix_eq_of_artinStep h ω)
    (fun h ↦ h.tristramLevineSignature_seifertMatrix_eq ω) (fun _ ↦ rfl) (fun _ ih ↦ ih.symm)
    (fun _ _ ih ih' ↦ ih.trans ih') h

/-- **The signatures of the Seifert matrix depend only on the braid.** Two braid words
representing the same braid have Seifert matrices with the same Tristram–Levine signatures. -/
theorem tristramLevineSignature_seifertMatrix_eq_of_toBraid_eq (h : w.toBraid = w'.toBraid)
    (ω : ℂ) :
    tristramLevineSignature (w.seifertMatrix.map ((↑) : ℤ → ℝ)) ω =
      tristramLevineSignature (w'.seifertMatrix.map ((↑) : ℤ → ℝ)) ω :=
  (toBraid_eq_iff_wordEquiv.mp h).tristramLevineSignature_seifertMatrix_eq ω

end BraidWord

end TauCeti
