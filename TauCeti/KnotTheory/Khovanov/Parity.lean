/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.CircleTensor
public import TauCeti.KnotTheory.Khovanov.EnhancedState.Parity

/-!
# Component parity of the Khovanov quantum grading

For an oriented planar diagram with `c` link components, every enhanced state has quantum
degree congruent to `c` modulo two
(`TauCeti.OrientedPDCode.enhancedQuantumDegree_mod_two` in
`TauCeti.KnotTheory.Khovanov.EnhancedState.Parity`). Consequently the shifted resolution modules
vanish in quantum degrees of the opposite parity, over every commutative coefficient ring.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000),
  §§2–3 (enhanced states and their grading).
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2 (the parity of the quantum grading).
-/

public section

namespace TauCeti.OrientedPDCode

variable {n : ℕ} (D : OrientedPDCode n)

/-- A normalized resolution module is zero in every quantum degree of the wrong component
parity. No nontriviality or characteristic assumption on the coefficient ring is needed. -/
theorem circleQuantumGrading_piece_eq_bot_of_mod_two_ne (hD : D.toPDCode.IsPlanar)
    (R : Type*) [CommRing R] (s : Fin n → Bool) {j : ℤ}
    (hj : j % 2 ≠ (D.componentCount : ℤ) % 2) :
    (Khovanov.circleQuantumGrading R (D.ResolvedCircle s)).piece
      (j - D.stateQuantumShift s) = ⊥ := by
  apply Khovanov.circleQuantumGrading_piece_eq_bot
  intro l hl
  have h := D.enhancedQuantumDegree_mod_two hD ⟨s, l⟩
  rw [enhancedQuantumDegree_def] at h
  dsimp only at h
  omega

end TauCeti.OrientedPDCode
