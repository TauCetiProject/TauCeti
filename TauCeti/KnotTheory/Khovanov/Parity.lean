/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.CircleTensor
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Planar
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Seifert

/-!
# Component parity of the Khovanov quantum grading

For an oriented planar diagram with `c` link components, every enhanced state has quantum
degree congruent to `c` modulo two. Consequently the shifted resolution modules vanish in
quantum degrees of the opposite parity, over every commutative coefficient ring.

The Seifert state supplies the reference parity: its circle count `s` satisfies
`s - n + c ≡ 0 (mod 2)`. Along a planar cube edge both the B-smoothing count and the circle
count change by one. Labelling a circle by `X` instead of `1` changes the degree by two.
Crossing-free circles are counted throughout, including for the empty diagram.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000),
  §§2–3 (enhanced states and their grading).
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2 (the parity of the quantum grading).
-/

public section

namespace TauCeti.OrientedPDCode

open Finset

variable {n : ℕ} (D : OrientedPDCode n)

/-- The normalized quantum shift plus the number of resolution circles has the parity of
the number of link components, independently of the state. -/
theorem stateQuantumShift_add_stateLoopCount_mod_two (hD : D.toPDCode.IsPlanar)
    (s : Fin n → Bool) :
    (D.stateQuantumShift s + D.stateLoopCount s) % 2 = (D.componentCount : ℤ) % 2 := by
  have hseifert := D.even_seifertCircleCount_sub_crossingCount_add_componentCount
  rw [Int.even_iff] at hseifert
  have hstates := hD.card_false_add_stateLoopCount_mod_two_eq s D.seifertState
  have hnegative : #{i | D.seifertState i = false} = D.negativeCrossingCount := by
    simp [negativeCrossingCount_def]
  rw [hnegative] at hstates
  have hcrossings := D.positiveCrossingCount_add_negativeCrossingCount
  rw [stateQuantumShift_def]
  omega

/-- Every enhanced state of a planar diagram has quantum degree congruent modulo two to
the number of link components. -/
theorem enhancedQuantumDegree_mod_two (hD : D.toPDCode.IsPlanar)
    (e : D.toPDCode.EnhancedState) :
    D.enhancedQuantumDegree e % 2 = (D.componentCount : ℤ) % 2 := by
  have h := D.stateQuantumShift_add_stateLoopCount_mod_two hD e.1
  rw [enhancedQuantumDegree_def, Khovanov.labelingQuantumDegree_eq,
    PDCode.card_resolvedCircle]
  omega

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
