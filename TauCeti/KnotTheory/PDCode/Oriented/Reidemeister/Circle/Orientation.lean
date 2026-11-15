/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Equivalence

/-!
# Reversing an isolated circle

The two directions on an isolated crossing-free circle give Reidemeister-equivalent
oriented diagrams, with every component of the surrounding diagram unchanged. This allows
circle-and-arc moves to be used on either side of an oriented arc. It does not assert
that an arbitrary component of an oriented link can be reversed.

The construction adds an isolated kink, relabels its four half-edges by a half-turn,
reads the crossing from the opposite slot, and removes the kink. It uses the existing
`OrientedPDCode.adjoinKink`, relabeling, and crossing-rotation constructions.

Reference: W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1.
-/

public section

namespace TauCeti.OrientedPDCode

open Equiv PDCode

variable {n : ℕ}

private def kinkHalfTurn (n : ℕ) : Fin (4 * (n + 1)) ≃ Fin (4 * (n + 1)) :=
  (halfEdgeSuccEquiv n).symm.trans
    ((Equiv.sumCongr (Equiv.refl _) ((finRotate 4).trans (finRotate 4))).trans
      (halfEdgeSuccEquiv n))

@[simp] private theorem kinkHalfTurn_inl (x : Fin (4 * n)) :
    kinkHalfTurn n (halfEdgeSuccEquiv n (.inl x)) = halfEdgeSuccEquiv n (.inl x) := by
  simp [kinkHalfTurn]

@[simp] private theorem kinkHalfTurn_inr (s : Fin 4) :
    kinkHalfTurn n (halfEdgeSuccEquiv n (.inr s)) =
      halfEdgeSuccEquiv n (.inr (s + 1 + 1)) := by
  simp [kinkHalfTurn]

@[simp] private theorem kinkHalfTurn_symm_inl (x : Fin (4 * n)) :
    (kinkHalfTurn n).symm (halfEdgeSuccEquiv n (.inl x)) =
      halfEdgeSuccEquiv n (.inl x) := by
  apply (kinkHalfTurn n).symm_apply_eq.mpr
  simp

@[simp] private theorem kinkHalfTurn_symm_inr (s : Fin 4) :
    (kinkHalfTurn n).symm (halfEdgeSuccEquiv n (.inr s)) =
      halfEdgeSuccEquiv n (.inr (s + 1 + 1)) := by
  apply (kinkHalfTurn n).symm_apply_eq.mpr
  rw [kinkHalfTurn_inr]
  fin_cases s <;> rfl

private theorem readKink_eq (D : OrientedPDCode n) (o b : Bool) :
    (((D.adjoinKink o b).relabel (kinkHalfTurn n) (Equiv.refl _)).rotateCrossing
      (Fin.last n)).rotateCrossing (Fin.last n) = D.adjoinKink (!o) b := by
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · apply Equiv.ext
      intro x
      obtain ⟨⟨j, s⟩, rfl⟩ := (crossingSlotEquiv (n + 1)).surjective x
      simp only [toPDCode_rotateCrossing, relabel_toPDCode, toPDCode_adjoinKink]
      induction j using Fin.lastCases with
      | last =>
          rw [rotateCrossing_crossing_self, rotateCrossing_crossing_self]
          rw [← crossing_apply, crossing_relabel]
          simp only [Equiv.refl_symm, Equiv.refl_apply,
            adjoinKink_crossing_last, kinkHalfTurn_inr]
          rw [← crossing_apply, adjoinKink_crossing_last]
          fin_cases s <;> rfl
      | cast j =>
          rw [rotateCrossing_crossing_of_ne _ _ (Fin.castSucc_ne_last j),
            rotateCrossing_crossing_of_ne _ _ (Fin.castSucc_ne_last j)]
          rw [← crossing_apply, crossing_relabel]
          simp
    · apply Subtype.ext
      ext x
      obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
      · simp [PerfectMatching.congr_val]
      · fin_cases s <;>
          simp [PerfectMatching.congr_val,
            slotSmoothing_true, Equiv.swap_apply_def]
    · simp
    · funext j
      induction j using Fin.lastCases <;> simp
  · funext x
    obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
    · simp
    · fin_cases s <;> cases o <;> simp
  · simp

/-- Reversing a newly adjoined isolated circle preserves oriented Reidemeister equivalence,
without reversing any component of the surrounding diagram. -/
theorem reidemeisterEquiv_adjoinCircle_not (D : OrientedPDCode n) (o : Bool) :
    ReidemeisterEquiv (D.adjoinCircle o) (D.adjoinCircle (!o)) := by
  have hread := (reidemeisterEquiv_relabel (D.adjoinKink o true)
    (kinkHalfTurn n) (Equiv.refl _)).trans
      ((reidemeisterEquiv_rotateCrossing _ (Fin.last n)).trans
        (reidemeisterEquiv_rotateCrossing _ (Fin.last n)))
  rw [readKink_eq] at hread
  exact (reidemeisterEquiv_adjoinKink D o true).trans
    (hread.trans (reidemeisterEquiv_adjoinKink D (!o) true).symm)

end TauCeti.OrientedPDCode
