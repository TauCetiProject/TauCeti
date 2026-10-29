/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Commutation.Invariance
public import TauCeti.KnotTheory.Grid.Homology.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Move.Stabilization
public import TauCeti.KnotTheory.Grid.Move.Components
public import TauCeti.KnotTheory.Grid.Stabilization.NorthEast.Basic

/-!
# Invariance of `τ` under grid moves

The diagram invariant `GridDiagram.IsKnot.tau` is unchanged by any sequence of grid moves.
The two corner stabilization comparisons, together with cyclic permutations and commutations,
cover all eight elementary stabilization types. Passing to the equivalence closure includes
arbitrary destabilizations and move sequences between diagrams of different sizes.

This establishes independence of the presenting diagram for the integer invariant `τ`.
It does not identify the homology maps associated to different move sequences.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3, 5 and 6.
The proof assembles the existing cyclic-permutation, commutation and corner-stabilization
invariance theorems using `GridDiagram.IsStabilization.exists_commutationMovesTo`.
-/

public section

namespace TauCeti.GridDiagram.IsKnot

variable {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}
    (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- Cyclic permutations and commutations preserve `τ` along every size-preserving sequence. -/
theorem tau_eq_of_commutationMovesTo {H : GridDiagram n} (hH : H.IsKnot)
    (h : G.CommutationMovesTo H) : hG.tau K = hH.tau K := by
  exact h.induction_on
    (motive := fun A B ↦ ∀ (hA : A.IsKnot) (hB : B.IsKnot), hA.tau K = hB.tau K)
    (fun _ hA _ ↦ (hA.tau_relabelRows_finRotate K).symm)
    (fun _ hA _ ↦ (hA.tau_relabelColumns_finRotate K).symm)
    (fun h hA hB ↦ hA.tau_eq_of_isCommutation K hB h)
    (fun _ _ _ ↦ rfl)
    (fun _ ih hA hB ↦ (ih hB hA).symm)
    (fun h _ ih ih' hA hB ↦
      (ih hA (h.movesTo.isKnot_iff.mpr hA)).trans
        (ih' (h.movesTo.isKnot_iff.mpr hA) hB)) hG hH

/-- Every elementary stabilization, of either marking and in any corner, preserves `τ`. -/
theorem tau_eq_of_isStabilization {H : GridDiagram (n + 1)} (hH : H.IsKnot)
    (h : G.IsStabilization H) : hG.tau K = hH.tau K := by
  obtain ⟨s, hs | hs⟩ := h.exists_commutationMovesTo
  · exact (hG.tau_stabilizeX s K).symm.trans
      (tau_eq_of_commutationMovesTo _ K hH hs.symm)
  · exact (hG.tau_stabilizeX_succ s K).symm.trans
      (tau_eq_of_commutationMovesTo _ K hH hs.symm)

/-- Each elementary grid move preserves `τ`, including a destabilization. -/
theorem tau_eq_of_isMove (hG' : G'.IsKnot) (h : IsMove ⟨n, G⟩ ⟨m, G'⟩) :
    hG.tau K = hG'.tau K := by
  cases h with
  | cyclicRows h =>
    rcases h with rfl | rfl
    · exact (hG.tau_relabelRows_finRotate K).symm
    · exact hG'.tau_relabelRows_finRotate K
  | cyclicColumns h =>
    rcases h with rfl | rfl
    · exact (hG.tau_relabelColumns_finRotate K).symm
    · exact hG'.tau_relabelColumns_finRotate K
  | commutation h => exact hG.tau_eq_of_isCommutation K hG' h
  | stabilization h => exact hG.tau_eq_of_isStabilization K hG' h
  | destabilization h =>
    exact (hG'.tau_eq_of_isStabilization K hG
      ((isDestabilization_iff_isStabilization _ _).mp h)).symm

/-- Knot grid diagrams connected by arbitrary grid moves have the same invariant `τ`. -/
theorem tau_eq_of_movesTo (hG' : G'.IsKnot) (h : G.MovesTo G') :
    hG.tau K = hG'.tau K := by
  exact h.induction_on
    (motive := fun A B ↦ ∀ (hA : A.2.IsKnot) (hB : B.2.IsKnot), hA.tau K = hB.tau K)
    (fun h hA hB ↦ hA.tau_eq_of_isMove K hB h)
    (fun _ _ _ ↦ rfl)
    (fun _ ih hA hB ↦ (ih hB hA).symm)
    (fun h _ ih ih' hA hB ↦
      (ih hA (h.isKnot_iff.mpr hA)).trans (ih' (h.isKnot_iff.mpr hA) hB)) hG hG'

end TauCeti.GridDiagram.IsKnot
