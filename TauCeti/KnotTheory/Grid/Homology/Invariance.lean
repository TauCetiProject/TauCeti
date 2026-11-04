/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Commutation.Invariance
public import TauCeti.KnotTheory.Grid.Homology.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Homology.Tau
public import TauCeti.KnotTheory.Grid.Move.Stabilization
public import TauCeti.KnotTheory.Grid.Move.Components
public import TauCeti.KnotTheory.Grid.Stabilization.NorthEast.Basic

/-!
# Invariance of `GH⁻` and of `τ` under grid moves

The unblocked grid homology `GH⁻` of a knot grid, as an Alexander-graded `K[U]`-module, does not
change under any sequence of grid moves: knot grids connected by grid moves have isomorphic `GH⁻`
in the sense of `GridDiagram.IsKnot.UnblockedHomologyIsomorphic`
(`GridDiagram.IsKnot.unblockedHomologyIsomorphic_of_movesTo`). The two corner stabilization
comparisons, together with cyclic permutations and commutations, cover all eight elementary
stabilization types. Passing to the equivalence closure includes arbitrary destabilizations and
move sequences between diagrams of different sizes. Consequently the diagram invariant
`GridDiagram.IsKnot.tau` is unchanged by grid moves (`GridDiagram.IsKnot.tau_eq_of_movesTo`).

This establishes independence of the presenting diagram for the isomorphism class of the
Alexander-graded `K[U]`-module `GH⁻`, and hence for `τ`. It does not identify the homology maps
associated to different move sequences, and it says nothing about the Maslov grading.

## Main results

* `TauCeti.GridDiagram.IsKnot.unblockedHomologyIsomorphic_of_isMove`: an elementary grid move,
  including a destabilization, preserves `GH⁻` as an Alexander-graded `K[U]`-module.
* `TauCeti.GridDiagram.IsKnot.unblockedHomologyIsomorphic_of_movesTo`: **invariance of `GH⁻`**,
  knot grids connected by grid moves have isomorphic Alexander-graded `GH⁻`.
* `TauCeti.GridDiagram.IsKnot.tau_eq_of_movesTo`: knot grids connected by grid moves have the
  same invariant `τ`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3, 5 and 6, in particular
the invariance of `GH⁻` under grid moves in Chapter 5.
The proof assembles the existing cyclic-permutation, commutation and corner-stabilization
invariance theorems using `GridDiagram.IsStabilization.exists_commutationMovesTo`.
-/

public section

namespace TauCeti.GridDiagram.IsKnot

variable {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}
    (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- Cyclic permutations and commutations preserve `GH⁻` along every size-preserving sequence. -/
theorem unblockedHomologyIsomorphic_of_commutationMovesTo {H : GridDiagram n} (hH : H.IsKnot)
    (h : G.CommutationMovesTo H) : hG.UnblockedHomologyIsomorphic hH K := by
  exact h.induction_on
    (motive := fun A B ↦ ∀ (hA : A.IsKnot) (hB : B.IsKnot), hA.UnblockedHomologyIsomorphic hB K)
    (fun _ hA _ ↦ hA.unblockedHomologyIsomorphic_relabelRows_finRotate K)
    (fun _ hA _ ↦ hA.unblockedHomologyIsomorphic_relabelColumns_finRotate K)
    (fun h hA hB ↦ hA.unblockedHomologyIsomorphic_of_isCommutation K hB h)
    (fun _ hA _ ↦ .refl hA K)
    (fun _ ih hA hB ↦ (ih hB hA).symm)
    (fun h _ ih ih' hA hB ↦
      (ih hA (h.movesTo.isKnot_iff.mpr hA)).trans
        (ih' (h.movesTo.isKnot_iff.mpr hA) hB)) hG hH

/-- Every elementary stabilization, of either marking and in any corner, preserves `GH⁻`. -/
theorem unblockedHomologyIsomorphic_of_isStabilization {H : GridDiagram (n + 1)} (hH : H.IsKnot)
    (h : G.IsStabilization H) : hG.UnblockedHomologyIsomorphic hH K := by
  obtain ⟨s, hs | hs⟩ := h.exists_commutationMovesTo
  · exact (hG.unblockedHomologyIsomorphic_stabilizeX s K).trans
      (unblockedHomologyIsomorphic_of_commutationMovesTo _ K hH hs.symm)
  · exact (hG.unblockedHomologyIsomorphic_stabilizeX_succ s K).trans
      (unblockedHomologyIsomorphic_of_commutationMovesTo _ K hH hs.symm)

/-- Each elementary grid move preserves `GH⁻` as an Alexander-graded `K[U]`-module, including a
destabilization. -/
theorem unblockedHomologyIsomorphic_of_isMove (hG' : G'.IsKnot) (h : IsMove ⟨n, G⟩ ⟨m, G'⟩) :
    hG.UnblockedHomologyIsomorphic hG' K := by
  cases h with
  | cyclicRows h =>
    rcases h with rfl | rfl
    · exact hG.unblockedHomologyIsomorphic_relabelRows_finRotate K
    · exact (hG'.unblockedHomologyIsomorphic_relabelRows_finRotate K).symm
  | cyclicColumns h =>
    rcases h with rfl | rfl
    · exact hG.unblockedHomologyIsomorphic_relabelColumns_finRotate K
    · exact (hG'.unblockedHomologyIsomorphic_relabelColumns_finRotate K).symm
  | commutation h => exact hG.unblockedHomologyIsomorphic_of_isCommutation K hG' h
  | stabilization h => exact hG.unblockedHomologyIsomorphic_of_isStabilization K hG' h
  | destabilization h =>
    exact (hG'.unblockedHomologyIsomorphic_of_isStabilization K hG
      ((isDestabilization_iff_isStabilization _ _).mp h)).symm

/-- **Invariance of `GH⁻` under grid moves.** Knot grid diagrams connected by arbitrary grid
moves have isomorphic unblocked grid homologies as Alexander-graded `K[U]`-modules. -/
theorem unblockedHomologyIsomorphic_of_movesTo (hG' : G'.IsKnot) (h : G.MovesTo G') :
    hG.UnblockedHomologyIsomorphic hG' K := by
  exact h.induction_on
    (motive := fun A B ↦ ∀ (hA : A.2.IsKnot) (hB : B.2.IsKnot),
      hA.UnblockedHomologyIsomorphic hB K)
    (fun h hA hB ↦ hA.unblockedHomologyIsomorphic_of_isMove K hB h)
    (fun _ hA _ ↦ .refl hA K)
    (fun _ ih hA hB ↦ (ih hB hA).symm)
    (fun h _ ih ih' hA hB ↦
      (ih hA (h.isKnot_iff.mpr hA)).trans (ih' (h.isKnot_iff.mpr hA) hB)) hG hG'

/-- Knot grid diagrams connected by arbitrary grid moves have the same invariant `τ`. -/
theorem tau_eq_of_movesTo (hG' : G'.IsKnot) (h : G.MovesTo G') :
    hG.tau K = hG'.tau K :=
  (hG.unblockedHomologyIsomorphic_of_movesTo K hG' h).tau_eq

end TauCeti.GridDiagram.IsKnot
