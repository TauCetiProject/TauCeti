/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Commutation
public import TauCeti.KnotTheory.Grid.Homology.Bigraded.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Move.Components
public import TauCeti.KnotTheory.Grid.Move.Stabilization
public import TauCeti.KnotTheory.Grid.Stabilization.Bigraded
public import TauCeti.KnotTheory.Grid.Stabilization.NorthEast.Grading

/-!
# Maslov--Alexander bigraded invariance of `GH⁻` under grid moves

For a knot grid over a commutative ring `K` of characteristic two, every elementary grid move
preserves the unblocked grid homology `GH⁻` as a Maslov--Alexander bigraded `K[U]`-module, in the
sense of `GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic`:
- cyclic row and column permutations (`bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate`,
  `bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate`);
- row and column commutations (`bigradedUnblockedHomologyIsomorphic_of_isCommutation`, in
  `TauCeti.KnotTheory.Grid.Homology.Bigraded.Commutation`);
- south-west and north-east corner `X`-stabilizations
  (`bigradedUnblockedHomologyIsomorphic_stabilizeX`,
  `bigradedUnblockedHomologyIsomorphic_stabilizeX_succ`), and hence all eight elementary
  stabilization types (`bigradedUnblockedHomologyIsomorphic_of_isStabilization`) and
  destabilizations.

Passing to the equivalence closure shows that knot grid diagrams connected by arbitrary grid moves
have isomorphic Maslov--Alexander bigraded `K[U]`-modules `GH⁻`
(`GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_of_movesTo`), and hence equal ground-ring
`finrank` in every Maslov--Alexander bidegree
(`GridDiagram.IsKnot.finrank_bigradedUnblockedHomologyGrading_piece_eq_of_movesTo`). For the
resulting `GridLink` piece-`finrank` invariant and its concrete evaluations on `GridLink.unknot`,
see `TauCeti.KnotTheory.Grid.Move.Bigraded`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3, 4.6 and Theorem 5.3.1
(Chapter 5). The move-closure induction adapts the Alexander-graded invariance argument in
`TauCeti.KnotTheory.Grid.Homology.Invariance`
(`GridDiagram.IsKnot.unblockedHomologyIsomorphic_of_movesTo`).
-/

public section

open MvPolynomial

namespace TauCeti.GridDiagram.IsKnot

variable {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}
  (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

open OddComponentGridDiagram in
/-- **Cyclic permutation of the rows preserves bigraded `GH⁻`** of a knot grid over `K[U]`. -/
theorem bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate :
    hG.BigradedUnblockedHomologyIsomorphic ((G.isKnot_relabelRows (finRotate n)).mpr hG) K := by
  refine .of_semilinearMap (σ := RingHom.id _) (fun _ ↦ rfl)
    (G.unblockedHomologyRelabelRowsFinRotateEquiv K).toLinearMap
    (G.unblockedHomologyRelabelRowsFinRotateEquiv K).bijective fun g y hy ↦ ?_
  rw [bigradedUnblockedHomologyGrading_piece] at hy ⊢
  exact (unblockedHomologyRelabelRowsFinRotateEquiv_mem_bigradedPiece_iff _ K).mpr hy

open OddComponentGridDiagram in
/-- **Cyclic permutation of the columns preserves bigraded `GH⁻`** of a knot grid over `K[U]`. -/
theorem bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate :
    hG.BigradedUnblockedHomologyIsomorphic ((G.isKnot_relabelColumns (finRotate n)).mpr hG) K := by
  refine .of_semilinearMap (fun p ↦ ?_)
    (G.unblockedHomologyRelabelColumnsFinRotateEquiv K).toLinearMap
    (G.unblockedHomologyRelabelColumnsFinRotateEquiv K).bijective fun g y hy ↦ ?_
  · simp [aeval_rename, Function.comp_def]
  · rw [bigradedUnblockedHomologyGrading_piece] at hy ⊢
    exact (unblockedHomologyRelabelColumnsFinRotateEquiv_mem_bigradedPiece_iff _ K).mpr hy

/-- **South-west corner `X`-stabilization preserves bigraded `GH⁻`** of a knot grid over `K[U]`. -/
theorem bigradedUnblockedHomologyIsomorphic_stabilizeX (s : Fin n) :
    hG.BigradedUnblockedHomologyIsomorphic
      ((G.isKnot_stabilizeX s.castSucc (G.X s).castSucc s).mpr hG) K := by
  refine (BigradedUnblockedHomologyIsomorphic.of_semilinearMap
    (fun p ↦ by rw [AlgHom.coe_toRingHom, aeval_rename, Function.comp_def])
    (G.stabilizeXHomologyMap s K) (G.stabilizeXHomologyMap_bijective s K) fun g y hy ↦ ?_).symm
  rw [bigradedUnblockedHomologyGrading_piece] at hy ⊢
  exact hG.toOddComponentGridDiagram.stabilizeXHomologyMap_mem_bigradedUnblockedHomologyPiece s K hy

/-- **North-east corner `X`-stabilization preserves bigraded `GH⁻`** of a knot grid over `K[U]`. -/
theorem bigradedUnblockedHomologyIsomorphic_stabilizeX_succ (s : Fin n) :
    hG.BigradedUnblockedHomologyIsomorphic
      ((G.isKnot_stabilizeX s.succ (G.X s).succ s).mpr hG) K := by
  refine (BigradedUnblockedHomologyIsomorphic.of_semilinearMap
    (fun p ↦ by rw [AlgHom.coe_toRingHom, aeval_rename, Function.comp_def])
    (G.stabilizeXSuccHomologyMap s K) (G.stabilizeXSuccHomologyMap_bijective s K)
    fun g y hy ↦ ?_).symm
  rw [bigradedUnblockedHomologyGrading_piece] at hy ⊢
  exact hG.toOddComponentGridDiagram.stabilizeXSuccHomologyMap_mem_bigradedUnblockedHomologyPiece
    s K hy

/-- Cyclic permutations and commutations preserve bigraded `GH⁻` along every size-preserving
sequence. -/
theorem bigradedUnblockedHomologyIsomorphic_of_commutationMovesTo {H : GridDiagram n}
    (hH : H.IsKnot) (h : G.CommutationMovesTo H) :
    hG.BigradedUnblockedHomologyIsomorphic hH K :=
  h.induction_on
    (motive := fun A B ↦ ∀ (hA : A.IsKnot) (hB : B.IsKnot),
      hA.BigradedUnblockedHomologyIsomorphic hB K)
    (fun _ hA _ ↦ hA.bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate K)
    (fun _ hA _ ↦ hA.bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate K)
    (fun h hA hB ↦ hA.bigradedUnblockedHomologyIsomorphic_of_isCommutation K hB h)
    (fun _ hA _ ↦ .refl hA K)
    (fun _ ih hA hB ↦ (ih hB hA).symm)
    (fun h _ ih ih' hA hB ↦
      (ih hA (h.movesTo.isKnot_iff.mpr hA)).trans
        (ih' (h.movesTo.isKnot_iff.mpr hA) hB)) hG hH

/-- Every elementary stabilization, of either marking and in any corner, preserves bigraded
`GH⁻`. -/
theorem bigradedUnblockedHomologyIsomorphic_of_isStabilization {H : GridDiagram (n + 1)}
    (hH : H.IsKnot) (h : G.IsStabilization H) :
    hG.BigradedUnblockedHomologyIsomorphic hH K := by
  obtain ⟨s, hs | hs⟩ := h.exists_commutationMovesTo
  · exact (hG.bigradedUnblockedHomologyIsomorphic_stabilizeX K s).trans
      (bigradedUnblockedHomologyIsomorphic_of_commutationMovesTo _ K hH hs.symm)
  · exact (hG.bigradedUnblockedHomologyIsomorphic_stabilizeX_succ K s).trans
      (bigradedUnblockedHomologyIsomorphic_of_commutationMovesTo _ K hH hs.symm)

/-- Each elementary grid move, including a destabilization, preserves `GH⁻` as a Maslov--Alexander
bigraded `K[U]`-module. -/
theorem bigradedUnblockedHomologyIsomorphic_of_isMove (hG' : G'.IsKnot)
    (h : IsMove ⟨n, G⟩ ⟨m, G'⟩) :
    hG.BigradedUnblockedHomologyIsomorphic hG' K := by
  cases h with
  | cyclicRows h =>
    rcases h with rfl | rfl
    · exact hG.bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate K
    · exact (hG'.bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate K).symm
  | cyclicColumns h =>
    rcases h with rfl | rfl
    · exact hG.bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate K
    · exact (hG'.bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate K).symm
  | commutation h => exact hG.bigradedUnblockedHomologyIsomorphic_of_isCommutation K hG' h
  | stabilization h => exact hG.bigradedUnblockedHomologyIsomorphic_of_isStabilization K hG' h
  | destabilization h =>
    exact (hG'.bigradedUnblockedHomologyIsomorphic_of_isStabilization K hG
      ((isDestabilization_iff_isStabilization _ _).mp h)).symm

/-- **Maslov--Alexander bigraded invariance of `GH⁻` under grid moves.** Knot grid diagrams
connected by arbitrary grid moves have isomorphic unblocked grid homologies as Maslov--Alexander
bigraded `K[U]`-modules. -/
theorem bigradedUnblockedHomologyIsomorphic_of_movesTo (hG' : G'.IsKnot) (h : G.MovesTo G') :
    hG.BigradedUnblockedHomologyIsomorphic hG' K :=
  h.induction_on
    (motive := fun A B ↦ ∀ (hA : A.2.IsKnot) (hB : B.2.IsKnot),
      hA.BigradedUnblockedHomologyIsomorphic hB K)
    (fun h hA hB ↦ hA.bigradedUnblockedHomologyIsomorphic_of_isMove K hB h)
    (fun _ hA _ ↦ .refl hA K)
    (fun _ ih hA hB ↦ (ih hB hA).symm)
    (fun h _ ih ih' hA hB ↦
      (ih hA (h.isKnot_iff.mpr hA)).trans (ih' (h.isKnot_iff.mpr hA) hB)) hG hG'

/-- Knot grid diagrams connected by arbitrary grid moves have equal ground-ring `finrank` in every
Maslov--Alexander bidegree of `GH⁻`. -/
theorem finrank_bigradedUnblockedHomologyGrading_piece_eq_of_movesTo (hG' : G'.IsKnot)
    (h : G.MovesTo G') (g : ℤ × ℤ) :
    Module.finrank K ((hG.bigradedUnblockedHomologyGrading K).piece g) =
      Module.finrank K ((hG'.bigradedUnblockedHomologyGrading K).piece g) :=
  (hG.bigradedUnblockedHomologyIsomorphic_of_movesTo K hG' h).finrank_piece_eq g

end TauCeti.GridDiagram.IsKnot
