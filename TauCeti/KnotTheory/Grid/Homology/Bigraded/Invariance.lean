/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Homology.Commutation.Invariance
public import TauCeti.KnotTheory.Grid.Homology.Transpose
public import TauCeti.KnotTheory.Grid.Move.Components
public import TauCeti.KnotTheory.Grid.Move.Stabilization
public import TauCeti.KnotTheory.Grid.Stabilization.Bigraded
public import TauCeti.KnotTheory.Grid.Stabilization.NorthEast.Grading

/-!
# Invariance of the bigraded `K[U]`-module `GH⁻` under grid moves

The unblocked grid homology `GH⁻` of a knot grid carries two gradings, the `O`-Maslov grading and
the Alexander grading (`OddComponentGridDiagram.bigradedUnblockedHomologyGrading`). Two knot grids
have isomorphic `GH⁻` as bigraded `K[U]`-modules
(`GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic`, in `Homology/Bigraded/Relation.lean`)
when some `K[U]`-linear equivalence between their homologies preserves the bigrading.

The cyclic permutations, the column commutations (through the pentagon map) and the south-west
and north-east corner `X`-stabilizations have specified comparison maps on `GH⁻` that preserve
both gradings. Row commutations reduce to column commutations through the diagonal reflection,
which is not a grid move but also preserves the bigrading
(`GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_transpose`, in
`Homology/Transpose.lean`). Since every stabilization type reduces to these two corners up to
cyclic permutations and commutations (`GridDiagram.IsStabilization.exists_commutationMovesTo`),
knot grids connected by grid moves have isomorphic `GH⁻` as bigraded `K[U]`-modules
(`GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_of_movesTo`), over every commutative ring
`K` of characteristic two. It concerns the isomorphism class of the bigraded module: the maps
attached to different move sequences are not compared.

Forgetting the Maslov grading gives the Alexander-graded relation
(`GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic.unblockedHomologyIsomorphic`). This is how
the invariance of the Alexander-graded `GH⁻` and of `τ` is derived in `Homology/Invariance.lean`.

## Main results

* `TauCeti.GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_of_isMove`: each elementary grid
  move, including a destabilization, preserves `GH⁻` as a bigraded `K[U]`-module.
* `TauCeti.GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_of_movesTo`: **invariance of the
  bigraded `GH⁻`**, knot grids connected by grid moves have isomorphic `GH⁻` as bigraded
  `K[U]`-modules.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Theorem 5.3.1 (invariance of the
bigraded `GH⁻` of a knot), with the commutation and stabilization comparisons of Sections 5.1 and
5.2; Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3
(arXiv:math/0610559).
-/

public section

open MvPolynomial

namespace TauCeti.GridDiagram.IsKnot

/-! ### The elementary moves -/

section Moves

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- **Cyclic permutation of the rows preserves the bigraded `GH⁻`** of a knot grid. -/
theorem bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate :
    hG.BigradedUnblockedHomologyIsomorphic ((G.isKnot_relabelRows (finRotate n)).mpr hG) K :=
  .of_semilinearMap (σ := RingHom.id _) (fun _ ↦ rfl)
    (G.unblockedHomologyRelabelRowsFinRotateEquiv K).toLinearMap
    (G.unblockedHomologyRelabelRowsFinRotateEquiv K).bijective fun _ _ hy ↦
      (OddComponentGridDiagram.unblockedHomologyRelabelRowsFinRotateEquiv_mem_bigradedPiece_iff
        hG.toOddComponentGridDiagram K).mpr hy

/-- **Cyclic permutation of the columns preserves the bigraded `GH⁻`** of a knot grid. -/
theorem bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate :
    hG.BigradedUnblockedHomologyIsomorphic ((G.isKnot_relabelColumns (finRotate n)).mpr hG) K :=
  .of_semilinearMap (fun _ ↦ by simp [aeval_rename, Function.comp_def])
    (G.unblockedHomologyRelabelColumnsFinRotateEquiv K).toLinearMap
    (G.unblockedHomologyRelabelColumnsFinRotateEquiv K).bijective fun _ _ hy ↦
      (OddComponentGridDiagram.unblockedHomologyRelabelColumnsFinRotateEquiv_mem_bigradedPiece_iff
        hG.toOddComponentGridDiagram K).mpr hy

/-- **The bigraded `GH⁻` is invariant under column commutation.** The commuted diagram of a knot
grid along validated column-commutation data has `GH⁻` isomorphic to that of the original as a
bigraded `K[U]`-module. -/
theorem bigradedUnblockedHomologyIsomorphic_swapColumns (C : ColumnCommutationData G) :
    hG.BigradedUnblockedHomologyIsomorphic (hG.swapColumns C.column (finRotate n C.column)) K := by
  refine .of_semilinearMap (fun _ ↦ by simp [aeval_rename, Function.comp_def])
    (G.unblockedHomologyCommutationMap K C) (G.unblockedHomologyCommutationMap_bijective C K)
    fun _ _ hy ↦ ?_
  -- The target piece is that of `hG.toOddComponentGridDiagram.swapColumns C`: both odd-component
  -- diagrams have underlying diagram `G.swapColumns C.column (finRotate n C.column)` by definition
  -- (`OddComponentGridDiagram.val_swapColumns`).
  change _ ∈ (hG.toOddComponentGridDiagram.swapColumns C).bigradedUnblockedHomologyPiece K _
  exact OddComponentGridDiagram.unblockedHomologyCommutationMap_mem_bigradedUnblockedHomologyPiece
    hG.toOddComponentGridDiagram K C hy

/-- **The bigraded `GH⁻` is invariant under elementary column commutations.** -/
theorem bigradedUnblockedHomologyIsomorphic_of_isColumnCommutation {G' : GridDiagram n}
    (hG' : G'.IsKnot) (h : IsColumnCommutation G G') :
    hG.BigradedUnblockedHomologyIsomorphic hG' K := by
  obtain ⟨C, rfl⟩ := isColumnCommutation_iff_exists_columnCommutationData.mp h
  exact hG.bigradedUnblockedHomologyIsomorphic_swapColumns K C

/-- **The bigraded `GH⁻` is invariant under elementary commutations.** A row commutation is a
column commutation of the diagonal reflections. -/
theorem bigradedUnblockedHomologyIsomorphic_of_isCommutation {G' : GridDiagram n}
    (hG' : G'.IsKnot) (h : IsCommutation G G') :
    hG.BigradedUnblockedHomologyIsomorphic hG' K := by
  rcases (isCommutation_iff G G').mp h with h | h
  · exact (hG.bigradedUnblockedHomologyIsomorphic_transpose K).trans
      ((bigradedUnblockedHomologyIsomorphic_of_isColumnCommutation _ K _
        ((isColumnCommutation_transpose G G').mpr h)).trans
        (hG'.bigradedUnblockedHomologyIsomorphic_transpose K).symm)
  · exact hG.bigradedUnblockedHomologyIsomorphic_of_isColumnCommutation K hG' h

/-- **The bigraded `GH⁻` is invariant under the south-west corner `X`-stabilization**, the
stabilization of a knot grid splitting the `X`-marking of column `s` with its new `O`-marking in
the south-west corner of the new block. -/
theorem bigradedUnblockedHomologyIsomorphic_stabilizeX (s : Fin n) :
    hG.BigradedUnblockedHomologyIsomorphic
      ((G.isKnot_stabilizeX s.castSucc (G.X s).castSucc s).mpr hG) K :=
  (BigradedUnblockedHomologyIsomorphic.of_semilinearMap
    (fun _ ↦ by rw [AlgHom.coe_toRingHom, aeval_rename, Function.comp_def])
    (G.stabilizeXHomologyMap s K) (G.stabilizeXHomologyMap_bijective s K) fun _ _ hy ↦
      hG.toOddComponentGridDiagram.stabilizeXHomologyMap_mem_bigradedUnblockedHomologyPiece s K
        hy).symm

/-- **The bigraded `GH⁻` is invariant under the north-east corner `X`-stabilization**, whose new
`O`-marking is the north-east corner of the new block. -/
theorem bigradedUnblockedHomologyIsomorphic_stabilizeX_succ (s : Fin n) :
    hG.BigradedUnblockedHomologyIsomorphic
      ((G.isKnot_stabilizeX s.succ (G.X s).succ s).mpr hG) K := by
  refine (BigradedUnblockedHomologyIsomorphic.of_semilinearMap
    (fun _ ↦ by rw [AlgHom.coe_toRingHom, aeval_rename, Function.comp_def])
    (G.stabilizeXSuccHomologyMap s K) (G.stabilizeXSuccHomologyMap_bijective s K)
    fun _ _ hy ↦ ?_).symm
  -- The source piece is that of `hG.toOddComponentGridDiagram.stabilizeXSucc s`: both
  -- odd-component diagrams have underlying diagram `G.stabilizeX s.succ (G.X s).succ s` by
  -- definition (`OddComponentGridDiagram.val_stabilizeXSucc`).
  change _ ∈ (hG.toOddComponentGridDiagram.stabilizeXSucc s).bigradedUnblockedHomologyPiece K _
    at hy
  exact OddComponentGridDiagram.stabilizeXSuccHomologyMap_mem_bigradedUnblockedHomologyPiece
    hG.toOddComponentGridDiagram s K hy

end Moves

/-! ### Move sequences -/

section MovesTo

variable {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}
    (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- Cyclic permutations and commutations preserve the bigraded `GH⁻` along every size-preserving
sequence. -/
theorem bigradedUnblockedHomologyIsomorphic_of_commutationMovesTo {H : GridDiagram n}
    (hH : H.IsKnot) (h : G.CommutationMovesTo H) :
    hG.BigradedUnblockedHomologyIsomorphic hH K := by
  exact h.induction_on
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

/-- Every elementary stabilization, of either marking and in any corner, preserves the bigraded
`GH⁻`. -/
theorem bigradedUnblockedHomologyIsomorphic_of_isStabilization {H : GridDiagram (n + 1)}
    (hH : H.IsKnot) (h : G.IsStabilization H) : hG.BigradedUnblockedHomologyIsomorphic hH K := by
  obtain ⟨s, hs | hs⟩ := h.exists_commutationMovesTo
  · exact (hG.bigradedUnblockedHomologyIsomorphic_stabilizeX K s).trans
      (bigradedUnblockedHomologyIsomorphic_of_commutationMovesTo _ K hH hs.symm)
  · exact (hG.bigradedUnblockedHomologyIsomorphic_stabilizeX_succ K s).trans
      (bigradedUnblockedHomologyIsomorphic_of_commutationMovesTo _ K hH hs.symm)

/-- Each elementary grid move, including a destabilization, preserves `GH⁻` as a bigraded
`K[U]`-module. -/
theorem bigradedUnblockedHomologyIsomorphic_of_isMove (hG' : G'.IsKnot)
    (h : IsMove ⟨n, G⟩ ⟨m, G'⟩) : hG.BigradedUnblockedHomologyIsomorphic hG' K := by
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

/-- **Invariance of the bigraded `GH⁻` under grid moves.** Knot grid diagrams connected by
arbitrary grid moves have isomorphic unblocked grid homologies as `(O-Maslov, Alexander)`-bigraded
`K[U]`-modules. -/
theorem bigradedUnblockedHomologyIsomorphic_of_movesTo (hG' : G'.IsKnot) (h : G.MovesTo G') :
    hG.BigradedUnblockedHomologyIsomorphic hG' K := by
  exact h.induction_on
    (motive := fun A B ↦ ∀ (hA : A.2.IsKnot) (hB : B.2.IsKnot),
      hA.BigradedUnblockedHomologyIsomorphic hB K)
    (fun h hA hB ↦ hA.bigradedUnblockedHomologyIsomorphic_of_isMove K hB h)
    (fun _ hA _ ↦ .refl hA K)
    (fun _ ih hA hB ↦ (ih hB hA).symm)
    (fun h _ ih ih' hA hB ↦
      (ih hA (h.isKnot_iff.mpr hA)).trans (ih' (h.isKnot_iff.mpr hA) hB)) hG hG'

end MovesTo

end TauCeti.GridDiagram.IsKnot
