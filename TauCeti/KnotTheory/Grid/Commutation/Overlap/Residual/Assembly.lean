/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Orientation
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Residual.SameSide
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Residual.TerminalMixed
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Sum

/-!
# Assembly of terminal pentagon--rectangle overlap terms

The terminal-side pentagon--rectangle terms in the commutation chain-map equation split into
same-side and mixed-side orientations. The same-side terms consist of two recut-partner families
and the sources of the terminal self-pairing. The mixed-side terms consist of the other two
recut-partner families, the turn cuts, and the other members of those self-pairs.

This file assembles those two partitions. Using the terminal self-pair partition, their total
weight vanishes in characteristic two, so the full off-diagonal terminal-side contribution is
exactly the four recut-partner sums and the turn-cut sum. This is the right-hand counterpart of
the rectangle--pentagon assembly in
`GridDiagram.sum_rectanglePentagonWeight_overlap_eq_sum_partners`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) {x z : GridState n}

variable (R : Type*) [CommSemiring R] [CharP R 2]

open scoped Classical in
/-- Off the diagonal, the terminal-side pentagon--rectangle overlap sum is the total weight of
the four recut-partner families and the turn cuts. The remaining same-side and mixed-side terms
form terminal self-pairs and cancel in characteristic two. -/
theorem sum_pentagonRectangleWeight_overlap_eq_sum_partners (hzx : z ≠ x) :
    ∑ D ∈ (G.pentagonRectangleDecompositions C x z).filter
          (fun D => ¬D.HasDisjointSides), G.pentagonRectangleWeight C R D =
      (∑ D ∈ G.initialOverlapPartners C x z, G.pentagonRectangleWeight C R D) +
        (∑ D ∈ G.terminalCrossOverlapPartners C x z, G.pentagonRectangleWeight C R D) +
          (∑ D ∈ G.leftRightOverlapPartners C x z, G.pentagonRectangleWeight C R D) +
            (∑ D ∈ G.rightLeftOverlapPartners C x z, G.pentagonRectangleWeight C R D) +
              ∑ D ∈ G.pentagonRectangleTurnCuts C x z,
                G.pentagonRectangleWeight C R D := by
  rw [sum_pentagonRectangle_overlap_eq_sameSide_add_mixedSide C
      (G.pentagonRectangleDecompositions C x z) (G.pentagonRectangleWeight C R) hzx,
    G.sum_pentagonRectangle_sameSide_eq_sum_partners_add_sum_selfSources C,
    G.sum_pentagonRectangle_mixedSide_eq_sum_partners_add_turnCuts_add_selfPairs C
      (G.pentagonRectangleWeight C R) hzx]
  have hself := G.sum_pentagonTerminalSelfPairs_eq_sum_sources_add_sum_mixed C
    (x := x) (z := z) (G.pentagonRectangleWeight C R)
  rw [G.sum_pentagonRectangleWeight_pentagonTerminalSelfPairs_eq_zero C R x z] at hself
  -- The four partner sums and the turn-cut sum occur on both sides; the residual self-pair
  -- contributions vanish together, even though neither orientation need vanish separately.
  calc
    _ = ((∑ D ∈ G.initialOverlapPartners C x z, G.pentagonRectangleWeight C R D) +
          (∑ D ∈ G.terminalCrossOverlapPartners C x z, G.pentagonRectangleWeight C R D) +
            (∑ D ∈ G.leftRightOverlapPartners C x z, G.pentagonRectangleWeight C R D) +
              (∑ D ∈ G.rightLeftOverlapPartners C x z, G.pentagonRectangleWeight C R D) +
                ∑ D ∈ G.pentagonRectangleTurnCuts C x z,
                  G.pentagonRectangleWeight C R D) +
        ((∑ D ∈ G.pentagonTerminalSelfPairSources C x z,
            G.pentagonRectangleWeight C R D) +
          ∑ D ∈ (G.pentagonTerminalSelfPairs C x z).filter
            (fun D => D.toRectangleDecomposition.HasMixedSideOverlap),
            G.pentagonRectangleWeight C R D) := by
      ac_rfl
    _ = _ := by rw [← hself, add_zero]

variable [IsCancelAdd R]

open scoped Classical in
/-- The commutation map is a chain map exactly when the remaining initial-side-pentagon overlap
terms agree after the terminal-side partner sums have been cancelled. The turn-cut terms cross
the equation because reading a turn cut exchanges the side on which its pentagon turns. -/
theorem commutationMap_comp_unblockedDifferential_eq_iff_initialPentagon_overlap :
    (G.commutationMap R C).comp (G.unblockedDifferential R) =
        ((G.swapColumns C.column (finRotate n C.column)).unblockedDifferential R).comp
          (G.commutationMap R C) ↔
      ∀ x z : GridState n, z ≠ x →
        (∑ D ∈ (G.rectangleInitialPentagonDecompositions C x z).filter
              (fun D => ¬D.toGridRectangleDecomposition.HasDisjointSides),
              G.rectangleInitialPentagonWeight C R D) +
            ∑ D ∈ G.initialPentagonRectangleTurnCuts C x z,
              G.initialPentagonRectangleWeight C R D =
          (∑ D ∈ (G.initialPentagonRectangleDecompositions C x z).filter
              (fun D => ¬D.toGridRectangleDecomposition.HasDisjointSides),
              G.initialPentagonRectangleWeight C R D) +
            ∑ D ∈ G.pentagonRectangleTurnCuts C x z,
              G.pentagonRectangleWeight C R D := by
  rw [G.commutationMap_comp_unblockedDifferential_eq_iff_oriented_overlap C R]
  refine forall_congr' fun x ↦ forall_congr' fun z ↦ imp_congr_right fun hzx ↦ ?_
  have hcancel : ∀ p u b v d : MvPolynomial (Fin n) R,
      (p + u) + b = (p + v) + d ↔ b + u = d + v := fun p u b v d => by
    rw [add_assoc, add_assoc, add_left_cancel_iff]
    constructor <;> intro h <;> simpa only [add_comm] using h
  conv_lhs =>
    rw [← sum_rectanglePentagon_overlap_eq_sameSide_add_mixedSide C
        (G.rectanglePentagonDecompositions C x z) (G.rectanglePentagonWeight C R) hzx,
      ← sum_rectangleInitialPentagon_overlap_eq_sameSide_add_mixedSide C
        (G.rectangleInitialPentagonDecompositions C x z)
          (G.rectangleInitialPentagonWeight C R) hzx,
      ← sum_pentagonRectangle_overlap_eq_sameSide_add_mixedSide C
        (G.pentagonRectangleDecompositions C x z) (G.pentagonRectangleWeight C R) hzx,
      ← sum_initialPentagonRectangle_overlap_eq_sameSide_add_mixedSide C
        (G.initialPentagonRectangleDecompositions C x z)
          (G.initialPentagonRectangleWeight C R) hzx,
      G.sum_rectanglePentagonWeight_overlap_eq_sum_partners C R hzx,
      G.sum_pentagonRectangleWeight_overlap_eq_sum_partners C R hzx]
  exact hcancel _ _ _ _ _

end TauCeti.GridDiagram
