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

This file assembles those two partitions. It first identifies the two residual self-pair pieces
with the complete terminal self-pair family. Their total weight vanishes in characteristic two,
so the full off-diagonal terminal-side contribution is exactly the four recut-partner sums and
the turn-cut sum. This is the right-hand counterpart of the rectangle--pentagon assembly in
`GridDiagram.sum_rectanglePentagonWeight_overlap_eq_sum_partners`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

open scoped Classical in
/-- The terminal self-pairs are their same-side source terms together with their mixed-side
partners. -/
theorem pentagonTerminalSelfPairSources_union_filter_hasMixedSideOverlap_eq_selfPairs :
    G.pentagonTerminalSelfPairSources C x z ∪
        (G.pentagonTerminalSelfPairs C x z).filter
          (fun D => D.toRectangleDecomposition.HasMixedSideOverlap) =
      G.pentagonTerminalSelfPairs C x z := by
  ext D
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (hsource | ⟨hpair, -⟩)
    · exact (G.mem_pentagonTerminalSelfPairs C D).2 (Or.inl hsource)
    · exact hpair
  · intro hpair
    obtain ⟨hcounted, hsource | ⟨hcommon, hother, -⟩⟩ :=
      (G.mem_pentagonTerminalSelfPairs_iff_sides C D).1 hpair
    · exact Or.inl ((G.mem_pentagonTerminalSelfPairSources C D).2 ⟨hcounted, hsource⟩)
    · right
      refine ⟨hpair, ?_⟩
      rw [GridRectangleDecomposition.hasMixedSideOverlap_iff]
      refine ⟨D.toRectangleDecomposition.hasOneCommonSide_of_left_eq_right
        (by simpa using hcommon.symm) (by simpa using hother.symm), Or.inl ?_⟩
      simpa using hcommon.symm

open scoped Classical in
private theorem disjoint_pentagonTerminalSelfPairSources_filter_hasMixedSideOverlap :
    Disjoint (G.pentagonTerminalSelfPairSources C x z)
      ((G.pentagonTerminalSelfPairs C x z).filter
        (fun D => D.toRectangleDecomposition.HasMixedSideOverlap)) := by
  refine Finset.disjoint_left.2 fun D hsource hmixed => ?_
  obtain ⟨-, hcommon, hcol⟩ := (G.mem_pentagonTerminalSelfPairSources C D).1 hsource
  have hone := D.toRectangleDecomposition.hasOneCommonSide_of_right_eq_right
    (by simpa using hcommon.symm) (by simpa using (Grid.ne_left_of_mem_cIoo hcol).symm)
  have hsame : D.toRectangleDecomposition.HasSameSideOverlap := by
    rw [GridRectangleDecomposition.hasSameSideOverlap_iff]
    exact ⟨hone, Or.inr (by simpa using hcommon.symm)⟩
  exact D.toRectangleDecomposition.not_hasMixedSideOverlap_of_hasSameSideOverlap hsame
    (Finset.mem_filter.1 hmixed).2

open scoped Classical in
/-- An additive weight on the complete terminal self-pair family is the sum of its same-side
source contribution and its mixed-side partner contribution. -/
theorem sum_pentagonTerminalSelfPairs_eq_sum_sources_add_sum_mixed
    {M : Type*} [AddCommMonoid M]
    (w : GridPentagonRectangleDecomposition C.column C.turnRow x z → M) :
    ∑ D ∈ G.pentagonTerminalSelfPairs C x z, w D =
      (∑ D ∈ G.pentagonTerminalSelfPairSources C x z, w D) +
        ∑ D ∈ (G.pentagonTerminalSelfPairs C x z).filter
          (fun D => D.toRectangleDecomposition.HasMixedSideOverlap), w D := by
  rw [← Finset.sum_union
    (G.disjoint_pentagonTerminalSelfPairSources_filter_hasMixedSideOverlap C),
    G.pentagonTerminalSelfPairSources_union_filter_hasMixedSideOverlap_eq_selfPairs C]

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
  rw [G.sum_pentagonRectangle_overlap_eq_sameSide_add_mixedSide C
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
  have hcancel : ∀ p u b v d : MvPolynomial (Fin n) R,
      (p + u) + b = (p + v) + d ↔ b + u = d + v := fun p u b v d => by
    rw [add_assoc, add_assoc, add_left_cancel_iff]
    constructor <;> intro h <;> simpa only [add_comm] using h
  constructor
  · intro h x z hzx
    let p : MvPolynomial (Fin n) R :=
      (∑ D ∈ G.initialOverlapPartners C x z, G.pentagonRectangleWeight C R D) +
        (∑ D ∈ G.terminalCrossOverlapPartners C x z, G.pentagonRectangleWeight C R D) +
          (∑ D ∈ G.leftRightOverlapPartners C x z, G.pentagonRectangleWeight C R D) +
            ∑ D ∈ G.rightLeftOverlapPartners C x z, G.pentagonRectangleWeight C R D
    have hx := h x z hzx
    rw [← G.sum_rectanglePentagon_overlap_eq_sameSide_add_mixedSide C
        (G.rectanglePentagonDecompositions C x z) (G.rectanglePentagonWeight C R) hzx,
      ← G.sum_rectangleInitialPentagon_overlap_eq_sameSide_add_mixedSide C
        (G.rectangleInitialPentagonDecompositions C x z)
          (G.rectangleInitialPentagonWeight C R) hzx,
      ← G.sum_pentagonRectangle_overlap_eq_sameSide_add_mixedSide C
        (G.pentagonRectangleDecompositions C x z) (G.pentagonRectangleWeight C R) hzx,
      ← G.sum_initialPentagonRectangle_overlap_eq_sameSide_add_mixedSide C
        (G.initialPentagonRectangleDecompositions C x z)
          (G.initialPentagonRectangleWeight C R) hzx,
      G.sum_rectanglePentagonWeight_overlap_eq_sum_partners C R hzx,
      G.sum_pentagonRectangleWeight_overlap_eq_sum_partners C R hzx] at hx
    exact (hcancel p _ _ _ _).1 hx
  · intro h x z hzx
    let p : MvPolynomial (Fin n) R :=
      (∑ D ∈ G.initialOverlapPartners C x z, G.pentagonRectangleWeight C R D) +
        (∑ D ∈ G.terminalCrossOverlapPartners C x z, G.pentagonRectangleWeight C R D) +
          (∑ D ∈ G.leftRightOverlapPartners C x z, G.pentagonRectangleWeight C R D) +
            ∑ D ∈ G.rightLeftOverlapPartners C x z, G.pentagonRectangleWeight C R D
    have hx := (hcancel p _ _ _ _).2 (h x z hzx)
    rw [← G.sum_rectanglePentagonWeight_overlap_eq_sum_partners C R hzx,
      ← G.sum_pentagonRectangleWeight_overlap_eq_sum_partners C R hzx,
      G.sum_rectanglePentagon_overlap_eq_sameSide_add_mixedSide C
        (G.rectanglePentagonDecompositions C x z) (G.rectanglePentagonWeight C R) hzx,
      G.sum_rectangleInitialPentagon_overlap_eq_sameSide_add_mixedSide C
        (G.rectangleInitialPentagonDecompositions C x z)
          (G.rectangleInitialPentagonWeight C R) hzx,
      G.sum_pentagonRectangle_overlap_eq_sameSide_add_mixedSide C
        (G.pentagonRectangleDecompositions C x z) (G.pentagonRectangleWeight C R) hzx,
      G.sum_initialPentagonRectangle_overlap_eq_sameSide_add_mixedSide C
        (G.initialPentagonRectangleDecompositions C x z)
          (G.initialPentagonRectangleWeight C R) hzx] at hx
    exact hx

end TauCeti.GridDiagram
