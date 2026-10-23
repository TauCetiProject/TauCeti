/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Mixed.LeftRight.Partners
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Mixed.RightLeft.Partners
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.PentagonTerminal.Sum

/-!
# Same-side pentagon--rectangle contributions in grid commutation

In the commutation chain-map equation, a pentagon followed by a rectangle can share its
initial side or its terminal side with the rectangle. The cyclic order of the remaining
columns partitions these terms into the two mixed-source recut partner families and the
sources of the terminal self-pairing. This file proves that the partition is exhaustive and
disjoint, splits arbitrary additive weights along it, and identifies the residual after
removing the recut partners.

The self-pair sources must remain in the residual: their cancelling partners have mixed-side
orientation. Consequently the same-side contribution alone need not vanish in characteristic
two. The partition supplies the same-side part of the geometric cancellation argument for the
pentagon-counting commutation map.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) {x z : GridState n}

open scoped Classical in
/-- The counted same-side pentagon--rectangle domains are exactly the two mixed-source recut
partner families together with the sources of the terminal self-pairing. -/
theorem filter_hasSameSideOverlap_pentagonRectangleDecompositions_eq_union :
    (G.pentagonRectangleDecompositions C x z).filter
        (fun D => D.toRectangleDecomposition.HasSameSideOverlap) =
      G.rightLeftOverlapPartners C x z ∪ G.leftRightOverlapPartners C x z ∪
        G.pentagonTerminalSelfPairSources C x z := by
  ext D
  have hP := D.pentagon.left_ne_right
  have hR := D.rectangle.left_ne_right
  have hleft (h : D.pentagon.left = D.rectangle.left)
      (hne : D.pentagon.right ≠ D.rectangle.right) :
      D.rectangle.right ∈ Grid.cIoo D.pentagon.left D.pentagon.right ∨
        D.pentagon.right ∈ Grid.cIoo D.pentagon.left D.rectangle.right := by
    rcases (Grid.mem_cIoo_or_mem_cIoo_swap_iff hP).2
      ⟨h ▸ hR.symm, hne.symm⟩ with hr | hr
    · exact Or.inl hr
    · exact Or.inr (Grid.mem_cIoo_cyclic_right hr)
  have hright (h : D.pentagon.right = D.rectangle.right)
      (hne : D.pentagon.left ≠ D.rectangle.left) :
      D.pentagon.left ∈ Grid.cIoo D.rectangle.left D.pentagon.right ∨
        D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right := by
    rcases (Grid.mem_cIoo_or_mem_cIoo_swap_iff hP).2
      ⟨hne.symm, h ▸ hR⟩ with hr | hr
    · exact Or.inr hr
    · exact Or.inl (Grid.mem_cIoo_cyclic_left hr)
  have hone := D.toRectangleDecomposition.side_eq_cases_of_hasOneCommonSide
  simp only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right] at hone
  simp only [Finset.mem_filter, GridRectangleDecomposition.hasSameSideOverlap_iff,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right,
    Finset.mem_union, mem_rightLeftOverlapPartners_iff_sides,
    mem_leftRightOverlapPartners_iff_sides, mem_pentagonTerminalSelfPairSources]
  -- The unique shared side excludes equal outer columns; the two cyclic orders then exhaust
  -- the same-side terms. Conversely, each family prescribes a shared side and distinct others.
  constructor
  · rintro ⟨hD, hcommon, hsides⟩
    have hcases := hone hcommon
    grind
  · rintro ((⟨hD, ⟨hc, hcol⟩ | ⟨hc, hcol⟩⟩ | ⟨hD, hc, hcol⟩) | ⟨hD, hc, hcol⟩)
    · refine ⟨hD, ?_, Or.inr hc⟩
      apply D.toRectangleDecomposition.hasOneCommonSide_of_right_eq_right
      · simpa using hc
      · simpa using Grid.ne_left_of_mem_cIoo hcol
    · refine ⟨hD, ?_, Or.inl hc⟩
      apply D.toRectangleDecomposition.hasOneCommonSide_of_left_eq_left
      · simpa using hc
      · simpa using (Grid.ne_right_of_mem_cIoo hcol).symm
    · refine ⟨hD, ?_, Or.inl hc⟩
      apply D.toRectangleDecomposition.hasOneCommonSide_of_left_eq_left
      · simpa using hc
      · simpa using Grid.ne_right_of_mem_cIoo hcol
    · refine ⟨hD, ?_, Or.inr hc.symm⟩
      apply D.toRectangleDecomposition.hasOneCommonSide_of_right_eq_right
      · simpa using hc.symm
      · simpa using (Grid.ne_left_of_mem_cIoo hcol).symm

/-- The recut partners of the two mixed-source orientations are disjoint. -/
private theorem disjoint_rightLeftOverlapPartners_leftRightOverlapPartners :
    Disjoint (G.rightLeftOverlapPartners C x z) (G.leftRightOverlapPartners C x z) := by
  classical
  refine Finset.disjoint_left.2 fun D h₁ h₂ => ?_
  obtain ⟨-, -, hcol⟩ := (G.mem_leftRightOverlapPartners_iff_sides C D).1 h₂
  obtain ⟨-, hterminal | hinitial⟩ := (G.mem_rightLeftOverlapPartners_iff_sides C D).1 h₁
  · exact Grid.ne_right_of_mem_cIoo hcol hterminal.1
  · exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _)
      hinitial.2 (Grid.mem_cIoo_cyclic_left hcol)

open scoped Classical in
/-- No mixed-source recut partner is a source of the terminal self-pairing. -/
private theorem disjoint_overlapPartners_pentagonTerminalSelfPairSources :
    Disjoint (G.rightLeftOverlapPartners C x z ∪ G.leftRightOverlapPartners C x z)
      (G.pentagonTerminalSelfPairSources C x z) := by
  classical
  refine Finset.disjoint_left.2 fun D h₁ h₂ => ?_
  obtain ⟨-, hcommon, hcol⟩ := (G.mem_pentagonTerminalSelfPairSources C D).1 h₂
  rcases Finset.mem_union.1 h₁ with hright | hleft
  · obtain ⟨-, hterminal | hinitial⟩ := (G.mem_rightLeftOverlapPartners_iff_sides C D).1 hright
    · exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _)
        hcol (Grid.mem_cIoo_cyclic_right hterminal.2)
    · exact Grid.ne_left_of_mem_cIoo hcol hinitial.1.symm
  · obtain ⟨-, -, hcol'⟩ := (G.mem_leftRightOverlapPartners_iff_sides C D).1 hleft
    exact Grid.ne_right_of_mem_cIoo hcol' hcommon.symm

open scoped Classical in
/-- Any additive weight on the same-side pentagon--rectangle terms splits into the two recut
partner sums and the terminal self-pair source sum, without double counting. -/
theorem sum_pentagonRectangle_sameSide_eq_sum_partners_add_sum_selfSources
    {M : Type*} [AddCommMonoid M]
    (w : GridPentagonRectangleDecomposition C.column C.turnRow x z → M) :
    ∑ D ∈ (G.pentagonRectangleDecompositions C x z).filter
        (fun D => D.toRectangleDecomposition.HasSameSideOverlap), w D =
      (∑ D ∈ G.rightLeftOverlapPartners C x z, w D) +
        (∑ D ∈ G.leftRightOverlapPartners C x z, w D) +
          ∑ D ∈ G.pentagonTerminalSelfPairSources C x z, w D := by
  rw [G.filter_hasSameSideOverlap_pentagonRectangleDecompositions_eq_union C,
    Finset.sum_union (G.disjoint_overlapPartners_pentagonTerminalSelfPairSources C),
    Finset.sum_union (G.disjoint_rightLeftOverlapPartners_leftRightOverlapPartners C)]

open scoped Classical in
/-- Removing both mixed-source recut partner families from the same-side pentagon--rectangle
terms leaves exactly the terminal self-pair sources. -/
theorem filter_sameSide_pentagonRectangleDecompositions_sdiff_partners_eq_selfPairSources :
    (G.pentagonRectangleDecompositions C x z).filter
          (fun D => D.toRectangleDecomposition.HasSameSideOverlap) \
        (G.rightLeftOverlapPartners C x z ∪ G.leftRightOverlapPartners C x z) =
      G.pentagonTerminalSelfPairSources C x z := by
  rw [G.filter_hasSameSideOverlap_pentagonRectangleDecompositions_eq_union C,
    Finset.union_sdiff_cancel_left
      (G.disjoint_overlapPartners_pentagonTerminalSelfPairSources C)]

end TauCeti.GridDiagram
