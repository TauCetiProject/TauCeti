/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Mixed.LeftRight.Partners
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Mixed.RightLeft.Partners
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.PentagonInitial.Mixed

/-!
# Same-side initial-side pentagon--rectangle contributions in grid commutation

In the commutation chain-map equation, a pentagon turning on its initial side, followed by a
rectangle of the commuted diagram, can share its initial side or its terminal side with the
rectangle. The cyclic order of the remaining two side columns partitions these terms into the
two mixed-source recut partner families, `GridDiagram.initialPentagonLeftRightOverlapPartners`
and `GridDiagram.initialPentagonRightLeftOverlapPartners`, and the sources of the initial-side
self-pairing, `GridDiagram.initialPentagonRectangleInitialSelfSources`. No condition on the
turn row is involved. This file proves that the partition is exhaustive and disjoint, and splits
arbitrary additive weights along it.

The self-pair sources do not cancel among the same-side terms: their cancelling partners have
mixed-side orientation, so the same-side contribution alone need not vanish in characteristic
two. This
is the initial-side counterpart of
`TauCeti.KnotTheory.Grid.Commutation.Overlap.Residual.SameSide`, and complements the mixed-side
partition of `TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Residual.Mixed`.

## Main results

* `GridDiagram.filter_hasSameSideOverlap_initialPentagonRectangleDecompositions_eq_union`: the
  counted same-side terms are the union of the three families.
* `GridDiagram.sum_initialPentagonRectangle_sameSide_eq_sum_partners_add_sum_selfSources`: the
  corresponding splitting of any additive weight.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

open scoped Classical in
/-- The counted same-side initial-side pentagon--rectangle domains are exactly the two
mixed-source recut partner families together with the sources of the initial-side
self-pairing. -/
theorem filter_hasSameSideOverlap_initialPentagonRectangleDecompositions_eq_union :
    (G.initialPentagonRectangleDecompositions C x z).filter
        (fun E => E.toGridRectangleDecomposition.HasSameSideOverlap) =
      G.initialPentagonRightLeftOverlapPartners C x z ∪
          G.initialPentagonLeftRightOverlapPartners C x z ∪
        G.initialPentagonRectangleInitialSelfSources C x z := by
  ext E
  have hP := E.first.left_ne_right
  have hR := E.second.left_ne_right
  have hleft (h : E.first.left = E.second.left) (hne : E.first.right ≠ E.second.right) :
      E.second.right ∈ Grid.cIoo E.first.left E.first.right ∨
        E.first.right ∈ Grid.cIoo E.first.left E.second.right := by
    rcases (Grid.mem_cIoo_or_mem_cIoo_swap_iff hP).2 ⟨h ▸ hR.symm, hne.symm⟩ with hr | hr
    · exact Or.inl hr
    · exact Or.inr (Grid.mem_cIoo_cyclic_right hr)
  have hright (h : E.first.right = E.second.right) (hne : E.first.left ≠ E.second.left) :
      E.second.left ∈ Grid.cIoo E.first.left E.first.right ∨
        E.first.left ∈ Grid.cIoo E.second.left E.first.right := by
    rcases (Grid.mem_cIoo_or_mem_cIoo_swap_iff hP).2 ⟨hne.symm, h ▸ hR⟩ with hr | hr
    · exact Or.inl hr
    · exact Or.inr (Grid.mem_cIoo_cyclic_left hr)
  have hone := E.toGridRectangleDecomposition.side_eq_cases_of_hasOneCommonSide
  simp only [Finset.mem_filter, GridRectangleDecomposition.hasSameSideOverlap_iff,
    Finset.mem_union, mem_initialPentagonRightLeftOverlapPartners_iff_sides,
    mem_initialPentagonLeftRightOverlapPartners_iff_sides,
    mem_initialPentagonRectangleInitialSelfSources]
  -- The unique shared side excludes equal outer columns; the two cyclic orders then exhaust
  -- the same-side terms. Conversely, each family prescribes a shared side and distinct others.
  constructor
  · rintro ⟨hE, hcommon, hsides⟩
    have hcases := hone hcommon
    grind
  · rintro ((⟨hE, hc, hcol⟩ | ⟨hE, ⟨hc, hcol⟩ | ⟨hc, hcol⟩⟩) | ⟨hE, hc, hcol⟩)
    · exact ⟨hE, E.toGridRectangleDecomposition.hasOneCommonSide_of_right_eq_right hc
        (Grid.ne_left_of_mem_cIoo hcol), Or.inr hc⟩
    · exact ⟨hE, E.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_left hc
        (Grid.ne_right_of_mem_cIoo hcol), Or.inl hc⟩
    · exact ⟨hE, E.toGridRectangleDecomposition.hasOneCommonSide_of_right_eq_right hc
        (Grid.ne_left_of_mem_cIoo hcol).symm, Or.inr hc⟩
    · exact ⟨hE, E.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_left hc
        (Grid.ne_right_of_mem_cIoo hcol).symm, Or.inl hc⟩

/-- The recut partners of the two mixed-source orientations are disjoint. -/
private theorem disjoint_initialPentagonRightLeftOverlapPartners_leftRightOverlapPartners :
    Disjoint (G.initialPentagonRightLeftOverlapPartners C x z)
      (G.initialPentagonLeftRightOverlapPartners C x z) := by
  classical
  refine Finset.disjoint_left.2 fun E h₁ h₂ => ?_
  obtain ⟨-, -, hcol⟩ := (G.mem_initialPentagonRightLeftOverlapPartners_iff_sides C E).1 h₁
  obtain ⟨-, ⟨hinitial, -⟩ | ⟨-, hcol'⟩⟩ :=
    (G.mem_initialPentagonLeftRightOverlapPartners_iff_sides C E).1 h₂
  · exact Grid.ne_left_of_mem_cIoo hcol hinitial
  · exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) hcol
      (Grid.mem_cIoo_cyclic_right hcol')

open scoped Classical in
/-- No mixed-source recut partner is a source of the initial-side self-pairing. -/
private theorem disjoint_initialPentagonOverlapPartners_initialSelfSources :
    Disjoint (G.initialPentagonRightLeftOverlapPartners C x z ∪
        G.initialPentagonLeftRightOverlapPartners C x z)
      (G.initialPentagonRectangleInitialSelfSources C x z) := by
  classical
  refine Finset.disjoint_left.2 fun E h₁ h₂ => ?_
  obtain ⟨-, hcommon, hcol⟩ := (G.mem_initialPentagonRectangleInitialSelfSources C E).1 h₂
  rcases Finset.mem_union.1 h₁ with hrl | hlr
  · obtain ⟨-, -, hcol'⟩ := (G.mem_initialPentagonRightLeftOverlapPartners_iff_sides C E).1 hrl
    exact Grid.ne_left_of_mem_cIoo hcol' hcommon
  · obtain ⟨-, ⟨-, hcol'⟩ | ⟨hterminal, -⟩⟩ :=
      (G.mem_initialPentagonLeftRightOverlapPartners_iff_sides C E).1 hlr
    · exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) hcol'
        (Grid.mem_cIoo_cyclic_left hcol)
    · exact Grid.ne_right_of_mem_cIoo hcol hterminal.symm

open scoped Classical in
/-- Any additive weight on the same-side initial-side pentagon--rectangle terms splits into the
two recut partner sums and the initial-side self-pair source sum, without double counting. -/
theorem sum_initialPentagonRectangle_sameSide_eq_sum_partners_add_sum_selfSources
    {M : Type*} [AddCommMonoid M]
    (w : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z → M) :
    ∑ E ∈ (G.initialPentagonRectangleDecompositions C x z).filter
        (fun E => E.toGridRectangleDecomposition.HasSameSideOverlap), w E =
      (∑ E ∈ G.initialPentagonRightLeftOverlapPartners C x z, w E) +
        (∑ E ∈ G.initialPentagonLeftRightOverlapPartners C x z, w E) +
          ∑ E ∈ G.initialPentagonRectangleInitialSelfSources C x z, w E := by
  rw [G.filter_hasSameSideOverlap_initialPentagonRectangleDecompositions_eq_union C,
    Finset.sum_union (G.disjoint_initialPentagonOverlapPartners_initialSelfSources C),
    Finset.sum_union
      (G.disjoint_initialPentagonRightLeftOverlapPartners_leftRightOverlapPartners C)]

end TauCeti.GridDiagram
