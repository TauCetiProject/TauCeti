/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Mixed.RightLeft.Basic

/-!
# Geometric characterization of initial-side mixed recut partners

The recuts of rectangle--initial-side-pentagon domains whose rectangle ends where the pentagon
starts and avoids the turn row are exactly the counted initial-side-pentagon--rectangle domains
sharing their terminal side, with the pentagon's initial side strictly inside the rectangle's
column interval. This describes the partner family without searching for a source and supplies
one case of the partition of the commutation chain-map coefficient sum.

The inverse recut enlarges the pentagon downwards through the rectangle's rows. Emptiness puts
the common corner strictly between the other two rows, so the enlarged pentagon contains the
turn row while the preceding rectangle avoids it. The existing forward recut square identity
then transports marking avoidance back to the source.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559). The argument uses the forward recut formalized in `RightLeft.Basic` and
is the initial-side counterpart of `Commutation.Overlap.Mixed.LeftRight.Partners`.
-/

public section

namespace TauCeti.GridInitialPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

private theorem rightLeftInverse_turn (E : GridInitialPentagonRectangleDecomposition a s x z)
    (hcommon : E.first.right = E.second.right)
    (hcol : E.first.left ∈ Grid.cIoo E.second.left E.first.right)
    (hf : E.first.IsEmpty) (hs : E.second.IsEmpty) :
    let hone := E.hasOneCommonSide_of_right_eq_right hcommon (Grid.ne_left_of_mem_cIoo hcol)
    let D := E.recut hone hf hs
    s ∈ Grid.cIco D.second.bottom D.second.top ∧
      s ∉ Grid.cIco D.first.bottom D.first.top := by
  intro hone D
  obtain ⟨-, -, hfb, hft, hsb, hst⟩ :=
    E.recut_geometry_of_right_eq_right_of_mem_cIoo hcommon hcol hf hs
  have hrow := (E.cyclicOrder_of_isEmpty_of_right_eq_right hcommon
    (Grid.ne_left_of_mem_cIoo hcol) hf hs).2
  rw [hfb, hft, hsb, hst]
  refine ⟨?_, fun h => Finset.disjoint_left.mp
    (Grid.disjoint_cIco_cIco_of_mem_cIoo hrow) h E.first_turn_mem⟩
  rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow]
  exact Finset.mem_union_right _ E.first_turn_mem

private noncomputable def rightLeftInverse (E : GridInitialPentagonRectangleDecomposition a s x z)
    (hcommon : E.first.right = E.second.right)
    (hcol : E.first.left ∈ Grid.cIoo E.second.left E.first.right)
    (hf : E.first.IsEmpty) (hs : E.second.IsEmpty) :
    GridRectangleInitialPentagonDecomposition a s x z where
  toGridRectangleDecomposition := E.recut
    (E.hasOneCommonSide_of_right_eq_right hcommon (Grid.ne_left_of_mem_cIoo hcol)) hf hs
  second_left_eq :=
    (E.recut_geometry_of_right_eq_right_of_mem_cIoo hcommon hcol hf hs).2.1.trans E.first_left_eq
  second_turn_mem := (E.rightLeftInverse_turn hcommon hcol hf hs).1

private theorem rightLeftInverse_toGridRectangleDecomposition
    (E : GridInitialPentagonRectangleDecomposition a s x z)
    (hcommon : E.first.right = E.second.right)
    (hcol : E.first.left ∈ Grid.cIoo E.second.left E.first.right)
    (hf : E.first.IsEmpty) (hs : E.second.IsEmpty) :
    (E.rightLeftInverse hcommon hcol hf hs).toGridRectangleDecomposition =
      E.recut (E.hasOneCommonSide_of_right_eq_right hcommon
        (Grid.ne_left_of_mem_cIoo hcol)) hf hs :=
  (rfl)

end TauCeti.GridInitialPentagonRectangleDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

/-- A counted initial-side-pentagon--rectangle domain sharing its terminal side, with the
pentagon's initial side inside the rectangle's column interval, is the recut of a counted mixed
`right = left` source whose rectangle avoids the turn row. -/
theorem mem_initialPentagonRightLeftOverlapPartners_of_right_eq_right
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.initialPentagonRectangleDecompositions C x z)
    (hcommon : E.first.right = E.second.right)
    (hcol : E.first.left ∈ Grid.cIoo E.second.left E.first.right) :
    E ∈ G.initialPentagonRightLeftOverlapPartners C x z := by
  obtain ⟨hf, hs⟩ := G.isEmpty_of_mem_initialPentagonRectangleDecompositions C hE
  have hone := E.hasOneCommonSide_of_right_eq_right hcommon (Grid.ne_left_of_mem_cIoo hcol)
  let D := E.rightLeftInverse hcommon hcol hf hs
  have hDrect := E.rightLeftInverse_toGridRectangleDecomposition hcommon hcol hf hs
  have hrecut : E.IsRecut D.toGridRectangleDecomposition := by
    rw [hDrect]
    exact E.isRecut_recut hone hf hs
  have hback := hrecut.symm hone hf hs
  have hDone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
    (E.target_ne_source_of_hasOneCommonSide hone)
  obtain ⟨hfr, hsl, -, -, -, -⟩ :=
    E.recut_geometry_of_right_eq_right_of_mem_cIoo hcommon hcol hf hs
  have hDcommon : D.first.right = D.second.left := hfr.trans hsl.symm
  have hturn : C.turnRow ∉ Grid.cIco D.first.bottom D.first.top :=
    (E.rightLeftInverse_turn hcommon hcol hf hs).2
  have hDp : D.pentagon.IsEmpty := by
    rw [D.pentagon_toGridRectangleBetween]
    exact hrecut.isEmpty_second
  have hEq : D.recutRightEqLeft hDcommon hrecut.isEmpty_first hDp hturn = E := by
    apply GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition_injective
    exact (D.existsUnique_isRecut hDone hrecut.isEmpty_first hrecut.isEmpty_second).unique
      (D.isRecut_recutRightEqLeft hDcommon hrecut.isEmpty_first hDp hturn) hback
  have hsquares := D.coveredSquares_val_add_val_recutRightEqLeft hDcommon
    hrecut.isEmpty_first hDp hturn
  rw [hEq] at hsquares
  -- Reverse the forward corrected-square identity to transport marking avoidance.
  have hD := G.mem_rectangleInitialPentagonDecompositions_of_val_add_val_eq_initialPentagonRectangle
    C hE hrecut.isEmpty_first hrecut.isEmpty_second hsquares.symm
  exact (G.mem_initialPentagonRightLeftOverlapPartners C E).2
    ⟨D, (G.mem_initialPentagonRightLeftOverlapSources C D).2 ⟨hD, hDcommon, hturn⟩, hback⟩

/-- The mixed `right = left` partners are exactly the counted initial-side-pentagon--rectangle
terms sharing their terminal side, with the pentagon's initial side strictly inside the
rectangle's column interval. -/
@[grind =]
theorem mem_initialPentagonRightLeftOverlapPartners_iff_sides
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.initialPentagonRightLeftOverlapPartners C x z ↔
      E ∈ G.initialPentagonRectangleDecompositions C x z ∧
        E.first.right = E.second.right ∧
          E.first.left ∈ Grid.cIoo E.second.left E.first.right := by
  constructor
  · intro hE
    refine ⟨G.initialPentagonRightLeftOverlapPartners_subset C hE, ?_⟩
    obtain ⟨D, hD, hrecut⟩ := (G.mem_initialPentagonRightLeftOverlapPartners C E).1 hE
    obtain ⟨hcounted, hcommon, hturn⟩ := (G.mem_initialPentagonRightLeftOverlapSources C D).1 hD
    obtain ⟨hR, hP⟩ := (G.mem_rectangleInitialPentagonDecompositions C D).1 hcounted
    have hf := G.isEmpty_of_mem_unblockedRectangles hR
    have hp := ((G.mem_initialPentagons _).1 hP).1
    have hs : D.second.IsEmpty := by
      simpa only [D.pentagon_toGridRectangleBetween] using hp
    have hone := D.hasOneCommonSide_of_right_eq_left hcommon
      (D.first_left_ne_second_right_of_right_eq_left hcommon hturn)
    have hEq : D.recutRightEqLeft hcommon hf hp hturn = E := by
      apply GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition_injective
      exact (D.existsUnique_isRecut hone hf hs).unique
        (D.isRecut_recutRightEqLeft hcommon hf hp hturn) hrecut
    obtain ⟨-, hfl, -⟩ := D.recutRightEqLeft_geometry hcommon hf hp hturn
    obtain ⟨hfr, hsl, hsr⟩ := D.recutRightEqLeft_sides hcommon hf hp hturn
    rw [hEq] at hfl hfr hsl hsr
    have hother := D.first_left_ne_second_right_of_right_eq_left hcommon hturn
    refine ⟨hfr.trans hsr.symm, ?_⟩
    rw [hfl, hsl, hfr, ← hcommon]
    exact (D.cyclicOrder_of_isEmpty_of_right_eq_left hcommon hother hf hs).1
  · rintro ⟨hE, hcommon, hcol⟩
    exact G.mem_initialPentagonRightLeftOverlapPartners_of_right_eq_right C E hE hcommon hcol

end TauCeti.GridDiagram
