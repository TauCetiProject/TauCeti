/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Initial.Basic

/-!
# Geometric characterization of common-initial-side cross partners

The recuts of common-initial-side rectangle--initial-pentagon cross domains are exactly the
counted initial-pentagon--rectangle domains whose pentagon ends where the rectangle starts,
with the rectangle's top strictly inside the pentagon's rows and the turn row in the half-open
arc from the rectangle's top to the pentagon's top.
This recognizes the recut image by side and row data for the partition of the commutation
chain-map coefficient sum.

The half-open convention includes a turn at the rectangle's top and excludes a turn at the
pentagon's top.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559). Related formalization:
`InitialPentagon.Overlap.PentagonInitial.Mixed`.
-/

public section

namespace TauCeti.GridInitialPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

private theorem initialCrossInverse_geometry
    (E : GridInitialPentagonRectangleDecomposition a s x z)
    (hcommon : E.first.right = E.second.left)
    (hone : E.toGridRectangleDecomposition.HasOneCommonSide)
    (hf : E.first.IsEmpty) (hs : E.second.IsEmpty)
    (hrow : E.second.top ∈ Grid.cIoo E.first.bottom E.first.top) :
    let D := E.toGridRectangleDecomposition.recut hone hf hs
    D.first.left = E.first.left ∧ D.second.left = E.first.left ∧
      D.second.bottom = E.second.top ∧ D.second.top = E.first.top := by
  intro D
  have hdata := E.toGridRectangleDecomposition.isRecutOfRightEqLeft_recut hcommon hone hf hs
  have htop := hdata.recut_sides.2
  rcases hdata.recut_branch with ⟨hrow', -, -, -⟩ | ⟨-, hmiddle, hfb, hsb⟩
  · -- The two strict cyclic row orders are mutually exclusive.
    exact (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) hrow
      (Grid.mem_cIoo_cyclic_left hrow')).elim
  · have hleft : D.first.left = E.first.left :=
      x.toPerm.injective (D.first.bottom_def.symm.trans (hfb.trans E.first.bottom_def))
    have hsecondLeft : D.second.left = E.first.left := by
      apply x.toPerm.injective
      have h : x.swapRows E.first.bottom E.second.top D.second.left = E.second.top :=
        (congrArg (fun y : GridState n => y D.second.left) hmiddle).symm.trans
          (D.second.bottom_def.symm.trans hsb)
      rw [GridState.swapRows_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
      exact h.trans E.first.bottom_def
    exact ⟨hleft, hsecondLeft, hsb, htop⟩

private noncomputable def initialCrossInverse
    (E : GridInitialPentagonRectangleDecomposition a s x z)
    (hcommon : E.first.right = E.second.left)
    (hone : E.toGridRectangleDecomposition.HasOneCommonSide)
    (hf : E.first.IsEmpty) (hs : E.second.IsEmpty)
    (hrow : E.second.top ∈ Grid.cIoo E.first.bottom E.first.top)
    (hturn : s ∈ Grid.cIco E.second.top E.first.top) :
    GridRectangleInitialPentagonDecomposition a s x z where
  toGridTwoStepDecomposition := E.toGridRectangleDecomposition.recut hone hf hs
  second_left_eq := (E.initialCrossInverse_geometry hcommon hone hf hs hrow).2.1.trans
    E.first_left_eq
  second_turn_mem := by
    obtain ⟨-, -, hb, ht⟩ := E.initialCrossInverse_geometry hcommon hone hf hs hrow
    rw [hb, ht]
    exact hturn

private theorem initialCrossInverse_toGridRectangleDecomposition
    (E : GridInitialPentagonRectangleDecomposition a s x z)
    (hcommon : E.first.right = E.second.left)
    (hone : E.toGridRectangleDecomposition.HasOneCommonSide)
    (hf : E.first.IsEmpty) (hs : E.second.IsEmpty)
    (hrow : E.second.top ∈ Grid.cIoo E.first.bottom E.first.top)
    (hturn : s ∈ Grid.cIco E.second.top E.first.top) :
    (E.initialCrossInverse hcommon hone hf hs hrow hturn).toGridRectangleDecomposition =
      E.toGridRectangleDecomposition.recut hone hf hs :=
  (rfl)

end TauCeti.GridInitialPentagonRectangleDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) {x z : GridState n}

/-- A counted mixed initial-pentagon--rectangle domain whose rectangle ends inside the
pentagon's rows, below or at the turn row, is the recut of a counted common-initial-side cross
source. -/
private theorem mem_initialPentagonInitialCrossOverlapPartners_of_right_eq_left
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.initialPentagonRectangleDecompositions C x z)
    (hcommon : E.first.right = E.second.left)
    (hrow : E.second.top ∈ Grid.cIoo E.first.bottom E.first.top)
    (hturn : C.turnRow ∈ Grid.cIco E.second.top E.first.top) :
    E ∈ G.initialPentagonInitialCrossOverlapPartners C x z := by
  have hother : E.first.left ≠ E.second.right := by
    intro h
    have ht : E.second.top = E.first.top := by
      rw [GridRectangleBetween.top_def, ← h, GridRectangleBetween.top_def]
      exact E.first.map_left
    simp only [ht, Grid.cIco_self, Finset.notMem_empty] at hturn
  have hone := E.toGridRectangleDecomposition.hasOneCommonSide_of_right_eq_left hcommon hother
  obtain ⟨hf, hs⟩ := G.isEmpty_of_mem_initialPentagonRectangleDecompositions C hE
  let D := E.initialCrossInverse hcommon hone hf hs hrow hturn
  have hDrect := E.initialCrossInverse_toGridRectangleDecomposition hcommon hone hf hs hrow hturn
  have hrecut : E.toGridRectangleDecomposition.IsRecut D.toGridRectangleDecomposition := by
    rw [hDrect]
    exact E.toGridRectangleDecomposition.isRecut_recut hone hf hs
  have hback := hrecut.symm hone hf hs
  have hDone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
    (E.toGridRectangleDecomposition.target_ne_source_of_hasOneCommonSide hone)
  obtain ⟨hleft, hsecondLeft, -, -⟩ :=
    E.initialCrossInverse_geometry hcommon hone hf hs hrow
  rw [← hDrect] at hleft hsecondLeft
  have hDcommon : D.first.left = D.second.left := hleft.trans hsecondLeft.symm
  have hDcol : D.second.right ∈ Grid.cIoo D.first.left D.first.right := by
    have hdata := hback.isRecutOfLeftEqLeft hDone hDcommon
    rcases hdata.recut_branch with ⟨-, -, hright, -⟩ | ⟨hcol, -⟩
    · exact (D.first.left_ne_right (hleft.trans hright)).elim
    · exact hcol
  have hEq : D.recutLeftEqLeft hDcommon hDcol hrecut.isEmpty_first hrecut.isEmpty_second = E := by
    apply GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition_injective
    exact (D.toGridRectangleDecomposition.existsUnique_isRecut hDone hrecut.isEmpty_first
      hrecut.isEmpty_second).unique
      (D.isRecut_recutLeftEqLeft hDcommon hDcol hrecut.isEmpty_first hrecut.isEmpty_second) hback
  have hsquares := D.coveredSquares_val_add_val_recutLeftEqLeft hDcommon hDcol
    hrecut.isEmpty_first hrecut.isEmpty_second
  rw [hEq] at hsquares
  have hD :=
    G.mem_rectangleInitialPentagonDecompositions_of_val_add_val_eq_initialPentagonRectangle
    C hE hrecut.isEmpty_first hrecut.isEmpty_second hsquares.symm
  exact (G.mem_initialPentagonInitialCrossOverlapPartners C E).2
    ⟨D, (G.mem_initialPentagonInitialCrossOverlapSources C D).2 ⟨hD, hDcommon, hDcol⟩, hback⟩

/-- The common-initial-side cross partners are exactly the counted mixed
initial-pentagon--rectangle domains whose rectangle's top lies strictly inside the pentagon's
rows and whose turn row lies in the half-open arc from that top to the pentagon's top. -/
@[grind =]
theorem mem_initialPentagonInitialCrossOverlapPartners_iff_sides
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.initialPentagonInitialCrossOverlapPartners C x z ↔
      E ∈ G.initialPentagonRectangleDecompositions C x z ∧
        E.first.right = E.second.left ∧
          E.second.top ∈ Grid.cIoo E.first.bottom E.first.top ∧
            C.turnRow ∈ Grid.cIco E.second.top E.first.top := by
  constructor
  · intro hE
    refine ⟨G.initialPentagonInitialCrossOverlapPartners_subset C hE, ?_⟩
    obtain ⟨D, hD, hrecut⟩ := (G.mem_initialPentagonInitialCrossOverlapPartners C E).1 hE
    obtain ⟨hcounted, hcommon, hcol⟩ :=
      (G.mem_initialPentagonInitialCrossOverlapSources C D).1 hD
    obtain ⟨hR, hP⟩ := (G.mem_rectangleInitialPentagonDecompositions C D).1 hcounted
    have hf := G.isEmpty_of_mem_unblockedRectangles hR
    have hs : D.second.IsEmpty := D.underlying_second_isEmpty ((G.mem_initialPentagons _).1 hP).1
    have hone :=
      D.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hcommon hcol
    have hEq : D.recutLeftEqLeft hcommon hcol hf hs = E := by
      apply GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition_injective
      exact (D.toGridRectangleDecomposition.existsUnique_isRecut hone hf hs).unique
        (D.isRecut_recutLeftEqLeft hcommon hcol hf hs) hrecut
    have hDrect :
        E.toGridRectangleDecomposition = D.toGridRectangleDecomposition.recut hone hf hs := by
      rw [← hEq, D.recutLeftEqLeft_toGridRectangleDecomposition]
    obtain ⟨-, hright, hleft, -⟩ :=
      D.toGridRectangleDecomposition.recut_sides_of_left_eq_left_of_mem_cIoo hcommon hcol hf hs
    obtain ⟨hbottom, htop⟩ :=
      D.toGridRectangleDecomposition.recut_first_bottom_top_of_left_eq_left_of_mem_cIoo hcommon hcol
        hf hs
    rw [← hDrect] at hright hleft hbottom htop
    have hsecondTop : E.second.top = D.first.top := by
      rw [GridRectangleBetween.top_def, GridRectangleBetween.top_def]
      have hdata := hrecut.isRecutOfLeftEqLeft hone hcommon
      rcases hdata.recut_branch with ⟨hcol', -⟩ | ⟨-, hmiddle, -, -⟩
      · exact (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) hcol
          (Grid.mem_cIoo_cyclic_left hcol')).elim
      · rw [hdata.recut_sides.2, hmiddle, GridState.swapColumns_apply,
          Equiv.swap_apply_of_ne_of_ne D.first.left_ne_right.symm
            (Grid.ne_right_of_mem_cIoo hcol).symm]
    refine ⟨hright.trans hleft.symm, ?_, ?_⟩
    · rw [hsecondTop, hbottom, htop]
      exact (D.toGridRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left hcommon
        (Grid.ne_right_of_mem_cIoo hcol).symm hf hs).2
    rw [hsecondTop, htop,
      ← D.toGridRectangleDecomposition.second_bottom_eq_first_top_of_left_eq_left hcommon]
    exact D.second_turn_mem
  · rintro ⟨hE, hcommon, hrow, hturn⟩
    exact G.mem_initialPentagonInitialCrossOverlapPartners_of_right_eq_left C E hE hcommon
      hrow hturn

end TauCeti.GridDiagram
