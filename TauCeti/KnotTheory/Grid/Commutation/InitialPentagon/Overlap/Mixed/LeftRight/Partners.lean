/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Mixed.LeftRight.Basic

/-!
# Geometric characterization of initial-side mixed `left = right` recut partners

Consider a rectangle followed by an initial-side commutation pentagon, where the rectangle
starts on the column where the pentagon ends. When the first piece of its recut contains the
turn row, the recut is an initial-side pentagon followed by a rectangle. Write `b` for the
replaced grid line. These recuts are exactly the counted initial-side-pentagon--rectangle
domains of the following two kinds:

* both pieces start on `b`, and the pentagon ends strictly inside the rectangle's column
  interval;
* both pieces end on the same column, and the rectangle starts strictly inside the pentagon's
  column interval.

The two kinds are the two branches of the recut, according to the order of the three corner
rows. `GridDiagram.mem_initialPentagonLeftRightOverlapPartners_iff_sides` describes the partner
family without quantifying over recut sources. This is one case of the partition of the
initial-side-pentagon--rectangle coefficient sum in the commutation chain-map equation. The
other common-initial-side order consists of self-pairs
(`GridDiagram.mem_initialPentagonRectangleInitialSelfPairs_iff_sides`). The other
common-terminal-side order consists of the mixed `right = left` partners
(`GridDiagram.mem_initialPentagonRightLeftOverlapPartners_iff_sides`).

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559). The argument inverts the forward recut formalized in `LeftRight.Basic`,
following the inverse recut of `InitialPentagon.Overlap.Mixed.RightLeft.Partners`.
-/

public section

namespace TauCeti.GridInitialPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- When both pieces start on the same column and the pentagon ends inside the rectangle's
column interval, the recut has a mixed `left = right` common side, its second piece starts
where the pentagon starts, and that piece contains the turn row. -/
private theorem leftRightInverse_geometry_of_left_eq_left
    (E : GridInitialPentagonRectangleDecomposition a s x z)
    (hcommon : E.first.left = E.second.left)
    (hcol : E.first.right ∈ Grid.cIoo E.first.left E.second.right)
    (hf : E.first.IsEmpty) (hs : E.second.IsEmpty) :
    let D := E.toGridRectangleDecomposition.recut
      (E.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_left hcommon
        (Grid.ne_right_of_mem_cIoo hcol)) hf hs
    D.first.left = D.second.right ∧ D.first.right ≠ D.second.left ∧
      D.second.left = E.first.left ∧ s ∈ Grid.cIco D.second.bottom D.second.top := by
  intro D
  have hdata := E.toGridRectangleDecomposition.isRecutOfLeftEqLeft_recut hcommon
    (E.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_left hcommon
      (Grid.ne_right_of_mem_cIoo hcol)) hf hs
  obtain ⟨hfr, hsr⟩ := hdata.recut_sides
  rcases hdata.recut_branch with ⟨-, hm, hfl, hsl⟩ | ⟨hcol', -⟩
  · have hne : E.first.left ≠ E.second.right := hcommon ▸ E.second.left_ne_right
    have hbottom : D.second.bottom = E.first.bottom := by
      rw [GridRectangleBetween.bottom_def, hsl, hm, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne E.first.left_ne_right hne,
        GridRectangleBetween.bottom_def]
    have htop : D.second.top = E.second.top := by
      rw [GridRectangleBetween.top_def, hsr, hm, GridState.swapColumns_apply,
        Equiv.swap_apply_left, GridRectangleBetween.top_def]
      exact (E.first.map_of_ne _ hne.symm (Grid.ne_right_of_mem_cIoo hcol).symm).symm
    refine ⟨hfl.trans hsr.symm, ?_, hsl, ?_⟩
    · rw [hfr, hsl]
      exact hne.symm
    · -- The pentagon's rows and the rectangle's rows together make up the recut piece's rows.
      have hrow := (E.toGridRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left hcommon
        (Grid.ne_right_of_mem_cIoo hcol) hf hs).2
      rw [hbottom, htop, ← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow]
      exact Finset.mem_union_left _ E.first_turn_mem
  · exact (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap E.first.left E.second.right)
      hcol (Grid.mem_cIoo_cyclic_left hcol')).elim

/-- When both pieces end on the same column and the rectangle starts inside the pentagon's
column interval, the recut has a mixed `left = right` common side, its second piece has the
pentagon's sides and rows, and that piece contains the turn row. -/
private theorem leftRightInverse_geometry_of_right_eq_right
    (E : GridInitialPentagonRectangleDecomposition a s x z)
    (hcommon : E.first.right = E.second.right)
    (hcol : E.second.left ∈ Grid.cIoo E.first.left E.first.right)
    (hf : E.first.IsEmpty) (hs : E.second.IsEmpty) :
    let D := E.toGridRectangleDecomposition.recut
      (E.toGridRectangleDecomposition.hasOneCommonSide_of_right_eq_right hcommon
        (Grid.ne_left_of_mem_cIoo hcol).symm) hf hs
    D.first.left = D.second.right ∧ D.first.right ≠ D.second.left ∧
      D.second.left = E.first.left ∧ s ∈ Grid.cIco D.second.bottom D.second.top := by
  intro D
  have hdata := E.toGridRectangleDecomposition.isRecutOfRightEqRight_recut hcommon
    (E.toGridRectangleDecomposition.hasOneCommonSide_of_right_eq_right hcommon
      (Grid.ne_left_of_mem_cIoo hcol).symm) hf hs
  obtain ⟨hfl, hsl⟩ := hdata.recut_sides
  rcases hdata.recut_branch with ⟨hcol', -⟩ | ⟨-, hm, hfr, hsr⟩
  · exact (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap E.first.left E.first.right)
      hcol (Grid.mem_cIoo_cyclic_right hcol')).elim
  · have hbottom : D.second.bottom = E.first.bottom := by
      rw [GridRectangleBetween.bottom_def, hsl, hm, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne (Grid.ne_left_of_mem_cIoo hcol).symm
          E.first.left_ne_right, GridRectangleBetween.bottom_def]
    have htop : D.second.top = E.first.top := by
      rw [GridRectangleBetween.top_def, hsr, hm, GridState.swapColumns_apply,
        Equiv.swap_apply_left, GridRectangleBetween.top_def]
    refine ⟨hfl.trans hsr.symm, ?_, hsl, ?_⟩
    · rw [hfr, hsl]
      exact E.first.left_ne_right.symm
    · rw [hbottom, htop]
      exact E.first_turn_mem

/-- Promote the recut of an initial-side-pentagon--rectangle domain to a rectangle followed by
an initial-side pentagon, when its second piece starts where the pentagon starts and contains
the turn row. -/
private noncomputable def leftRightInverse
    (E : GridInitialPentagonRectangleDecomposition a s x z)
    (hone : E.toGridRectangleDecomposition.HasOneCommonSide)
    (hf : E.first.IsEmpty) (hs : E.second.IsEmpty)
    (hleft : (E.toGridRectangleDecomposition.recut hone hf hs).second.left = E.first.left)
    (hturn : s ∈ Grid.cIco (E.toGridRectangleDecomposition.recut hone hf hs).second.bottom
      (E.toGridRectangleDecomposition.recut hone hf hs).second.top) :
    GridRectangleInitialPentagonDecomposition a s x z where
  toGridTwoStepDecomposition := E.toGridRectangleDecomposition.recut hone hf hs
  second_left_eq := hleft.trans E.first_left_eq
  second_turn_mem := hturn

private theorem leftRightInverse_toGridRectangleDecomposition
    (E : GridInitialPentagonRectangleDecomposition a s x z)
    (hone : E.toGridRectangleDecomposition.HasOneCommonSide)
    (hf : E.first.IsEmpty) (hs : E.second.IsEmpty)
    (hleft : (E.toGridRectangleDecomposition.recut hone hf hs).second.left = E.first.left)
    (hturn : s ∈ Grid.cIco (E.toGridRectangleDecomposition.recut hone hf hs).second.bottom
      (E.toGridRectangleDecomposition.recut hone hf hs).second.top) :
    (E.leftRightInverse hone hf hs hleft hturn).toGridRectangleDecomposition =
      E.toGridRectangleDecomposition.recut hone hf hs :=
  (rfl)

end TauCeti.GridInitialPentagonRectangleDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) {x z : GridState n}

/-- A counted initial-side-pentagon--rectangle domain whose recut is a mixed `left = right`
domain, with second piece starting where the pentagon starts and containing the turn row, is a
mixed `left = right` partner. -/
private theorem mem_initialPentagonLeftRightOverlapPartners_of_recut
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.initialPentagonRectangleDecompositions C x z)
    (hone : E.toGridRectangleDecomposition.HasOneCommonSide) (hf : E.first.IsEmpty)
    (hs : E.second.IsEmpty)
    (hcommon : (E.toGridRectangleDecomposition.recut hone hf hs).first.left =
      (E.toGridRectangleDecomposition.recut hone hf hs).second.right)
    (hother : (E.toGridRectangleDecomposition.recut hone hf hs).first.right ≠
      (E.toGridRectangleDecomposition.recut hone hf hs).second.left)
    (hleft : (E.toGridRectangleDecomposition.recut hone hf hs).second.left = E.first.left)
    (hturn : C.turnRow ∈ Grid.cIco (E.toGridRectangleDecomposition.recut hone hf hs).second.bottom
      (E.toGridRectangleDecomposition.recut hone hf hs).second.top) :
    E ∈ G.initialPentagonLeftRightOverlapPartners C x z := by
  let D := E.leftRightInverse hone hf hs hleft hturn
  have hDrect := E.leftRightInverse_toGridRectangleDecomposition hone hf hs hleft hturn
  have hrecut : E.toGridRectangleDecomposition.IsRecut D.toGridRectangleDecomposition := by
    rw [hDrect]
    exact E.toGridRectangleDecomposition.isRecut_recut hone hf hs
  have hback := hrecut.symm hone hf hs
  have hDone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
    (E.toGridRectangleDecomposition.target_ne_source_of_hasOneCommonSide hone)
  rw [← hDrect] at hcommon hother
  have hDf : D.first.IsEmpty := hrecut.isEmpty_first
  have hDp : D.pentagon.IsEmpty := by
    rw [D.pentagon_toGridRectangleBetween]
    exact hrecut.isEmpty_second
  -- The generic recut of the source is `E` itself, whose pentagon contains the turn row.
  have hcut : D.leftRightRecut hcommon hother hDf hDp = E.toGridRectangleDecomposition :=
    (D.toGridRectangleDecomposition.existsUnique_isRecut hDone hrecut.isEmpty_first
      hrecut.isEmpty_second).unique
      (D.isRecut_leftRightRecut hcommon hother hDf hDp) hback
  have hDturn : C.turnRow ∈ Grid.cIco (D.leftRightRecut hcommon hother hDf hDp).first.bottom
      (D.leftRightRecut hcommon hother hDf hDp).first.top := by
    rw [hcut]
    exact E.first_turn_mem
  have hEq : D.recutLeftEqRightFirst hcommon hother hDf hDp hDturn = E := by
    apply GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition_injective
    rw [D.recutLeftEqRightFirst_toGridRectangleDecomposition, hcut]
  have hsquares := D.coveredSquares_val_add_val_recutLeftEqRightFirst hcommon hother hDf hDp
    hDturn
  rw [hEq] at hsquares
  -- Reverse the forward corrected-square identity to transport marking avoidance.
  have hD := G.mem_rectangleInitialPentagonDecompositions_of_val_add_val_eq_initialPentagonRectangle
    C hE hrecut.isEmpty_first hrecut.isEmpty_second hsquares.symm
  exact (G.mem_initialPentagonLeftRightOverlapPartners C E).2
    ⟨D, (G.mem_initialPentagonLeftRightOverlapSources C D).2
      ⟨hD, hcommon, hother, E.toGridRectangleDecomposition, hback, E.first_turn_mem⟩, hback⟩

/-- A counted common-initial-side initial-side-pentagon--rectangle domain whose pentagon ends
strictly inside the rectangle's column interval is the recut of a counted mixed `left = right`
source. -/
theorem mem_initialPentagonLeftRightOverlapPartners_of_left_eq_left
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.initialPentagonRectangleDecompositions C x z)
    (hcommon : E.first.left = E.second.left)
    (hcol : E.first.right ∈ Grid.cIoo E.first.left E.second.right) :
    E ∈ G.initialPentagonLeftRightOverlapPartners C x z := by
  obtain ⟨hf, hs⟩ := G.isEmpty_of_mem_initialPentagonRectangleDecompositions C hE
  obtain ⟨hDcommon, hDother, hleft, hturn⟩ :=
    E.leftRightInverse_geometry_of_left_eq_left hcommon hcol hf hs
  exact G.mem_initialPentagonLeftRightOverlapPartners_of_recut C E hE _ hf hs
    hDcommon hDother hleft hturn

/-- A counted common-terminal-side initial-side-pentagon--rectangle domain whose rectangle
starts strictly inside the pentagon's column interval is the recut of a counted mixed
`left = right` source. -/
theorem mem_initialPentagonLeftRightOverlapPartners_of_right_eq_right
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (hE : E ∈ G.initialPentagonRectangleDecompositions C x z)
    (hcommon : E.first.right = E.second.right)
    (hcol : E.second.left ∈ Grid.cIoo E.first.left E.first.right) :
    E ∈ G.initialPentagonLeftRightOverlapPartners C x z := by
  obtain ⟨hf, hs⟩ := G.isEmpty_of_mem_initialPentagonRectangleDecompositions C hE
  obtain ⟨hDcommon, hDother, hleft, hturn⟩ :=
    E.leftRightInverse_geometry_of_right_eq_right hcommon hcol hf hs
  exact G.mem_initialPentagonLeftRightOverlapPartners_of_recut C E hE _ hf hs
    hDcommon hDother hleft hturn

/-- A mixed `left = right` partner either shares its initial side, with the pentagon ending
strictly inside the rectangle's column interval, or shares its terminal side, with the rectangle
starting strictly inside the pentagon's column interval. -/
private theorem sides_of_mem_initialPentagonLeftRightOverlapPartners
    {E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z}
    (hE : E ∈ G.initialPentagonLeftRightOverlapPartners C x z) :
    (E.first.left = E.second.left ∧ E.first.right ∈ Grid.cIoo E.first.left E.second.right) ∨
      (E.first.right = E.second.right ∧
        E.second.left ∈ Grid.cIoo E.first.left E.first.right) := by
  obtain ⟨D, hD, hrecut⟩ := (G.mem_initialPentagonLeftRightOverlapPartners C E).1 hE
  obtain ⟨hcounted, hcommon, hother, -⟩ :=
    (G.mem_initialPentagonLeftRightOverlapSources C D).1 hD
  obtain ⟨hR, hP⟩ := (G.mem_rectangleInitialPentagonDecompositions C D).1 hcounted
  have hf := G.isEmpty_of_mem_unblockedRectangles hR
  have hs : D.second.IsEmpty := by
    simpa only [D.pentagon_toGridRectangleBetween] using ((G.mem_initialPentagons _).1 hP).1
  have hone := D.toGridRectangleDecomposition.hasOneCommonSide_of_left_eq_right hcommon hother
  have hcut : E.toGridRectangleDecomposition = D.toGridRectangleDecomposition.recut hone hf hs :=
    (D.toGridRectangleDecomposition.existsUnique_isRecut hone hf hs).unique hrecut
      (D.toGridRectangleDecomposition.isRecut_recut hone hf hs)
  have hdata := D.toGridRectangleDecomposition.isRecutOfLeftEqRight_recut hcommon hone hf hs
  rw [← hcut] at hdata
  -- The two pieces of the partner differ in both their bottom rows and their top rows.
  have hrows : E.first.bottom ≠ E.second.bottom ∧ E.first.top ≠ E.second.top := by
    obtain ⟨hfb, hsb⟩ := hdata.recut_sides
    rw [hfb, hsb]
    rcases hdata.recut_branch with ⟨hrow, -, hft, hst⟩ | ⟨hrow, -, hft, hst⟩
    · rw [hft, hst]
      exact ⟨(Grid.ne_left_of_mem_cIoo hrow).symm, Grid.ne_right_of_mem_cIoo hrow⟩
    · rw [hft, hst]
      exact ⟨Grid.ne_left_of_mem_cIoo hrow, (Grid.ne_right_of_mem_cIoo hrow).symm⟩
  have hfirstLeft : E.first.left = D.second.left :=
    E.first_left_eq.trans D.second_left_eq.symm
  rcases (hrecut.symm hone hf hs).orientation with hdir | hdir | hdir | hdir
  · rcases hdir.recut_branch with ⟨hcol, -⟩ | ⟨-, -, hleft, -⟩
    · exact Or.inl ⟨hdir.side_eq, hcol⟩
    · exact (D.second.left_ne_right ((hleft.trans hfirstLeft).symm.trans hcommon)).elim
  · rcases hdir.recut_branch with ⟨-, -, hright, -⟩ | ⟨hcol, -⟩
    · exact (hother (hright.trans hfirstLeft)).elim
    · exact Or.inr ⟨hdir.side_eq, hcol⟩
  · -- A common column initial for the pentagon and terminal for the rectangle forces equal
    -- top rows.
    refine (hrows.2 ?_).elim
    rw [GridRectangleBetween.top_def, GridRectangleBetween.top_def, ← hdir.side_eq,
      E.first.map_left]
  · -- A common column terminal for the pentagon and initial for the rectangle forces equal
    -- bottom rows.
    refine (hrows.1 ?_).elim
    rw [GridRectangleBetween.bottom_def, GridRectangleBetween.bottom_def, ← hdir.side_eq,
      E.first.map_right]

/-- The mixed `left = right` partners of initial-side pentagons are exactly the counted
initial-side-pentagon--rectangle terms that either share their initial side, with the
pentagon ending strictly inside the rectangle's column interval, or share their terminal side,
with the rectangle starting strictly inside the pentagon's column interval. -/
@[grind =]
theorem mem_initialPentagonLeftRightOverlapPartners_iff_sides
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.initialPentagonLeftRightOverlapPartners C x z ↔
      E ∈ G.initialPentagonRectangleDecompositions C x z ∧
        ((E.first.left = E.second.left ∧
            E.first.right ∈ Grid.cIoo E.first.left E.second.right) ∨
          (E.first.right = E.second.right ∧
            E.second.left ∈ Grid.cIoo E.first.left E.first.right)) := by
  refine ⟨fun hE => ⟨G.initialPentagonLeftRightOverlapPartners_subset C hE,
    G.sides_of_mem_initialPentagonLeftRightOverlapPartners C hE⟩, ?_⟩
  rintro ⟨hE, ⟨hcommon, hcol⟩ | ⟨hcommon, hcol⟩⟩
  · exact G.mem_initialPentagonLeftRightOverlapPartners_of_left_eq_left C E hE hcommon hcol
  · exact G.mem_initialPentagonLeftRightOverlapPartners_of_right_eq_right C E hE hcommon hcol

end TauCeti.GridDiagram
