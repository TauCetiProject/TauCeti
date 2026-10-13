/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Initial.Sum

/-!
# The mixed partners of common-initial-side overlaps

Let `C` be a validated column commutation of a grid diagram `G`, replacing the grid line
`b = finRotate n a`. `GridDiagram.initialOverlapPartners` collects the recuts of the counted
rectangle--pentagon domains whose two pieces share their initial side and no other side; these
recuts are pentagon--rectangle domains. This file identifies them without reference to the
sources: they are exactly the counted pentagon--rectangle domains of two mixed kinds.

* The rectangle starts on `b`, where the pentagon ends, with no other common side, and the turn
  row lies outside the rectangle's rows. Both pieces then start in the same row, and emptiness
  puts the rectangle's top row strictly inside the pentagon's rows, above the turn row.
* The rectangle ends where the pentagon starts, with no other common side, and the pentagon's
  bottom row lies strictly between the rectangle's bottom row and the pentagon's top row.

In both cases the generic empty-rectangle recut consists of two rectangles sharing their initial
side, the second ending on `b` and containing the turn row: a rectangle followed by a pentagon.
The two composite domains cover the same squares with the same multiplicities, so the recut is a
counted common-initial-side source, and the original domain is its partner. Conversely, the
recut of a common-initial-side source is of one of these two kinds, according to the column order
of the two terminal sides. In the first kind the turn row lies in the pentagon's rows of the
source, which are disjoint from its rectangle's rows.

In particular, a counted pentagon--rectangle domain whose rectangle starts on `b` with no other
common side is either a partner of a common-initial-side source or cut at the turn point
(`GridDiagram.pentagonRectangleTurnCuts`).

## Main results

* `TauCeti.GridPentagonRectangleDecomposition.hasOneCommonSide_of_left_eq_right` and
  `TauCeti.GridPentagonRectangleDecomposition.hasOneCommonSide_of_right_eq_left`: the two mixed
  orientations with distinct other sides share exactly one side column.
* `TauCeti.GridDiagram.mem_initialOverlapPartners_iff_sides`: the partners of the
  common-initial-side sources are the counted pentagon--rectangle domains of the two kinds above.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- A pentagon followed by a rectangle starting on the pentagon's terminal side has exactly one
common side column when its two other sides differ. -/
theorem hasOneCommonSide_of_left_eq_right (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.rectangle.left = E.pentagon.right)
    (hother : E.rectangle.right ≠ E.pentagon.left) :
    E.toRectangleDecomposition.HasOneCommonSide := by
  apply E.toRectangleDecomposition.hasOneCommonSide_iff_existsUnique.mpr
  refine ⟨E.pentagon.right, ?_, ?_⟩
  · simp [GridRectangleBetween.mem_sideColumns, hcommon]
  · intro c hc
    simp only [GridRectangleBetween.mem_sideColumns, toRectangleDecomposition_first_left,
      toRectangleDecomposition_first_right, toRectangleDecomposition_second_left,
      toRectangleDecomposition_second_right] at hc
    have hfirst := E.pentagon.left_ne_right
    have hsecond := E.rectangle.left_ne_right
    grind

/-- A pentagon followed by a rectangle ending on the pentagon's initial side has exactly one
common side column when its two other sides differ. -/
theorem hasOneCommonSide_of_right_eq_left (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.rectangle.right = E.pentagon.left)
    (hother : E.rectangle.left ≠ E.pentagon.right) :
    E.toRectangleDecomposition.HasOneCommonSide := by
  apply E.toRectangleDecomposition.hasOneCommonSide_iff_existsUnique.mpr
  refine ⟨E.pentagon.left, ?_, ?_⟩
  · simp [GridRectangleBetween.mem_sideColumns, hcommon]
  · intro c hc
    simp only [GridRectangleBetween.mem_sideColumns, toRectangleDecomposition_first_left,
      toRectangleDecomposition_first_right, toRectangleDecomposition_second_left,
      toRectangleDecomposition_second_right] at hc
    have hfirst := E.pentagon.left_ne_right
    have hsecond := E.rectangle.left_ne_right
    grind

/-- If the intermediate state of a two-step decomposition exchanges two rows of the source state,
the second rectangle ends on the column of its top row, when that row is neither of the two. -/
private theorem second_right_eq_of_middle_eq_swapRows {D : GridRectangleDecomposition x z}
    {u v j : Fin n} (hmiddle : D.middle = x.swapRows u v) (htop : D.second.top = x j)
    (hu : x j ≠ u) (hv : x j ≠ v) : D.second.right = j := by
  apply x.toPerm.injective
  have h := (congrArg (fun y : GridState n => y D.second.right) hmiddle).symm.trans
    ((GridRectangleBetween.top_def _).symm.trans htop)
  rwa [GridState.swapRows_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne hu hv] at h

/-- If the intermediate state of a two-step decomposition exchanges the rows `u` and `v` of the
source state and the second rectangle starts in row `v`, the source state has row `u` on its
initial side. -/
private theorem source_second_left_eq_of_middle_eq_swapRows {D : GridRectangleDecomposition x z}
    {u v : Fin n} (hmiddle : D.middle = x.swapRows u v) (hbottom : D.second.bottom = v) :
    x D.second.left = u := by
  have h := (congrArg (fun y : GridState n => y D.second.left) hmiddle).symm.trans
    ((GridRectangleBetween.bottom_def _).symm.trans hbottom)
  rwa [GridState.swapRows_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h

/-- The rows of the two underlying rectangles of a pentagon followed by a rectangle. -/
private theorem underlying_rows (E : GridPentagonRectangleDecomposition a s x z) :
    E.toRectangleDecomposition.first.bottom = E.pentagon.bottom ∧
      E.toRectangleDecomposition.first.top = E.pentagon.top ∧
        E.toRectangleDecomposition.second.bottom = E.rectangle.bottom ∧
          E.toRectangleDecomposition.second.top = E.rectangle.top := by
  simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
    toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
    toRectangleDecomposition_second_left, toRectangleDecomposition_second_right,
    toRectangleDecomposition_middle, and_self]

/-- In a pentagon followed by a rectangle starting on the pentagon's terminal side, with no other
common side, whose turn row lies outside the rectangle's rows, the generic recut consists of two
rectangles sharing their initial side; the second ends on the replaced line, starts at the
rectangle's top row, which lies strictly inside the pentagon's rows, and contains the turn row. -/
private theorem recut_geometry_of_left_eq_right (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.rectangle.left = E.pentagon.right)
    (hone : E.toRectangleDecomposition.HasOneCommonSide)
    (hfirst : E.toRectangleDecomposition.first.IsEmpty)
    (hsecond : E.toRectangleDecomposition.second.IsEmpty)
    (hturn : s ∉ Grid.cIco E.rectangle.bottom E.rectangle.top) :
    x (E.toRectangleDecomposition.recut hone hfirst hsecond).first.left = E.pentagon.bottom ∧
      x (E.toRectangleDecomposition.recut hone hfirst hsecond).second.left =
        E.pentagon.bottom ∧
      (E.toRectangleDecomposition.recut hone hfirst hsecond).second.right = finRotate n a ∧
      (E.toRectangleDecomposition.recut hone hfirst hsecond).second.bottom = E.rectangle.top ∧
      (E.toRectangleDecomposition.recut hone hfirst hsecond).second.top = E.pentagon.top ∧
      E.rectangle.top ∈ Grid.cIoo E.pentagon.bottom E.pentagon.top ∧
      s ∈ Grid.cIco E.rectangle.top E.pentagon.top := by
  set D := E.toRectangleDecomposition.recut hone hfirst hsecond
  obtain ⟨hfb, hft, hsb, hst⟩ := E.underlying_rows
  have hdata : E.toRectangleDecomposition.IsRecutOfRightEqLeft D :=
    E.toRectangleDecomposition.isRecutOfRightEqLeft_recut
      (by simpa only [toRectangleDecomposition_first_right,
        toRectangleDecomposition_second_left] using hcommon.symm) hone hfirst hsecond
  obtain ⟨hDft, hDst⟩ := hdata.recut_sides
  rw [hst] at hDft
  rw [hft] at hDst
  -- Both pieces start in the row of the source state on the pentagon's initial side.
  have hbottom : E.rectangle.bottom = E.pentagon.bottom := by
    rw [GridRectangleBetween.bottom_def, hcommon, E.pentagon.map_right,
      GridRectangleBetween.bottom_def]
  have hb : x (finRotate n a) = E.pentagon.top := by
    rw [GridRectangleBetween.top_def, E.pentagon.right_eq]
  have hturnP := E.pentagon.turn_mem_cIco_bottom_top
  rw [hbottom] at hturn
  rcases hdata.recut_branch with ⟨hrow, -⟩ | ⟨hrow, hmiddle, hDfb, hDsb⟩
  · -- Otherwise the pentagon's rows would lie inside the rectangle's, turn row included.
    rw [hfb, hft, hst] at hrow
    exfalso
    simp only [Grid.mem_cIco, Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hrow hturn hturnP
    split_ifs at hrow hturn hturnP <;> omega
  · rw [hfb, hft, hst] at hrow
    rw [hfb, hst] at hmiddle
    rw [hfb] at hDfb
    rw [hst] at hDsb
    have hsecondRight : D.second.right = finRotate n a :=
      second_right_eq_of_middle_eq_swapRows hmiddle (hDst.trans hb.symm)
        (by rw [hb]; exact E.pentagon.bottom_ne_top.symm)
        (by rw [hb]; exact (Grid.ne_right_of_mem_cIoo hrow).symm)
    have hs : s ∈ Grid.cIco E.rectangle.top E.pentagon.top := by
      rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow] at hturnP
      exact (Finset.mem_union.mp hturnP).resolve_left hturn
    exact ⟨(GridRectangleBetween.bottom_def _).symm.trans hDfb,
      source_second_left_eq_of_middle_eq_swapRows hmiddle hDsb, hsecondRight, hDsb, hDst, hrow,
      hs⟩

/-- In a pentagon followed by a rectangle ending on the pentagon's initial side, with no other
common side, whose pentagon's bottom row lies strictly between the rectangle's bottom row and the
pentagon's top row, the generic recut consists of two rectangles sharing their initial side; the
second ends on the replaced line and has the pentagon's rows. -/
private theorem recut_geometry_of_right_eq_left (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.rectangle.right = E.pentagon.left)
    (hone : E.toRectangleDecomposition.HasOneCommonSide)
    (hfirst : E.toRectangleDecomposition.first.IsEmpty)
    (hsecond : E.toRectangleDecomposition.second.IsEmpty)
    (hrow : E.pentagon.bottom ∈ Grid.cIoo E.rectangle.bottom E.pentagon.top) :
    x (E.toRectangleDecomposition.recut hone hfirst hsecond).first.left = E.rectangle.bottom ∧
      x (E.toRectangleDecomposition.recut hone hfirst hsecond).second.left =
        E.rectangle.bottom ∧
      (E.toRectangleDecomposition.recut hone hfirst hsecond).second.right = finRotate n a ∧
      (E.toRectangleDecomposition.recut hone hfirst hsecond).second.bottom =
        E.pentagon.bottom ∧
      (E.toRectangleDecomposition.recut hone hfirst hsecond).second.top = E.pentagon.top := by
  set D := E.toRectangleDecomposition.recut hone hfirst hsecond
  obtain ⟨hfb, hft, hsb, -⟩ := E.underlying_rows
  have hdata : E.toRectangleDecomposition.IsRecutOfLeftEqRight D :=
    E.toRectangleDecomposition.isRecutOfLeftEqRight_recut
      (by simpa only [toRectangleDecomposition_first_left,
        toRectangleDecomposition_second_right] using hcommon.symm) hone hfirst hsecond
  obtain ⟨hDfb, hDsb⟩ := hdata.recut_sides
  rw [hsb] at hDfb
  rw [hfb] at hDsb
  have hb : x (finRotate n a) = E.pentagon.top := by
    rw [GridRectangleBetween.top_def, E.pentagon.right_eq]
  rcases hdata.recut_branch with ⟨-, hmiddle, -, hDst⟩ | ⟨hrow', -⟩
  · rw [hsb, hfb] at hmiddle
    rw [hft] at hDst
    have hsecondRight : D.second.right = finRotate n a :=
      second_right_eq_of_middle_eq_swapRows hmiddle (hDst.trans hb.symm)
        (by rw [hb]; exact (((Grid.mem_cIoo _ _ _).1 hrow).1).symm)
        (by rw [hb]; exact E.pentagon.bottom_ne_top.symm)
    exact ⟨(GridRectangleBetween.bottom_def _).symm.trans hDfb,
      source_second_left_eq_of_middle_eq_swapRows hmiddle hDsb, hsecondRight, hDsb, hDst⟩
  · -- The other branch puts the rectangle's bottom row strictly inside the pentagon's rows.
    rw [hfb, hft, hsb] at hrow'
    exfalso
    simp only [Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hrow hrow'
    split_ifs at hrow hrow' <;> omega

end TauCeti.GridPentagonRectangleDecomposition

namespace TauCeti.GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The recut of a rectangle--pentagon domain whose two empty pieces share their initial side and
no other side, read as a pentagon followed by a rectangle, is of one of two mixed kinds: its
rectangle starts on the replaced line, avoiding the turn row, or it ends where the pentagon starts,
the pentagon's bottom row lying strictly between the rectangle's bottom row and the pentagon's top
row. -/
private theorem pentagonRectangle_sides_of_isRecut_of_left_eq_left
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    {E : GridPentagonRectangleDecomposition a s x z}
    (hrecut : D.toRectangleDecomposition.IsRecut E.toRectangleDecomposition) :
    (E.rectangle.left = E.pentagon.right ∧ E.rectangle.right ≠ E.pentagon.left ∧
        s ∉ Grid.cIco E.rectangle.bottom E.rectangle.top) ∨
      (E.rectangle.right = E.pentagon.left ∧ E.rectangle.left ≠ E.pentagon.right ∧
        E.pentagon.bottom ∈ Grid.cIoo E.rectangle.bottom E.pentagon.top) := by
  have hcommon' : D.toRectangleDecomposition.first.left =
      D.toRectangleDecomposition.second.left := by
    simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_second_left] using
      hcommon
  have hdata : D.toRectangleDecomposition.IsRecutOfLeftEqLeft E.toRectangleDecomposition := by
    rcases hrecut.orientation with h | h | h | h
    · exact h
    · refine absurd ?_ (D.toRectangleDecomposition.sideColumns_ne_of_hasOneCommonSide hone)
      rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hcommon',
        h.side_eq]
    · exact (D.toRectangleDecomposition.second.left_ne_right
        (hcommon'.symm.trans h.side_eq)).elim
    · exact (D.toRectangleDecomposition.first.left_ne_right
        (hcommon'.trans h.side_eq.symm)).elim
  have hright : D.rectangle.right ≠ D.pentagon.right := by
    intro h
    apply D.toRectangleDecomposition.sideColumns_ne_of_hasOneCommonSide hone
    simp only [GridRectangleBetween.sideColumns, toRectangleDecomposition_first_left,
      toRectangleDecomposition_first_right, toRectangleDecomposition_second_left,
      toRectangleDecomposition_second_right, hcommon, h]
  -- Emptiness puts the rectangle's top row strictly between its bottom row and the pentagon's
  -- top row.
  have hrow : D.rectangle.top ∈ Grid.cIoo D.rectangle.bottom D.pentagon.top := by
    simpa only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
      toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right, toRectangleDecomposition_middle] using
      (D.toRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left hcommon'
        (by simpa only [toRectangleDecomposition_first_right,
          toRectangleDecomposition_second_right] using hright)
        (by simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)).2
  -- The source state keeps its row on the pentagon's terminal side across the rectangle.
  have hctop : D.pentagon.top = x D.pentagon.right := by
    rw [GridRectangleBetween.top_def,
      D.rectangle.map_of_ne _ (hcommon ▸ D.pentagon.left_ne_right.symm) hright.symm]
  obtain ⟨hEPright, hErright⟩ := hdata.recut_sides
  simp only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right,
    toRectangleDecomposition_first_right, toRectangleDecomposition_second_right]
    at hEPright hErright
  rcases hdata.recut_branch with ⟨-, -, hEPleft, hErleft⟩ | ⟨-, -, hEPleft, hErleft⟩
  · -- The rectangle's terminal side lies between the common side and the replaced line: the recut
    -- rectangle ends where the recut pentagon starts.
    simp only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left,
      toRectangleDecomposition_first_left, toRectangleDecomposition_first_right] at hEPleft hErleft
    refine Or.inr ⟨hErright.trans hEPleft.symm, ?_, ?_⟩
    · rw [hErleft, hEPright, hcommon]
      exact D.pentagon.left_ne_right
    · have hErbottom : E.rectangle.bottom = D.rectangle.bottom := by
        rw [GridRectangleBetween.bottom_def, GridRectangleBetween.bottom_def, hErleft,
          E.pentagon.map_of_ne _ (by rw [hEPleft]; exact D.rectangle.left_ne_right)
            (by rw [hEPright, hcommon]; exact D.pentagon.left_ne_right)]
      have hEPbottom : E.pentagon.bottom = D.rectangle.top := by
        rw [GridRectangleBetween.bottom_def, hEPleft, ← GridRectangleBetween.top_def]
      have hEPtop : E.pentagon.top = D.pentagon.top := by
        rw [GridRectangleBetween.top_def, hEPright, ← hctop]
      rw [hErbottom, hEPbottom, hEPtop]
      exact hrow
  · -- The replaced line lies between the common side and the rectangle's terminal side: the
    -- recut rectangle starts where the recut pentagon ends, in the rows of the original rectangle.
    simp only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left,
      toRectangleDecomposition_first_left, toRectangleDecomposition_second_right] at hEPleft hErleft
    refine Or.inl ⟨hErleft.trans hEPright.symm, ?_, ?_⟩
    · rw [hErright, hEPleft]
      exact D.rectangle.left_ne_right.symm
    · have hErbottom : E.rectangle.bottom = D.rectangle.bottom := by
        rw [GridRectangleBetween.bottom_def, GridRectangleBetween.bottom_def, hErleft,
          ← hEPright, E.pentagon.map_right, hEPleft]
      have hErtop : E.rectangle.top = D.rectangle.top := by
        rw [GridRectangleBetween.top_def, GridRectangleBetween.top_def, hErright,
          E.pentagon.map_of_ne _ (by rw [hEPleft]; exact D.rectangle.left_ne_right.symm)
            (by rw [hEPright]; exact hright)]
      have hturn : s ∈ Grid.cIco D.rectangle.top D.pentagon.top := by
        have h := D.pentagon.turn_mem_cIco_bottom_top
        rwa [GridRectangleBetween.bottom_def, ← hcommon, D.rectangle.map_left,
          ← GridRectangleBetween.top_def] at h
      rw [hErbottom, hErtop]
      exact Finset.disjoint_right.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hrow) hturn

end TauCeti.GridRectanglePentagonDecomposition

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

/-- A counted pentagon--rectangle domain is a partner of a common-initial-side source when its
generic recut consists of two rectangles sharing their initial side, the second ending on the
replaced line and containing the turn row, and the two composite domains balance in the two
columns next to the replaced line. -/
private theorem mem_initialOverlapPartners_of_recut
    {E : GridPentagonRectangleDecomposition C.column C.turnRow x z}
    (hE : E ∈ G.pentagonRectangleDecompositions C x z)
    (hone : E.toRectangleDecomposition.HasOneCommonSide)
    (hfirst : E.toRectangleDecomposition.first.IsEmpty)
    (hsecond : E.toRectangleDecomposition.second.IsEmpty)
    (hleft : x (E.toRectangleDecomposition.recut hone hfirst hsecond).first.left =
      x (E.toRectangleDecomposition.recut hone hfirst hsecond).second.left)
    (hright : (E.toRectangleDecomposition.recut hone hfirst hsecond).second.right =
      finRotate n C.column)
    (hturn : C.turnRow ∈
      Grid.cIco (E.toRectangleDecomposition.recut hone hfirst hsecond).second.bottom
        (E.toRectangleDecomposition.recut hone hfirst hsecond).second.top)
    (hcol : ∀ t : Fin n,
      ((if (C.column, t) ∈ E.rectangle.toGridRectangle.coveredSquares then 1 else 0) +
          if t ∈ Grid.cIco E.pentagon.bottom C.turnRow then 1 else 0 : ℕ) =
        (if (finRotate n C.column, t) ∈ E.rectangle.toGridRectangle.coveredSquares then 1
          else 0) +
          if t ∈ Grid.cIco (E.toRectangleDecomposition.recut hone hfirst hsecond).second.bottom
            C.turnRow then 1 else 0) :
    E ∈ G.initialOverlapPartners C x z := by
  set R := E.toRectangleDecomposition.recut hone hfirst hsecond
  let D : GridRectanglePentagonDecomposition C.column C.turnRow x z :=
    { middle := R.middle
      rectangle := R.first
      pentagon := GridPentagonBetween.ofRightEq R.second hright hturn }
  have hD : D.toRectangleDecomposition = R := by
    apply GridRectangleDecomposition.ext <;> simp [D, hright]
  have hrecut : E.toRectangleDecomposition.IsRecut D.toRectangleDecomposition := by
    rw [hD]
    exact E.toRectangleDecomposition.isRecut_recut hone hfirst hsecond
  have hback := hrecut.symm hone hfirst hsecond
  have hcounted : D ∈ G.rectanglePentagonDecompositions C x z :=
    G.mem_rectanglePentagonDecompositions_of_val_add_val_eq_pentagonRectangle C hE
      (D.isEmpty_rectangle_of_isRecut hrecut) (D.isEmpty_pentagon_of_isRecut hrecut)
      (D.coveredSquares_val_add_val_eq_of_isRepartition E hback.isRepartition
        (by simpa only [D, GridPentagonBetween.ofRightEq_bottom] using hcol))
  refine (G.mem_initialOverlapPartners C E).2 ⟨D, (G.mem_initialOverlapSources C D).2
    ⟨hcounted, ?_, GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback
      (E.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide hone)⟩, hback⟩
  simpa only [D, GridPentagonBetween.ofRightEq_left] using x.toPerm.injective hleft

/-- The partners of the common-initial-side sources are the counted pentagon--rectangle domains of
two mixed kinds: those whose rectangle starts on the replaced line, where the pentagon ends, with no
other common side and with the turn row outside the rectangle's rows; and those whose rectangle
ends where the pentagon starts, with no other common side, the pentagon's bottom row lying strictly
between the rectangle's bottom row and the pentagon's top row. -/
theorem mem_initialOverlapPartners_iff_sides
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.initialOverlapPartners C x z ↔
      E ∈ G.pentagonRectangleDecompositions C x z ∧
        ((E.rectangle.left = E.pentagon.right ∧ E.rectangle.right ≠ E.pentagon.left ∧
            C.turnRow ∉ Grid.cIco E.rectangle.bottom E.rectangle.top) ∨
          (E.rectangle.right = E.pentagon.left ∧ E.rectangle.left ≠ E.pentagon.right ∧
            E.pentagon.bottom ∈ Grid.cIoo E.rectangle.bottom E.pentagon.top)) := by
  constructor
  · intro hE
    refine ⟨G.initialOverlapPartners_subset_pentagonRectangleDecompositions C hE, ?_⟩
    obtain ⟨D, hD, hrecut⟩ := (G.mem_initialOverlapPartners C E).1 hE
    obtain ⟨hcounted, hcommon, hone⟩ := (G.mem_initialOverlapSources C D).1 hD
    obtain ⟨hr, hP⟩ := (G.mem_rectanglePentagonDecompositions C D).1 hcounted
    exact D.pentagonRectangle_sides_of_isRecut_of_left_eq_left hcommon hone
      ((G.mem_unblockedRectangles _).1 hr).1 ((G.mem_pentagons _).1 hP).1 hrecut
  · rintro ⟨hE, hsides⟩
    obtain ⟨hP, hR⟩ := (G.mem_pentagonRectangleDecompositions C E).1 hE
    have hfirst : E.toRectangleDecomposition.first.IsEmpty := by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        GridPentagonRectangleDecomposition.toRectangleDecomposition_first_toGridRectangle] using
        ((G.mem_pentagons _).1 hP).1
    have hsecond : E.toRectangleDecomposition.second.IsEmpty := by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        GridPentagonRectangleDecomposition.toRectangleDecomposition_middle,
        GridPentagonRectangleDecomposition.toRectangleDecomposition_second_toGridRectangle] using
        (((G.swapColumns C.column (finRotate n C.column)).mem_unblockedRectangles _).1 hR).1
    rcases hsides with ⟨hcommon, hother, hturn⟩ | ⟨hcommon, hother, hrow⟩
    · have hone := E.hasOneCommonSide_of_left_eq_right hcommon hother
      obtain ⟨hfl, hsl, hright, hsb, hst, hrow, hs⟩ :=
        E.recut_geometry_of_left_eq_right hcommon hone hfirst hsecond hturn
      refine G.mem_initialOverlapPartners_of_recut C hE hone hfirst hsecond (hfl.trans hsl.symm)
        hright (by rwa [hsb, hst]) fun t => ?_
      -- The rectangle starts on the replaced line, so it misses the column before it; in the
      -- column after it, its rows and those of the second recut piece up to the turn row make up
      -- the pentagon's rows up to the turn row.
      have hbottom : E.rectangle.bottom = E.pentagon.bottom := by
        rw [GridRectangleBetween.bottom_def, hcommon, E.pentagon.map_right,
          GridRectangleBetween.bottom_def]
      have hleftR : E.rectangle.left = finRotate n C.column := hcommon.trans E.pentagon.right_eq
      have ha : C.column ∉ Grid.cIco E.rectangle.left E.rectangle.right := by
        rw [hleftR]
        simp
      have hb : finRotate n C.column ∈ Grid.cIco E.rectangle.left E.rectangle.right :=
        hleftR ▸ Grid.left_mem_cIco (hleftR ▸ E.rectangle.left_ne_right)
      simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares, ha, hb,
        ← GridRectangleBetween.bottom_def, ← GridRectangleBetween.top_def, hbottom, hsb,
        false_and, true_and, ↓reduceIte, zero_add]
      exact Grid.ite_mem_cIco_eq_add_of_mem_cIoo hrow hs t
    · have hone := E.hasOneCommonSide_of_right_eq_left hcommon hother
      obtain ⟨hfl, hsl, hright, hsb, hst⟩ :=
        E.recut_geometry_of_right_eq_left hcommon hone hfirst hsecond hrow
      refine G.mem_initialOverlapPartners_of_recut C hE hone hfirst hsecond (hfl.trans hsl.symm)
        hright (by rw [hsb, hst]; exact E.pentagon.turn_mem_cIco_bottom_top) fun t => ?_
      -- Neither side of the rectangle is the replaced line, so it covers the two columns next to
      -- that line together or misses them together.
      have hab : finRotate n C.column ∈ Grid.cIco E.rectangle.left E.rectangle.right ↔
          C.column ∈ Grid.cIco E.rectangle.left E.rectangle.right :=
        Grid.mem_cIco_finRotate_iff_of_ne (by rw [← E.pentagon.right_eq]; exact hother)
          (by rw [hcommon]; exact E.pentagon.left_ne)
      simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares, hab, hsb]

end TauCeti.GridDiagram
