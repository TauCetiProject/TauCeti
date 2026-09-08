/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.OverlapOrder
public import TauCeti.KnotTheory.Grid.Differential.Square.Repartition
public import TauCeti.KnotTheory.Grid.Rectangle.Juxtaposition

/-!
# Recutting a two-step grid rectangle decomposition sharing its terminal side column

A nondiagonal term in the square of the unblocked grid differential `∂⁻` is a pair of composable
empty rectangles whose two pairs of side columns are either disjoint or share exactly one column.
In the second case the two rectangles meet at a corner and their union is an L-shaped hexagon,
which can be cut into two rectangles in exactly one other way. This file builds that alternate cut
in the orientation where the two rectangles share their *terminal* side column, the mirror of the
initial-side orientation built in `TauCeti.KnotTheory.Grid.Differential.Square.Recut.Initial`.

The two orientations are genuinely different configurations rather than one another's image under
a symmetry of the situation. Reversing a rectangle (`GridRectangleBetween.symm`) does exchange its
two side columns, but it spans the complementary arc of columns and hence does not preserve
emptiness; and the diagonal reflection `GridRectangleDecomposition.transpose` exchanges side
columns with corner rows, so it carries a common terminal side column to a coincidence of corner
rows rather than to a common initial side column. Both cuts are therefore proved directly, from
the same geometric inputs: the cyclic order forced by emptiness
(`cyclicOrder_of_isEmpty_of_right_eq_right`) and the finite-domain repartition identities for the
covered squares (`GridRectangle.coveredSquares_union_eq_of_mem_cIoo_common_right` and its
complementary form). Emptiness of the new rectangles is not part of those identities: it is proved
here, and it is where emptiness of *both* old rectangles is used, one for the columns below the
cut and one for the columns above it.

The relation between the two cuts is packaged as `GridRectangleDecomposition.IsRepartition`: the
rectangles of each cut cover disjoint sets of squares, and the two unions agree. The geometric
construction separately proves that the two cuts have different intermediate states, and records
the intermediate state and the side columns of the new cut.

Two orientations of the shared side column remain: the terminal side of one rectangle may be the
initial side of the other. Those two, and the assembly of the disjoint, overlapping and annular
cases into `∂⁻ ∘ ∂⁻ = 0`, are separate steps.

## Main results

* `TauCeti.GridRectangleDecomposition.exists_isRepartition_of_isEmpty_of_right_eq_right`: two
  composable empty rectangles sharing their terminal side column admit a recut by two empty
  rectangles, whose intermediate state and side columns are computed.
* `GridRectangleDecomposition.exists_isRepartition_of_mem_unblockedRectangles_of_right_eq_right`:
  for each two-step term of `∂⁻ ∘ ∂⁻` whose two rectangles share their terminal side column there
  is a unique second such term through a different intermediate state.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and
`∂² = 0`", specifically the overlapping case of its juxtaposition case analysis. The recut follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-! ### The two old rectangles read in the source state -/

/-- When the two rectangles share their terminal side, that side differs from the second
rectangle's initial side. -/
private theorem second_left_ne_first_right_of_right_eq_right
    (D : GridRectangleDecomposition x z)
    (hright : D.first.right = D.second.right) : D.second.left ≠ D.first.right :=
  fun h => D.second.left_ne_right (h.trans hright)

/-- The common terminal side and distinct initial sides determine the source-state values of the
intermediate state at the common side and the second initial side. -/
private theorem middle_apply_of_right_eq_right (D : GridRectangleDecomposition x z)
    (hright : D.first.right = D.second.right) (hleft : D.first.left ≠ D.second.left) :
    D.middle D.first.right = x D.first.left ∧
      D.middle D.second.left = x D.second.left :=
  ⟨D.first.map_right,
    D.first.map_of_ne _ hleft.symm (D.second_left_ne_first_right_of_right_eq_right hright)⟩

/-- The second rectangle of a decomposition whose two rectangles share their terminal side column,
written in terms of the source state: its two horizontal sides are the rows of the source state at
the initial columns of the two rectangles. -/
private theorem toGridRectangle_second_of_right_eq_right (D : GridRectangleDecomposition x z)
    (hright : D.first.right = D.second.right) (hleft : D.first.left ≠ D.second.left) :
    D.second.toGridRectangle =
      { left := D.second.left, right := D.first.right, bottom := x D.second.left,
        top := x D.first.left } := by
  obtain ⟨hmid_first, hmid_second⟩ := D.middle_apply_of_right_eq_right hright hleft
  have htop : D.middle D.second.right = x D.first.left := by
    rw [← hright, hmid_first]
  rw [D.second.toGridRectangle_eq, hmid_second, htop, ← hright]

/-- Emptiness of the second rectangle of a decomposition whose two rectangles share their terminal
side column, read back in the source state.

Away from the two side columns of the first rectangle the intermediate state agrees with the
source state, so emptiness may be tested against the source state there. -/
private theorem forall_notMem_cIoo_second_of_right_eq_right (D : GridRectangleDecomposition x z)
    (hright : D.first.right = D.second.right) (hleft : D.first.left ≠ D.second.left)
    (hsecond : D.second.IsEmpty) :
    ∀ c ∈ Grid.cIoo D.second.left D.first.right, c ≠ D.first.left → c ≠ D.first.right →
      x c ∉ Grid.cIoo (x D.second.left) (x D.first.left) := by
  obtain ⟨hmid_first, hmid_second⟩ := D.middle_apply_of_right_eq_right hright hleft
  have h := hsecond
  rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo] at h
  simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, ← hright, hmid_first,
    hmid_second] at h
  intro c hc hca hcb
  have hcm := h c hc
  rwa [D.first.map_of_ne c hca hcb] at hcm

/-! ### Building the recut -/

/-- If a column belongs to both old column spans, the emptiness of the old rectangles excludes
its grid-state point from the open arc between the two extreme corner rows.

Here the two old rectangles are stacked along the row `x a`: the lower one spans the columns from
`d` to `b`, the upper one the columns from `a` to `b`. -/
private theorem notMem_cIoo_of_mem_cIoo_of_mem_cIoo_common_right {a b d c : Fin n}
    (hrow : x a ∈ Grid.cIoo (x d) (x b))
    (hfirst : ∀ c ∈ Grid.cIoo a b, x c ∉ Grid.cIoo (x a) (x b))
    (hsecond : ∀ c ∈ Grid.cIoo d b, c ≠ a → c ≠ b →
      x c ∉ Grid.cIoo (x d) (x a))
    (hcab : c ∈ Grid.cIoo a b) (hcdb : c ∈ Grid.cIoo d b) :
    x c ∉ Grid.cIoo (x d) (x b) := by
  intro hmem
  have hca : c ≠ a := Grid.ne_left_of_mem_cIoo hcab
  have hcb : c ≠ b := Grid.ne_right_of_mem_cIoo hcab
  have hcut : x c ∈ Grid.cIoo (x d) (x a) ∪ insert (x a) (Grid.cIoo (x a) (x b)) := by
    rw [Grid.cIoo_union_insert_cIoo_eq_cIoo_of_mem_cIoo hrow]
    exact hmem
  rw [Finset.mem_union, Finset.mem_insert] at hcut
  rcases hcut with hcut | hcut | hcut
  · exact hsecond c hcdb hca hcb hcut
  · exact hca (x.toPerm.injective hcut)
  · exact hfirst c hcab hcut

/-- The recut in the configuration where the initial side of the first rectangle lies strictly
inside the column span of the second one.

The two rectangles `{a, b} × {x a, x b}` and `{d, b} × {x d, x a}` are cut apart along the column
line `a` instead of the row line `x a`. -/
private theorem exists_isRepartition_col_cut_common_right {a b d : Fin n}
    (hab : a ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (hz : z = (x.swapColumns a b).swapColumns d b)
    (hcol : a ∈ Grid.cIoo d b) (hrow : x a ∈ Grid.cIoo (x d) (x b))
    (hfirst : ∀ c ∈ Grid.cIoo a b, x c ∉ Grid.cIoo (x a) (x b))
    (hsecond : ∀ c ∈ Grid.cIoo d b, c ≠ a → c ≠ b → x c ∉ Grid.cIoo (x d) (x a)) :
    ∃ E : GridRectangleDecomposition x z,
      (E.middle = x.swapColumns d a ∧ E.first.left = d ∧ E.first.right = a ∧
          E.second.left = a ∧ E.second.right = b) ∧
        E.first.toGridRectangle = { left := d, right := a, bottom := x d, top := x a } ∧
          E.second.toGridRectangle = { left := a, right := b, bottom := x d, top := x b } ∧
            E.first.IsEmpty ∧ E.second.IsEmpty := by
  have hz' : z = (x.swapColumns d a).swapColumns a b := by
    rw [hz, GridState.swapColumns_swapColumns_conj x d a a b,
      Equiv.swap_apply_of_ne_of_ne hda hdb, Equiv.swap_apply_left]
  have hmid_a : (x.swapColumns d a) a = x d := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_right]
  have hmid_b : (x.swapColumns d a) b = x b := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hdb.symm hab.symm]
  refine ⟨{ middle := x.swapColumns d a
            first := GridRectangleBetween.ofSwapColumns x _ d a hda rfl
            second := GridRectangleBetween.ofSwapColumns _ z a b hab hz' },
          ⟨rfl, by simp, by simp, by simp, by simp⟩, by simp, by simp [hmid_a, hmid_b], ?_, ?_⟩
  · rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
    simp only [GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right,
      GridRectangleBetween.ofSwapColumns_bottom, GridRectangleBetween.ofSwapColumns_top]
    intro c hc
    have hcdb : c ∈ Grid.cIoo d b := Grid.cIoo_subset_cIoo_right_of_mem_cIoo hcol hc
    have hca : c ≠ a := Grid.ne_right_of_mem_cIoo hc
    have hcb : c ≠ b := Grid.ne_right_of_mem_cIoo hcdb
    exact hsecond c hcdb hca hcb
  · rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
    simp only [GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right,
      GridRectangleBetween.ofSwapColumns_bottom, GridRectangleBetween.ofSwapColumns_top, hmid_a,
      hmid_b]
    intro c hc hmem
    have hca : c ≠ a := Grid.ne_left_of_mem_cIoo hc
    have hcdb : c ∈ Grid.cIoo d b := Grid.cIoo_subset_cIoo_left_of_mem_cIoo hcol hc
    have hcd : c ≠ d := Grid.ne_left_of_mem_cIoo hcdb
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcd hca] at hmem
    exact notMem_cIoo_of_mem_cIoo_of_mem_cIoo_common_right hrow hfirst hsecond hc hcdb hmem

/-- The recut in the configuration where the initial side of the second rectangle lies strictly
inside the column span of the first one.

The two rectangles `{a, b} × {x a, x b}` and `{d, b} × {x d, x a}` are cut apart along the column
line `d` instead of the row line `x a`. -/
private theorem exists_isRepartition_complementary_col_cut_common_right {a b d : Fin n}
    (hab : a ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (hz : z = (x.swapColumns a b).swapColumns d b)
    (hcol : d ∈ Grid.cIoo a b) (hrow : x a ∈ Grid.cIoo (x d) (x b))
    (hfirst : ∀ c ∈ Grid.cIoo a b, x c ∉ Grid.cIoo (x a) (x b))
    (hsecond : ∀ c ∈ Grid.cIoo d b, c ≠ a → c ≠ b → x c ∉ Grid.cIoo (x d) (x a)) :
    ∃ E : GridRectangleDecomposition x z,
      (E.middle = x.swapColumns d b ∧ E.first.left = d ∧ E.first.right = b ∧
          E.second.left = a ∧ E.second.right = d) ∧
        E.first.toGridRectangle = { left := d, right := b, bottom := x d, top := x b } ∧
          E.second.toGridRectangle = { left := a, right := d, bottom := x a, top := x b } ∧
            E.first.IsEmpty ∧ E.second.IsEmpty := by
  have hz' : z = (x.swapColumns d b).swapColumns a d := by
    rw [hz, GridState.swapColumns_swapColumns_conj x a b d b,
      Equiv.swap_apply_of_ne_of_ne hda.symm hab, Equiv.swap_apply_right]
  have hmid_a : (x.swapColumns d b) a = x a := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hda.symm hab]
  have hmid_d : (x.swapColumns d b) d = x b := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_left]
  refine ⟨{ middle := x.swapColumns d b
            first := GridRectangleBetween.ofSwapColumns x _ d b hdb rfl
            second := GridRectangleBetween.ofSwapColumns _ z a d hda.symm hz' },
          ⟨rfl, by simp, by simp, by simp, by simp⟩, by simp, by simp [hmid_a, hmid_d], ?_, ?_⟩
  · rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
    simp only [GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right,
      GridRectangleBetween.ofSwapColumns_bottom, GridRectangleBetween.ofSwapColumns_top]
    intro c hc
    have hcab : c ∈ Grid.cIoo a b := Grid.cIoo_subset_cIoo_left_of_mem_cIoo hcol hc
    exact notMem_cIoo_of_mem_cIoo_of_mem_cIoo_common_right hrow hfirst hsecond hcab hc
  · rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
    simp only [GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right,
      GridRectangleBetween.ofSwapColumns_bottom, GridRectangleBetween.ofSwapColumns_top, hmid_a,
      hmid_d]
    intro c hc
    have hcab : c ∈ Grid.cIoo a b := Grid.cIoo_subset_cIoo_right_of_mem_cIoo hcol hc
    have hcd : c ≠ d := Grid.ne_right_of_mem_cIoo hc
    have hcb : c ≠ b := Grid.ne_right_of_mem_cIoo hcab
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcd hcb]
    exact hfirst c hcab

/-! ### The recut of a decomposition sharing its terminal side column -/

/-- Two composable empty rectangles that share their terminal side column and no other side admit
a *recut*: the L-shaped union of their domains has a second decomposition into two empty
rectangles, through a different intermediate grid state.

The two cyclic orders of the three side columns give the two shapes of the new cut, and in each
of them the intermediate state and the four side columns of the recut are computed, which by
`GridRectangleDecomposition.ext` determine it.

Emptiness of both rectangles enters twice. It fixes the cyclic order of the three side columns
and of the three corner rows, and it then transfers to the two new rectangles: the part of a new
rectangle below the cut is controlled by the second old rectangle and the part above it by the
first. -/
theorem exists_isRepartition_of_isEmpty_of_right_eq_right (D : GridRectangleDecomposition x z)
    (hright : D.first.right = D.second.right) (hleft : D.first.left ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty) :
    ∃! E : GridRectangleDecomposition x z,
      D.IsRepartition E ∧ E.middle ≠ D.middle ∧ E.first.IsEmpty ∧ E.second.IsEmpty ∧
        E.first.left = D.second.left ∧ E.second.left = D.first.left ∧
          ((D.first.left ∈ Grid.cIoo D.second.left D.first.right ∧
              E.middle = x.swapColumns D.second.left D.first.left ∧
                E.first.right = D.first.left ∧ E.second.right = D.first.right) ∨
            (D.second.left ∈ Grid.cIoo D.first.left D.first.right ∧
              E.middle = x.swapColumns D.second.left D.first.right ∧
                E.first.right = D.first.right ∧ E.second.right = D.second.left)) := by
  -- The three side columns, the target state and the two old rectangles, all read in the source
  -- state `x`.
  have hab : D.first.left ≠ D.first.right := D.first.left_ne_right
  have hdb := D.second_left_ne_first_right_of_right_eq_right hright
  obtain ⟨hmid_first, hmid_second⟩ := D.middle_apply_of_right_eq_right hright hleft
  have hmid : D.middle = x.swapColumns D.first.left D.first.right :=
    D.first.target_eq_swapColumns
  have hz : z = (x.swapColumns D.first.left D.first.right).swapColumns D.second.left
      D.first.right := by
    rw [← hmid, hright]
    exact D.second.target_eq_swapColumns
  obtain ⟨hcolcase, hrow⟩ := D.cyclicOrder_of_isEmpty_of_right_eq_right hright hleft hfirst hsecond
  simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hmid_second] at hrow
  have hfirst' : ∀ c ∈ Grid.cIoo D.first.left D.first.right,
      x c ∉ Grid.cIoo (x D.first.left) (x D.first.right) := by
    have h := hfirst
    rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo] at h
    simpa only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def] using h
  have hsecond' := D.forall_notMem_cIoo_second_of_right_eq_right hright hleft hsecond
  have hD1 : D.first.toGridRectangle =
      { left := D.first.left, right := D.first.right, bottom := x D.first.left,
        top := x D.first.right } := D.first.toGridRectangle_eq
  have hD2 := D.toGridRectangle_second_of_right_eq_right hright hleft
  have hDdisj : Disjoint D.first.toGridRectangle.coveredSquares
      D.second.toGridRectangle.coveredSquares := by
    rw [hD1, hD2]
    exact (GridRectangle.disjoint_coveredSquares_of_row_cut hrow).symm
  have hcol_exclusive : ¬(D.first.left ∈ Grid.cIoo D.second.left D.first.right ∧
      D.second.left ∈ Grid.cIoo D.first.left D.first.right) := by
    rw [Grid.mem_cIoo, Grid.mem_cIoo]
    rintro ⟨⟨_, hfirstLeft⟩, ⟨_, hsecondLeft⟩⟩
    split_ifs at hfirstLeft hsecondLeft <;> omega
  rcases hcolcase with hcol | hcol
  -- The initial side of the first rectangle lies inside the column span of the second one: the
  -- new cut runs along that column.
  · obtain ⟨E, ⟨hmidE, hE1left, hE1right, hE2left, hE2right⟩, hE1, hE2, hEfirst, hEsecond⟩ :=
      exists_isRepartition_col_cut_common_right hab hleft.symm hdb hz hcol hrow hfirst' hsecond'
    have hmiddle : E.middle ≠ D.middle := by
      intro h
      have hval : E.middle D.second.left = D.middle D.second.left := by rw [h]
      rw [hmidE, hmid_second] at hval
      simp only [GridState.swapColumns_apply, Equiv.swap_apply_left] at hval
      exact hleft (x.toPerm.injective hval)
    have hEdisj : Disjoint E.first.toGridRectangle.coveredSquares
        E.second.toGridRectangle.coveredSquares := by
      rw [hE1, hE2]
      exact GridRectangle.disjoint_coveredSquares_of_col_cut hcol
    have hunion : E.first.toGridRectangle.coveredSquares ∪
        E.second.toGridRectangle.coveredSquares =
          D.first.toGridRectangle.coveredSquares ∪
            D.second.toGridRectangle.coveredSquares := by
      rw [hE1, hE2, hD1, hD2]
      exact (GridRectangle.coveredSquares_union_eq_of_mem_cIoo_common_right hcol hrow).symm
    refine ⟨E, ⟨⟨hDdisj, hEdisj, hunion⟩, hmiddle, hEfirst, hEsecond, hE1left,
      hE2left, Or.inl ⟨hcol, hmidE, hE1right, hE2right⟩⟩, ?_⟩
    intro E' hE'
    rcases hE' with ⟨_, _, _, _, hE1left', hE2left', hcols'⟩
    have hrights : E'.first.right = D.first.left ∧
        E'.second.right = D.first.right := by
      rcases hcols' with ⟨_, _, hE1right', hE2right'⟩ |
          ⟨hcol', _, _, _⟩
      · exact ⟨hE1right', hE2right'⟩
      · exact (hcol_exclusive ⟨hcol, hcol'⟩).elim
    exact GridRectangleDecomposition.ext (hE1left'.trans hE1left.symm)
      (hrights.1.trans hE1right.symm) (hE2left'.trans hE2left.symm)
      (hrights.2.trans hE2right.symm)
  -- The initial side of the second rectangle lies inside the column span of the first one: the
  -- new cut runs along that column instead.
  · obtain ⟨E, ⟨hmidE, hE1left, hE1right, hE2left, hE2right⟩, hE1, hE2, hEfirst, hEsecond⟩ :=
      exists_isRepartition_complementary_col_cut_common_right hab hleft.symm hdb hz hcol hrow
        hfirst' hsecond'
    have hmiddle : E.middle ≠ D.middle := by
      intro h
      have hval : E.middle D.first.right = D.middle D.first.right := by rw [h]
      rw [hmidE, hmid_first] at hval
      simp only [GridState.swapColumns_apply, Equiv.swap_apply_right] at hval
      exact hleft (x.toPerm.injective hval).symm
    have hEdisj : Disjoint E.first.toGridRectangle.coveredSquares
        E.second.toGridRectangle.coveredSquares := by
      rw [hE1, hE2]
      exact (GridRectangle.disjoint_coveredSquares_of_col_cut hcol).symm
    have hunion : E.first.toGridRectangle.coveredSquares ∪
        E.second.toGridRectangle.coveredSquares =
          D.first.toGridRectangle.coveredSquares ∪
            D.second.toGridRectangle.coveredSquares := by
      rw [hE1, hE2, hD1, hD2]
      exact (GridRectangle.coveredSquares_union_eq_of_mem_cIoo_common_right_complementary_col_cut
        hcol hrow).symm
    refine ⟨E, ⟨⟨hDdisj, hEdisj, hunion⟩, hmiddle, hEfirst, hEsecond, hE1left,
      hE2left, Or.inr ⟨hcol, hmidE, hE1right, hE2right⟩⟩, ?_⟩
    intro E' hE'
    rcases hE' with ⟨_, _, _, _, hE1left', hE2left', hcols'⟩
    have hrights : E'.first.right = D.first.right ∧
        E'.second.right = D.second.left := by
      rcases hcols' with ⟨hcol', _, _, _⟩ |
          ⟨_, _, hE1right', hE2right'⟩
      · exact (hcol_exclusive ⟨hcol', hcol⟩).elim
      · exact ⟨hE1right', hE2right'⟩
    exact GridRectangleDecomposition.ext (hE1left'.trans hE1left.symm)
      (hrights.1.trans hE1right.symm) (hE2left'.trans hE2left.symm)
      (hrights.2.trans hE2right.symm)

/-- For each two-step term of `∂⁻ ∘ ∂⁻` whose two rectangles share their terminal side column
there is a unique second such term through a different intermediate grid state. Its domain is a
repartition of the original domain, so its weight agrees over every coefficient ring. -/
theorem exists_isRepartition_of_mem_unblockedRectangles_of_right_eq_right (G : GridDiagram n)
    (D : GridRectangleDecomposition x z)
    (hright : D.first.right = D.second.right) (hleft : D.first.left ≠ D.second.left)
    (hfirst : D.first ∈ G.unblockedRectangles x D.middle)
    (hsecond : D.second ∈ G.unblockedRectangles D.middle z) :
    ∃! E : GridRectangleDecomposition x z,
      D.IsRepartition E ∧ E.middle ≠ D.middle ∧
        E.first ∈ G.unblockedRectangles x E.middle ∧
          E.second ∈ G.unblockedRectangles E.middle z ∧
            E.first.left = D.second.left ∧ E.second.left = D.first.left ∧
              ((D.first.left ∈ Grid.cIoo D.second.left D.first.right ∧
                  E.middle = x.swapColumns D.second.left D.first.left ∧
                    E.first.right = D.first.left ∧ E.second.right = D.first.right) ∨
                (D.second.left ∈ Grid.cIoo D.first.left D.first.right ∧
                  E.middle = x.swapColumns D.second.left D.first.right ∧
                    E.first.right = D.first.right ∧ E.second.right = D.second.left)) := by
  obtain ⟨E, ⟨hrecut, hmiddle, hEfirst, hEsecond, hE1left, hE2left, hcols⟩, hunique⟩ :=
    D.exists_isRepartition_of_isEmpty_of_right_eq_right hright hleft
    (G.isEmpty_of_mem_unblockedRectangles hfirst) (G.isEmpty_of_mem_unblockedRectangles hsecond)
  have hX₁ := G.disjoint_XSet_of_mem_unblockedRectangles hfirst
  have hX₂ := G.disjoint_XSet_of_mem_unblockedRectangles hsecond
  refine ⟨E, ⟨hrecut, hmiddle,
    (G.mem_unblockedRectangles _).mpr
      ⟨hEfirst, hrecut.disjoint_coveredSquares_first hX₁ hX₂⟩,
    (G.mem_unblockedRectangles _).mpr
      ⟨hEsecond, hrecut.disjoint_coveredSquares_second hX₁ hX₂⟩,
    hE1left, hE2left, hcols⟩, ?_⟩
  intro E' hE'
  apply hunique E'
  exact ⟨hE'.1, hE'.2.1, (G.mem_unblockedRectangles _).mp hE'.2.2.1 |>.1,
    (G.mem_unblockedRectangles _).mp hE'.2.2.2.1 |>.1, hE'.2.2.2.2⟩

end GridRectangleDecomposition

end TauCeti
