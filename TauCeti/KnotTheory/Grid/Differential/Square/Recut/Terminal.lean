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
a symmetry of the situation. Reversing a rectangle (to the one from `y` to `x`) does exchange its
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

## Main results

* `TauCeti.GridRectangleDecomposition.exists_isRepartition_of_isEmpty_of_right_eq_right`: two
  composable empty rectangles sharing their terminal side column admit a recut by two empty
  rectangles, whose intermediate state and side columns are computed.

## References

The recut follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.6.
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

/-- The target of a decomposition whose two rectangles share their terminal side column is obtained
from the source by the two column swaps of the rectangles. -/
private theorem target_eq_swapColumns_swapColumns_of_right_eq_right
    (D : GridRectangleDecomposition x z) (hright : D.first.right = D.second.right) :
    z = (x.swapColumns D.first.left D.first.right).swapColumns D.second.left D.first.right := by
  have hmid : D.middle = x.swapColumns D.first.left D.first.right := D.first.target_eq_swapColumns
  rw [← hmid, hright]
  exact D.second.target_eq_swapColumns

/-- The two old rectangles of a decomposition sharing their terminal side column cover disjoint
sets of squares once the shared corner row lies strictly between the other two corner rows. -/
private theorem disjoint_coveredSquares_of_right_eq_right (D : GridRectangleDecomposition x z)
    (hright : D.first.right = D.second.right) (hleft : D.first.left ≠ D.second.left)
    (hrow : x D.first.left ∈ Grid.cIoo (x D.second.left) (x D.first.right)) :
    Disjoint D.first.toGridRectangle.coveredSquares D.second.toGridRectangle.coveredSquares := by
  rw [D.first.toGridRectangle_eq, D.toGridRectangle_second_of_right_eq_right hright hleft]
  exact (GridRectangle.disjoint_coveredSquares_of_row_cut hrow).symm

/-- The initial sides of the two rectangles cannot each lie strictly inside the column span of the
other rectangle. -/
private theorem not_mem_cIoo_and_mem_cIoo {a b d : Fin n} :
    ¬(a ∈ Grid.cIoo d b ∧ d ∈ Grid.cIoo a b) := by
  rintro ⟨h, h'⟩
  exact (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap a b)) h' (Grid.mem_cIoo_cyclic_right h)

/-- The recut of a decomposition sharing its terminal side column, in the configuration where the
initial side of the first rectangle lies strictly inside the column span of the second one. -/
private theorem exists_isRepartition_of_right_eq_right_of_mem_cIoo_left
    (D : GridRectangleDecomposition x z)
    (hright : D.first.right = D.second.right) (hleft : D.first.left ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)
    (hcol : D.first.left ∈ Grid.cIoo D.second.left D.first.right)
    (hrow : x D.first.left ∈ Grid.cIoo (x D.second.left) (x D.first.right)) :
    ∃ E : GridRectangleDecomposition x z,
      D.IsRepartition E ∧ E.middle ≠ D.middle ∧ E.first.IsEmpty ∧ E.second.IsEmpty ∧
        E.first.left = D.second.left ∧ E.second.left = D.first.left ∧
          (D.first.left ∈ Grid.cIoo D.second.left D.first.right ∧
            E.middle = x.swapColumns D.second.left D.first.left ∧
              E.first.right = D.first.left ∧ E.second.right = D.first.right) := by
  obtain ⟨E, ⟨hmidE, hE1left, hE1right, hE2left, hE2right⟩, hE1, hE2, hEfirst, hEsecond⟩ :=
    exists_isRepartition_col_cut_common_right D.first.left_ne_right hleft.symm
      (D.second_left_ne_first_right_of_right_eq_right hright)
      (D.target_eq_swapColumns_swapColumns_of_right_eq_right hright) hcol hrow
      (D.first.isEmpty_iff_forall_notMem_cIoo.mp hfirst)
      (D.forall_notMem_cIoo_second_of_right_eq_right hright hleft hsecond)
  have hmiddle : E.middle ≠ D.middle := by
    intro h
    have hval : E.middle D.second.left = D.middle D.second.left := by rw [h]
    rw [hmidE, (D.middle_apply_of_right_eq_right hright hleft).2] at hval
    simp only [GridState.swapColumns_apply, Equiv.swap_apply_left] at hval
    exact hleft (x.toPerm.injective hval)
  have hEdisj : Disjoint E.first.toGridRectangle.coveredSquares
      E.second.toGridRectangle.coveredSquares := by
    rw [hE1, hE2]
    exact GridRectangle.disjoint_coveredSquares_of_col_cut hcol
  have hunion : E.first.toGridRectangle.coveredSquares ∪ E.second.toGridRectangle.coveredSquares =
      D.first.toGridRectangle.coveredSquares ∪ D.second.toGridRectangle.coveredSquares := by
    rw [hE1, hE2, D.first.toGridRectangle_eq,
      D.toGridRectangle_second_of_right_eq_right hright hleft]
    exact (GridRectangle.coveredSquares_union_eq_of_mem_cIoo_common_right hcol hrow).symm
  exact ⟨E, ⟨D.disjoint_coveredSquares_of_right_eq_right hright hleft hrow, hEdisj, hunion⟩,
    hmiddle, hEfirst, hEsecond, hE1left, hE2left, hcol, hmidE, hE1right, hE2right⟩

/-- The recut of a decomposition sharing its terminal side column, in the configuration where the
initial side of the second rectangle lies strictly inside the column span of the first one. -/
private theorem exists_isRepartition_of_right_eq_right_of_mem_cIoo_right
    (D : GridRectangleDecomposition x z)
    (hright : D.first.right = D.second.right) (hleft : D.first.left ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)
    (hcol : D.second.left ∈ Grid.cIoo D.first.left D.first.right)
    (hrow : x D.first.left ∈ Grid.cIoo (x D.second.left) (x D.first.right)) :
    ∃ E : GridRectangleDecomposition x z,
      D.IsRepartition E ∧ E.middle ≠ D.middle ∧ E.first.IsEmpty ∧ E.second.IsEmpty ∧
        E.first.left = D.second.left ∧ E.second.left = D.first.left ∧
          (D.second.left ∈ Grid.cIoo D.first.left D.first.right ∧
            E.middle = x.swapColumns D.second.left D.first.right ∧
              E.first.right = D.first.right ∧ E.second.right = D.second.left) := by
  obtain ⟨E, ⟨hmidE, hE1left, hE1right, hE2left, hE2right⟩, hE1, hE2, hEfirst, hEsecond⟩ :=
    exists_isRepartition_complementary_col_cut_common_right D.first.left_ne_right hleft.symm
      (D.second_left_ne_first_right_of_right_eq_right hright)
      (D.target_eq_swapColumns_swapColumns_of_right_eq_right hright) hcol hrow
      (D.first.isEmpty_iff_forall_notMem_cIoo.mp hfirst)
      (D.forall_notMem_cIoo_second_of_right_eq_right hright hleft hsecond)
  have hmiddle : E.middle ≠ D.middle := by
    intro h
    have hval : E.middle D.first.right = D.middle D.first.right := by rw [h]
    rw [hmidE, (D.middle_apply_of_right_eq_right hright hleft).1] at hval
    simp only [GridState.swapColumns_apply, Equiv.swap_apply_right] at hval
    exact hleft (x.toPerm.injective hval).symm
  have hEdisj : Disjoint E.first.toGridRectangle.coveredSquares
      E.second.toGridRectangle.coveredSquares := by
    rw [hE1, hE2]
    exact (GridRectangle.disjoint_coveredSquares_of_col_cut hcol).symm
  have hunion : E.first.toGridRectangle.coveredSquares ∪ E.second.toGridRectangle.coveredSquares =
      D.first.toGridRectangle.coveredSquares ∪ D.second.toGridRectangle.coveredSquares := by
    rw [hE1, hE2, D.first.toGridRectangle_eq,
      D.toGridRectangle_second_of_right_eq_right hright hleft]
    exact (GridRectangle.coveredSquares_union_eq_of_mem_cIoo_common_right_complementary_col_cut
      hcol hrow).symm
  exact ⟨E, ⟨D.disjoint_coveredSquares_of_right_eq_right hright hleft hrow, hEdisj, hunion⟩,
    hmiddle, hEfirst, hEsecond, hE1left, hE2left, hcol, hmidE, hE1right, hE2right⟩

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
  obtain ⟨hcolcase, hrow⟩ := D.cyclicOrder_of_isEmpty_of_right_eq_right hright hleft hfirst hsecond
  simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
    (D.middle_apply_of_right_eq_right hright hleft).2] at hrow
  refine existsUnique_of_exists_of_unique ?_ ?_
  · rcases hcolcase with hcol | hcol
    · obtain ⟨E, h⟩ := D.exists_isRepartition_of_right_eq_right_of_mem_cIoo_left hright hleft hfirst
        hsecond hcol hrow
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
      exact ⟨E, h1, h2, h3, h4, h5, h6, Or.inl h7⟩
    · obtain ⟨E, h⟩ := D.exists_isRepartition_of_right_eq_right_of_mem_cIoo_right hright hleft
        hfirst hsecond hcol hrow
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
      exact ⟨E, h1, h2, h3, h4, h5, h6, Or.inr h7⟩
  · rintro E E' ⟨-, -, -, -, hE1left, hE2left, hcols⟩ ⟨-, -, -, -, hE1left', hE2left', hcols'⟩
    have hrights : E.first.right = E'.first.right ∧ E.second.right = E'.second.right := by
      rcases hcols with ⟨hcol, -, hE1right, hE2right⟩ | ⟨hcol, -, hE1right, hE2right⟩ <;>
        rcases hcols' with ⟨hcol', -, hE1right', hE2right'⟩ | ⟨hcol', -, hE1right', hE2right'⟩
      · exact ⟨hE1right.trans hE1right'.symm, hE2right.trans hE2right'.symm⟩
      · exact (not_mem_cIoo_and_mem_cIoo ⟨hcol, hcol'⟩).elim
      · exact (not_mem_cIoo_and_mem_cIoo ⟨hcol', hcol⟩).elim
      · exact ⟨hE1right.trans hE1right'.symm, hE2right.trans hE2right'.symm⟩
    exact GridRectangleDecomposition.ext (hE1left.trans hE1left'.symm) hrights.1
      (hE2left.trans hE2left'.symm) hrights.2

end GridRectangleDecomposition

end TauCeti
