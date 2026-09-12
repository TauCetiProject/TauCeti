/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Mixed

/-!
# The recut pairing on two-step grid rectangle decompositions

A nondiagonal term in the square of the unblocked grid differential `∂⁻` is a pair of composable
empty rectangles whose two pairs of side columns are disjoint or share exactly one column. In the
second case the two rectangles meet at a corner, their union is an L-shaped hexagon, and cutting
that hexagon the other way gives a second such pair through a different intermediate grid state.
The four orientations of the common column are constructed in `Recut/Initial.lean`,
`Recut/Terminal.lean` and `Recut/Mixed.lean`, each as the unique decomposition carrying the side
data computed there. This file assembles those four constructions into a single involution, the
pairing that cancels the one-common-side terms of `∂⁻ ∘ ∂⁻` in characteristic two.

`GridRectangleDecomposition.IsRecut` collects the four side-data alternatives into one relation.
A decomposition has at most one orientation of its common column, so exactly one alternative can
hold and the relation has a unique solution. Recutting twice returns the original decomposition:
a common initial or terminal column recuts to a mixed common column and conversely, and in each of
the eight resulting configurations the original decomposition satisfies precisely the side data
that describes the recut of the recut. On the decompositions the unblocked differential counts
whose two rectangles share exactly one side column -- the only ones for which a recut is
constructed -- the relation is therefore symmetric, and uniqueness turns it into an involution
`GridRectangleDecomposition.recut` of that set. It has no fixed point, since the intermediate state
changes, and it preserves the covered-square domain, hence the weight `V^{O(r₁)} · V^{O(r₂)}` that
the square of the differential attaches to a two-step term.

The geometric input is the cyclic order forced by emptiness of both rectangles: for a common
initial or terminal column the corner row of the common side lies strictly between the other two
corner rows, and for a mixed common column the terminal side of the first rectangle lies strictly
between the other two side columns. That one order fact decides which of the two alternatives of
the recut's own side data holds.

## Main definitions

* `TauCeti.GridRectangleDecomposition.IsRecutOfLeftEqLeft`,
  `TauCeti.GridRectangleDecomposition.IsRecutOfRightEqRight`,
  `TauCeti.GridRectangleDecomposition.IsRecutOfLeftEqRight` and
  `TauCeti.GridRectangleDecomposition.IsRecutOfRightEqLeft`: the side data computed for the recut
  in each of the four orientations of the common side column.
* `TauCeti.GridRectangleDecomposition.IsRecut`: a second two-step decomposition repartitioning the
  same domain into rectangles the unblocked differential counts, through a different intermediate
  state, with the side data of the matching orientation.
* `TauCeti.GridRectangleDecomposition.recut`: the recut of a decomposition sharing exactly one
  side column.

## Main results

* `TauCeti.GridRectangleDecomposition.existsUnique_isRecut`: a counted decomposition sharing
  exactly one side column has exactly one recut.
* `TauCeti.GridRectangleDecomposition.IsRecut.symm`: a counted decomposition sharing exactly one
  side column is a recut of its own recut.
* `TauCeti.GridRectangleDecomposition.recut_recut`: recutting is an involution.
* `TauCeti.GridRectangleDecomposition.recut_ne`: it has no fixed point.
* `TauCeti.GridRectangleDecomposition.hasOneCommonSide_recut`: the recut again shares exactly one
  side column, so the involution stays inside the one-common-side terms.

## References

The recut of an L-shaped juxtaposition follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots
and Links*, Chapter 4.6.
-/
public section

namespace TauCeti

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-- The side data of the recut of a decomposition whose two rectangles share their initial side
column. -/
def IsRecutOfLeftEqLeft (D E : GridRectangleDecomposition x z) : Prop :=
  D.first.left = D.second.left ∧
    E.first.right = D.second.right ∧ E.second.right = D.first.right ∧
      ((D.first.right ∈ Grid.cIoo D.first.left D.second.right ∧
          E.middle = x.swapColumns D.first.right D.second.right ∧
            E.first.left = D.first.right ∧ E.second.left = D.first.left) ∨
        (D.second.right ∈ Grid.cIoo D.first.left D.first.right ∧
          E.middle = x.swapColumns D.first.left D.second.right ∧
            E.first.left = D.first.left ∧ E.second.left = D.second.right))

/-- The side data of the recut of a decomposition whose two rectangles share their terminal side
column. -/
def IsRecutOfRightEqRight (D E : GridRectangleDecomposition x z) : Prop :=
  D.first.right = D.second.right ∧
    E.first.left = D.second.left ∧ E.second.left = D.first.left ∧
      ((D.first.left ∈ Grid.cIoo D.second.left D.first.right ∧
          E.middle = x.swapColumns D.second.left D.first.left ∧
            E.first.right = D.first.left ∧ E.second.right = D.first.right) ∨
        (D.second.left ∈ Grid.cIoo D.first.left D.first.right ∧
          E.middle = x.swapColumns D.second.left D.first.right ∧
            E.first.right = D.first.right ∧ E.second.right = D.second.left))

/-- The side data of the recut of a decomposition whose common column is the initial side of its
first rectangle and the terminal side of its second. -/
def IsRecutOfLeftEqRight (D E : GridRectangleDecomposition x z) : Prop :=
  D.first.left = D.second.right ∧
    E.first.bottom = D.second.bottom ∧ E.second.bottom = D.first.bottom ∧
      ((D.first.bottom ∈ Grid.cIoo D.second.bottom D.first.top ∧
          E.middle = x.swapRows D.second.bottom D.first.bottom ∧
            E.first.top = D.first.bottom ∧ E.second.top = D.first.top) ∨
        (D.second.bottom ∈ Grid.cIoo D.first.bottom D.first.top ∧
          E.middle = x.swapRows D.second.bottom D.first.top ∧
            E.first.top = D.first.top ∧ E.second.top = D.second.bottom))

/-- The side data of the recut of a decomposition whose common column is the terminal side of its
first rectangle and the initial side of its second. -/
def IsRecutOfRightEqLeft (D E : GridRectangleDecomposition x z) : Prop :=
  D.first.right = D.second.left ∧
    E.first.top = D.second.top ∧ E.second.top = D.first.top ∧
      ((D.first.top ∈ Grid.cIoo D.first.bottom D.second.top ∧
          E.middle = x.swapRows D.first.top D.second.top ∧
            E.first.bottom = D.first.top ∧ E.second.bottom = D.first.bottom) ∨
        (D.second.top ∈ Grid.cIoo D.first.bottom D.first.top ∧
          E.middle = x.swapRows D.first.bottom D.second.top ∧
            E.first.bottom = D.first.bottom ∧ E.second.bottom = D.second.top))

/-- `E` is the recut of the two-step decomposition `D`: it repartitions the same domain into two
rectangles the unblocked differential counts, passes through a different intermediate state, and
carries the side data computed for the orientation of the common side column of `D`. -/
def IsRecut (G : GridDiagram n) (D E : GridRectangleDecomposition x z) : Prop :=
  D.IsRepartition E ∧ E.middle ≠ D.middle ∧
    E.first ∈ G.unblockedRectangles x E.middle ∧
      E.second ∈ G.unblockedRectangles E.middle z ∧
        (D.IsRecutOfLeftEqLeft E ∨ D.IsRecutOfRightEqRight E ∨
          D.IsRecutOfLeftEqRight E ∨ D.IsRecutOfRightEqLeft E)

/-! ### Existence and uniqueness of the recut -/

/-- A two-step decomposition counted by the unblocked differential whose two rectangles share
exactly one side column has exactly one recut. -/
theorem existsUnique_isRecut (G : GridDiagram n) (D : GridRectangleDecomposition x z)
    (hone : D.HasOneCommonSide)
    (hfirst : D.first ∈ G.unblockedRectangles x D.middle)
    (hsecond : D.second ∈ G.unblockedRectangles D.middle z) :
    ∃! E : GridRectangleDecomposition x z, D.IsRecut G E := by
  rcases D.side_eq_cases_of_hasOneCommonSide hone with
      ⟨hcommon, hother⟩ | ⟨hcommon, hother⟩ | ⟨hcommon, hother⟩ | ⟨hcommon, hother⟩
  · obtain ⟨E, ⟨hrep, hmid, hEf, hEs, hE₁, hE₂, hbranch⟩, hunique⟩ :=
      D.exists_isRepartition_of_mem_unblockedRectangles_of_left_eq_left G hcommon hother hfirst
        hsecond
    refine ⟨E, ⟨hrep, hmid, hEf, hEs, Or.inl ⟨hcommon, hE₁, hE₂, hbranch⟩⟩, ?_⟩
    rintro E' ⟨hrep', hmid', hEf', hEs', hdata'⟩
    rcases hdata' with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact hunique E' ⟨hrep', hmid', hEf', hEs', h⟩
    · exact absurd h hother
    · exact absurd (hcommon.symm.trans h) D.second.left_ne_right
    · exact absurd (h.trans hcommon.symm) D.first.left_ne_right.symm
  · obtain ⟨E, ⟨hrep, hmid, hEf, hEs, hE₁, hE₂, hbranch⟩, hunique⟩ :=
      D.exists_isRepartition_of_mem_unblockedRectangles_of_left_eq_right G hcommon hother hfirst
        hsecond
    refine ⟨E, ⟨hrep, hmid, hEf, hEs, Or.inr (Or.inr (Or.inl ⟨hcommon, hE₁, hE₂, hbranch⟩))⟩, ?_⟩
    rintro E' ⟨hrep', hmid', hEf', hEs', hdata'⟩
    rcases hdata' with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd (hcommon.symm.trans h) D.second.left_ne_right.symm
    · exact absurd (hcommon.trans h.symm) D.first.left_ne_right
    · exact hunique E' ⟨hrep', hmid', hEf', hEs', h⟩
    · exact absurd h hother
  · obtain ⟨E, ⟨hrep, hmid, hEf, hEs, hE₁, hE₂, hbranch⟩, hunique⟩ :=
      D.exists_isRepartition_of_mem_unblockedRectangles_of_right_eq_left G hcommon hother hfirst
        hsecond
    refine ⟨E, ⟨hrep, hmid, hEf, hEs, Or.inr (Or.inr (Or.inr ⟨hcommon, hE₁, hE₂, hbranch⟩))⟩, ?_⟩
    rintro E' ⟨hrep', hmid', hEf', hEs', hdata'⟩
    rcases hdata' with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd (h.trans hcommon.symm) D.first.left_ne_right
    · exact absurd (hcommon.symm.trans h) D.second.left_ne_right
    · exact absurd h hother
    · exact hunique E' ⟨hrep', hmid', hEf', hEs', h⟩
  · obtain ⟨E, ⟨hrep, hmid, hEf, hEs, hE₁, hE₂, hbranch⟩, hunique⟩ :=
      D.exists_isRepartition_of_mem_unblockedRectangles_of_right_eq_right G hcommon hother hfirst
        hsecond
    refine ⟨E, ⟨hrep, hmid, hEf, hEs, Or.inr (Or.inl ⟨hcommon, hE₁, hE₂, hbranch⟩)⟩, ?_⟩
    rintro E' ⟨hrep', hmid', hEf', hEs', hdata'⟩
    rcases hdata' with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hother
    · exact hunique E' ⟨hrep', hmid', hEf', hEs', h⟩
    · exact absurd (h.trans hcommon.symm) D.first.left_ne_right
    · exact absurd (hcommon.symm.trans h) D.second.left_ne_right.symm

/-! ### The recut of the recut -/

/-- A column read off the row it occupies after a column swap. -/
private theorem eq_swap_of_swapColumns_apply_eq {a b c d : Fin n}
    (h : x.swapColumns a b c = x d) : c = Equiv.swap a b d :=
  Equiv.swap_apply_eq_iff.mp (x.toPerm.injective (by rwa [GridState.swapColumns_apply] at h))

/-- The recut of a counted decomposition whose two rectangles share their initial side column
carries the side data describing the original decomposition as its own recut. The common column
of the recut is mixed, so which of the two mixed alternatives holds is decided by the cyclic
order of the three corner rows that emptiness forces. -/
private theorem isRecut_symm_of_left_eq_left {D E : GridRectangleDecomposition x z}
    (hdata : D.IsRecutOfLeftEqLeft E) (hone : D.HasOneCommonSide)
    (hDempty₁ : D.first.IsEmpty) (hDempty₂ : D.second.IsEmpty) :
    E.IsRecutOfLeftEqLeft D ∨ E.IsRecutOfRightEqRight D ∨
      E.IsRecutOfLeftEqRight D ∨ E.IsRecutOfRightEqLeft D := by
  obtain ⟨hcommon, hE₁, hE₂, hbranch⟩ := hdata
  have hDmid := D.first.target_eq_swapRows
  have hother : D.first.right ≠ D.second.right := fun hr =>
    D.sideColumns_ne_of_hasOneCommonSide hone
      (by rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hcommon, hr])
  have hvm : D.second.right ≠ D.first.left := by
    rw [hcommon]
    exact D.second.left_ne_right.symm
  have hrow := (D.cyclicOrder_of_isEmpty_of_left_eq_left hcommon hother hDempty₁ hDempty₂).2
  have hDbot₂ : D.second.bottom = x D.first.right := by
    rw [GridRectangleBetween.bottom_def, ← hcommon, D.first.target_apply, Equiv.swap_apply_left]
  have hDtop₂ : D.second.top = x D.second.right := by
    rw [GridRectangleBetween.top_def, D.first.target_apply,
      Equiv.swap_apply_of_ne_of_ne hvm hother.symm]
  rw [hDtop₂] at hrow
  rcases hbranch with ⟨-, hEmid, hEl₁, hEl₂⟩ | ⟨-, hEmid, hEl₁, hEl₂⟩
  · -- the recut has its common column initial for the first and terminal for the second
    have hEbot₁ : E.first.bottom = x D.first.right := by
      rw [GridRectangleBetween.bottom_def, hEl₁]
    have hEtop₁ : E.first.top = x D.second.right := by
      rw [GridRectangleBetween.top_def, hE₁]
    have hEbot₂ : E.second.bottom = x D.first.left := by
      rw [GridRectangleBetween.bottom_def, hEl₂, hEmid, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne D.first.left_ne_right hvm.symm]
    refine Or.inr (Or.inr (Or.inl ⟨hEl₁.trans hE₂.symm, ?_, ?_, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩))
    · rw [hEbot₂, GridRectangleBetween.bottom_def]
    · rw [hEbot₁, hDbot₂]
    · rw [hEbot₁, hEbot₂, hEtop₁]
      exact hrow
    · rw [hEbot₁, hEbot₂]
      exact hDmid
    · rw [hEbot₁, GridRectangleBetween.top_def]
    · rw [hEtop₁, hDtop₂]
  · -- the recut has its common column terminal for the first and initial for the second
    have hEbot₁ : E.first.bottom = x D.first.left := by
      rw [GridRectangleBetween.bottom_def, hEl₁]
    have hEtop₁ : E.first.top = x D.second.right := by
      rw [GridRectangleBetween.top_def, hE₁]
    have hEtop₂ : E.second.top = x D.first.right := by
      rw [GridRectangleBetween.top_def, hE₂, hEmid, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne D.first.left_ne_right.symm hother]
    refine Or.inr (Or.inr (Or.inr ⟨hE₁.trans hEl₂.symm, ?_, ?_, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩))
    · rw [hEtop₂, GridRectangleBetween.top_def]
    · rw [hEtop₁, hDtop₂]
    · rw [hEtop₂, hEbot₁, hEtop₁]
      exact hrow
    · rw [hEbot₁, hEtop₂]
      exact hDmid
    · rw [hEbot₁, GridRectangleBetween.bottom_def]
    · rw [hEtop₂, hDbot₂]

/-- The recut of a counted decomposition whose two rectangles share their terminal side column
carries the side data describing the original decomposition as its own recut. As in the initial
case the common column of the recut is mixed, and the cyclic order of the corner rows decides
which mixed alternative holds. -/
private theorem isRecut_symm_of_right_eq_right {D E : GridRectangleDecomposition x z}
    (hdata : D.IsRecutOfRightEqRight E) (hone : D.HasOneCommonSide)
    (hDempty₁ : D.first.IsEmpty) (hDempty₂ : D.second.IsEmpty) :
    E.IsRecutOfLeftEqLeft D ∨ E.IsRecutOfRightEqRight D ∨
      E.IsRecutOfLeftEqRight D ∨ E.IsRecutOfRightEqLeft D := by
  obtain ⟨hcommon, hE₁, hE₂, hbranch⟩ := hdata
  have hDmid := D.first.target_eq_swapRows
  have hother : D.first.left ≠ D.second.left := fun hl =>
    D.sideColumns_ne_of_hasOneCommonSide hone
      (by rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hcommon, hl])
  have hvm : D.second.left ≠ D.first.right := by
    rw [hcommon]
    exact D.second.left_ne_right
  have hrow := (D.cyclicOrder_of_isEmpty_of_right_eq_right hcommon hother hDempty₁ hDempty₂).2
  have hDbot₂ : D.second.bottom = x D.second.left := by
    rw [GridRectangleBetween.bottom_def, D.first.target_apply,
      Equiv.swap_apply_of_ne_of_ne hother.symm hvm]
  have hDtop₂ : D.second.top = x D.first.left := by
    rw [GridRectangleBetween.top_def, ← hcommon, D.first.target_apply, Equiv.swap_apply_right]
  rw [hDbot₂] at hrow
  rcases hbranch with ⟨-, hEmid, hEr₁, hEr₂⟩ | ⟨-, hEmid, hEr₁, hEr₂⟩
  · -- the recut has its common column terminal for the first and initial for the second
    have hEbot₁ : E.first.bottom = x D.second.left := by
      rw [GridRectangleBetween.bottom_def, hE₁]
    have hEtop₁ : E.first.top = x D.first.left := by
      rw [GridRectangleBetween.top_def, hEr₁]
    have hEtop₂ : E.second.top = x D.first.right := by
      rw [GridRectangleBetween.top_def, hEr₂, hEmid, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne hvm.symm D.first.left_ne_right.symm]
    refine Or.inr (Or.inr (Or.inr ⟨hEr₁.trans hE₂.symm, ?_, ?_, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩))
    · rw [hEtop₂, GridRectangleBetween.top_def]
    · rw [hEtop₁, hDtop₂]
    · rw [hEtop₁, hEbot₁, hEtop₂]
      exact hrow
    · rw [hEtop₁, hEtop₂]
      exact hDmid
    · rw [hEtop₁, GridRectangleBetween.bottom_def]
    · rw [hEbot₁, hDbot₂]
  · -- the recut has its common column initial for the first and terminal for the second
    have hEbot₁ : E.first.bottom = x D.second.left := by
      rw [GridRectangleBetween.bottom_def, hE₁]
    have hEtop₁ : E.first.top = x D.first.right := by
      rw [GridRectangleBetween.top_def, hEr₁]
    have hEbot₂ : E.second.bottom = x D.first.left := by
      rw [GridRectangleBetween.bottom_def, hE₂, hEmid, GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne hother D.first.left_ne_right]
    refine Or.inr (Or.inr (Or.inl ⟨hE₁.trans hEr₂.symm, ?_, ?_, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩))
    · rw [hEbot₂, GridRectangleBetween.bottom_def]
    · rw [hEbot₁, hDbot₂]
    · rw [hEbot₂, hEbot₁, hEtop₁]
      exact hrow
    · rw [hEbot₂, hEtop₁]
      exact hDmid
    · rw [hEtop₁, GridRectangleBetween.top_def]
    · rw [hEbot₂, hDtop₂]

/-- The recut of a counted decomposition whose common column is initial for its first rectangle
and terminal for its second carries the side data describing the original decomposition as its
own recut. Here the recut has both its rectangles on one side column, so the intermediate state
is a column swap and the side columns are read off the rows they occupy. -/
private theorem isRecut_symm_of_left_eq_right {D E : GridRectangleDecomposition x z}
    (hdata : D.IsRecutOfLeftEqRight E) (hone : D.HasOneCommonSide)
    (hDempty₁ : D.first.IsEmpty) (hDempty₂ : D.second.IsEmpty) :
    E.IsRecutOfLeftEqLeft D ∨ E.IsRecutOfRightEqRight D ∨
      E.IsRecutOfLeftEqRight D ∨ E.IsRecutOfRightEqLeft D := by
  obtain ⟨hcommon, hE₁, hE₂, hbranch⟩ := hdata
  have hother : D.first.right ≠ D.second.left := fun hr =>
    D.sideColumns_ne_of_hasOneCommonSide hone
      (by rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hcommon, hr,
        Finset.pair_comm])
  have hvm : D.second.left ≠ D.first.left := by
    rw [hcommon]
    exact D.second.left_ne_right
  have hcol := (D.cyclicOrder_of_isEmpty_of_left_eq_right hcommon hother hDempty₁ hDempty₂).1
  have hrot : D.first.left ∈ Grid.cIoo D.second.left D.first.right :=
    Grid.mem_cIoo_cyclic_right hcol
  have hDbot₂ : D.second.bottom = x D.second.left := by
    rw [GridRectangleBetween.bottom_def, D.first.target_apply,
      Equiv.swap_apply_of_ne_of_ne hvm hother.symm]
  have hDtop₂ : D.second.top = x D.first.right := by
    rw [GridRectangleBetween.top_def, ← hcommon, D.first.target_apply, Equiv.swap_apply_left]
  rcases hbranch with ⟨-, hEmid, hEt₁, hEt₂⟩ | ⟨-, hEmid, hEt₁, hEt₂⟩
  · -- the recut has both its rectangles on the same initial side column
    have hEmid' : E.middle = x.swapColumns D.second.left D.first.left := by
      rw [hEmid, hDbot₂, GridRectangleBetween.bottom_def, GridState.swapColumns_eq_swapRows]
    have hxEl₁ : x E.first.left = x D.second.left := by exact hE₁.trans hDbot₂
    have hEl₁ : E.first.left = D.second.left := x.toPerm.injective hxEl₁
    have hxEr₁ : x E.first.right = x D.first.left := by exact hEt₁
    have hEr₁ : E.first.right = D.first.left := x.toPerm.injective hxEr₁
    have hEl₂ : E.second.left = Equiv.swap D.second.left D.first.left D.first.left :=
      eq_swap_of_swapColumns_apply_eq (by rw [← hEmid']; exact hE₂)
    have hEr₂ : E.second.right = Equiv.swap D.second.left D.first.left D.first.right :=
      eq_swap_of_swapColumns_apply_eq (by rw [← hEmid']; exact hEt₂)
    rw [Equiv.swap_apply_right] at hEl₂
    rw [Equiv.swap_apply_of_ne_of_ne hother D.first.left_ne_right.symm] at hEr₂
    refine Or.inl ⟨hEl₁.trans hEl₂.symm, hEr₂.symm, ?_, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [hEr₁]
      exact hcommon.symm
    · rw [hEr₁, hEl₁, hEr₂]
      exact hrot
    · rw [hEr₁, hEr₂]
      exact D.first.target_eq_swapColumns
    · rw [hEr₁]
    · rw [hEl₁]
  · -- the recut has both its rectangles on the same terminal side column
    have hEmid' : E.middle = x.swapColumns D.second.left D.first.right := by
      rw [hEmid, hDbot₂, GridRectangleBetween.top_def, GridState.swapColumns_eq_swapRows]
    have hxEl₁ : x E.first.left = x D.second.left := by exact hE₁.trans hDbot₂
    have hEl₁ : E.first.left = D.second.left := x.toPerm.injective hxEl₁
    have hxEr₁ : x E.first.right = x D.first.right := by exact hEt₁
    have hEr₁ : E.first.right = D.first.right := x.toPerm.injective hxEr₁
    have hEl₂ : E.second.left = Equiv.swap D.second.left D.first.right D.first.left :=
      eq_swap_of_swapColumns_apply_eq (by rw [← hEmid']; exact hE₂)
    have hEr₂ : E.second.right = Equiv.swap D.second.left D.first.right D.second.left :=
      eq_swap_of_swapColumns_apply_eq (by rw [← hEmid']; exact hEt₂.trans hDbot₂)
    rw [Equiv.swap_apply_of_ne_of_ne hvm.symm D.first.left_ne_right] at hEl₂
    rw [Equiv.swap_apply_left] at hEr₂
    refine Or.inr (Or.inl ⟨hEr₁.trans hEr₂.symm, hEl₂.symm, ?_, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩)
    · rw [hEl₁]
    · rw [hEl₂, hEl₁, hEr₁]
      exact hrot
    · rw [hEl₂, hEr₁]
      exact D.first.target_eq_swapColumns
    · rw [hEr₁]
    · rw [hEl₂]
      exact hcommon.symm

/-- The recut of a counted decomposition whose common column is terminal for its first rectangle
and initial for its second carries the side data describing the original decomposition as its own
recut. As in the previous case the recut shares a side column and its side columns are read off
the rows they occupy. -/
private theorem isRecut_symm_of_right_eq_left {D E : GridRectangleDecomposition x z}
    (hdata : D.IsRecutOfRightEqLeft E) (hone : D.HasOneCommonSide)
    (hDempty₁ : D.first.IsEmpty) (hDempty₂ : D.second.IsEmpty) :
    E.IsRecutOfLeftEqLeft D ∨ E.IsRecutOfRightEqRight D ∨
      E.IsRecutOfLeftEqRight D ∨ E.IsRecutOfRightEqLeft D := by
  obtain ⟨hcommon, hE₁, hE₂, hbranch⟩ := hdata
  have hother : D.first.left ≠ D.second.right := fun hl =>
    D.sideColumns_ne_of_hasOneCommonSide hone
      (by rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hcommon, hl,
        Finset.pair_comm])
  have hvm : D.second.right ≠ D.first.right := by
    rw [hcommon]
    exact D.second.left_ne_right.symm
  have hcol := (D.cyclicOrder_of_isEmpty_of_right_eq_left hcommon hother hDempty₁ hDempty₂).1
  have hDbot₂ : D.second.bottom = x D.first.left := by
    rw [GridRectangleBetween.bottom_def, ← hcommon, D.first.target_apply,
      Equiv.swap_apply_right]
  have hDtop₂ : D.second.top = x D.second.right := by
    rw [GridRectangleBetween.top_def, D.first.target_apply,
      Equiv.swap_apply_of_ne_of_ne hother.symm hvm]
  rcases hbranch with ⟨-, hEmid, hEb₁, hEb₂⟩ | ⟨-, hEmid, hEb₁, hEb₂⟩
  · -- the recut has both its rectangles on the same terminal side column
    have hEmid' : E.middle = x.swapColumns D.first.right D.second.right := by
      rw [hEmid, hDtop₂, GridRectangleBetween.top_def, GridState.swapColumns_eq_swapRows]
    have hxEl₁ : x E.first.left = x D.first.right := by exact hEb₁
    have hEl₁ : E.first.left = D.first.right := x.toPerm.injective hxEl₁
    have hxEr₁ : x E.first.right = x D.second.right := by exact hE₁.trans hDtop₂
    have hEr₁ : E.first.right = D.second.right := x.toPerm.injective hxEr₁
    have hEl₂ : E.second.left = Equiv.swap D.first.right D.second.right D.first.left :=
      eq_swap_of_swapColumns_apply_eq (by rw [← hEmid']; exact hEb₂)
    have hEr₂ : E.second.right = Equiv.swap D.first.right D.second.right D.first.right :=
      eq_swap_of_swapColumns_apply_eq (by rw [← hEmid']; exact hE₂)
    rw [Equiv.swap_apply_of_ne_of_ne D.first.left_ne_right hother] at hEl₂
    rw [Equiv.swap_apply_left] at hEr₂
    refine Or.inr (Or.inl ⟨hEr₁.trans hEr₂.symm, hEl₂.symm, ?_, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩)
    · rw [hEl₁]
      exact hcommon.symm
    · rw [hEl₁, hEl₂, hEr₁]
      exact hcol
    · rw [hEl₂, hEl₁]
      exact D.first.target_eq_swapColumns
    · rw [hEl₁]
    · rw [hEr₁]
  · -- the recut has both its rectangles on the same initial side column
    have hEmid' : E.middle = x.swapColumns D.first.left D.second.right := by
      rw [hEmid, hDtop₂, GridRectangleBetween.bottom_def, GridState.swapColumns_eq_swapRows]
    have hxEl₁ : x E.first.left = x D.first.left := by exact hEb₁
    have hEl₁ : E.first.left = D.first.left := x.toPerm.injective hxEl₁
    have hxEr₁ : x E.first.right = x D.second.right := by exact hE₁.trans hDtop₂
    have hEr₁ : E.first.right = D.second.right := x.toPerm.injective hxEr₁
    have hEl₂ : E.second.left = Equiv.swap D.first.left D.second.right D.second.right :=
      eq_swap_of_swapColumns_apply_eq (by rw [← hEmid']; exact hEb₂.trans hDtop₂)
    have hEr₂ : E.second.right = Equiv.swap D.first.left D.second.right D.first.right :=
      eq_swap_of_swapColumns_apply_eq (by rw [← hEmid']; exact hE₂)
    rw [Equiv.swap_apply_right] at hEl₂
    rw [Equiv.swap_apply_of_ne_of_ne D.first.left_ne_right.symm hvm.symm] at hEr₂
    refine Or.inl ⟨hEl₁.trans hEl₂.symm, hEr₂.symm, hEr₁.symm, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [hEr₂, hEl₁, hEr₁]
      exact hcol
    · rw [hEl₁, hEr₂]
      exact D.first.target_eq_swapColumns
    · rw [hEl₁]
    · rw [hEr₂]
      exact hcommon.symm

/-- If `E` is a recut of a counted two-step decomposition `D` whose rectangles share exactly one
side column, then `D` is a recut of `E`: in each of the four orientations of the common column of
`D`, the recut carries precisely the side data that describes `D` as its recut. -/
theorem IsRecut.symm {G : GridDiagram n} {D E : GridRectangleDecomposition x z}
    (h : D.IsRecut G E) (hone : D.HasOneCommonSide)
    (hfirst : D.first ∈ G.unblockedRectangles x D.middle)
    (hsecond : D.second ∈ G.unblockedRectangles D.middle z) :
    E.IsRecut G D := by
  obtain ⟨hrep, hmid, hEf, hEs, hdata⟩ := h
  have hDempty₁ := G.isEmpty_of_mem_unblockedRectangles hfirst
  have hDempty₂ := G.isEmpty_of_mem_unblockedRectangles hsecond
  refine ⟨hrep.symm, hmid.symm, hfirst, hsecond, ?_⟩
  rcases hdata with hdata | hdata | hdata | hdata
  · exact isRecut_symm_of_left_eq_left hdata hone hDempty₁ hDempty₂
  · exact isRecut_symm_of_right_eq_right hdata hone hDempty₁ hDempty₂
  · exact isRecut_symm_of_left_eq_right hdata hone hDempty₁ hDempty₂
  · exact isRecut_symm_of_right_eq_left hdata hone hDempty₁ hDempty₂

/-! ### The recut as an involution -/

/-- The two decompositions of a recut pair repartition the same domain. -/
theorem IsRecut.isRepartition {G : GridDiagram n} {D E : GridRectangleDecomposition x z}
    (h : D.IsRecut G E) : D.IsRepartition E := h.1

/-- A recut passes through a different intermediate grid state. -/
theorem IsRecut.middle_ne {G : GridDiagram n} {D E : GridRectangleDecomposition x z}
    (h : D.IsRecut G E) : E.middle ≠ D.middle := h.2.1

/-- The unblocked differential counts the first rectangle of a recut. -/
theorem IsRecut.mem_unblockedRectangles_first {G : GridDiagram n}
    {D E : GridRectangleDecomposition x z} (h : D.IsRecut G E) :
    E.first ∈ G.unblockedRectangles x E.middle := h.2.2.1

/-- The unblocked differential counts the second rectangle of a recut. -/
theorem IsRecut.mem_unblockedRectangles_second {G : GridDiagram n}
    {D E : GridRectangleDecomposition x z} (h : D.IsRecut G E) :
    E.second ∈ G.unblockedRectangles E.middle z := h.2.2.2.1

/-- A nondiagonal decomposition admitting a recut has exactly one common side column: the side
data of that recut records which of the four orientations the decomposition's own common column
has. -/
theorem hasOneCommonSide_of_isRecut {G : GridDiagram n} {D E : GridRectangleDecomposition x z}
    (h : E.IsRecut G D) (hzx : z ≠ x) : E.HasOneCommonSide := by
  obtain ⟨-, -, -, -, hdata⟩ := h
  rcases hdata with ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
  · exact E.hasOneCommonSide_of_mem_commonSideColumns (c := E.first.left) (by simp [hc]) hzx
  · exact E.hasOneCommonSide_of_mem_commonSideColumns (c := E.first.right) (by simp [hc]) hzx
  · exact E.hasOneCommonSide_of_mem_commonSideColumns (c := E.first.left) (by simp [hc]) hzx
  · exact E.hasOneCommonSide_of_mem_commonSideColumns (c := E.first.right) (by simp [hc]) hzx

/-- The recut of a two-step decomposition counted by the unblocked differential whose two
rectangles share exactly one side column. -/
noncomputable def recut (G : GridDiagram n) (D : GridRectangleDecomposition x z)
    (hone : D.HasOneCommonSide) (hfirst : D.first ∈ G.unblockedRectangles x D.middle)
    (hsecond : D.second ∈ G.unblockedRectangles D.middle z) :
    GridRectangleDecomposition x z :=
  (D.existsUnique_isRecut G hone hfirst hsecond).choose

/-- The recut of a decomposition is a recut of it. -/
theorem isRecut_recut (G : GridDiagram n) (D : GridRectangleDecomposition x z)
    (hone : D.HasOneCommonSide) (hfirst : D.first ∈ G.unblockedRectangles x D.middle)
    (hsecond : D.second ∈ G.unblockedRectangles D.middle z) :
    D.IsRecut G (D.recut G hone hfirst hsecond) :=
  (D.existsUnique_isRecut G hone hfirst hsecond).choose_spec.1

/-- The recut of a decomposition again shares exactly one side column. -/
theorem hasOneCommonSide_recut (G : GridDiagram n) (D : GridRectangleDecomposition x z)
    (hone : D.HasOneCommonSide) (hfirst : D.first ∈ G.unblockedRectangles x D.middle)
    (hsecond : D.second ∈ G.unblockedRectangles D.middle z) :
    (D.recut G hone hfirst hsecond).HasOneCommonSide :=
  hasOneCommonSide_of_isRecut
    ((D.isRecut_recut G hone hfirst hsecond).symm hone hfirst hsecond)
    (D.target_ne_source_of_hasOneCommonSide hone)

/-- The recut of a decomposition is different from it: the two pass through different
intermediate grid states. -/
theorem recut_ne (G : GridDiagram n) (D : GridRectangleDecomposition x z)
    (hone : D.HasOneCommonSide) (hfirst : D.first ∈ G.unblockedRectangles x D.middle)
    (hsecond : D.second ∈ G.unblockedRectangles D.middle z) :
    D.recut G hone hfirst hsecond ≠ D := fun h =>
  (D.isRecut_recut G hone hfirst hsecond).middle_ne (congrArg GridRectangleDecomposition.middle h)

/-- Recutting is an involution on the two-step decompositions counted by the unblocked
differential whose two rectangles share exactly one side column. -/
@[simp] theorem recut_recut (G : GridDiagram n) (D : GridRectangleDecomposition x z)
    (hone : D.HasOneCommonSide) (hfirst : D.first ∈ G.unblockedRectangles x D.middle)
    (hsecond : D.second ∈ G.unblockedRectangles D.middle z) :
    (D.recut G hone hfirst hsecond).recut G
      (D.hasOneCommonSide_recut G hone hfirst hsecond)
      ((D.isRecut_recut G hone hfirst hsecond).mem_unblockedRectangles_first)
      ((D.isRecut_recut G hone hfirst hsecond).mem_unblockedRectangles_second) = D :=
  ((D.recut G hone hfirst hsecond).existsUnique_isRecut G
      (D.hasOneCommonSide_recut G hone hfirst hsecond)
      ((D.isRecut_recut G hone hfirst hsecond).mem_unblockedRectangles_first)
      ((D.isRecut_recut G hone hfirst hsecond).mem_unblockedRectangles_second)).unique
    ((D.recut G hone hfirst hsecond).isRecut_recut G
      (D.hasOneCommonSide_recut G hone hfirst hsecond)
      ((D.isRecut_recut G hone hfirst hsecond).mem_unblockedRectangles_first)
      ((D.isRecut_recut G hone hfirst hsecond).mem_unblockedRectangles_second))
    ((D.isRecut_recut G hone hfirst hsecond).symm hone hfirst hsecond)

end GridRectangleDecomposition

end TauCeti
