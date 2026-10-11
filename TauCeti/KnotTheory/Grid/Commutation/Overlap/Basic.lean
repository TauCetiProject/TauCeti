/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing

/-!
# Overlapping domains in the grid commutation map

The chain-map equation for a column commutation pairs a rectangle followed by a pentagon with a
pentagon followed by a rectangle. When the two domains share exactly one vertical side, forgetting
the pentagon's turn point produces the same L-shaped rectangle domain that occurs in the proof
that the grid differential squares to zero. This file begins transporting that generic recut back
to the commutation setting.

When the rectangle and pentagon share their initial side, the generic recut has its first
rectangle terminate on the replaced grid line. The cyclic row order forced by emptiness also
shows that this new terminal side still contains the original turn point. Thus the first recut
rectangle canonically promotes to a pentagon, producing a pentagon--rectangle decomposition.
Forgetting the turn point recovers exactly the generic recut, so its emptiness and covered-square
repartition data remain available without duplicating the rectangle geometry.

This module treats the common-initial-side orientation and preserves the underlying rectangle
repartition and its rectangle weights. It also records the two possible cuts in the
common-terminal-side orientation: in that orientation exactly one recut rectangle ends on the
replaced grid line, and the branch data below identifies which one from the column geometry
(the turn-row transports building on it live in `Overlap/TurnRow.lean`).

## Main results

* `TauCeti.GridPentagonRectangleDecomposition.isEmpty_pentagon_of_isRecut` and the
  corresponding rectangle--pentagon lemmas: recut emptiness and repartition identities
  transfer to either typed decomposition shape after forgetting the turn row.
* `TauCeti.GridRectanglePentagonDecomposition.recutLeftEqLeft`: promote the one-common-side
  rectangle recut to a pentagon--rectangle decomposition when the common side is initial for both
  original domains.
* `TauCeti.GridRectanglePentagonDecomposition.recutLeftEqLeft_toRectangleDecomposition`:
  forgetting the promoted turn point gives the generic recut.
* `TauCeti.GridRectanglePentagonDecomposition.isRecut_recutLeftEqLeft`: the promoted
  decomposition retains the generic recut relation, including its covered-square repartition.
* `TauCeti.GridRectanglePentagonDecomposition.OMonomial_mul_OMonomial_recutLeftEqLeft`: the
  product of the two underlying rectangle weights is preserved.
* `TauCeti.GridRectanglePentagonDecomposition.hasOneCommonSide_of_right_eq_right`: a common
  terminal side with distinct initial sides is the only common side column.
* `TauCeti.GridRectanglePentagonDecomposition.isRecutOfRightEqRight_recut`: the generic recut
  is classified by the common-terminal-side orientation of the original rectangle and pentagon.
* `TauCeti.GridRectanglePentagonDecomposition.recut_first_or_second_right_eq_pentagon_right`:
  exactly one of the two new rectangles has the original pentagon's terminal side.
* `TauCeti.GridRectanglePentagonDecomposition.recutOfIsEmpty`: the shared underlying
  rectangle recut with the emptiness hypotheses discharged once, used by the terminal-side
  overlap results (branch determination, turn-row transport, and promotion) and the
  X-avoidance results instead of repeating the construction.
* `TauCeti.GridRectanglePentagonDecomposition.recutOfIsEmpty_eq_recut`: the shared recut
  identified with the underlying rectangle decomposition's recut, for consumers that need the
  definitional unfolding.
* `TauCeti.GridRectanglePentagonDecomposition.isRecut_recutOfIsEmpty`: the shared recut
  retains the recut relation after forgetting the turn row.
* `TauCeti.GridRectanglePentagonDecomposition.first_recut_branch_data_of_right_eq_right`:
  when the first recut rectangle carries the pentagon's terminal side, the recut branch is
  forced, fixing the column geometry of the shared recut.
* `TauCeti.GridRectanglePentagonDecomposition.second_recut_branch_data_of_right_eq_right`:
  when the second recut rectangle carries the pentagon's terminal side, the recut branch is
  forced, fixing the column geometry of the shared recut.
* `TauCeti.GridRectanglePentagonDecomposition.recut_first_bottom_eq_pentagon_bottom_of_branch1`:
  in the first recut branch, the recut's first rectangle's bottom row equals the original
  pentagon's bottom row.
* `TauCeti.GridRectanglePentagonDecomposition.recut_rectangle_branch_data_of_left_eq_left`:
  the promoted recut rectangle's sides and rows in the two common-initial-side branches.

These are the recut/repartition combinatorics and weight transfers for the pentagon-counting
commutation chain map.

## References

These are two overlap orientations in the pentagon--rectangle juxtaposition argument of
Ozsvath--Stipsicz--Szabo, *Grid Homology for Knots and Links*, Section 5.1.
-/

public section

namespace TauCeti

namespace GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The turn row lies outside the following rectangle when two empty pieces share their
initial side and have distinct terminal sides. -/
theorem turn_notMem_cIco_rectangle_of_left_eq_left
    (E : GridPentagonRectangleDecomposition a s x z)
    (hcommon : E.pentagon.left = E.rectangle.left)
    (hother : E.pentagon.right ≠ E.rectangle.right)
    (hp : E.pentagon.IsEmpty) (hr : E.rectangle.IsEmpty) :
    s ∉ Grid.cIco E.rectangle.bottom E.rectangle.top := by
  have hrow := (E.toRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left
    (by simpa using hcommon) (by simpa using hother)
    (E.underlying_first_isEmpty hp) (E.underlying_second_isEmpty hr)).2
  have hb := E.toRectangleDecomposition.second_bottom_eq_first_top_of_left_eq_left
    (by simpa using hcommon)
  simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def,
    toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
    toRectangleDecomposition_second_left, toRectangleDecomposition_second_right,
    toRectangleDecomposition_middle] at hrow hb
  rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hb]
  exact fun hs => Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hrow)
    E.pentagon.turn_mem hs

/-- A recut into a pentagon followed by a rectangle has an empty pentagon. -/
theorem isEmpty_pentagon_of_isRecut (E : GridPentagonRectangleDecomposition a s x z)
    {D : GridRectangleDecomposition x z}
    (h : D.IsRecut E.toRectangleDecomposition) :
    E.pentagon.IsEmpty := by
  simpa only [toRectangleDecomposition_first_toGridRectangle,
    GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] using h.isEmpty_first

/-- A recut into a pentagon followed by a rectangle has an empty rectangle. -/
theorem isEmpty_rectangle_of_isRecut (E : GridPentagonRectangleDecomposition a s x z)
    {D : GridRectangleDecomposition x z}
    (h : D.IsRecut E.toRectangleDecomposition) :
    E.rectangle.IsEmpty := by
  simpa only [toRectangleDecomposition_middle, toRectangleDecomposition_second_toGridRectangle,
    GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] using h.isEmpty_second

/-- The underlying rectangles of a repartition into a pentagon and rectangle cover the
original region. -/
theorem coveredSquares_union_of_isRepartition (E : GridPentagonRectangleDecomposition a s x z)
    (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.toRectangleDecomposition.IsRepartition E.toRectangleDecomposition) :
    E.pentagon.toGridRectangle.coveredSquares ∪ E.rectangle.toGridRectangle.coveredSquares =
      D.rectangle.toGridRectangle.coveredSquares ∪ D.pentagon.toGridRectangle.coveredSquares := by
  simpa only [toRectangleDecomposition_first_toGridRectangle,
    toRectangleDecomposition_second_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_second_toGridRectangle] using
      h.coveredSquares_union_eq

/-- Repartition into a pentagon and rectangle preserves the product of the underlying
rectangle `O`-monomials. -/
theorem OMonomial_mul_OMonomial_of_isRepartition
    (E : GridPentagonRectangleDecomposition a s x z)
    (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.toRectangleDecomposition.IsRepartition E.toRectangleDecomposition)
    (G : GridDiagram n) (R : Type*) [CommSemiring R] :
    G.OMonomial R E.pentagon.toGridRectangle * G.OMonomial R E.rectangle.toGridRectangle =
      G.OMonomial R D.rectangle.toGridRectangle * G.OMonomial R D.pentagon.toGridRectangle := by
  simpa only [toRectangleDecomposition_first_toGridRectangle,
    toRectangleDecomposition_second_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_second_toGridRectangle] using
      h.OMonomial_mul_OMonomial G R

end GridPentagonRectangleDecomposition

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- A recut into a rectangle followed by a pentagon has an empty rectangle. -/
theorem isEmpty_rectangle_of_isRecut (E : GridRectanglePentagonDecomposition a s x z)
    {D : GridRectangleDecomposition x z}
    (h : D.IsRecut E.toRectangleDecomposition) :
    E.rectangle.IsEmpty := by
  simpa only [toRectangleDecomposition_middle, toRectangleDecomposition_first_toGridRectangle,
    GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] using h.isEmpty_first

/-- A recut into a rectangle followed by a pentagon has an empty pentagon. -/
theorem isEmpty_pentagon_of_isRecut (E : GridRectanglePentagonDecomposition a s x z)
    {D : GridRectangleDecomposition x z}
    (h : D.IsRecut E.toRectangleDecomposition) :
    E.pentagon.IsEmpty := by
  simpa only [toRectangleDecomposition_middle, toRectangleDecomposition_second_toGridRectangle,
    GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor] using h.isEmpty_second

/-- The underlying rectangles of a repartition into a rectangle and pentagon cover the
original region. -/
theorem coveredSquares_union_of_isRepartition
    (E D : GridRectanglePentagonDecomposition a s x z)
    (h : D.toRectangleDecomposition.IsRepartition E.toRectangleDecomposition) :
    E.rectangle.toGridRectangle.coveredSquares ∪ E.pentagon.toGridRectangle.coveredSquares =
      D.rectangle.toGridRectangle.coveredSquares ∪ D.pentagon.toGridRectangle.coveredSquares := by
  simpa only [toRectangleDecomposition_first_toGridRectangle,
    toRectangleDecomposition_second_toGridRectangle] using h.coveredSquares_union_eq

/-- Repartition into a rectangle and pentagon preserves the product of the underlying
rectangle `O`-monomials. -/
theorem OMonomial_mul_OMonomial_of_isRepartition
    (E D : GridRectanglePentagonDecomposition a s x z)
    (h : D.toRectangleDecomposition.IsRepartition E.toRectangleDecomposition)
    (G : GridDiagram n) (R : Type*) [CommSemiring R] :
    G.OMonomial R E.rectangle.toGridRectangle * G.OMonomial R E.pentagon.toGridRectangle =
      G.OMonomial R D.rectangle.toGridRectangle * G.OMonomial R D.pentagon.toGridRectangle := by
  simpa only [toRectangleDecomposition_first_toGridRectangle,
    toRectangleDecomposition_second_toGridRectangle] using h.OMonomial_mul_OMonomial G R

end GridRectanglePentagonDecomposition

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

private theorem right_ne_right_of_left_eq_left
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide) :
    D.toRectangleDecomposition.first.right ≠ D.toRectangleDecomposition.second.right := by
  have hcommon' : D.toRectangleDecomposition.first.left =
      D.toRectangleDecomposition.second.left := by
    simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_second_left] using
      hcommon
  intro hright
  apply D.toRectangleDecomposition.sideColumns_ne_of_hasOneCommonSide hone
  rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hcommon', hright]

/-- Emptiness of the two typed domains remains emptiness after forgetting the pentagon turn row. -/
private theorem isRecutOfLeftEqLeft_recut
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    D.toRectangleDecomposition.IsRecutOfLeftEqLeft
      (D.toRectangleDecomposition.recut hone
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)) :=
  D.toRectangleDecomposition.isRecutOfLeftEqLeft_recut
    (by
      simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_second_left] using
        hcommon)
    hone _ _

/-- In the common-initial-side overlap, the first rectangle of the recut terminates on the
replaced grid line and hence has the required terminal side of a commutation pentagon. -/
theorem recut_first_right_of_left_eq_left
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    ((D.toRectangleDecomposition.recut hone
      (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)).first).right =
        finRotate n a := by
  have hdata := D.isRecutOfLeftEqLeft_recut hcommon hone hrectangle hpentagon
  calc
    _ = D.toRectangleDecomposition.second.right := hdata.recut_sides.1
    _ = D.pentagon.right := toRectangleDecomposition_second_right D
    _ = finRotate n a := D.pentagon.right_eq

/-- In the common-initial-side overlap, the first rectangle of the recut still contains the
pentagon's turn row on its terminal side. -/
theorem turn_mem_recut_first_of_left_eq_left
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    s ∈ Grid.cIco
      (D.toRectangleDecomposition.recut hone
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)).first.bottom
      (D.toRectangleDecomposition.recut hone
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)).first.top := by
  -- Work in the forgotten rectangle decomposition to use its emptiness and cyclic-order facts.
  have hempty : D.toRectangleDecomposition.first.IsEmpty ∧
      D.toRectangleDecomposition.second.IsEmpty :=
    ⟨by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle,
      by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon⟩
  have hcommon' : D.toRectangleDecomposition.first.left =
      D.toRectangleDecomposition.second.left := by
    simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_second_left] using
      hcommon
  have hright := D.right_ne_right_of_left_eq_left hcommon hone
  have hrow := (D.toRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left
    hcommon' hright hempty.1 hempty.2).2
  -- Convert the cyclic row order and pentagon turn interval to the original corner rows.
  have hfirstBottom : D.toRectangleDecomposition.first.bottom =
      x D.toRectangleDecomposition.first.left :=
    D.toRectangleDecomposition.first.bottom_def
  have hfirstTop : D.toRectangleDecomposition.first.top =
      x D.toRectangleDecomposition.first.right :=
    D.toRectangleDecomposition.first.top_def
  have hsecondBottom : D.toRectangleDecomposition.second.bottom =
      x D.toRectangleDecomposition.first.right := by
    rw [GridRectangleBetween.bottom_def, ← hcommon',
      D.toRectangleDecomposition.first.map_left]
  have hsecondRight_ne_firstLeft : D.toRectangleDecomposition.second.right ≠
      D.toRectangleDecomposition.first.left := by
    intro h
    exact D.toRectangleDecomposition.second.left_ne_right
      (hcommon'.symm.trans h.symm)
  have hsecondTop : D.toRectangleDecomposition.second.top =
      x D.toRectangleDecomposition.second.right := by
    rw [GridRectangleBetween.top_def]
    exact D.toRectangleDecomposition.first.map_of_ne _ hsecondRight_ne_firstLeft hright.symm
  have hturn : s ∈ Grid.cIco D.toRectangleDecomposition.second.bottom
      D.toRectangleDecomposition.second.top := by
    simpa only [toRectangleDecomposition_middle, GridRectangleBetween.bottom_def,
      GridRectangleBetween.top_def,
      toRectangleDecomposition_second_left, toRectangleDecomposition_second_right] using
      D.pentagon.turn_mem
  have hdata := D.isRecutOfLeftEqLeft_recut hcommon hone hrectangle hpentagon
  -- The first recut branch preserves the full interval; the second splits it at the middle row.
  have hrecutRight := hdata.recut_sides.1
  have hbranch := hdata.recut_branch
  rcases hbranch with ⟨-, -, hrecutLeft, -⟩ | ⟨-, -, hrecutLeft, -⟩
  · rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hrecutLeft,
      hrecutRight, ← hsecondBottom, ← hsecondTop]
    exact hturn
  · have hrow' : x D.toRectangleDecomposition.first.right ∈
        Grid.cIoo (x D.toRectangleDecomposition.first.left)
          (x D.toRectangleDecomposition.second.right) := by
      simpa only [hfirstBottom, hfirstTop, hsecondTop] using hrow
    have hturn' : s ∈ Grid.cIco (x D.toRectangleDecomposition.first.right)
        (x D.toRectangleDecomposition.second.right) := by
      simpa only [hsecondBottom, hsecondTop] using hturn
    rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hrecutLeft,
      hrecutRight, ← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow']
    exact Finset.mem_union.mpr (Or.inr hturn')

/-- Recut a rectangle followed by a pentagon when their unique common side is initial for both,
then promote the first new rectangle to a pentagon using the transported turn point. -/
noncomputable def recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    GridPentagonRectangleDecomposition a s x z := by
  have hempty : D.toRectangleDecomposition.first.IsEmpty ∧
      D.toRectangleDecomposition.second.IsEmpty :=
    ⟨by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle,
      by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon⟩
  let E := D.toRectangleDecomposition.recut hone hempty.1 hempty.2
  exact {
    middle := E.middle
    pentagon := GridPentagonBetween.ofRightEq E.first
      (D.recut_first_right_of_left_eq_left hcommon hone hrectangle hpentagon)
      (D.turn_mem_recut_first_of_left_eq_left hcommon hone hrectangle hpentagon)
    rectangle := E.second }

/-- Forgetting the turn point after the common-initial-side overlap construction recovers the
generic one-common-side rectangle recut. -/
@[simp]
theorem recutLeftEqLeft_toRectangleDecomposition
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).toRectangleDecomposition =
      D.toRectangleDecomposition.recut hone
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon) := by
  have hempty : D.toRectangleDecomposition.first.IsEmpty ∧
      D.toRectangleDecomposition.second.IsEmpty :=
    ⟨by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle,
      by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon⟩
  let E := D.toRectangleDecomposition.recut hone hempty.1 hempty.2
  have hpentagon := GridPentagonBetween.ofRightEq_toGridRectangleBetween E.first
    (D.recut_first_right_of_left_eq_left hcommon hone hrectangle hpentagon)
    (D.turn_mem_recut_first_of_left_eq_left hcommon hone hrectangle hpentagon)
  apply GridRectangleDecomposition.ext
  · simpa only [recutLeftEqLeft,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left, E] using
        congrArg GridRectangleBetween.left hpentagon
  · simpa only [recutLeftEqLeft,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right, E] using
        congrArg GridRectangleBetween.right hpentagon
  · simp only [recutLeftEqLeft,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left]
  · simp only [recutLeftEqLeft,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right]

/-- The promoted pentagon--rectangle decomposition carries the generic recut relation. In
particular, the two new underlying rectangles are empty and repartition the same covered squares
as the original rectangle and underlying rectangle of the pentagon. -/
theorem isRecut_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    D.toRectangleDecomposition.IsRecut
      (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).toRectangleDecomposition := by
  rw [D.recutLeftEqLeft_toRectangleDecomposition hcommon hone hrectangle hpentagon]
  exact D.toRectangleDecomposition.isRecut_recut hone
    (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
    (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)

/-- The promoted pentagon in the overlap recut is empty. -/
@[simp]
theorem isEmpty_pentagon_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.IsEmpty := by
  have h := D.isRecut_recutLeftEqLeft hcommon hone hrectangle hpentagon
  exact (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).isEmpty_pentagon_of_isRecut h

/-- The rectangle in the overlap recut is empty. -/
@[simp]
theorem isEmpty_rectangle_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).rectangle.IsEmpty := by
  have h := D.isRecut_recutLeftEqLeft hcommon hone hrectangle hpentagon
  exact (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).isEmpty_rectangle_of_isRecut h

/-- The underlying rectangles of the promoted overlap recut cover the same squares as the
original rectangle and the rectangle underlying the original pentagon. -/
theorem coveredSquares_union_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.recutLeftEqLeft hcommon hone hrectangle
          hpentagon).pentagon.toGridRectangle.coveredSquares ∪
    (D.recutLeftEqLeft hcommon hone hrectangle
          hpentagon).rectangle.toGridRectangle.coveredSquares =
      D.rectangle.toGridRectangle.coveredSquares ∪ D.pentagon.toGridRectangle.coveredSquares := by
  have h := D.isRecut_recutLeftEqLeft hcommon hone hrectangle hpentagon
  exact
    (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).coveredSquares_union_of_isRepartition D
      h.isRepartition

/-- The promoted overlap recut preserves the product of the `O`-monomials of its two underlying
rectangles. This is the rectangle-weight consequence of the generic covered-square repartition;
the correction from an underlying rectangle to the commutation pentagon weight is separate. -/
theorem OMonomial_mul_OMonomial_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (G : GridDiagram n) (R : Type*) [CommSemiring R] :
    G.OMonomial R
          (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.toGridRectangle *
        G.OMonomial R
          (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).rectangle.toGridRectangle =
      G.OMonomial R D.rectangle.toGridRectangle *
        G.OMonomial R D.pentagon.toGridRectangle := by
  have h := D.isRecut_recutLeftEqLeft hcommon hone hrectangle hpentagon
  exact
    (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).OMonomial_mul_OMonomial_of_isRepartition D
      h.isRepartition G R

end GridRectanglePentagonDecomposition

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- A rectangle and pentagon sharing their terminal side have exactly one common side column when
their initial sides differ. -/
theorem hasOneCommonSide_of_right_eq_right (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hother : D.rectangle.left ≠ D.pentagon.left) :
    D.toRectangleDecomposition.HasOneCommonSide := by
  apply D.toRectangleDecomposition.hasOneCommonSide_iff_existsUnique.mpr
  refine ⟨D.pentagon.right, ?_, ?_⟩
  · simp [GridRectangleBetween.mem_sideColumns, hcommon]
  · intro c hc
    simp only [GridRectangleBetween.mem_sideColumns, toRectangleDecomposition_first_left,
      toRectangleDecomposition_first_right, toRectangleDecomposition_second_left,
      toRectangleDecomposition_second_right, hcommon] at hc
    grind

/-- When the rectangle and pentagon share their terminal side, their underlying rectangle
decomposition's recut is classified by the original common-terminal-side orientation. -/
theorem isRecutOfRightEqRight_recut
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    D.toRectangleDecomposition.IsRecutOfRightEqRight
      (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)) := by
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  exact D.toRectangleDecomposition.isRecutOfRightEqRight_recut hcommon' hone
    (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
    (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)

/-- In a common-terminal-side overlap, the generic recut places the terminal side of the
original pentagon on one of its two new rectangles. The alternatives are disjoint because those
rectangles have different terminal sides. -/
theorem recut_first_or_second_right_eq_pentagon_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    let E := D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)
    (E.first.right = D.pentagon.right ∧ E.second.right ≠ D.pentagon.right) ∨
      (E.first.right ≠ D.pentagon.right ∧ E.second.right = D.pentagon.right) := by
  let E := D.toRectangleDecomposition.recut hone
    (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
    (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)
  dsimp only
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  have hbranches :
      (E.first.right = D.toRectangleDecomposition.second.right ∧
        E.second.right ≠ D.toRectangleDecomposition.second.right) ∨
        (E.first.right ≠ D.toRectangleDecomposition.second.right ∧
          E.second.right = D.toRectangleDecomposition.second.right) := by
    rcases hdata.recut_branch with ⟨-, -, hfirst, hsecond⟩ | ⟨-, -, hfirst, hsecond⟩
    · right
      refine ⟨?_, hsecond.trans hcommon'⟩
      intro h
      rw [hfirst, ← hcommon'] at h
      exact D.toRectangleDecomposition.first.left_ne_right h
    · left
      refine ⟨hfirst.trans hcommon', ?_⟩
      intro h
      rw [hsecond] at h
      exact D.toRectangleDecomposition.second.left_ne_right h
  simpa only [D.toRectangleDecomposition_second_right] using hbranches

/-- The shared recut construction for overlap arguments: `D.toRectangleDecomposition`
recut along its common side, with the rectangle emptiness supplied from `hrectangle` and the
pentagon emptiness from `hpentagon`. The terminal-side overlap results (branch determination,
turn-row transport, and promotion) and the X-avoidance results work with this single
construction rather than repeating it. -/
noncomputable def recutOfIsEmpty
    (D : GridRectanglePentagonDecomposition a s x z)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    GridRectangleDecomposition x z :=
  D.toRectangleDecomposition.recut hone
    (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
    (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using
      hpentagon)

/-- The shared recut unfolds to the underlying rectangle decomposition's recut along its
common side. This is the private `rfl` core of `recutOfIsEmpty_eq_recut`: since
`recutOfIsEmpty` is not `@[expose]`d, an exported proof may not unfold its body, so the
exported characterization below applies this private unfolding instead. -/
private theorem recutOfIsEmpty_eq_recut_aux
    (D : GridRectanglePentagonDecomposition a s x z)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    D.recutOfIsEmpty hone hrectangle hpentagon = D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon) := rfl

/-- The shared recut is the underlying rectangle decomposition's recut along its common side.
Consumers needing the definitional unfolding rewrite with this instead. -/
theorem recutOfIsEmpty_eq_recut
    (D : GridRectanglePentagonDecomposition a s x z)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    D.recutOfIsEmpty hone hrectangle hpentagon = D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon) :=
  D.recutOfIsEmpty_eq_recut_aux hone hrectangle hpentagon

/-- The shared recut of two empty typed domains is a recut of their underlying rectangles. -/
theorem isRecut_recutOfIsEmpty
    (D : GridRectanglePentagonDecomposition a s x z)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    D.toRectangleDecomposition.IsRecut
      (D.recutOfIsEmpty hone hrectangle hpentagon) := by
  rw [D.recutOfIsEmpty_eq_recut hone hrectangle hpentagon]
  exact D.toRectangleDecomposition.isRecut_recut hone _ _

/-- The promoted rectangle's side data in both common-initial-side recut branches.
In the second branch its middle state and row endpoints also agree with the indicated
column swap and the original rectangle. -/
theorem recut_rectangle_branch_data_of_left_eq_left
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    let E := D.recutLeftEqLeft hcommon hone hrectangle hpentagon
    (D.rectangle.right ∈ Grid.cIoo D.rectangle.left (finRotate n a) ∧
      E.rectangle.left = D.rectangle.left ∧ E.rectangle.right = D.rectangle.right) ∨
    (finRotate n a ∈ Grid.cIoo D.rectangle.left D.rectangle.right ∧
      E.rectangle.left = finRotate n a ∧ E.rectangle.right = D.rectangle.right ∧
      E.middle = x.swapColumns D.rectangle.left (finRotate n a) ∧
      E.rectangle.bottom = D.rectangle.bottom ∧ E.rectangle.top = D.rectangle.top) := by
  let E := D.recutLeftEqLeft hcommon hone hrectangle hpentagon
  -- The theorem's `let E` and this local `E` are definitionally the same recut.
  change (D.rectangle.right ∈ Grid.cIoo D.rectangle.left (finRotate n a) ∧
      E.rectangle.left = D.rectangle.left ∧ E.rectangle.right = D.rectangle.right) ∨
    (finRotate n a ∈ Grid.cIoo D.rectangle.left D.rectangle.right ∧
      E.rectangle.left = finRotate n a ∧ E.rectangle.right = D.rectangle.right ∧
      E.middle = x.swapColumns D.rectangle.left (finRotate n a) ∧
      E.rectangle.bottom = D.rectangle.bottom ∧ E.rectangle.top = D.rectangle.top)
  have hE : E.toRectangleDecomposition = D.recutOfIsEmpty hone hrectangle hpentagon := by
    simpa only [E, D.recutOfIsEmpty_eq_recut] using
      D.recutLeftEqLeft_toRectangleDecomposition hcommon hone hrectangle hpentagon
  have hdata : D.toRectangleDecomposition.IsRecutOfLeftEqLeft
      (D.recutOfIsEmpty hone hrectangle hpentagon) := by
    rw [D.recutOfIsEmpty_eq_recut]
    exact D.toRectangleDecomposition.isRecutOfLeftEqLeft_recut
      (by simpa only [toRectangleDecomposition_first_left,
        toRectangleDecomposition_second_left] using hcommon) hone _ _
  have hEright : E.rectangle.right = D.rectangle.right := by
    have h := hdata.recut_sides.2
    rw [← hE] at h
    simpa only [toRectangleDecomposition_first_right,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right] using h
  rcases hdata.recut_branch with ⟨hcol, _, _, hsecondleft⟩ |
    ⟨hcol, hmiddle, _, hsecondleft⟩
  · have hEleft : E.rectangle.left = D.rectangle.left := by
      rw [← hE] at hsecondleft
      simpa only [toRectangleDecomposition_first_left,
        GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left] using hsecondleft
    have hcol' : D.rectangle.right ∈
        Grid.cIoo D.rectangle.left (finRotate n a) := by
      simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
        toRectangleDecomposition_second_right, D.pentagon.right_eq] using hcol
    exact Or.inl ⟨hcol', hEleft, hEright⟩
  · have hEleft : E.rectangle.left = finRotate n a := by
      rw [← hE] at hsecondleft
      simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left,
        toRectangleDecomposition_second_right, D.pentagon.right_eq] using hsecondleft
    have hcol' : finRotate n a ∈
        Grid.cIoo D.rectangle.left D.rectangle.right := by
      simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
        toRectangleDecomposition_second_right, D.pentagon.right_eq] using hcol
    have hEmiddle : E.middle = x.swapColumns D.rectangle.left (finRotate n a) := by
      rw [← hE] at hmiddle
      simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_middle,
        toRectangleDecomposition_first_left, toRectangleDecomposition_second_right,
        D.pentagon.right_eq] using hmiddle
    have hEbottom : E.rectangle.bottom = D.rectangle.bottom := by
      rw [GridRectangleBetween.bottom_def, hEleft, hEmiddle,
        GridState.swapColumns_apply, Equiv.swap_apply_right,
        ← GridRectangleBetween.bottom_def]
    have hEtop : E.rectangle.top = D.rectangle.top := by
      rw [GridRectangleBetween.top_def, hEright, hEmiddle,
        GridState.swapColumns_apply,
        Equiv.swap_apply_of_ne_of_ne D.rectangle.left_ne_right.symm
          (Grid.ne_right_of_mem_cIoo hcol').symm,
        ← GridRectangleBetween.top_def]
    exact Or.inr ⟨hcol', hEleft, hEright, hEmiddle, hEbottom, hEtop⟩

/-- Common setup for the terminal-side branch determination: the pentagon's terminal side
is the common right side of the forgotten rectangle decomposition. -/
private theorem terminal_side_common_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right) :
    D.toRectangleDecomposition.first.right = D.toRectangleDecomposition.second.right ∧
      D.pentagon.right = D.toRectangleDecomposition.first.right := by
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  refine ⟨hcommon', ?_⟩
  rw [← toRectangleDecomposition_second_right D, ← hcommon']

/-- If the first recut rectangle carries the pentagon's terminal side, the recut branch is
forced: the first recut rectangle spans from the original second rectangle's left side to
the original first rectangle's right side, and the original second rectangle's left side
lies in the original first rectangle's open column interval. -/
theorem first_recut_branch_data_of_right_eq_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right = D.pentagon.right) :
    D.toRectangleDecomposition.second.left ∈
        Grid.cIoo D.toRectangleDecomposition.first.left
          D.toRectangleDecomposition.first.right ∧
      (D.recutOfIsEmpty hone hrectangle hpentagon).first.right =
        D.toRectangleDecomposition.first.right ∧
      (D.recutOfIsEmpty hone hrectangle hpentagon).first.left =
        D.toRectangleDecomposition.second.left := by
  obtain ⟨hcommon', hpen_right⟩ := D.terminal_side_common_right hcommon
  -- View the branch data as data about the shared recut, via the characteristic
  -- identification `recutOfIsEmpty_eq_recut` (proof irrelevance of the emptiness arguments).
  have hdata : D.toRectangleDecomposition.IsRecutOfRightEqRight
      (D.recutOfIsEmpty hone hrectangle hpentagon) := by
    rw [D.recutOfIsEmpty_eq_recut]
    exact D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  have hbranch := hdata.recut_branch
  rcases hbranch with ⟨-, -, hEfirst, -⟩ | ⟨hcol, -, hEfirstB, -⟩
  · -- First branch: E.first.right = D.first.left, so D.first.left = D.pentagon.right
    -- = D.first.right, contradicting left_ne_right.
    exfalso
    rw [hEfirst, hpen_right] at hfirst
    exact D.toRectangleDecomposition.first.left_ne_right hfirst
  · exact ⟨hcol, hEfirstB, hdata.recut_sides.1⟩

/-- If the second recut rectangle carries the pentagon's terminal side, the recut branch is
forced: the second recut rectangle spans from the original first rectangle's left side to
the original first rectangle's right side with the column-swapped middle state, and the
original first rectangle's left side lies in the original second rectangle's open column
interval. -/
theorem second_recut_branch_data_of_right_eq_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right = D.pentagon.right) :
    D.toRectangleDecomposition.first.left ∈
        Grid.cIoo D.toRectangleDecomposition.second.left
          D.toRectangleDecomposition.first.right ∧
      (D.recutOfIsEmpty hone hrectangle hpentagon).second.right =
        D.toRectangleDecomposition.first.right ∧
      (D.recutOfIsEmpty hone hrectangle hpentagon).second.left =
        D.toRectangleDecomposition.first.left ∧
      (D.recutOfIsEmpty hone hrectangle hpentagon).middle =
        x.swapColumns D.toRectangleDecomposition.second.left
          D.toRectangleDecomposition.first.left := by
  obtain ⟨hcommon', hpen_right⟩ := D.terminal_side_common_right hcommon
  -- View the branch data as data about the shared recut, via the characteristic
  -- identification `recutOfIsEmpty_eq_recut` (proof irrelevance of the emptiness arguments).
  have hdata : D.toRectangleDecomposition.IsRecutOfRightEqRight
      (D.recutOfIsEmpty hone hrectangle hpentagon) := by
    rw [D.recutOfIsEmpty_eq_recut]
    exact D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  have hbranch := hdata.recut_branch
  rcases hbranch with ⟨hcol, hmiddleA, -, hEsecondA⟩ | ⟨-, -, -, hEsecondB⟩
  · exact ⟨hcol, hEsecondA, hdata.recut_sides.2, hmiddleA⟩
  · -- Second branch: E.second.right = D.second.left, so D.second.left = D.pentagon.right
    -- = D.first.right = D.second.right (by hcommon'), contradicting left_ne_right.
    exfalso
    rw [hEsecondB, hpen_right, hcommon'] at hsecond
    exact D.toRectangleDecomposition.second.left_ne_right hsecond

/-- In the first recut branch, the recut's first rectangle's bottom row equals the original
pentagon's bottom row. Call sites needing strip X-avoidance extract the strip clause from
`GridPentagonBetween.disjoint_coveredSquares_XSet_iff` and rewrite with this bottom-row
equation. -/
theorem recut_first_bottom_eq_pentagon_bottom_of_branch1
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirstLeft : (D.recutOfIsEmpty hone hrectangle hpentagon).first.left =
      D.toRectangleDecomposition.first.right) :
    (D.recutOfIsEmpty hone hrectangle hpentagon).first.bottom = D.pentagon.bottom := by
  have hnew : (D.recutOfIsEmpty hone hrectangle hpentagon).first.bottom =
      x D.toRectangleDecomposition.first.right := by
    have h1 : (D.recutOfIsEmpty hone hrectangle hpentagon).first.bottom =
        x ((D.recutOfIsEmpty hone hrectangle hpentagon).first.left) :=
      GridRectangleBetween.bottom_def _
    rw [h1, hfirstLeft]
  have hold : D.pentagon.bottom = x D.toRectangleDecomposition.first.right := by
    have h1 : D.pentagon.bottom = D.middle D.pentagon.left := rfl
    rw [h1, ← hcommon, D.rectangle.map_left, D.toRectangleDecomposition_first_right]
  rw [hnew, hold]

end GridRectanglePentagonDecomposition

end TauCeti
