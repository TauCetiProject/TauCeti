/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.SimplyBlocked
public import TauCeti.KnotTheory.Grid.SmallGrid.Gradings
import TauCeti.KnotTheory.Grid.Rectangle.Count
import Mathlib.Tactic.FinCases

/-!
# The simply blocked differential of the two-by-two unknot

The simply blocked complex of the standard two-by-two unknot has two grid-state generators.
After blocking the `O`-marking in column zero, its differential sends the identity state to the
transposition state with coefficient the sole surviving variable, and sends the transposition
state to zero. Thus the complex has the concrete form

`R[V] · id ⊕ R[V] · swap`, with `d(id) = V · swap` and `d(swap) = 0`.

The transposition generator is a homogeneous cycle of Maslov--Alexander bidegree `(0, 0)`.
The subsequent homology computation amounts to taking the cokernel of multiplication by `V`;
this file supplies the geometric and chain-level calculation needed for that quotient step.

## Main definitions

* `TauCeti.GridDiagram.twoByTwoSurvivingColumn`: the unblocked column after column zero is
  blocked.
* `TauCeti.GridDiagram.twoByTwoSimplyBlockedCycle`: the transposition-state cycle.

## Main results

* `TauCeti.GridDiagram.twoByTwo_simplyBlockedCoefficient_id_swap` and
  `TauCeti.GridDiagram.twoByTwo_simplyBlockedCoefficient_swap_id`: the off-diagonal matrix
  coefficients.
* `TauCeti.GridDiagram.twoByTwo_simplyBlockedDifferential_apply`: the differential on an
  arbitrary chain.
* `TauCeti.GridDiagram.twoByTwoSimplyBlockedCycle_mem_bigradedChainHatPiece`: the surviving cycle
  has bidegree `(0, 0)`.

## References

The computation follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Sections 4.4 and 4.6.
-/

public section

open MvPolynomial

namespace TauCeti.GridDiagram

/-- The unique column remaining after column zero is blocked in a two-by-two grid. -/
abbrev twoByTwoSurvivingColumn : {c : Fin 2 // c ≠ 0} :=
  ⟨1, by decide⟩

private noncomputable def twoByTwoRectangleZeroOne :
    GridRectangleBetween GridState.twoByTwoId GridState.twoByTwoSwap where
  left := 0
  right := 1
  left_ne_right := by decide
  map_left := by simp
  map_right := by simp
  map_of_ne c hc₀ hc₁ := by
    fin_cases c <;> simp_all

private noncomputable def twoByTwoRectangleOneZero :
    GridRectangleBetween GridState.twoByTwoId GridState.twoByTwoSwap :=
  twoByTwoRectangleZeroOne.swapSides

private theorem twoByTwoRectangle_eq (r :
    GridRectangleBetween GridState.twoByTwoId GridState.twoByTwoSwap) :
    r = twoByTwoRectangleZeroOne ∨ r = twoByTwoRectangleOneZero :=
  twoByTwoRectangleZeroOne.eq_or_eq_swapSides r

private theorem twoByTwoRectangleZeroOne_ne_oneZero :
    twoByTwoRectangleZeroOne ≠ twoByTwoRectangleOneZero := by
  intro h
  have hleft := congrArg GridRectangleBetween.left h
  simp [twoByTwoRectangleZeroOne, twoByTwoRectangleOneZero] at hleft

private theorem cIco_zero_one : Grid.cIco (0 : Fin 2) 1 = {0} :=
  Grid.cIco_eq_singleton_iff.mpr (by decide)

private theorem cIco_one_zero : Grid.cIco (1 : Fin 2) 0 = {1} :=
  Grid.cIco_eq_singleton_iff.mpr (by decide)

private theorem twoByTwoRectangleZeroOne_squares :
    twoByTwoRectangleZeroOne.toGridRectangle.coveredSquares = {(0, 0)} := by
  have hleft : twoByTwoRectangleZeroOne.toGridRectangle.left = 0 := rfl
  have hright : twoByTwoRectangleZeroOne.toGridRectangle.right = 1 := rfl
  have hbottom : twoByTwoRectangleZeroOne.toGridRectangle.bottom = 0 := rfl
  have htop : twoByTwoRectangleZeroOne.toGridRectangle.top = 1 := rfl
  rw [GridRectangle.coveredSquares_def, GridRectangle.coveredColumns_def,
    GridRectangle.coveredRows_def, hleft, hright, hbottom, htop, cIco_zero_one]
  ext p
  simp

private theorem twoByTwoRectangleOneZero_squares :
    twoByTwoRectangleOneZero.toGridRectangle.coveredSquares = {(1, 1)} := by
  have hleft : twoByTwoRectangleOneZero.toGridRectangle.left = 1 := by
    simp [twoByTwoRectangleOneZero, twoByTwoRectangleZeroOne]
  have hright : twoByTwoRectangleOneZero.toGridRectangle.right = 0 := by
    simp [twoByTwoRectangleOneZero, twoByTwoRectangleZeroOne]
  have hbottom : twoByTwoRectangleOneZero.toGridRectangle.bottom = 1 := by
    rw [GridRectangleBetween.toGridRectangle_bottom, twoByTwoRectangleOneZero,
      GridRectangleBetween.swapSides_bottom,
      GridRectangleBetween.top_def]
    rfl
  have htop : twoByTwoRectangleOneZero.toGridRectangle.top = 0 := by
    rw [GridRectangleBetween.toGridRectangle_top, twoByTwoRectangleOneZero,
      GridRectangleBetween.swapSides_top,
      GridRectangleBetween.bottom_def]
    rfl
  rw [GridRectangle.coveredSquares_def, GridRectangle.coveredColumns_def,
    GridRectangle.coveredRows_def, hleft, hright, hbottom, htop, cIco_one_zero]
  ext p
  simp

private theorem twoByTwo_simplyBlockedRectangles_id_swap :
    twoByTwo.simplyBlockedRectangles 0 GridState.twoByTwoId GridState.twoByTwoSwap =
      {twoByTwoRectangleOneZero} := by
  ext r
  rw [mem_simplyBlockedRectangles]
  rcases twoByTwoRectangle_eq r with rfl | rfl
  · simp [twoByTwoRectangleZeroOne_squares,
      twoByTwo_XSet, twoByTwoRectangleZeroOne_ne_oneZero]
  · simp [GridRectangleBetween.IsEmpty, GridRectangle.IsEmptyFor,
      GridRectangle.interior_eq_empty_of_le_two (n := 2) le_rfl,
      twoByTwoRectangleOneZero_squares, twoByTwo_XSet]

private theorem twoByTwo_simplyBlockedRectangles_swap_id :
    twoByTwo.simplyBlockedRectangles 0 GridState.twoByTwoSwap GridState.twoByTwoId = ∅ := by
  ext r
  simp only [mem_simplyBlockedRectangles, Finset.notMem_empty, iff_false, not_and]
  intro _ hdisjoint _
  apply Finset.disjoint_left.mp hdisjoint
    (GridRectangle.squares_eq_coveredSquares r.toGridRectangle ▸ r.left_bottom_mem_squares)
  exact twoByTwo.mk_mem_XSet r.left (GridState.twoByTwoSwap r.left) |>.mpr rfl

variable (R : Type*) [CommSemiring R]

/-- The nonzero off-diagonal simply blocked coefficient of the standard two-by-two unknot is the
sole surviving variable. -/
@[simp]
theorem twoByTwo_simplyBlockedCoefficient_id_swap :
    twoByTwo.simplyBlockedCoefficient R 0
        GridState.twoByTwoId GridState.twoByTwoSwap =
      MvPolynomial.X twoByTwoSurvivingColumn := by
  rw [simplyBlockedCoefficient_eq_sum, twoByTwo_simplyBlockedRectangles_id_swap]
  have hO : twoByTwo.OColumns twoByTwoRectangleOneZero.toGridRectangle = {1} := by
    ext c
    rw [mem_OColumns, twoByTwoRectangleOneZero_squares]
    fin_cases c <;> simp
  simp only [Finset.sum_singleton]
  rw [hO]
  have hs : Finset.subtype (fun c : Fin 2 => c ≠ 0) ({1} : Finset (Fin 2)) =
      {twoByTwoSurvivingColumn} := by
    ext c
    simp only [Finset.mem_subtype, Finset.mem_singleton]
    constructor
    · intro hc
      exact Subtype.ext hc
    · intro hc
      exact congrArg Subtype.val hc
  rw [hs]
  simp

/-- There is no simply blocked differential term from the transposition state back to the
identity state in the standard two-by-two unknot. -/
@[simp]
theorem twoByTwo_simplyBlockedCoefficient_swap_id :
    twoByTwo.simplyBlockedCoefficient R 0
        GridState.twoByTwoSwap GridState.twoByTwoId = 0 := by
  rw [simplyBlockedCoefficient_eq_sum, twoByTwo_simplyBlockedRectangles_swap_id]
  simp

/-- The simply blocked differential on the standard two-by-two unknot is
`d(a · id + b · swap) = (a V) · swap`. -/
@[simp]
theorem twoByTwo_simplyBlockedDifferential_apply
    (c : GridChainHat R 2 0) :
    twoByTwo.simplyBlockedDifferential R 0 c =
      Finsupp.single GridState.twoByTwoSwap
        (c GridState.twoByTwoId * MvPolynomial.X twoByTwoSurvivingColumn) := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add x a c hx ha ih =>
      rw [map_add, ih]
      rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x with rfl | rfl
      · ext y : 1
        rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap y with rfl | rfl <;>
          simp [add_mul]
      · ext y : 1
        rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap y with rfl | rfl <;>
          simp

/-- The surviving cycle in the simply blocked complex of the standard two-by-two unknot. -/
noncomputable def twoByTwoSimplyBlockedCycle : GridChainHat R 2 0 :=
  Finsupp.single GridState.twoByTwoSwap 1

/-- The named surviving chain is killed by the simply blocked differential. -/
theorem twoByTwo_simplyBlockedDifferential_cycle :
    twoByTwo.simplyBlockedDifferential R 0 (twoByTwoSimplyBlockedCycle R) = 0 := by
  rw [twoByTwo_simplyBlockedDifferential_apply]
  simp [twoByTwoSimplyBlockedCycle]

/-- The surviving two-by-two simply blocked cycle is homogeneous of
Maslov--Alexander bidegree `(0, 0)`. -/
theorem twoByTwoSimplyBlockedCycle_mem_bigradedChainHatPiece :
    twoByTwoSimplyBlockedCycle R ∈
      OddComponentGridDiagram.twoByTwo.bigradedChainHatPiece R 0 (0, 0) := by
  rw [OddComponentGridDiagram.mem_bigradedChainHatPiece]
  intro x e he
  have hx : x = GridState.twoByTwoSwap := by
    rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x with rfl | h
    · simp [twoByTwoSimplyBlockedCycle] at he
    · exact h
  subst x
  have hezero : e = 0 := by
    by_contra h
    simp [twoByTwoSimplyBlockedCycle, MvPolynomial.coeff_one, Ne.symm h] at he
  subst e
  rw [Prod.ext_iff]
  simp [Finsupp.degree_apply, OddComponentGridDiagram.bidegree_twoByTwo_twoByTwoSwap]

end TauCeti.GridDiagram
