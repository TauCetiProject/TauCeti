/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.GradingInteger
public import TauCeti.KnotTheory.Grid.SmallGridDifferential
public import TauCeti.KnotTheory.Grid.StateCardinality
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The standard two-by-two grid grading computation

This file records the first explicit grading calculation for the grid-combinatorial lane.
There are exactly two grid states in grid size two: the identity graph and the transposition
graph. The standard `2 × 2` grid diagram used for the unknot has `O` markings on the identity
graph and `X` markings on the transposition graph.

The fully blocked differential is already known to vanish on every `2 × 2` grid. Here we
combine that with the integer grading API to compute the two generators' Maslov and Alexander
gradings in this concrete diagram.

## Main definitions

* `TauCeti.GridState.twoByTwoId`: the identity grid state in size two.
* `TauCeti.GridState.twoByTwoSwap`: the transposition grid state in size two.
* `TauCeti.GridDiagram.twoByTwo`: the standard `2 × 2` grid diagram with diagonal `O`
  markings and off-diagonal `X` markings.

## Main results

* `TauCeti.GridState.eq_twoByTwoId_or_eq_twoByTwoSwap`: the two named states exhaust
  the generators in grid size two.
* `TauCeti.GridDiagram.fullyBlockedDifferential_twoByTwo`: the fully blocked differential
  on the standard `2 × 2` diagram is zero.
* `TauCeti.GridDiagram.maslovOℤ_twoByTwo_twoByTwoId`,
  `TauCeti.GridDiagram.maslovXℤ_twoByTwo_twoByTwoId`,
  `TauCeti.GridDiagram.alexander_twoByTwo_twoByTwoId`, and the corresponding `twoByTwoSwap`
  lemmas: the exact small-grid bigrading data.

## References

This supplies a small prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`,
Lane G.3, "The complexes and `∂² = 0`", and the acceptance criterion that grid homology
compute on the `2 × 2` unknot grid with its bigradings. The grid and grading conventions
follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3 and 4.
-/

public section

namespace TauCeti

namespace GridState

/-- The identity grid state on a `2 × 2` grid. -/
@[expose]
def twoByTwoId : GridState 2 :=
  ⟨1⟩

/-- The transposition grid state on a `2 × 2` grid. -/
@[expose]
def twoByTwoSwap : GridState 2 :=
  ⟨Equiv.swap (0 : Fin 2) 1⟩

/-- The identity two-by-two state sends column `0` to row `0`. -/
@[simp]
theorem twoByTwoId_zero : twoByTwoId 0 = 0 :=
  rfl

/-- The identity two-by-two state sends column `1` to row `1`. -/
@[simp]
theorem twoByTwoId_one : twoByTwoId 1 = 1 :=
  rfl

/-- The transposition two-by-two state sends column `0` to row `1`. -/
@[simp]
theorem twoByTwoSwap_zero : twoByTwoSwap 0 = 1 := by
  simp [twoByTwoSwap]

/-- The transposition two-by-two state sends column `1` to row `0`. -/
@[simp]
theorem twoByTwoSwap_one : twoByTwoSwap 1 = 0 := by
  simp [twoByTwoSwap]

/-- The two named `2 × 2` grid states are distinct. -/
theorem twoByTwoId_ne_twoByTwoSwap : twoByTwoId ≠ twoByTwoSwap := by
  intro h
  exact Fin.zero_ne_one (congrArg (fun x : GridState 2 => x 0) h)

/-- The two grid states on a `2 × 2` grid are exactly the identity state and the transposition
state. -/
theorem eq_twoByTwoId_or_eq_twoByTwoSwap (x : GridState 2) :
    x = twoByTwoId ∨ x = twoByTwoSwap := by
  have hx := eq_equivPerm_symm_one_or_eq_equivPerm_symm_swap x
  rw [equivPerm_symm_apply, equivPerm_symm_apply] at hx
  simpa [twoByTwoId, twoByTwoSwap] using hx

/-- The finite set of all `2 × 2` grid states is the two explicit states. -/
theorem univ_two :
    (Finset.univ : Finset (GridState 2)) = {twoByTwoId, twoByTwoSwap} := by
  ext x
  constructor
  · intro _
    exact (Finset.mem_insert.mpr <|
      (eq_twoByTwoId_or_eq_twoByTwoSwap x).elim Or.inl fun h => Or.inr <| by simpa using h)
  · intro _
    simp

end GridState

namespace GridDiagram

/-- The standard `2 × 2` grid diagram with `O` markings on the identity state and `X`
markings on the transposition state. This is the usual smallest grid diagram for the unknot. -/
@[expose]
def twoByTwo : GridDiagram 2 where
  O := GridState.twoByTwoId
  X := GridState.twoByTwoSwap
  disjoint := by
    intro c h
    fin_cases c <;> simp at h

/-- The `O`-marking state of the standard two-by-two diagram is the identity state. -/
@[simp]
theorem twoByTwo_O : twoByTwo.O = GridState.twoByTwoId :=
  rfl

/-- The `X`-marking state of the standard two-by-two diagram is the transposition state. -/
@[simp]
theorem twoByTwo_X : twoByTwo.X = GridState.twoByTwoSwap :=
  rfl

/-- The standard two-by-two diagram has `O` markings at `(0,0)` and `(1,1)`. -/
theorem twoByTwo_OSet :
    twoByTwo.OSet = {(0, 0), (1, 1)} := by
  ext p
  rcases p with ⟨c, r⟩
  fin_cases c <;> fin_cases r <;> simp [OSet, GridState.twoByTwoId]

/-- The standard two-by-two diagram has `X` markings at `(0,1)` and `(1,0)`. -/
theorem twoByTwo_XSet :
    twoByTwo.XSet = {(0, 1), (1, 0)} := by
  ext p
  rcases p with ⟨c, r⟩
  fin_cases c <;> fin_cases r <;> simp [XSet, GridState.twoByTwoSwap]

/-- The fully blocked differential of the standard two-by-two grid diagram is zero. -/
theorem fullyBlockedDifferential_twoByTwo :
    twoByTwo.fullyBlockedDifferential =
      (0 : GridChain (ZMod 2) 2 →ₗ[ZMod 2] GridChain (ZMod 2) 2) :=
  twoByTwo.fullyBlockedDifferential_eq_zero_of_two

/-- The integer `O`-Maslov grading of the identity generator in the standard two-by-two
diagram is `1`. -/
theorem maslovOℤ_twoByTwo_twoByTwoId :
    twoByTwo.maslovOℤ GridState.twoByTwoId = 1 := by
  decide

/-- The integer `X`-Maslov grading of the identity generator in the standard two-by-two
diagram is `2`. -/
theorem maslovXℤ_twoByTwo_twoByTwoId :
    twoByTwo.maslovXℤ GridState.twoByTwoId = 2 := by
  decide

/-- Twice the Alexander grading of the identity generator in the standard two-by-two diagram
is `-2`. -/
theorem alexanderTwoℤ_twoByTwo_twoByTwoId :
    twoByTwo.alexanderTwoℤ GridState.twoByTwoId = -2 := by
  decide

/-- The Alexander grading of the identity generator in the standard two-by-two diagram is `-1`. -/
theorem alexander_twoByTwo_twoByTwoId :
    twoByTwo.alexander GridState.twoByTwoId = -1 := by
  rw [alexander_def, twoByTwo.maslovO_eq_intCast, twoByTwo.maslovX_eq_intCast,
    maslovOℤ_twoByTwo_twoByTwoId, maslovXℤ_twoByTwo_twoByTwoId]
  norm_num

/-- The integer `O`-Maslov grading of the transposition generator in the standard two-by-two
diagram is `2`. -/
theorem maslovOℤ_twoByTwo_twoByTwoSwap :
    twoByTwo.maslovOℤ GridState.twoByTwoSwap = 2 := by
  decide

/-- The integer `X`-Maslov grading of the transposition generator in the standard two-by-two
diagram is `1`. -/
theorem maslovXℤ_twoByTwo_twoByTwoSwap :
    twoByTwo.maslovXℤ GridState.twoByTwoSwap = 1 := by
  decide

/-- Twice the Alexander grading of the transposition generator in the standard two-by-two
diagram is `0`. -/
theorem alexanderTwoℤ_twoByTwo_twoByTwoSwap :
    twoByTwo.alexanderTwoℤ GridState.twoByTwoSwap = 0 := by
  decide

/-- The Alexander grading of the transposition generator in the standard two-by-two diagram
is `0`. -/
theorem alexander_twoByTwo_twoByTwoSwap :
    twoByTwo.alexander GridState.twoByTwoSwap = 0 := by
  rw [alexander_def, twoByTwo.maslovO_eq_intCast, twoByTwo.maslovX_eq_intCast,
    maslovOℤ_twoByTwo_twoByTwoSwap, maslovXℤ_twoByTwo_twoByTwoSwap]
  norm_num

/-- Every generator of the standard two-by-two diagram has one of the two computed Alexander
gradings. -/
theorem alexander_twoByTwo_eq_neg_one_or_eq_zero (x : GridState 2) :
    twoByTwo.alexander x = -1 ∨ twoByTwo.alexander x = 0 := by
  rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x with rfl | rfl
  · exact Or.inl alexander_twoByTwo_twoByTwoId
  · exact Or.inr alexander_twoByTwo_twoByTwoSwap

end GridDiagram

end TauCeti
