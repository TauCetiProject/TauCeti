/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Tactic.Ring
public import TauCeti.KnotTheory.Grid.Gradings

/-!
# Integer-valuedness of the Maslov gradings

The Maslov gradings `M_O` and `M_X` of a grid state are defined in
`TauCeti.KnotTheory.Grid.Gradings` as rational-valued formulas through the `J`-function, which is
itself a half-integer (the symmetrization of a point-pair count divided by two). This file proves
that the two Maslov gradings are in fact integers, by exhibiting explicit integer formulas and
the corresponding rational casts. As an immediate consequence the Alexander grading is a
half-integer: its double is an integer.

The key elementary fact is that the `J`-function on a point set with *itself* is already an
integer, `J(s, s) = I(s, s)`, because the symmetrized numerator `JNum(s, s) = 2 · I(s, s)` is
even. Feeding this into the formula `M_O(x) = J(x, x) - 2 · J(x, O) + J(O, O) + 1` cancels every
remaining half: `2 · J(x, O) = JNum(x, O)` is an integer, and the two self-pairings are integers,
so `M_O(x)` is an integer. The same computation handles `M_X`.

## Main definitions

* `TauCeti.GridDiagram.maslovOℤ`, `TauCeti.GridDiagram.maslovXℤ`: the integer-valued Maslov
  gradings.
* `TauCeti.GridDiagram.alexanderTwoℤ`: the integer numerator of twice the Alexander grading.

## Main results

* `TauCeti.GridDiagram.maslovO_eq_intCast`, `TauCeti.GridDiagram.maslovX_eq_intCast`: the
  rational Maslov gradings are the casts of their integer counterparts.
* `TauCeti.GridDiagram.maslovO_exists_int`, `TauCeti.GridDiagram.maslovX_exists_int`: the Maslov
  gradings are integers.
* `TauCeti.GridDiagram.two_mul_alexander_eq_intCast`,
  `TauCeti.GridDiagram.two_mul_alexander_exists_int`: twice the Alexander grading is an integer.
* `TauCeti.GridDiagram.maslovOℤ_transpose`, `TauCeti.GridDiagram.maslovXℤ_transpose`,
  `TauCeti.GridDiagram.alexanderTwoℤ_transpose`: the integer-valued gradings are invariant
  under the diagonal reflection of a grid state and diagram.
* `TauCeti.GridDiagram.maslovOℤ_rotate`, `TauCeti.GridDiagram.maslovXℤ_rotate`,
  `TauCeti.GridDiagram.alexanderTwoℤ_rotate`: the integer-valued gradings are invariant
  under the half-turn rotation of a grid state and diagram.
* `TauCeti.GridDiagram.maslovOℤ_swapMarkings`, `TauCeti.GridDiagram.maslovXℤ_swapMarkings`,
  `TauCeti.GridDiagram.alexanderTwoℤ_swapMarkings`: the integer-valued gradings transform
  under the marking swap.
* `TauCeti.GridDiagram.maslovOℤ_eq_card`, `TauCeti.GridDiagram.maslovXℤ_eq_card`: the integer
  Maslov gradings written entirely as counts over column indices, so they evaluate on an
  explicit grid without unfolding any point-pair product.
* `TauCeti.GridDiagram.maslovOℤ_O`, `TauCeti.GridDiagram.maslovXℤ_X`: the integer Maslov grading
  of a marking state against its own markings is always `1`.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G item 2, "Gradings.
The `J`-function, `M_O`, `M_X`, `A`; integer-valuedness of `A`; grading-change formulas across a
rectangle." The integrality of the Maslov gradings is the prerequisite that the (parity-sensitive)
integrality of the Alexander grading itself builds on; see Ozsváth--Stipsicz--Szabó, *Grid Homology
for Knots and Links*, Chapter 4.
-/

@[expose] public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The integer-valued `O`-Maslov grading of a grid state.

This is the integer formula `M_O(x) = I(x, x) - JNum(x, O) + I(O, O) + 1` obtained from the
rational definition once the two halves coming from the `J`-function cancel. -/
def maslovOℤ (x : GridState n) : ℤ :=
  (GridPoint.I x.pointSet x.pointSet : ℤ) - GridPoint.JNum x.pointSet G.OSet
    + GridPoint.I G.OSet G.OSet + 1

/-- The integer `O`-Maslov grading restated as its defining formula. -/
@[simp]
theorem maslovOℤ_def (x : GridState n) :
    G.maslovOℤ x =
      (GridPoint.I x.pointSet x.pointSet : ℤ) - GridPoint.JNum x.pointSet G.OSet
        + GridPoint.I G.OSet G.OSet + 1 :=
  rfl

/-- The integer-valued `X`-Maslov grading of a grid state. -/
def maslovXℤ (x : GridState n) : ℤ :=
  (GridPoint.I x.pointSet x.pointSet : ℤ) - GridPoint.JNum x.pointSet G.XSet
    + GridPoint.I G.XSet G.XSet + 1

/-- The integer `X`-Maslov grading restated as its defining formula. -/
@[simp]
theorem maslovXℤ_def (x : GridState n) :
    G.maslovXℤ x =
      (GridPoint.I x.pointSet x.pointSet : ℤ) - GridPoint.JNum x.pointSet G.XSet
        + GridPoint.I G.XSet G.XSet + 1 :=
  rfl

/-- The integer `O`-Maslov grading of a grid state written entirely as counts over column
indices. Every southwest count in `maslovOℤ` is a state or marking point-set count, so it collapses
to a column-pair count and the grading evaluates without unfolding any point-pair product. -/
theorem maslovOℤ_eq_card (x : GridState n) :
    G.maslovOℤ x =
      ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < x p.2).card : ℤ)
        - ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < G.O p.2).card
          + (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.O p.1 < x p.2).card)
        + (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.O p.1 < G.O p.2).card + 1 := by
  rw [maslovOℤ_def, OSet, GridState.I_self_pointSet_eq_card x,
    GridState.JNum_pointSet_eq_card x G.O, GridState.I_self_pointSet_eq_card G.O]
  push_cast
  ring

/-- The integer `X`-Maslov grading of a grid state written entirely as counts over column
indices. -/
theorem maslovXℤ_eq_card (x : GridState n) :
    G.maslovXℤ x =
      ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < x p.2).card : ℤ)
        - ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < G.X p.2).card
          + (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.X p.1 < x p.2).card)
        + (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.X p.1 < G.X p.2).card + 1 := by
  rw [maslovXℤ_def, XSet, GridState.I_self_pointSet_eq_card x,
    GridState.JNum_pointSet_eq_card x G.X, GridState.I_self_pointSet_eq_card G.X]
  push_cast
  ring

/-- The integer `O`-Maslov grading of the `O`-marking state is always `1`. -/
theorem maslovOℤ_O : G.maslovOℤ G.O = 1 := by
  rw [maslovOℤ_eq_card]
  ring

/-- The integer `X`-Maslov grading of the `X`-marking state is always `1`. -/
theorem maslovXℤ_X : G.maslovXℤ G.X = 1 := by
  rw [maslovXℤ_eq_card]
  ring

/-- The rational `O`-Maslov grading is the cast of its integer counterpart: `M_O` is an
integer. This specializes the general self-pairing integrality `GridPoint.JDiff_self_eq_intCast`
to the `O`-markings. -/
theorem maslovO_eq_intCast (x : GridState n) : G.maslovO x = (G.maslovOℤ x : ℚ) := by
  rw [maslovO_def, GridPoint.JDiff_self_eq_intCast, maslovOℤ]
  push_cast
  ring

/-- The rational `X`-Maslov grading is the cast of its integer counterpart: `M_X` is an
integer. This specializes the general self-pairing integrality `GridPoint.JDiff_self_eq_intCast`
to the `X`-markings. -/
theorem maslovX_eq_intCast (x : GridState n) : G.maslovX x = (G.maslovXℤ x : ℚ) := by
  rw [maslovX_def, GridPoint.JDiff_self_eq_intCast, maslovXℤ]
  push_cast
  ring

/-- The `O`-Maslov grading is an integer. -/
theorem maslovO_exists_int (x : GridState n) : ∃ m : ℤ, G.maslovO x = (m : ℚ) :=
  ⟨G.maslovOℤ x, G.maslovO_eq_intCast x⟩

/-- The `X`-Maslov grading is an integer. -/
theorem maslovX_exists_int (x : GridState n) : ∃ m : ℤ, G.maslovX x = (m : ℚ) :=
  ⟨G.maslovXℤ x, G.maslovX_eq_intCast x⟩

/-- The integer numerator of twice the Alexander grading, `2 · A(x) = M_O(x) - M_X(x) - (n - 1)`.
The normalization shift `(n - 1)` is taken over `ℤ`, so the formula is literal at every `n`. -/
def alexanderTwoℤ (x : GridState n) : ℤ :=
  G.maslovOℤ x - G.maslovXℤ x - ((n : ℤ) - 1)

/-- The integer numerator of twice the Alexander grading restated as its defining formula. -/
@[simp]
theorem alexanderTwoℤ_def (x : GridState n) :
    G.alexanderTwoℤ x = G.maslovOℤ x - G.maslovXℤ x - ((n : ℤ) - 1) :=
  rfl

/-- Twice the Alexander grading is an integer: it is the difference of the integer Maslov
gradings, corrected by the normalization shift. This stops short of integrality of `A` itself,
which is the genuinely parity-sensitive statement. -/
theorem two_mul_alexander_eq_intCast (x : GridState n) :
    2 * G.alexander x = (G.alexanderTwoℤ x : ℚ) := by
  rw [alexander_def, G.maslovO_eq_intCast, G.maslovX_eq_intCast, alexanderTwoℤ]
  push_cast
  ring

/-- Twice the Alexander grading is an integer; equivalently, the Alexander grading is a
half-integer. -/
theorem two_mul_alexander_exists_int (x : GridState n) :
    ∃ m : ℤ, 2 * G.alexander x = (m : ℚ) :=
  ⟨G.alexanderTwoℤ x, G.two_mul_alexander_eq_intCast x⟩

/-- The integer-valued `O`-Maslov grading is invariant under the diagonal reflection. -/
theorem maslovOℤ_transpose (x : GridState n) :
    G.transpose.maslovOℤ x.transpose = G.maslovOℤ x := by
  rw [maslovOℤ_def, maslovOℤ_def, GridState.transpose_pointSet, transpose_OSet,
    GridPoint.I_image_swap, GridPoint.JNum_image_swap, GridPoint.I_image_swap]

/-- The integer-valued `X`-Maslov grading is invariant under the diagonal reflection. -/
theorem maslovXℤ_transpose (x : GridState n) :
    G.transpose.maslovXℤ x.transpose = G.maslovXℤ x := by
  rw [maslovXℤ_def, maslovXℤ_def, GridState.transpose_pointSet, transpose_XSet,
    GridPoint.I_image_swap, GridPoint.JNum_image_swap, GridPoint.I_image_swap]

/-- The integer numerator of twice the Alexander grading is invariant under the diagonal
reflection. -/
theorem alexanderTwoℤ_transpose (x : GridState n) :
    G.transpose.alexanderTwoℤ x.transpose = G.alexanderTwoℤ x := by
  rw [alexanderTwoℤ_def, alexanderTwoℤ_def, maslovOℤ_transpose, maslovXℤ_transpose]

/-- The integer-valued `O`-Maslov grading is invariant under the half-turn rotation. -/
theorem maslovOℤ_rotate (x : GridState n) :
    G.rotate.maslovOℤ x.rotate = G.maslovOℤ x := by
  rw [maslovOℤ_def, maslovOℤ_def, GridState.rotate_pointSet, rotate_OSet,
    GridPoint.I_image_rev, GridPoint.JNum_image_rev, GridPoint.I_image_rev]

/-- The integer-valued `X`-Maslov grading is invariant under the half-turn rotation. -/
theorem maslovXℤ_rotate (x : GridState n) :
    G.rotate.maslovXℤ x.rotate = G.maslovXℤ x := by
  rw [maslovXℤ_def, maslovXℤ_def, GridState.rotate_pointSet, rotate_XSet,
    GridPoint.I_image_rev, GridPoint.JNum_image_rev, GridPoint.I_image_rev]

/-- The integer numerator of twice the Alexander grading is invariant under the half-turn
rotation. -/
theorem alexanderTwoℤ_rotate (x : GridState n) :
    G.rotate.alexanderTwoℤ x.rotate = G.alexanderTwoℤ x := by
  rw [alexanderTwoℤ_def, alexanderTwoℤ_def, maslovOℤ_rotate, maslovXℤ_rotate]

/-- The marking swap exchanges the integer-valued Maslov gradings. -/
@[simp]
theorem maslovOℤ_swapMarkings (x : GridState n) :
    G.swapMarkings.maslovOℤ x = G.maslovXℤ x := by
  rw [maslovOℤ_def, maslovXℤ_def, swapMarkings_OSet]

/-- The marking swap exchanges the integer-valued Maslov gradings. -/
@[simp]
theorem maslovXℤ_swapMarkings (x : GridState n) :
    G.swapMarkings.maslovXℤ x = G.maslovOℤ x := by
  rw [maslovXℤ_def, maslovOℤ_def, swapMarkings_XSet]

/-- The marking swap negates the integer numerator of twice the Alexander grading, up to twice
the normalization shift: `2·A_swap(x) = −2·A(x) − 2(n − 1)`. -/
theorem alexanderTwoℤ_swapMarkings (x : GridState n) :
    G.swapMarkings.alexanderTwoℤ x = -G.alexanderTwoℤ x - 2 * ((n : ℤ) - 1) := by
  rw [alexanderTwoℤ_def, alexanderTwoℤ_def, maslovOℤ_swapMarkings, maslovXℤ_swapMarkings]
  ring

end GridDiagram

end TauCeti
