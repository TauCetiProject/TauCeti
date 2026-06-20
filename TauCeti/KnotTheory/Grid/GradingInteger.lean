/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Ring
import TauCeti.KnotTheory.Grid.Gradings

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

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G item 2, "Gradings.
The `J`-function, `M_O`, `M_X`, `A`; integer-valuedness of `A`; grading-change formulas across a
rectangle." The integrality of the Maslov gradings is the prerequisite that the (parity-sensitive)
integrality of the Alexander grading itself builds on; see Ozsváth--Stipsicz--Szabó, *Grid Homology
for Knots and Links*, Chapter 4.
-/

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

end GridDiagram

end TauCeti
