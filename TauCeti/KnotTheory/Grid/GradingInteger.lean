/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
  `TauCeti.GridDiagram.alexander_two_mul_exists_int`: twice the Alexander grading is an integer.

## References

This advances `TauCetiRoadmap/HeegaardFloer/README.md`, Lane G.2, "Gradings. The `J`-function,
`M_O`, `M_X`, `A`; integer-valuedness of `A`; grading-change formulas across a rectangle." The
integrality of the Maslov gradings is the prerequisite that the (parity-sensitive) integrality of
the Alexander grading itself builds on; see Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 4.
-/

namespace TauCeti

namespace GridPoint

variable {n : ℕ}

/-- The symmetrized numerator of the `J`-function on a point set with itself is even: it is twice
the ordered southwest count. -/
theorem JNum_self (s : Finset (Fin n × Fin n)) : JNum s s = 2 * I s s := by
  rw [JNum_def, two_mul]

/-- The `J`-function on a point set with itself is an integer, namely the ordered southwest
count. The two southwest comparisons of a pair contribute symmetrically, so the division by two
is exact. -/
theorem J_self (s : Finset (Fin n × Fin n)) : GridPoint.J s s = (I s s : ℚ) := by
  rw [J_def, JNum_self]
  push_cast
  ring

end GridPoint

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The integer-valued `O`-Maslov grading of a grid state.

This is the integer formula `M_O(x) = I(x, x) - JNum(x, O) + I(O, O) + 1` obtained from the
rational definition once the two halves coming from the `J`-function cancel. -/
def maslovOℤ (x : GridState n) : ℤ :=
  (GridPoint.I x.pointSet x.pointSet : ℤ) - GridPoint.JNum x.pointSet G.OSet
    + GridPoint.I G.OSet G.OSet + 1

/-- The integer-valued `X`-Maslov grading of a grid state. -/
def maslovXℤ (x : GridState n) : ℤ :=
  (GridPoint.I x.pointSet x.pointSet : ℤ) - GridPoint.JNum x.pointSet G.XSet
    + GridPoint.I G.XSet G.XSet + 1

/-- The rational `O`-Maslov grading is the cast of its integer counterpart: `M_O` is an
integer. -/
theorem maslovO_eq_intCast (x : GridState n) : G.maslovO x = (G.maslovOℤ x : ℚ) := by
  have hxx : GridState.J x x = (GridPoint.I x.pointSet x.pointSet : ℚ) := by
    rw [GridState.J_def, GridPoint.J_self]
  have hOO : GridState.J G.O G.O = (GridPoint.I G.OSet G.OSet : ℚ) := by
    rw [GridState.J_def, GridPoint.J_self, OSet]
  have hJO : 2 * G.JO x = (GridPoint.JNum x.pointSet G.OSet : ℚ) := by
    rw [JO_def, GridPoint.J_def]
    ring
  rw [maslovO_eq, hxx, hJO, hOO, maslovOℤ]
  push_cast
  ring

/-- The rational `X`-Maslov grading is the cast of its integer counterpart: `M_X` is an
integer. -/
theorem maslovX_eq_intCast (x : GridState n) : G.maslovX x = (G.maslovXℤ x : ℚ) := by
  have hxx : GridState.J x x = (GridPoint.I x.pointSet x.pointSet : ℚ) := by
    rw [GridState.J_def, GridPoint.J_self]
  have hXX : GridState.J G.X G.X = (GridPoint.I G.XSet G.XSet : ℚ) := by
    rw [GridState.J_def, GridPoint.J_self, XSet]
  have hJX : 2 * G.JX x = (GridPoint.JNum x.pointSet G.XSet : ℚ) := by
    rw [JX_def, GridPoint.J_def]
    ring
  rw [maslovX_eq, hxx, hJX, hXX, maslovXℤ]
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
theorem alexander_two_mul_exists_int (x : GridState n) :
    ∃ m : ℤ, 2 * G.alexander x = (m : ℚ) :=
  ⟨G.alexanderTwoℤ x, G.two_mul_alexander_eq_intCast x⟩

end GridDiagram

end TauCeti
