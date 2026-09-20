/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.ModEq
public import TauCeti.LinearAlgebra.Matrix.Step

import Mathlib.Tactic.NormNum

/-!
# Short-root quotient coordinates of type F4

The integral matrices of the twenty-six-dimensional short-root representation of type `F4` span,
together with the matrices of all forty-eight root vectors and the four Cartan generators, the
represented Chevalley algebra inside `Matrix (Fin 26) (Fin 26) ℤ`. Modulo two the twenty-four
short root vectors and the last two Cartan generators span an ideal, the radical of the reduced
trace form, and the twenty-four long root vectors together with the first two Cartan generators
represent a basis of the quotient by it. This file tabulates those twenty-six representing
matrices and the twenty-six coordinate functionals dual to them modulo two, in the enumeration of
the short-root weight basis under which the length-exchanging map of the type-`F4` diagram sends
the `q`th representative to the `q`th coordinate vector.

Each representative is a *step matrix*: a matrix with at most one nonzero entry in each column,
recorded by a target table and a coefficient table. Each coordinate functional is the sum of at
most two matrix entries, again read from tables; only the two zero-weight indices `12` and `13`
read a second entry. Consequently every value of a coordinate functional on a product of step
matrices is a sum of at most two products of table lookups, and identities between such values
are finite entrywise computations.

Neither the represented Chevalley algebra nor its short-root ideal is constructed here, and
nothing below asserts that the twenty-six matrices are linearly independent, that they span a
complement of that ideal, or that the functionals annihilate it. Only the explicit matrices, the
explicit functionals and their duality modulo two are used.

## Main definitions

* `TauCeti.F4ShortRoot.quotientMatrix`: the twenty-six representing integer matrices.
* `TauCeti.F4ShortRoot.quotientCoordinate`: the twenty-six coordinate functionals, over any ring.

## Main results

* `TauCeti.F4ShortRoot.isStep_quotientMatrix`: the step structure of the tabulated matrices.
* `TauCeti.F4ShortRoot.quotientCoordinate_eq_of_isStep` and
  `TauCeti.F4ShortRoot.quotientCoordinate_of_isStep`: the value of a coordinate functional on a
  step matrix, as a table lookup.
* `TauCeti.F4ShortRoot.quotientCoordinate_quotientMatrix`: the twenty-six functionals are dual to
  the twenty-six matrices modulo two.

## References

The numbering follows N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII. The
short-root ideal in characteristic two and the length-exchanging map of the diagram are those of
R. Steinberg, *Lectures on Chevalley Groups*, §11, and R. W. Carter, *Simple Groups of Lie
Type*, §12.3.

The tables and their formal verification are adapted from the unmerged
[Tau Ceti PR #6711](https://github.com/TauCetiProject/TauCeti/pull/6711).
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [Ring R]

/-! ## The representing matrices -/

/-- The target table of the twenty-six representing matrices. -/
@[expose] def quotientTarget : Fin 26 → Fin 26 → Fin 26 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0, 19, 1, 21, 2, 3, 5, 7],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 17, 18, 1, 20, 2, 22, 4, 6, 9],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 15, 16, 1, 18, 19, 20, 3, 4, 23, 8, 11],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 2, 16, 17, 18, 5, 6, 21, 22, 10, 24, 14],
    ![0, 1, 2, 3, 4, 5, 6, 7, 1, 9, 2, 11, 12, 13, 14, 15, 7, 17, 9, 19, 20, 21, 22, 15, 17, 25],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 11, 12, 13, 14, 3, 16, 5, 18, 19, 8, 21, 10, 23, 24, 16],
    ![0, 1, 2, 3, 4, 5, 1, 7, 8, 9, 3, 11, 12, 13, 7, 15, 16, 17, 11, 19, 20, 21, 15, 23, 19, 25],
    ![0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 14, 4, 16, 6, 18, 8, 20, 10, 22, 23, 24, 18],
    ![0, 1, 2, 3, 2, 5, 6, 7, 5, 9, 10, 7, 12, 13, 14, 15, 16, 17, 14, 19, 17, 21, 22, 21, 24, 25],
    ![0, 1, 2, 3, 4, 1, 6, 7, 8, 9, 4, 11, 12, 13, 9, 15, 11, 17, 18, 19, 20, 15, 22, 23, 20, 25],
    ![0, 1, 2, 3, 3, 5, 5, 7, 8, 7, 10, 11, 12, 13, 14, 15, 16, 17, 16, 19, 19, 21, 21, 23, 24, 25],
    ![0, 1, 2, 2, 4, 5, 6, 7, 6, 9, 10, 9, 12, 13, 14, 15, 14, 17, 18, 17, 20, 21, 22, 22, 24, 25],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
    ![0, 1, 3, 3, 4, 5, 8, 7, 8, 11, 10, 11, 12, 13, 16, 15, 16, 19, 18, 19, 20, 21, 23, 23, 24,
      25],
    ![0, 1, 2, 4, 4, 6, 6, 9, 8, 9, 10, 11, 12, 13, 14, 15, 18, 17, 18, 20, 20, 22, 22, 23, 24, 25],
    ![0, 5, 2, 3, 10, 5, 6, 7, 8, 14, 10, 16, 12, 13, 14, 21, 16, 17, 18, 19, 24, 21, 22, 23, 24,
      25],
    ![0, 1, 4, 3, 4, 8, 6, 11, 8, 9, 10, 11, 12, 13, 18, 15, 16, 20, 18, 19, 20, 23, 22, 23, 24,
      25],
    ![7, 1, 2, 3, 15, 5, 17, 7, 19, 9, 21, 11, 12, 13, 14, 15, 16, 17, 25, 19, 20, 21, 22, 23, 24,
      25],
    ![0, 6, 2, 10, 4, 5, 6, 14, 8, 9, 10, 18, 12, 13, 14, 22, 16, 17, 18, 24, 20, 21, 22, 23, 24,
      25],
    ![9, 1, 2, 15, 4, 17, 6, 7, 20, 9, 22, 11, 12, 13, 14, 15, 25, 17, 18, 19, 20, 21, 22, 23, 24,
      25],
    ![0, 8, 10, 3, 4, 5, 6, 16, 8, 18, 10, 11, 12, 13, 14, 23, 16, 24, 18, 19, 20, 21, 22, 23, 24,
      25],
    ![11, 1, 15, 3, 4, 19, 20, 7, 8, 9, 23, 11, 12, 13, 25, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
      25],
    ![14, 17, 2, 21, 22, 5, 6, 7, 24, 9, 10, 25, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
      24, 25],
    ![16, 19, 21, 3, 23, 5, 24, 7, 8, 25, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
      24, 25],
    ![18, 20, 22, 23, 4, 24, 6, 25, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
      24, 25]]

/-- The coefficient table of the twenty-six representing matrices. -/
@[expose] def quotientCoeff : Fin 26 → Fin 26 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, -1, -1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, -1, -1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 1, 0, 0, -1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, -1, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0],
    ![0, 0, 1, -1, 0, 0, 1, 0, -1, 1, 0, -1, 0, 0, 1, 0, -1, 1, 0, -1, 0, 0, 1, -1, 0, 0],
    ![0, 0, 0, 1, -1, 1, -1, 1, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, -1, 1, -1, 1, -1, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0],
    ![1, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 1, 0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, -1, 0, 0, 1, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, -1, -1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The `q`th representing matrix: for `q` other than the two zero-weight indices `12` and `13`,
the root vector of the long root whose image under the length-exchanging map has the `q`th weight
of the short-root basis; at `13` and `12` the first and the second Cartan generator. -/
def quotientMatrix (q : Fin 26) : Matrix (Fin 26) (Fin 26) ℤ :=
  Matrix.of fun a b => if a = quotientTarget q b then quotientCoeff q b else 0

/-- The entrywise formula for a representing matrix. -/
@[simp]
theorem quotientMatrix_apply (q a b : Fin 26) :
    quotientMatrix q a b = if a = quotientTarget q b then quotientCoeff q b else 0 := by
  rw [quotientMatrix, Matrix.of_apply]

/-- Every representing matrix is a step matrix. -/
theorem isStep_quotientMatrix (q : Fin 26) :
    (quotientMatrix q).IsStep (quotientTarget q) (quotientCoeff q) :=
  Matrix.isStep_of_apply (quotientMatrix_apply q)

/-! ## The coordinate functionals -/

/-- The rows read by the twenty-six coordinate functionals. -/
@[expose] def coordinateRow : Fin 2 → Fin 26 → Fin 26 :=
  ![![0, 0, 0, 0, 1, 0, 1, 0, 2, 1, 3, 2, 0, 0, 3, 4, 5, 4, 7, 6, 9, 8, 11, 14, 16, 18],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The columns read by the twenty-six coordinate functionals. -/
@[expose] def coordinateCol : Fin 2 → Fin 26 → Fin 26 :=
  ![![18, 16, 14, 11, 8, 9, 6, 7, 4, 5, 4, 3, 0, 0, 2, 3, 1, 2, 0, 1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The coefficients of the twenty-six coordinate functionals. Only the two zero-weight indices
`12` and `13` read a second entry. -/
@[expose] def coordinateCoeff : Fin 2 → Fin 26 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The `p`th short-root quotient coordinate of a matrix: one or two of its entries, added up. -/
def quotientCoordinate (p : Fin 26) (Y : Matrix (Fin 26) (Fin 26) R) : R :=
  (coordinateCoeff 0 p : R) * Y (coordinateRow 0 p) (coordinateCol 0 p) +
    (coordinateCoeff 1 p : R) * Y (coordinateRow 1 p) (coordinateCol 1 p)

/-- The two entries a quotient coordinate reads. -/
theorem quotientCoordinate_def (p : Fin 26) (Y : Matrix (Fin 26) (Fin 26) R) :
    quotientCoordinate p Y =
      (coordinateCoeff 0 p : R) * Y (coordinateRow 0 p) (coordinateCol 0 p) +
        (coordinateCoeff 1 p : R) * Y (coordinateRow 1 p) (coordinateCol 1 p) := by
  rw [quotientCoordinate]

/-- Quotient coordinates are additive. -/
theorem quotientCoordinate_add (p : Fin 26) (Y Z : Matrix (Fin 26) (Fin 26) R) :
    quotientCoordinate p (Y + Z) = quotientCoordinate p Y + quotientCoordinate p Z := by
  rw [quotientCoordinate, quotientCoordinate, quotientCoordinate]
  simp only [Matrix.add_apply, mul_add]
  ac_rfl

/-- Quotient coordinates are homogeneous. -/
theorem quotientCoordinate_smul (p : Fin 26) (c : R) (Y : Matrix (Fin 26) (Fin 26) R) :
    quotientCoordinate p (c • Y) = c * quotientCoordinate p Y := by
  rw [quotientCoordinate, quotientCoordinate]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [mul_add]
  congr 1 <;> rw [← mul_assoc, Int.cast_comm, mul_assoc]

/-- Quotient coordinates commute with entrywise integer casts. -/
theorem quotientCoordinate_map_intCast (p : Fin 26) (Y : Matrix (Fin 26) (Fin 26) ℤ) :
    quotientCoordinate p (Y.map (Int.cast : ℤ → R)) = ((quotientCoordinate p Y : ℤ) : R) := by
  rw [quotientCoordinate, quotientCoordinate]
  simp only [Matrix.map_apply, Int.cast_add, Int.cast_mul, Int.cast_id]

/-- The `p`th quotient coordinate of the step matrix with target table `t` and coefficient table
`c`. -/
@[expose] def quotientCoordinateStep (p : Fin 26) (t : Fin 26 → Fin 26) (c : Fin 26 → ℤ) : ℤ :=
  (if coordinateRow 0 p = t (coordinateCol 0 p) then
      coordinateCoeff 0 p * c (coordinateCol 0 p) else 0) +
    (if coordinateRow 1 p = t (coordinateCol 1 p) then
      coordinateCoeff 1 p * c (coordinateCol 1 p) else 0)

/-- **A quotient coordinate of a step matrix is a table lookup**, over any ring. -/
theorem quotientCoordinate_eq_of_isStep {M : Matrix (Fin 26) (Fin 26) R} {t : Fin 26 → Fin 26}
    {c : Fin 26 → R} (h : M.IsStep t c) (p : Fin 26) :
    quotientCoordinate p M =
      (if coordinateRow 0 p = t (coordinateCol 0 p) then
          (coordinateCoeff 0 p : R) * c (coordinateCol 0 p) else 0) +
        (if coordinateRow 1 p = t (coordinateCol 1 p) then
          (coordinateCoeff 1 p : R) * c (coordinateCol 1 p) else 0) := by
  rw [quotientCoordinate, h.apply, h.apply]
  split_ifs <;> simp

/-- A quotient coordinate of an integral step matrix, as the integer table lookup. -/
theorem quotientCoordinate_of_isStep {M : Matrix (Fin 26) (Fin 26) ℤ} {t : Fin 26 → Fin 26}
    {c : Fin 26 → ℤ} (h : M.IsStep t c) (p : Fin 26) :
    quotientCoordinate p M = quotientCoordinateStep p t c := by
  rw [quotientCoordinate_eq_of_isStep h p, quotientCoordinateStep]
  simp only [Int.cast_id]

/-- **The twenty-six coordinate functionals are dual, modulo two, to the twenty-six representing
matrices.** -/
theorem quotientCoordinate_quotientMatrix (p q : Fin 26) :
    quotientCoordinate p (quotientMatrix q) ≡ (if p = q then 1 else 0) [ZMOD 2] := by
  rw [quotientCoordinate_of_isStep (isStep_quotientMatrix q)]
  revert p q
  decide +kernel

end TauCeti.F4ShortRoot
