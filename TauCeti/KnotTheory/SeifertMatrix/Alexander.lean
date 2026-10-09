/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.SeifertMatrix.SEquivalence

/-!
# The Alexander polynomial under S-equivalence

The normalized Alexander polynomial of an integral square matrix is constant on
S-equivalence classes. Elementary enlargements change the matrix size by two; simultaneous
reindexing identifies their sum-indexed formulas with the canonical finite-indexed moves.
Unimodular integral congruences preserve the polynomial because their determinants square
to one.

The theorem works on the ambient relation on matrices of arbitrary sizes. It therefore applies
to knot Seifert matrices without requiring their even-size or intersection-form conditions.
It is an algebraic invariance result: constructing a Seifert matrix from a knot and proving
that different Seifert surfaces give S-equivalent matrices are separate geometric questions.

The elementary calculations come from `TauCeti.KnotTheory.Alexander`; the equivalence closure
is `TauCeti.KnotTheory.IntegralSquareMatrix.SEquivalent`.

## Main result

* `TauCeti.KnotTheory.IntegralSquareMatrix.SEquivalent.alexander_eq`: S-equivalent integral
  matrices have equal normalized Alexander polynomials, even when their sizes differ.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997),
  Chapters 6 and 8 (Seifert matrices and S-equivalence).
-/

public section

open Matrix

namespace TauCeti.KnotTheory.IntegralSquareMatrix

/-- Every elementary S-equivalence move preserves the normalized Alexander polynomial. -/
theorem IsMove.alexander_eq {V W : IntegralSquareMatrix} (h : IsMove V W) :
    alexander V.2 = alexander W.2 := by
  cases h with
  | congr V P hP =>
      have hsq : P.det ^ 2 = 1 := by
        rcases Int.isUnit_eq_one_or hP with hdet | hdet <;> simp [hdet]
      exact (alexander_congruence_of_det_sq_eq_one V hsq).symm
  | enlargeColumn V xi =>
      simp only [enlargeColumnFin_def, alexander_submatrix_equiv_self,
        alexander_enlargeColumn]
  | enlargeRow V eta =>
      simp only [enlargeRowFin_def, alexander_submatrix_equiv_self,
        alexander_enlargeRow]

/-- **The normalized Alexander polynomial is invariant under S-equivalence.** This compares
matrices of possibly different sizes and uses equality, rather than association up to a
Laurent monomial unit. -/
theorem SEquivalent.alexander_eq {V W : IntegralSquareMatrix} (h : SEquivalent V W) :
    alexander V.2 = alexander W.2 := by
  apply Relation.EqvGen.eqvGen_le
    (r' := Setoid.ker fun X : IntegralSquareMatrix ↦ alexander X.2) ?_ V W h
  intro X Y hmove
  exact hmove.alexander_eq

end TauCeti.KnotTheory.IntegralSquareMatrix
