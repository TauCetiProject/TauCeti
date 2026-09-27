/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Weight.Enumerator

/-!
# MacWilliams checks for the zero and whole-space codes

The zero code has weight enumerator `X^n`, whereas the whole space over a finite semiring of
cardinality `q` has enumerator `(X + (q - 1)Y)^n`. Substituting the MacWilliams variables
interchanges these two polynomials, with the factor `q^n` in the whole-space case. These
calculations check the division-free MacWilliams identity at both extremal codes, including
the empty coordinate type.

The general MacWilliams theorem is in `TauCeti.InformationTheory.Coding.MacWilliams.Basic`.
The enumerator of the whole space is `TauCeti.weightEnumerator_univ`.

Reference: F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting Codes*,
Chapter 5, §2.
-/

public section

namespace TauCeti

open MvPolynomial

variable {R ι : Type*} [Semiring R] [DecidableEq R] [Fintype ι]

variable [Finite R]

/-- The MacWilliams substitution sends the enumerator of the zero code to that of the
whole word space. -/
theorem aeval_weightEnumerator_bot :
    aeval ![X 0 + (Nat.card R - 1 : MvPolynomial (Fin 2) ℤ) * X 1, X 0 - X 1]
        ((⊥ : Submodule R (ι → R)) : Set (ι → R)).weightEnumerator =
      ((⊤ : Submodule R (ι → R)) : Set (ι → R)).weightEnumerator := by
  rw [weightEnumerator_bot, Submodule.top_coe, weightEnumerator_univ]
  simp

/-- The MacWilliams substitution sends the whole-space enumerator to `q^n` times the
zero-code enumerator. -/
theorem aeval_weightEnumerator_top :
    aeval ![X 0 + (Nat.card R - 1 : MvPolynomial (Fin 2) ℤ) * X 1, X 0 - X 1]
        ((⊤ : Submodule R (ι → R)) : Set (ι → R)).weightEnumerator =
      (Nat.card R : MvPolynomial (Fin 2) ℤ) ^ Fintype.card ι *
        ((⊥ : Submodule R (ι → R)) : Set (ι → R)).weightEnumerator := by
  rw [Submodule.top_coe, weightEnumerator_univ, weightEnumerator_bot]
  simp only [map_pow, map_add, map_mul, map_sub, aeval_X, map_natCast, map_one,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hsub : (X 0 + ((Nat.card R : MvPolynomial (Fin 2) ℤ) - 1) * X 1) +
      ((Nat.card R : MvPolynomial (Fin 2) ℤ) - 1) * (X 0 - X 1) =
      (Nat.card R : MvPolynomial (Fin 2) ℤ) * X 0 := by ring
  rw [hsub, mul_pow]

end TauCeti
