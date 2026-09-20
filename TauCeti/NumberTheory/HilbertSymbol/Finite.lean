/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Finite.Quadratic
public import TauCeti.NumberTheory.HilbertSymbol.Basic

/-!
# The Hilbert symbol over a finite field

This file computes the norm-equation Hilbert symbol `TauCeti.hilbertSymbol` over a finite field:
it is always `1`, by the universality of the binary form `x ^ 2 - a * y ^ 2` proved in
`TauCeti.FieldTheory.Finite.Quadratic`.

The statement is the residue-field input for the computation of the symbol of two units of a
nonarchimedean local field away from residue characteristic two, where a solution modulo the
maximal ideal is lifted by Hensel's lemma.

## Main results

* `TauCeti.hilbertSymbol_eq_one_of_finite`: the symbol is trivial over a finite field.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter I, §2, Proposition 5.
* O. T. O'Meara, *Introduction to Quadratic Forms*, 62:1b.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [Finite K]

/-- Over a finite field the Hilbert symbol is always `1`. -/
@[simp]
theorem hilbertSymbol_eq_one_of_finite (a b : Kˣ) : hilbertSymbol a b = 1 :=
  (hilbertSymbol_eq_one_iff a b).mpr (exists_eq_sq_sub_mul_sq_of_finite a.ne_zero (b : K))

end TauCeti
