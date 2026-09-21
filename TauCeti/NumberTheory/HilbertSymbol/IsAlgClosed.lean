/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.NumberTheory.HilbertSymbol.Basic

/-!
# The Hilbert symbol over algebraically closed fields

This file computes the norm-equation Hilbert symbol `TauCeti.hilbertSymbol` over algebraically
closed fields. Every element is a square, so the symbol is always `1`.

## Main results

* `TauCeti.hilbertSymbol_eq_one_of_isAlgClosed`: the symbol is trivial over an algebraically closed
  field.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.1.
* O. T. O'Meara, *Introduction to Quadratic Forms*, 71:18.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field, such as `ℂ`, the Hilbert symbol is always `1`. -/
@[simp]
theorem hilbertSymbol_eq_one_of_isAlgClosed (a b : Kˣ) : hilbertSymbol a b = 1 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (b : K)
  exact (hilbertSymbol_eq_one_iff a b).mpr ⟨z, 0, by rw [hz]; ring⟩

end TauCeti
