/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import TauCeti.Algebra.Polynomial.Derivative

/-!
# Polynomials over discrete valuation rings

For a polynomial `f` with unit leading coefficient over a discrete valuation ring `A`, the
additive valuation of the `(f.natDegree - 1)`-th coefficient of `f.derivative` equals the
additive valuation of `f.natDegree`.
-/

public section

namespace Polynomial

open IsDiscreteValuationRing

/-- For a polynomial `f` with unit leading coefficient over a discrete valuation ring `A`, the
additive valuation of the `(f.natDegree - 1)`-th coefficient of `f.derivative` equals
`addVal A (f.natDegree : A)`. -/
theorem addVal_coeff_derivative_natDegree_sub_one_of_isUnit_leadingCoeff
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (f : A[X]) (hu : IsUnit f.leadingCoeff) :
    addVal A ((derivative f).coeff (f.natDegree - 1)) = addVal A (f.natDegree : A) := by
  rw [coeff_derivative_natDegree_sub_one, addVal_mul, (addVal_eq_zero_iff).mpr hu, zero_add]

end Polynomial
