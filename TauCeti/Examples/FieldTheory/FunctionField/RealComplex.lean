/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.FieldTheory.FunctionField.RiemannRoch.RealComplex
import TauCeti.RingTheory.TensorProduct.Complex

/-!
# Extending function-field constants can introduce zero divisors

The field `ℂ(x)` is a function field over `ℝ`, but its real constants are not exact:
its zero-divisor Riemann–Roch space has real dimension two. The real tensor product
`ℂ ⊗[ℝ] ℂ(x)` has zero divisors, so extending constants cannot in general be implemented
by putting a field structure on the raw tensor product.

These checks connect the explicit tensor-product zero divisors with the intrinsic
function-field predicate and the existing real/complex Riemann–Roch computation.
For the role of exact constants in constant extensions, see Stichtenoth,
*Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

open TauCeti TensorProduct

example : IsFunctionField ℝ (RatFunc ℂ) :=
  (IsFunctionField.ratFunc ℂ).of_finiteDimensional

example : ¬ IsIntegrallyClosedIn ℝ (RatFunc ℂ) := by
  intro h
  have hdim := Divisor.dim_zero_of_isIntegrallyClosedIn
    ((IsFunctionField.ratFunc ℂ).of_finiteDimensional (k := ℝ)) h
  rw [Divisor.dim_zero_real_ratFunc_complex] at hdim
  norm_num at hdim

-- Use the module from the existing real algebra structure in the tensor product.
attribute [local instance high] Algebra.toModule

example : ¬ IsDomain (ℂ ⊗[ℝ] RatFunc ℂ) :=
  not_isDomain_complex_tensorProduct (RatFunc ℂ)
