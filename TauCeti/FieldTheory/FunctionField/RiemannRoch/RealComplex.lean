/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Basic

/-!
# The constants of `ℂ(x)` over `ℝ`

The rational function field `ℂ(x)` is a function field over `ℝ`, but its full constant field is
`ℂ`. Consequently its zero-divisor Riemann–Roch space has real dimension two. This concrete
example shows why the equality `ℓ(0) = 1` requires the exact-constants hypothesis.
-/

public section

namespace TauCeti

open AlgebraicGeometry

namespace Divisor

/-- The zero-divisor Riemann–Roch space of `ℂ(x)` has real dimension two. -/
@[simp]
theorem dim_zero_real_ratFunc_complex :
    dim (0 : Divisor ℝ (RatFunc ℂ)) = 2 := by
  have hF : IsFunctionField ℝ (RatFunc ℂ) :=
    (IsFunctionField.ratFunc ℂ).of_finiteDimensional
  rw [dim_zero_eq_finrank_of_isIntegrallyClosedIn hF (IsFunctionField.ratFunc ℂ)
    isIntegrallyClosedIn_ratFunc, Complex.finrank_real_complex]

end Divisor

end TauCeti
