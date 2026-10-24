/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Real iterated derivatives of the complex exponential

Mathlib records that every complex derivative of `exp : ℂ → ℂ` is `exp` itself
(`Complex.iter_deriv_exp`). Faà di Bruno estimates for a composite `exp ∘ q` with
`q : E → ℂ` defined on a real normed space need the derivatives of `exp` as a function of a real
variable, that is, its iterated Fréchet derivatives over `ℝ`. This file records that they have
the same norm `‖exp z‖`, since a real iterated derivative of a complex-differentiable function is
the restriction of scalars of the complex one.

## Main declarations

* `Complex.norm_iteratedFDeriv_real_exp`: `‖iteratedFDeriv ℝ n exp z‖ = ‖exp z‖`.
-/

public section

namespace Complex

/-- Every real iterated Fréchet derivative of `exp : ℂ → ℂ` at `z` has norm `‖exp z‖`. -/
@[simp]
theorem norm_iteratedFDeriv_real_exp (n : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ n exp z‖ = ‖exp z‖ := by
  rw [← (contDiff_exp (𝕜 := ℂ) (n := n)).contDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_exp]

end Complex
