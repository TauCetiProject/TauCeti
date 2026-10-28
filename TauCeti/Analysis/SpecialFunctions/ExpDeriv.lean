/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-!
# Real iterated derivatives of the complex exponential

Viewed as a function of a real vector variable, `Complex.exp` has the same iterated derivatives
as it has over `ℂ`, restricted to real scalars. Since every complex derivative of `exp` is `exp`,
every real iterated derivative of `Complex.exp` at `z` has norm `‖exp z‖`. This is the input a
Faà di Bruno bound needs for compositions `Complex.exp ∘ f` with a real-differentiable `f`.

## Main results

* `TauCeti.norm_iteratedFDeriv_real_cexp`: every real iterated derivative of `Complex.exp` at `z`
  has norm `‖exp z‖`.
-/

public section

namespace TauCeti

/-- Every real iterated derivative of the complex exponential at `z` has norm `‖exp z‖`. -/
theorem norm_iteratedFDeriv_real_cexp (n : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ n Complex.exp z‖ = ‖Complex.exp z‖ := by
  rw [← ((Complex.contDiff_exp (𝕜 := ℂ) (n := n)).contDiffAt).restrictScalars_iteratedFDeriv
      (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]

end TauCeti
