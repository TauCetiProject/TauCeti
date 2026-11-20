/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The logarithmic derivative of a complex exponential

The logarithmic derivative of `x ↦ exp (L x)` is `deriv L`, and multiplying a function `g` by
`exp ∘ L` adds `deriv L` to its logarithmic derivative wherever `g` is nonzero. This is the shape
in which an exponential factor `exp (a + b z)` enters a Weierstrass or Hadamard factorization.
The variable ranges over any nontrivially normed field `𝕜` over which `ℂ` is a normed algebra.

## Main results

* `TauCeti.logDeriv_cexp`: `logDeriv (fun x ↦ exp (L x)) x = deriv L x`.
* `TauCeti.logDeriv_mul_cexp`: `logDeriv (fun x ↦ g x * exp (L x)) x = logDeriv g x + deriv L x`.
* `TauCeti.logDeriv_cexp_mul`: `logDeriv (fun x ↦ exp (L x) * g x) x = deriv L x + logDeriv g x`.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {g L : 𝕜 → ℂ} {x : 𝕜}

/-- The logarithmic derivative of `exp ∘ L` is the derivative of `L`. -/
theorem logDeriv_cexp (hL : DifferentiableAt 𝕜 L x) :
    logDeriv (fun y ↦ Complex.exp (L y)) x = deriv L x := by
  rw [logDeriv_apply, deriv_cexp hL, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]

/-- Multiplying by `exp ∘ L` adds the derivative of `L` to the logarithmic derivative. -/
theorem logDeriv_mul_cexp (hgx : g x ≠ 0) (hg : DifferentiableAt 𝕜 g x)
    (hL : DifferentiableAt 𝕜 L x) :
    logDeriv (fun y ↦ g y * Complex.exp (L y)) x = logDeriv g x + deriv L x := by
  rw [logDeriv_fun_mul x hgx (Complex.exp_ne_zero _) hg hL.cexp, logDeriv_cexp hL]

/-- Multiplying by `exp ∘ L` on the left adds the derivative of `L` to the logarithmic
derivative. -/
theorem logDeriv_cexp_mul (hgx : g x ≠ 0) (hg : DifferentiableAt 𝕜 g x)
    (hL : DifferentiableAt 𝕜 L x) :
    logDeriv (fun y ↦ Complex.exp (L y) * g y) x = deriv L x + logDeriv g x := by
  rw [logDeriv_fun_mul x (Complex.exp_ne_zero _) hgx hL.cexp hg, logDeriv_cexp hL]

end TauCeti
