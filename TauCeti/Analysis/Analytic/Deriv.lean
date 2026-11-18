/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# First and second derivatives of `p · (F ∘ φ)` for analytic data

For functions `p`, `φ`, `F` of one variable over a complete nontrivially normed field, with `p`
and `φ` analytic at `z` and `F` analytic at `φ z`, the product and chain rules give

`(p · (F ∘ φ))′ = p′ · (F ∘ φ) + p · (F′ ∘ φ) · φ′`

on a neighbourhood of `z`, and hence

`(p · (F ∘ φ))′′ = p′′ · (F ∘ φ) + 2 p′ · (F′ ∘ φ) · φ′ + p · ((F′′ ∘ φ) · φ′ ^ 2 + (F′ ∘ φ) · φ′′)`

at `z`. These are the formulas used to transform a linear second-order differential equation
under a change of dependent variable `w = p · u` combined with a change of independent variable
`ζ = φ(z)`, as in the passage from the hypergeometric equation to Riemann's equation.

## Main results

* `AnalyticAt.deriv_mul_comp_eventuallyEq`: the first derivative, on a neighbourhood.
* `AnalyticAt.deriv_deriv_mul_comp`: the second derivative at the point.
-/

public section

open Filter Topology

namespace AnalyticAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {p φ F : 𝕜 → 𝕜} {z : 𝕜}

/-- The derivative of `p · (F ∘ φ)` near a point `z` where `p` and `φ` are analytic and `F` is
analytic at `φ z`: it agrees on a neighbourhood of `z` with `p′ · (F ∘ φ) + p · (F′ ∘ φ) · φ′`. -/
theorem deriv_mul_comp_eventuallyEq (hp : AnalyticAt 𝕜 p z) (hφ : AnalyticAt 𝕜 φ z)
    (hF : AnalyticAt 𝕜 F (φ z)) :
    deriv (fun w => p w * F (φ w)) =ᶠ[𝓝 z]
      fun w => deriv p w * F (φ w) + p w * (deriv F (φ w) * deriv φ w) := by
  filter_upwards [hp.eventually_analyticAt, hφ.eventually_analyticAt,
    hφ.continuousAt.tendsto.eventually hF.eventually_analyticAt] with w h1 h2 h3
  exact (h1.differentiableAt.hasDerivAt.mul
    (h3.differentiableAt.hasDerivAt.comp w h2.differentiableAt.hasDerivAt)).deriv

/-- The second derivative of `p · (F ∘ φ)` at a point `z` where `p` and `φ` are analytic and `F`
is analytic at `φ z`:
`p′′ · F(φ) + 2 p′ · F′(φ) · φ′ + p · (F′′(φ) · φ′ ^ 2 + F′(φ) · φ′′)`. -/
theorem deriv_deriv_mul_comp (hp : AnalyticAt 𝕜 p z) (hφ : AnalyticAt 𝕜 φ z)
    (hF : AnalyticAt 𝕜 F (φ z)) :
    deriv (deriv (fun w => p w * F (φ w))) z =
      deriv (deriv p) z * F (φ z) + 2 * deriv p z * (deriv F (φ z) * deriv φ z) +
        p z * (deriv (deriv F) (φ z) * deriv φ z ^ 2 + deriv F (φ z) * deriv (deriv φ) z) := by
  rw [(hp.deriv_mul_comp_eventuallyEq hφ hF).deriv_eq]
  -- Differentiate the first-derivative formula once more, term by term.
  have hFφ := hF.differentiableAt.hasDerivAt.comp z hφ.differentiableAt.hasDerivAt
  have hF'φ := hF.deriv.differentiableAt.hasDerivAt.comp z hφ.differentiableAt.hasDerivAt
  have h := (hp.deriv.differentiableAt.hasDerivAt.mul hFφ).add
    (hp.differentiableAt.hasDerivAt.mul (hF'φ.mul hφ.deriv.differentiableAt.hasDerivAt))
  refine h.deriv.trans ?_
  simp only [Function.comp_apply, Pi.mul_apply]
  ring

end AnalyticAt
