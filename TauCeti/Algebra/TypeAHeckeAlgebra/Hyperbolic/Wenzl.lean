/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam.Analytic
import TauCeti.Analysis.SpecialFunctions.Hyperbolic

/-!
# Wenzl's balanced-projection convention in hyperbolic parameters

In `TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Basic`, at the Hecke parameter `q = exp (-θ)` and
rescaled braid generators `γ i = I * exp (-α) • T i`, the positive and negative stabilization
constants of a Markov trace with native projection parameter `η` agree (for `cosh α * cosh θ ≠ 0`)
if and only if

`η = (1 - tanh α * tanh θ) / 2` (`TauCeti.hyperbolicProjParam`),

while Wenzl's complementary projection convention `e_i^W = 1 - P_i`
(`TauCeti.BalancedProjectionAlgebra.wenzlHeckeEquiv`) assigns to the same Markov trace the
projection parameter

`η_W = 1 - η = (1 + tanh α * tanh θ) / 2` (`TauCeti.hyperbolicWenzlProjParam`).

This file establishes the balanced-projection compatibility and Wenzl's projection rule in
hyperbolic parameters `q = exp (-θ)`, `Q = q ^ 2 = exp (-2 * θ)`. The exceptional discrete line
dictionary is in `TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.ExceptionalLine`.

## Main results

* `TauCeti.wenzlParam_neg_two_mul_hyperbolicHeckeParam_add_inv_sq` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_mul_hyperbolic_wenzlProjection`:
  balanced-projection compatibility and Wenzl's projection rule in hyperbolic parameters.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§5–6, 11.
-/

public section

open Complex

namespace TauCeti

/-! ### Wenzl's projection convention in hyperbolic parameters -/

/-- When `cosh θ ≠ 0`, the Jones parameter `a_(-2)(exp (-2 * θ))` satisfies the balanced-projection
compatibility `τ * (q + q⁻¹) ^ 2 = 1` for `q = hyperbolicHeckeParam θ`. -/
theorem wenzlParam_neg_two_mul_hyperbolicHeckeParam_add_inv_sq {θ : ℂ} (hθ : cosh θ ≠ 0) :
    wenzlParam (-2) (exp (-2 * θ)) *
      ((hyperbolicHeckeParam θ : ℂ) + ↑(hyperbolicHeckeParam θ)⁻¹) ^ 2 = 1 := by
  have hsum : (hyperbolicHeckeParam θ : ℂ) + ↑(hyperbolicHeckeParam θ)⁻¹ = 2 * cosh θ := by
    rw [val_hyperbolicHeckeParam, val_inv_hyperbolicHeckeParam, two_cosh, add_comm]
  have hne : ((hyperbolicHeckeParam θ : ℂ) + ↑(hyperbolicHeckeParam θ)⁻¹) ^ 2 ≠ 0 := by
    rw [hsum]
    exact pow_ne_zero 2 (mul_ne_zero two_ne_zero hθ)
  rw [← val_hyperbolicHeckeParam_sq, wenzlParam_neg_two_sq, Units.val_inv_eq_inv_val]
  exact inv_mul_cancel₀ (by simpa only [Units.val_inv_eq_inv_val] using hne)

namespace InfiniteTypeAHeckeAlgebra

variable {θ z ηW : ℂ} {τ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ) →ₗ[ℂ] ℂ}

/-- **Wenzl's projection rule in hyperbolic parameters.** When `cosh θ ≠ 0` and
`z = exp (-θ) * (1 - η_W) - exp θ * η_W`, appending Wenzl's projection
`(1 + exp (-2 * θ))⁻¹ • (exp (-2 * θ) - exp (-θ) • T n)` to `x` in the stage on `n + 1` strands
multiplies a Markov trace `τ` by `η_W`. -/
theorem IsMarkovTrace.map_mul_hyperbolic_wenzlProjection (hτ : IsMarkovTrace z τ)
    (hθ : cosh θ ≠ 0) (hz : z = exp (-θ) * (1 - ηW) - exp θ * ηW) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ)}
    (hx : x ∈ stage ℂ (hyperbolicHeckeParam θ) (n + 1)) :
    τ (x * (1 + exp (-2 * θ))⁻¹ • (algebraMap ℂ _ (exp (-2 * θ)) - exp (-θ) • T _ n)) =
      ηW * τ x := by
  have hu0 : 1 + exp (-2 * θ) ≠ 0 := by
    rw [neg_mul, ← mul_neg, one_add_exp_two_mul, cosh_neg]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hθ) (exp_ne_zero _)
  have h := hτ.map_mul_wenzlProjection (Units.mk0 (1 + exp (-2 * θ)) hu0)
    (by rw [Units.val_mk0, val_hyperbolicHeckeParam_sq]) (η := 1 - ηW)
    (by rw [val_hyperbolicHeckeParam, val_inv_hyperbolicHeckeParam, sub_sub_cancel, hz]) hx
  rw [val_hyperbolicHeckeParam_sq] at h
  simpa only [Units.val_inv_eq_inv_val, Units.val_mk0, val_hyperbolicHeckeParam,
    sub_sub_cancel] using h

end InfiniteTypeAHeckeAlgebra

end TauCeti
