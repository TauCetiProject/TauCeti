/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# The exponential generating function of the probabilists' Hermite polynomials

Mathlib defines `Polynomial.hermite` by the one-step recursion
`hermite (n + 1) = X * hermite n - derivative (hermite n)` and develops its coefficient and
derivative API. This file proves the classical exponential generating function

  `∑' n, Hₙ(x) · tⁿ / n! = exp (x · t - t² / 2)`,

which packages the whole family at once and is the standard tool for orthogonality and
completeness arguments for the Hermite functions.

## Main statements

* `Polynomial.hasSum_hermite_generating_function`: for complex `x` and `t`, the series
  `∑ Hₙ(x) · tⁿ / n!` converges to `exp (x · t - t² / 2)` (`HasSum` form).
* `Polynomial.hermite_generating_function`: the real `tsum` form, obtained by casting `ℝ → ℂ`.

## Proof outline

Fix `x : ℂ` and work with the entire function `f z = exp (x·z - z²/2)` on `ℂ`. An induction on
`n`, using only the chain rule and the defining recursion of `hermite`, evaluates its iterated
derivatives in closed form,

  `iteratedDeriv n f z = aeval (x - z) (hermite n) · f z`,

so `iteratedDeriv n f 0 = Hₙ(x)`. Since `f` is entire, `Complex.hasSum_taylorSeries_of_entire`
says `f` equals its Taylor series about `0` at every point, which is the generating function
identity at an arbitrary complex `t`.

## References

* [Mathlib PR #42724](https://github.com/leanprover-community/mathlib4/pull/42724)
  (Kim Morrison), an upstream adaptation of this file and of `Derivative.lean`; the
  `Polynomial`-namespace names here (after `Polynomial.bernoulli_generating_function`) follow it.
-/

public section

namespace TauCeti

open Polynomial Complex
open scoped Nat

/-- Derivative of the entire function `z ↦ exp (x·z - z²/2)`: its value at `z` times `x - z`. -/
private theorem hasDerivAt_cexp_quadratic (x z : ℂ) :
    HasDerivAt (fun w : ℂ => cexp (x * w - w ^ 2 / 2)) (cexp (x * z - z ^ 2 / 2) * (x - z)) z :=
  (((hasDerivAt_id' z).const_mul x).sub ((hasDerivAt_pow 2 z).div_const 2)).cexp.congr_deriv
    (by norm_num)

/-- Closed form for the iterated derivatives of `z ↦ exp (x·z - z²/2)`: the `n`-th derivative at
`z` is `Hₙ(x - z)` times the function value. -/
private theorem iteratedDeriv_cexp_quadratic (x : ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w : ℂ => cexp (x * w - w ^ 2 / 2)) z
      = aeval (x - z) (hermite n) * cexp (x * z - z ^ 2 / 2) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    have hP := ((hermite n).hasDerivAt_aeval (x - z)).comp z ((hasDerivAt_id' z).const_sub x)
    rw [iteratedDeriv_succ, funext ih]
    refine (hP.mul (hasDerivAt_cexp_quadratic x z)).deriv.trans ?_
    simp only [Function.comp_apply, hermite_succ, map_sub, map_mul, aeval_X]
    ring

/-- **Exponential generating function of the probabilists' Hermite polynomials, summable form.**
For all complex `x` and `t`, the family `Hₙ(x) · tⁿ / n!` is summable with sum
`exp (x · t - t² / 2)`, where `Hₙ = Polynomial.hermite n`. -/
theorem _root_.Polynomial.hasSum_hermite_generating_function (x t : ℂ) :
    HasSum (fun n : ℕ => aeval x (hermite n) * t ^ n / n !) (cexp (x * t - t ^ 2 / 2)) := by
  have hf : Differentiable ℂ fun z : ℂ => cexp (x * z - z ^ 2 / 2) := by fun_prop
  convert hasSum_taylorSeries_of_entire hf 0 t using 2 with n
  simp [iteratedDeriv_cexp_quadratic]
  ring

/-- **Exponential generating function of the probabilists' Hermite polynomials.** For all real `x`
and `t`,
`∑' n, Hₙ(x) · tⁿ / n! = exp (x · t - t² / 2)`,
where `Hₙ = Polynomial.hermite n`. This is the real specialization of
`hasSum_hermite_generating_function`. -/
theorem _root_.Polynomial.hermite_generating_function (x t : ℝ) :
    ∑' n : ℕ, aeval x (hermite n) * t ^ n / n ! = Real.exp (x * t - t ^ 2 / 2) := by
  refine (Complex.hasSum_ofReal.mp ?_).tsum_eq
  convert hasSum_hermite_generating_function x t using 1
  · ext n
    push_cast
    congr 2
    exact (aeval_algHom_apply (Complex.ofRealAm.restrictScalars ℤ) x (hermite n)).symm
  · simp

end TauCeti
