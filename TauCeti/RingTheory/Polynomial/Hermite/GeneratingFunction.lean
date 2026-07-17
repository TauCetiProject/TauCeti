module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The exponential generating function of the probabilists' Hermite polynomials

Mathlib defines `Polynomial.hermite` by the one-step recursion
`hermite (n + 1) = X * hermite n - derivative (hermite n)` and develops its coefficient and
derivative API, but it records nothing about the classical exponential generating function

  `∑' n, Hₙ(x) · tⁿ / n! = exp (x · t - t² / 2)`.

This file proves that identity (target **A1** of the `OrthogonalL2Bases` roadmap, listed in
`TauCetiRoadmap/OrthogonalL2Bases/README.md` and `Suggested.lean`). It is the analytic companion of
the algebraic Hermite recurrences: the generating function is the standard tool that packages the
whole family at once and, together with the weighted-orthogonality integral, drives the
orthogonal-polynomial completeness arguments the roadmap builds on.

## Proof outline

Fix `x : ℝ` and work with the entire function `f z = exp (x·z - z²/2)` on `ℂ`. A short induction on
`n`, using only the chain rule and the defining recursion `hermite (n + 1) = X · hermite n -
derivative (hermite n)`, evaluates its iterated derivatives in closed form,

  `iteratedDeriv n f z = aeval (x - z) (hermite n) · f z`,

so at the base point `z = 0` (where `f 0 = 1`) we get `iteratedDeriv n f 0 = Hₙ(x)`. Because `f` is
complex differentiable everywhere, Mathlib's `Complex.hasSum_taylorSeries_of_entire` says `f` equals
its Taylor series about `0` at every point; specializing to a real argument `t` and pushing the
resulting complex `HasSum` back down to `ℝ` yields the generating function.

The main statement is `TauCeti.hermite_generating_function`;
`TauCeti.hermite_generating_function_zero` records the `t = 0` boundary value `1`.
-/

public section

namespace TauCeti

open Polynomial Complex

/-- **Exponential generating function of the probabilists' Hermite polynomials.** For all real `x`
and `t`,
`∑' n, Hₙ(x) · tⁿ / n! = exp (x · t - t² / 2)`,
where `Hₙ = Polynomial.hermite n`. -/
theorem hermite_generating_function (x t : ℝ) :
    ∑' n : ℕ, aeval x (hermite n) * t ^ n / (n.factorial : ℝ)
      = Real.exp (x * t - t ^ 2 / 2) := by
  -- The entire function `f z = exp (x·z - z²/2)` on the complex plane.
  set f : ℂ → ℂ := fun z => Complex.exp ((x : ℂ) * z - z ^ 2 / 2) with hf_def
  -- Its derivative at every point: `f' z = f z · (x - z)`.
  have hu : ∀ z : ℂ, HasDerivAt (fun w : ℂ => (x : ℂ) * w - w ^ 2 / 2) ((x : ℂ) - z) z := by
    intro z
    have h1 : HasDerivAt (fun w : ℂ => (x : ℂ) * w) ((x : ℂ) * 1) z :=
      (hasDerivAt_id z).const_mul _
    have h2 := (hasDerivAt_pow 2 z).div_const (2 : ℂ)
    have hv : (x : ℂ) * 1 - ((2 : ℕ) : ℂ) * z ^ (2 - 1) / 2 = (x : ℂ) - z := by
      have he : (2 : ℕ) - 1 = 1 := rfl
      rw [he, pow_one]
      push_cast
      ring
    have h3 := h1.sub h2
    rw [hv] at h3
    exact h3
  have hderiv_f : ∀ z : ℂ, HasDerivAt f (f z * ((x : ℂ) - z)) z := by
    intro z
    rw [hf_def]
    exact (hu z).cexp
  have hf_diff : Differentiable ℂ f := by
    rw [hf_def]
    exact fun z => ((hu z).cexp).differentiableAt
  -- Closed form for the iterated derivatives, by induction on `n`.
  have key : ∀ (n : ℕ) (z : ℂ),
      iteratedDeriv n f z = aeval ((x : ℂ) - z) (hermite n) * f z := by
    intro n
    induction n with
    | zero => intro z; simp [iteratedDeriv_zero, hermite_zero]
    | succ n ih =>
      intro z
      have hfun : iteratedDeriv n f = fun z : ℂ => aeval ((x : ℂ) - z) (hermite n) * f z :=
        funext ih
      have hP : HasDerivAt (fun z : ℂ => aeval ((x : ℂ) - z) (hermite n))
          (-aeval ((x : ℂ) - z) (derivative (hermite n))) z := by
        have h1 : HasDerivAt (fun w : ℂ => (x : ℂ) - w) (-1) z := by
          simpa using (hasDerivAt_id z).const_sub (x : ℂ)
        have h3 := ((hermite n).hasDerivAt_aeval ((x : ℂ) - z)).comp z h1
        simpa [Function.comp_def, mul_neg_one] using h3
      have hHD : HasDerivAt (iteratedDeriv n f)
          (-aeval ((x : ℂ) - z) (derivative (hermite n)) * f z
            + aeval ((x : ℂ) - z) (hermite n) * (f z * ((x : ℂ) - z))) z := by
        rw [hfun]
        exact hP.mul (hderiv_f z)
      rw [iteratedDeriv_succ, hHD.deriv, hermite_succ]
      simp only [map_sub, map_mul, aeval_X]
      ring
  -- Evaluating at `z = 0` gives `iteratedDeriv n f 0 = Hₙ(x)`.
  have hval : ∀ n : ℕ, iteratedDeriv n f 0 = aeval ((x : ℂ)) (hermite n) := by
    intro n
    rw [key n 0]
    simp [hf_def]
  -- Compatibility of `aeval` with the coercion `ℝ → ℂ`.
  have hcast_aeval : ∀ n : ℕ, ((aeval x (hermite n) : ℝ) : ℂ) = aeval ((x : ℂ)) (hermite n) := by
    intro n
    have h : (algebraMap ℤ ℂ).comp (RingHom.id ℤ) = (algebraMap ℝ ℂ).comp (algebraMap ℤ ℝ) := by
      ext k; simp
    simpa [Polynomial.map_id, Complex.coe_algebraMap] using
      map_aeval_eq_aeval_map h (hermite n) x
  -- The `n`-th Taylor term equals the real generating-function term, cast to `ℂ`.
  have hcast : ∀ n : ℕ,
      (n.factorial : ℂ)⁻¹ • ((t : ℂ) - 0) ^ n • iteratedDeriv n f 0
        = ((aeval x (hermite n) * t ^ n / (n.factorial : ℝ) : ℝ) : ℂ) := by
    intro n
    rw [hval n, ← hcast_aeval n]
    simp only [sub_zero, smul_eq_mul]
    push_cast
    ring
  -- The value of `f` at a real point is the real exponential, cast to `ℂ`.
  have hft : f ((t : ℂ)) = ((Real.exp (x * t - t ^ 2 / 2) : ℝ) : ℂ) := by
    simp only [hf_def, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  -- `f` equals its Taylor series about `0`; specialize at the real argument `t`.
  have htaylor := hasSum_taylorSeries_of_entire hf_diff 0 (t : ℂ)
  have hfun_eq :
      (fun n : ℕ => (n.factorial : ℂ)⁻¹ • ((t : ℂ) - 0) ^ n • iteratedDeriv n f 0)
        = fun n : ℕ => ((aeval x (hermite n) * t ^ n / (n.factorial : ℝ) : ℝ) : ℂ) :=
    funext hcast
  rw [hfun_eq, hft] at htaylor
  exact (Complex.hasSum_ofReal.mp htaylor).tsum_eq

/-- The Hermite generating function at `t = 0` collapses to `1` (only the `n = 0` term survives). -/
theorem hermite_generating_function_zero (x : ℝ) :
    ∑' n : ℕ, aeval x (hermite n) * (0 : ℝ) ^ n / (n.factorial : ℝ) = 1 := by
  rw [hermite_generating_function x 0]
  simp

end TauCeti
