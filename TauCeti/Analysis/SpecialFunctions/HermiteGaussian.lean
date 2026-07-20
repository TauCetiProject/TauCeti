/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.Analysis.SpecialFunctions.GaussianPolynomialIntegrable
public import TauCeti.RingTheory.Polynomial.Hermite.Derivative
public import TauCeti.RingTheory.Polynomial.Hermite.Real

/-!
# Gaussian orthogonality integrals for the Hermite polynomials

This file proves the analytic A1 inputs for the probabilists' Hermite polynomials
`Polynomial.hermite` with respect to the Gaussian weight `e^{-x²/2}`:
`∫ Hₘ(x)·Hₙ(x)·e^{-x²/2} dx = if m = n then n!·√(2π) else 0`.
These are the integral identities and calculus steps consumed by the downstream
`OrthogonalL2Bases` Hilbert-basis construction; this file does not construct that L² basis or the
measure-space bridge itself.

## Main results

* `Polynomial.hermiteℝ`, with simp lemmas `Polynomial.eval_hermiteℝ` and
  `Polynomial.aeval_hermiteℝ` : the real-polynomial realization of `Polynomial.hermite`,
  characterized without unfolding.
* `Polynomial.integrable_aeval_mul_gaussian` : any integer polynomial is integrable against
  the Gaussian weight `e^{-x²/2}`.
* `TauCeti.Hermite.integral_hermite_mul_hermite_mul_gaussian` : the orthogonality relation
  `∫ Hₘ·Hₙ·e^{-x²/2} = if m = n then n!·√(2π) else 0`.
* `TauCeti.Hermite.integral_hermite_mul_hermite_mul_gaussianPDFReal` : the same relation against
  the standard Gaussian density, in `aeval` form.
* `TauCeti.Hermite.integral_hermite_mul_hermite_gaussianReal` : the same relation against the
  standard Gaussian **measure**, `∫ Hₘ·Hₙ ∂N(0,1) = if m = n then n! else 0`;
  this is the canonical A1 form named by the roadmap.
* `TauCeti.Hermite.integral_hermiteℝ_mul_hermiteℝ_mul_gaussianPDFReal` : the
  bridge-shaped density form
  `∫ (hermiteℝ m).eval x * (hermiteℝ n).eval x * gaussianPDFReal 0 1 x`
  with value `if m = n then n! else 0`.

## Implementation notes

The Mathlib `Polynomial.hermite` lives in `ℤ[X]`; we evaluate it in `ℝ` via `aeval`. The auxiliary
`Polynomial.hermiteℝ` is its image in `ℝ[X]`, used to combine two factors into a single polynomial
for integrability. The generic polynomial-times-Gaussian integrability lemmas live in
`TauCeti.Analysis.SpecialFunctions.GaussianPolynomialIntegrable`. The boundary-term-free
integration by parts over `ℝ` is
`MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`, whose hypotheses are met because
polynomials times the Gaussian are integrable and the weight kills the boundary contributions.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Polynomial
open scoped Nat NNReal

namespace TauCeti.Hermite

/-- A real polynomial times a Hermite polynomial is integrable against the Gaussian weight. -/
private theorem integrable_aeval_mul_hermite_mul_gaussian (p : ℝ[X]) (m : ℕ) :
    Integrable
      (fun x : ℝ => aeval x p * aeval x (hermite m) * Real.exp (-(x ^ 2 / 2))) := by
  have h := Polynomial.integrable_eval_mul_gaussian (p * hermiteℝ m)
  refine h.congr ?_
  filter_upwards with x
  simp only [eval_mul, eval_hermiteℝ, coe_aeval_eq_eval]

/-- Rodrigues derivative for the probabilists' Hermite polynomials with Gaussian weight: the
derivative of `Hₙ(x)·e^{-x²/2}` is `-Hₙ₊₁(x)·e^{-x²/2}`. -/
private theorem hasDerivAt_hermite_mul_gaussian (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => aeval y (hermite n) * Real.exp (-(y ^ 2 / 2)))
      (-(aeval x (hermite (n + 1)) * Real.exp (-(x ^ 2 / 2)))) x := by
  have hH : HasDerivAt (fun y => aeval y (hermite n)) (aeval x (derivative (hermite n))) x :=
    (hermite n).hasDerivAt_aeval x
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    have h := (hasDerivAt_pow 2 x).div_const 2
    norm_num at h
    exact h
  have hin : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x := h1.neg
  have hg : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))
      (Real.exp (-(x ^ 2 / 2)) * -x) x := (Real.hasDerivAt_exp _).comp x hin
  have hmul := hH.mul hg
  have hD : -(aeval x (hermite (n + 1)) * Real.exp (-(x ^ 2 / 2)))
      = aeval x (derivative (hermite n)) * Real.exp (-(x ^ 2 / 2))
        + aeval x (hermite n) * (Real.exp (-(x ^ 2 / 2)) * -x) := by
    rw [hermite_succ]
    simp only [map_sub, map_mul, aeval_X]
    ring
  rw [hD]
  exact hmul

/-- One-step weighted-pairing recursion for Hermite polynomials: integration by parts with the
Rodrigues derivative gives `∫ p·Hₙ₊₁·w = ∫ p'·Hₙ·w` for `w(x) = e^{-x²/2}`. -/
private theorem integral_aeval_mul_hermite_succ (p : ℝ[X]) (n : ℕ) :
    ∫ x, aeval x p * aeval x (hermite (n + 1)) * Real.exp (-(x ^ 2 / 2))
      = ∫ x, aeval x (derivative p) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)) := by
  have key := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x => aeval x p) (u' := fun x => aeval x (derivative p))
    (v := fun y => aeval y (hermite n) * Real.exp (-(y ^ 2 / 2)))
    (v' := fun x => -(aeval x (hermite (n + 1)) * Real.exp (-(x ^ 2 / 2))))
    (fun x _ => p.hasDerivAt_aeval x)
    (fun x _ => hasDerivAt_hermite_mul_gaussian n x)
    (by
      have := (integrable_aeval_mul_hermite_mul_gaussian p (n + 1)).neg
      refine this.congr ?_; filter_upwards with x; simp only [Pi.mul_apply, Pi.neg_apply]; ring)
    (by
      have := integrable_aeval_mul_hermite_mul_gaussian (derivative p) n
      refine this.congr ?_; filter_upwards with x; simp only [Pi.mul_apply]; ring)
    (by
      have := integrable_aeval_mul_hermite_mul_gaussian p n
      refine this.congr ?_; filter_upwards with x; simp only [Pi.mul_apply]; ring)
  simp only [mul_neg] at key
  rw [integral_neg, neg_inj] at key
  simp_rw [mul_assoc]
  exact key

/-- Iterating the recursion: `∫ p·Hₙ·w = ∫ (p^{(n)})·w`; the right Hermite factor is
consumed. -/
private theorem integral_aeval_mul_hermite (p : ℝ[X]) (n : ℕ) :
    ∫ x, aeval x p * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))
      = ∫ x, aeval x (derivative^[n] p) * Real.exp (-(x ^ 2 / 2)) := by
  induction n generalizing p with
  | zero =>
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [hermite_zero]
  | succ n ih =>
    rw [integral_aeval_mul_hermite_succ p n, ih (derivative p), Function.iterate_succ_apply]

/-- The Gaussian integral with the `e^{-x²/2}` normalisation: `∫ e^{-x²/2} = √(2π)`. -/
private theorem integral_gaussian_half :
    ∫ x : ℝ, Real.exp (-(x ^ 2 / 2)) = Real.sqrt (2 * π) := by
  -- `integral_gaussian` expects the coefficient form `-(1 / 2) * x ^ 2`; isolate the
  -- real arithmetic rewrites so the normalization step is explicit.
  have h_exp : ∀ x : ℝ, -(x ^ 2 / 2) = -(1 / 2) * x ^ 2 := by
    intro x
    ring
  have h_const : (π : ℝ) / (1 / 2) = 2 * π := by
    ring
  have h : ∫ x : ℝ, Real.exp (-(x ^ 2 / 2)) = ∫ x : ℝ, Real.exp (-(1 / 2) * x ^ 2) := by
    congr 1
    funext x
    rw [h_exp x]
  rw [h, integral_gaussian, h_const]

/-- Off-diagonal vanishing: if `m < n` then `∫ Hₘ·Hₙ·e^{-x²/2} = 0`. -/
private theorem integral_hermite_mul_hermite_mul_gaussian_of_lt {m n : ℕ} (h : m < n) :
    ∫ x, aeval x (hermite m) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)) = 0 := by
  have key := integral_aeval_mul_hermite (hermiteℝ m) n
  simp only [aeval_hermiteℝ] at key
  rw [key]
  have hz : (⇑derivative)^[n] (hermiteℝ m) = 0 := by
    have hzℤ : (⇑derivative)^[n] (hermite m) = 0 :=
      iterate_derivative_eq_zero (by rw [natDegree_hermite]; exact h)
    rw [Polynomial.hermiteℝ_def, iterate_derivative_map, hzℤ, Polynomial.map_zero]
  simp [hz]

/-- **Hermite L²-orthogonality against the Gaussian weight** (roadmap `OrthogonalL2Bases`, A1):
`∫ Hₘ(x)·Hₙ(x)·e^{-x²/2} dx = if m = n then n!·√(2π) else 0`. -/
theorem integral_hermite_mul_hermite_mul_gaussian (m n : ℕ) :
    ∫ x, aeval x (hermite m) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))
      = if m = n then (n ! : ℝ) * Real.sqrt (2 * π) else 0 := by
  rcases lt_trichotomy m n with h | h | h
  · rw [if_neg (Nat.ne_of_lt h)]
    exact integral_hermite_mul_hermite_mul_gaussian_of_lt h
  · subst h
    rw [if_pos rfl]
    have key := integral_aeval_mul_hermite (hermiteℝ m) m
    simp only [aeval_hermiteℝ] at key
    rw [key]
    have hval : ∀ x : ℝ, aeval x ((⇑derivative)^[m] (hermiteℝ m)) = (m ! : ℝ) := by
      intro x
      rw [Polynomial.hermiteℝ_def, iterate_derivative_map, coe_aeval_eq_eval,
        ← eval₂_eq_eval_map, ← algebraMap_int_eq, ← aeval_def, iterate_derivative_hermite,
        Nat.descFactorial_self, Nat.sub_self]
      simp
    rw [integral_congr_ae (Filter.Eventually.of_forall fun x => by rw [hval x]),
      integral_const_mul, integral_gaussian_half]
  · rw [if_neg (Nat.ne_of_gt h)]
    have comm : ∫ x, aeval x (hermite m) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))
        = ∫ x, aeval x (hermite n) * aeval x (hermite m) * Real.exp (-(x ^ 2 / 2)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [comm]
    exact integral_hermite_mul_hermite_mul_gaussian_of_lt h

/-- Hermite orthogonality against the standard Gaussian density, in `aeval` form:
`∫ Hₘ(x)·Hₙ(x)·gaussianPDFReal 0 1 x dx = if m = n then n! else 0`. -/
theorem integral_hermite_mul_hermite_mul_gaussianPDFReal (m n : ℕ) :
    ∫ x, aeval x (hermite m) * aeval x (hermite n) * gaussianPDFReal 0 1 x
      = if m = n then (n ! : ℝ) else 0 := by
  have hs : Real.sqrt (2 * π) ≠ 0 := ne_of_gt (by positivity)
  have hpdf : ∀ x : ℝ, gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ *
      Real.exp (-(x ^ 2 / 2)) := by
    intro x
    simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
    congr 2
    ring
  calc
    ∫ x, aeval x (hermite m) * aeval x (hermite n) * gaussianPDFReal 0 1 x
        = (Real.sqrt (2 * π))⁻¹ *
          ∫ x, aeval x (hermite m) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only
          rw [hpdf x]
          ring
    _ = if m = n then (n ! : ℝ) else 0 := by
      rw [integral_hermite_mul_hermite_mul_gaussian]
      split_ifs with h
      · rw [mul_comm (n ! : ℝ) (Real.sqrt (2 * π)), ← mul_assoc, inv_mul_cancel₀ hs,
          one_mul]
      · rw [mul_zero]

/-- Bridge-shaped Hermite orthogonality for `hilbertBasisOfWeightedMeasure`: with
`p := hermiteℝ`, `w := gaussianPDFReal 0 1`, and `c n := n!`, this is exactly the weighted-volume
orthogonality hypothesis `∫ (p m).eval x * (p n).eval x * w x = if m = n then c n else 0`. -/
theorem integral_hermiteℝ_mul_hermiteℝ_mul_gaussianPDFReal (m n : ℕ) :
    ∫ x, (hermiteℝ m).eval x * (hermiteℝ n).eval x * gaussianPDFReal 0 1 x
      = if m = n then (n ! : ℝ) else 0 := by
  calc
    ∫ x, (hermiteℝ m).eval x * (hermiteℝ n).eval x * gaussianPDFReal 0 1 x
        = ∫ x, aeval x (hermite m) * aeval x (hermite n) * gaussianPDFReal 0 1 x := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [eval_hermiteℝ]
    _ = if m = n then (n ! : ℝ) else 0 :=
        integral_hermite_mul_hermite_mul_gaussianPDFReal m n

/-- **Hermite L²-orthogonality against the standard Gaussian measure** (roadmap
`OrthogonalL2Bases`, the canonical A1 form):
`∫ Hₘ(x)·Hₙ(x) ∂N(0,1) = if m = n then n! else 0`. This is the Lebesgue form divided by the
`√(2π)` density normalisation; it is what the weighted-measure Hilbert-basis bridge consumes. -/
theorem integral_hermite_mul_hermite_gaussianReal (m n : ℕ) :
    ∫ x, aeval x (hermite m) * aeval x (hermite n) ∂(gaussianReal 0 1)
      = if m = n then (n ! : ℝ) else 0 := by
  have hs : Real.sqrt (2 * π) ≠ 0 := ne_of_gt (by positivity)
  have hpdf : ∀ x : ℝ, gaussianPDFReal 0 1 x =
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
    intro x
    simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
    congr 2
    ring
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero)]
  have hint : (∫ x, gaussianPDFReal 0 1 x • (aeval x (hermite m) * aeval x (hermite n)))
      = (Real.sqrt (2 * π))⁻¹ *
          ∫ x, aeval x (hermite m) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, hpdf]; ring
  rw [hint, integral_hermite_mul_hermite_mul_gaussian]
  split_ifs with h
  · rw [mul_comm (n ! : ℝ) (Real.sqrt (2 * π)), ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  · rw [mul_zero]

end TauCeti.Hermite
