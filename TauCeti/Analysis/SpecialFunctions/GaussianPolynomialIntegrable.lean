/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomial integrability against the Gaussian weight

This file collects generic polynomial integrability results for the Gaussian weight, in the
`Polynomial` namespace. The primary results are stated at full generality — a real polynomial
(`eval` form) resp. an integer polynomial (`aeval` form) is integrable against *every* positive
Gaussian weight `e^{-a·x²}` (`a > 0`) — with the standard weight `e^{-x²/2}` recovered as a
corollary (`integrable_eval_mul_gaussian`, `integrable_aeval_mul_gaussian`).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Real Polynomial
open scoped Nat

/-- `xⁿ` is integrable against every positive Gaussian weight `e^{-a*x²}`. -/
private theorem integrable_pow_mul_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-(a * x ^ 2))) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := a) ha
    (s := (k : ℝ)) (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg k))
  simp_rw [Real.rpow_natCast] at h
  refine h.congr ?_
  filter_upwards with x
  congr 2
  ring

/-- Any real polynomial is integrable against every positive Gaussian weight `e^{-a*x²}`. -/
theorem _root_.Polynomial.integrable_eval_mul_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) (p : ℝ[X]) :
    Integrable (fun x : ℝ => p.eval x * Real.exp (-(a * x ^ 2))) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine (hp.add hq).congr ?_
    filter_upwards with x
    simp only [Pi.add_apply, eval_add, add_mul]
  | monomial k c =>
    have := (integrable_pow_mul_exp_neg_mul_sq ha k).const_mul c
    refine this.congr ?_
    filter_upwards with x
    simp only [eval_monomial]
    ring

/-- Evaluating the `ℝ`-realisation of an integer polynomial agrees with `aeval` of the
original. -/
private theorem eval_map_intCast (x : ℝ) (q : ℤ[X]) :
    (q.map (Int.castRingHom ℝ)).eval x = aeval x q := by
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq]

/-- Any integer polynomial is integrable against every positive Gaussian weight `e^{-a*x²}`. -/
theorem _root_.Polynomial.integrable_aeval_mul_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) (p : ℤ[X]) :
    Integrable (fun x : ℝ => aeval x p * Real.exp (-(a * x ^ 2))) := by
  have h := integrable_eval_mul_exp_neg_mul_sq ha (p.map (Int.castRingHom ℝ))
  refine h.congr ?_
  filter_upwards with x
  rw [eval_map_intCast]

/-- Any real polynomial is integrable against the standard Gaussian weight `e^{-x²/2}` — the
`a = 1/2` corollary of `Polynomial.integrable_eval_mul_exp_neg_mul_sq`. -/
theorem _root_.Polynomial.integrable_eval_mul_gaussian (p : ℝ[X]) :
    Integrable (fun x : ℝ => p.eval x * Real.exp (-(x ^ 2 / 2))) := by
  have h := integrable_eval_mul_exp_neg_mul_sq (a := (1 : ℝ) / 2) (by norm_num) p
  refine h.congr ?_
  filter_upwards with x
  have hhalf : -((1 : ℝ) / 2 * x ^ 2) = -(x ^ 2 / 2) := by ring
  rw [hhalf]

/-- Any integer polynomial is integrable against the standard Gaussian weight `e^{-x²/2}` — the
`a = 1/2` corollary of `Polynomial.integrable_aeval_mul_exp_neg_mul_sq`. -/
theorem _root_.Polynomial.integrable_aeval_mul_gaussian (p : ℤ[X]) :
    Integrable (fun x : ℝ => aeval x p * Real.exp (-(x ^ 2 / 2))) := by
  have h := integrable_aeval_mul_exp_neg_mul_sq (a := (1 : ℝ) / 2) (by norm_num) p
  refine h.congr ?_
  filter_upwards with x
  have hhalf : -((1 : ℝ) / 2 * x ^ 2) = -(x ^ 2 / 2) := by ring
  rw [hhalf]

end TauCeti
