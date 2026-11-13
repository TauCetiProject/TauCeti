/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Hermite.Heat
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The backward heat equation for Hermite polynomials

The polynomials `hermiteHeat n t` satisfy `∂ₜ H + (1/2) ∂ₓₓ H = 0` and are jointly
smooth even at time zero. At positive times they are `t^(n/2) Heₙ(x / √t)`, where
`Heₙ` is Mathlib's probabilists' Hermite polynomial.

These are the space-time polynomials used with Itô's formula to represent Hermite
functionals of Brownian increments. The identities here are deterministic; no stochastic
integral or martingale representation is asserted. In particular, polynomial regularity at
time zero avoids a singular square-root formula when starting an increment interval.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.4, for the Brownian martingale representation argument.
-/

public section

noncomputable section

open Polynomial Real

namespace TauCeti

/-- The usual positive-time scaled Hermite formula. Unlike this formula, the polynomial
construction itself needs no division by the square root of time. -/
theorem eval_hermiteHeat (n : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (hermiteHeat n t).eval x =
      (√t) ^ n * Polynomial.aeval (x / √t) (Polynomial.hermite n) := by
  have h := eval_hermiteHeat_sq_mul n (√t) (x / √t)
  rwa [sq_sqrt ht.le, mul_div_cancel₀ _ (sqrt_pos.mpr ht).ne'] at h

/-- Space-time Hermite polynomials are jointly smooth on the entire time-spot plane,
including time zero. -/
theorem contDiff_hermiteHeat (n : ℕ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (fun p : ℝ × ℝ ↦ (hermiteHeat n p.1).eval p.2) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using (contDiff_const : ContDiff ℝ k (fun _ : ℝ × ℝ ↦ (1 : ℝ)))
  | one => simpa using (contDiff_snd : ContDiff ℝ k (fun p : ℝ × ℝ ↦ p.2))
  | more n ih ih' =>
    simp only [hermiteHeat_add_two, eval_sub, eval_mul, eval_X, eval_C]
    exact (contDiff_snd.mul ih').sub ((contDiff_fst.mul contDiff_const).mul ih)

/-- Time differentiation is minus one half of the spatial second derivative,
including at time zero. -/
theorem hasDerivAt_hermiteHeat_time (n : ℕ) (t x : ℝ) :
    HasDerivAt (fun u ↦ (hermiteHeat n u).eval x)
      (-1 / 2 * (derivative (derivative (hermiteHeat n t))).eval x) t := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using hasDerivAt_const t (1 : ℝ)
  | one => simpa using hasDerivAt_const t x
  | more n ih ih' =>
    have h := (ih'.const_mul x).sub
      (((hasDerivAt_id t).mul_const (n + 1 : ℝ)).mul ih)
    have hode := congrArg (fun p : ℝ[X] ↦ p.eval x) (hermiteHeat_ode n t)
    have hdd : (derivative (derivative (hermiteHeat (n + 1) t))).eval x =
        (n + 1 : ℝ) * (derivative (hermiteHeat n t)).eval x := by
      rw [derivative_hermiteHeat_succ, derivative_mul]
      simp
    simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_zero] at hode
    convert h using 1
    · ext u
      simp [hermiteHeat_add_two]
    · rw [derivative_derivative_hermiteHeat_add_two, eval_mul, eval_C, hdd]
      simp only [id_eq]
      linear_combination -(n + 1 : ℝ) / 2 * hode

/-- The spatial derivative of a space-time Hermite polynomial. -/
theorem hasDerivAt_hermiteHeat_spot (n : ℕ) (t x : ℝ) :
    HasDerivAt (fun y ↦ (hermiteHeat (n + 1) t).eval y)
      ((n + 1 : ℝ) * (hermiteHeat n t).eval x) x := by
  simpa only [derivative_hermiteHeat_succ, eval_mul, eval_C] using
    (hermiteHeat (n + 1) t).hasDerivAt x

/-- The backward heat equation for the space-time Hermite polynomials,
with ordinary derivatives valid even at time zero. -/
theorem hermiteHeat_heat_equation (n : ℕ) (t x : ℝ) :
    deriv (fun u ↦ (hermiteHeat n u).eval x) t +
      1 / 2 * deriv (deriv fun y ↦ (hermiteHeat n t).eval y) x = 0 := by
  have hspace : deriv (fun y ↦ (hermiteHeat n t).eval y) =
      fun y ↦ (derivative (hermiteHeat n t)).eval y :=
    funext fun y ↦ (hermiteHeat n t).deriv
  rw [(hasDerivAt_hermiteHeat_time n t x).deriv, hspace,
    (derivative (hermiteHeat n t)).deriv]
  ring

end TauCeti
