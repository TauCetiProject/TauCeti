/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Hermite.Heat
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Operations
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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Space-time Hermite polynomials are jointly smooth on the entire time-space plane,
including time zero. -/
theorem contDiff_hermiteHeat (n : ℕ) (k : WithTop ℕ∞) :
    ContDiff 𝕜 k (fun p : 𝕜 × 𝕜 ↦ (hermiteHeat n p.1).eval p.2) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using (contDiff_const : ContDiff 𝕜 k (fun _ : 𝕜 × 𝕜 ↦ (1 : 𝕜)))
  | one => simpa using (contDiff_snd : ContDiff 𝕜 k (fun p : 𝕜 × 𝕜 ↦ p.2))
  | more n ih ih' =>
    simp only [hermiteHeat_add_two, eval_sub, eval_mul, eval_X, eval_C]
    exact (contDiff_snd.mul ih').sub ((contDiff_fst.mul contDiff_const).mul ih)

private theorem hasDerivAt_hermiteHeat_time_aux [CharZero 𝕜] (n : ℕ) (t x : 𝕜) :
    HasDerivAt (fun u ↦ (hermiteHeat n u).eval x)
      (-1 / 2 * (derivative (derivative (hermiteHeat n t))).eval x) t := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using hasDerivAt_const t (1 : 𝕜)
  | one => simpa using hasDerivAt_const t x
  | more n ih ih' =>
    have h := (ih'.const_mul x).sub
      (((hasDerivAt_id t).mul_const (n + 1 : 𝕜)).mul ih)
    have hode := congrArg (fun p : 𝕜[X] ↦ p.eval x) (hermiteHeat_ode n t)
    simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_zero] at hode
    convert h using 1
    · ext u
      simp [hermiteHeat_add_two]
    · rw [derivative_hermiteHeat_succ (n + 1), derivative_C_mul,
        derivative_hermiteHeat_succ, derivative_C_mul]
      simp only [eval_mul, eval_C, Nat.cast_add, Nat.cast_one, id_eq]
      linear_combination -(n + 1 : 𝕜) / 2 * hode

/-- Time differentiation lowers the index by two, including at time zero. -/
theorem hasDerivAt_hermiteHeat_time [CharZero 𝕜] (n : ℕ) (t x : 𝕜) :
    HasDerivAt (fun u ↦ (hermiteHeat n u).eval x)
      (-((n.descFactorial 2 : 𝕜) / 2) * (hermiteHeat (n - 2) t).eval x) t := by
  have hdd := iterate_derivative_hermiteHeat n 2 t
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] at hdd
  convert hasDerivAt_hermiteHeat_time_aux n t x using 1
  rw [hdd, eval_mul, eval_C]
  ring

/-- The ordinary time derivative of a space-time Hermite polynomial. -/
@[simp]
theorem deriv_hermiteHeat_time [CharZero 𝕜] (n : ℕ) (t x : 𝕜) :
    deriv (fun u ↦ (hermiteHeat n u).eval x) t =
      -((n.descFactorial 2 : 𝕜) / 2) * (hermiteHeat (n - 2) t).eval x :=
  (hasDerivAt_hermiteHeat_time n t x).deriv

/-- The spatial derivative of a space-time Hermite polynomial, including the constant case. -/
theorem hasDerivAt_hermiteHeat_space (n : ℕ) (t x : 𝕜) :
    HasDerivAt (fun y ↦ (hermiteHeat n t).eval y)
      ((n : 𝕜) * (hermiteHeat (n - 1) t).eval x) x := by
  simpa only [derivative_hermiteHeat, eval_mul, eval_C] using
    (hermiteHeat n t).hasDerivAt x

/-- The second spatial derivative lowers the index by two, including low degrees. -/
theorem hasDerivAt_deriv_hermiteHeat_space (n : ℕ) (t x : 𝕜) :
    HasDerivAt (deriv fun y ↦ (hermiteHeat n t).eval y)
      ((n.descFactorial 2 : 𝕜) * (hermiteHeat (n - 2) t).eval x) x := by
  have hspace : deriv (fun y ↦ (hermiteHeat n t).eval y) =
      fun y ↦ (derivative (hermiteHeat n t)).eval y :=
    funext fun y ↦ (hermiteHeat n t).deriv
  rw [hspace]
  have hdd := iterate_derivative_hermiteHeat n 2 t
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] at hdd
  simpa only [hdd, eval_mul, eval_C] using (derivative (hermiteHeat n t)).hasDerivAt x

/-- The ordinary second spatial derivative of a space-time Hermite polynomial. -/
@[simp]
theorem deriv_deriv_hermiteHeat_space (n : ℕ) (t x : 𝕜) :
    deriv (deriv fun y ↦ (hermiteHeat n t).eval y) x =
      (n.descFactorial 2 : 𝕜) * (hermiteHeat (n - 2) t).eval x :=
  (hasDerivAt_deriv_hermiteHeat_space n t x).deriv

/-- The backward heat equation for the space-time Hermite polynomials,
with ordinary derivatives valid even at time zero. -/
theorem hermiteHeat_heat_equation [CharZero 𝕜] (n : ℕ) (t x : 𝕜) :
    deriv (fun u ↦ (hermiteHeat n u).eval x) t +
      1 / 2 * deriv (deriv fun y ↦ (hermiteHeat n t).eval y) x = 0 := by
  rw [deriv_hermiteHeat_time, deriv_deriv_hermiteHeat_space]
  ring

end TauCeti
