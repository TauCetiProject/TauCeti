/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Hermite.Derivative
import Mathlib.Tactic.LinearCombination

/-!
# Hermite polynomials with a variance parameter

`hermiteHeat n t` is the probabilists' Hermite polynomial with variance parameter `t`.
At `t = 1` it agrees with Mathlib's `Polynomial.hermite`; at `t = 0` it is `X ^ n`.
The lowering identity, three-term recursion, differential equation and scaling identity
are algebraic and hold over any commutative ring.

Over the reals these polynomials solve the backward heat equation; the analytic statements
are in `TauCeti.Analysis.SpecialFunctions.Hermite.Heat`. They give the space-time
polynomials used in Itô representations of Hermite functionals of Brownian increments.

The lowering-identity argument follows `Polynomial.derivative_hermite_succ`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.4, for the Brownian martingale representation argument.
-/

public section

noncomputable section

open Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- The space-time probabilists' Hermite polynomial, with variance parameter `t`.
The definition is polynomial and requires no positivity or invertibility of `t`. -/
def hermiteHeat : ℕ → R → R[X]
  | 0, _ => 1
  | n + 1, t => X * hermiteHeat n t - C t * derivative (hermiteHeat n t)

/-- The degree-zero space-time Hermite polynomial is constant one. -/
@[simp]
theorem hermiteHeat_zero (t : R) : hermiteHeat 0 t = 1 := (rfl)

/-- Raising recursion for the space-time Hermite polynomials. -/
theorem hermiteHeat_succ (n : ℕ) (t : R) :
    hermiteHeat (n + 1) t = X * hermiteHeat n t - C t * derivative (hermiteHeat n t) := (rfl)

/-- The degree-one space-time Hermite polynomial is the spatial coordinate. -/
@[simp]
theorem hermiteHeat_one (t : R) : hermiteHeat 1 t = X := by
  simp [hermiteHeat_succ]

/-- Spatial differentiation lowers the degree by one. -/
@[simp]
theorem derivative_hermiteHeat_succ (n : ℕ) (t : R) :
    derivative (hermiteHeat (n + 1) t) = C (n + 1 : R) * hermiteHeat n t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermiteHeat_succ (n + 1), derivative_sub, derivative_mul, derivative_mul, ih,
      hermiteHeat_succ n]
    simp only [derivative_X, derivative_C, derivative_one, zero_mul,
      zero_add, derivative_mul, Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

/-- The three-term recursion, with no spatial derivatives on its right side. -/
theorem hermiteHeat_add_two (n : ℕ) (t : R) :
    hermiteHeat (n + 2) t =
      X * hermiteHeat (n + 1) t - C (t * (n + 1 : R)) * hermiteHeat n t := by
  rw [hermiteHeat_succ (n + 1), derivative_hermiteHeat_succ, map_mul]
  ring

/-- The degree-two space-time Hermite polynomial is `X² - t`. -/
@[simp]
theorem hermiteHeat_two (t : R) : hermiteHeat 2 t = X ^ 2 - C t := by
  simp [hermiteHeat_add_two, pow_two]

/-- At time zero the space-time Hermite polynomials are monomials. -/
@[simp]
theorem hermiteHeat_time_zero (n : ℕ) : hermiteHeat n (0 : R) = X ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [hermiteHeat_succ, ih, pow_succ, mul_comm]

/-- At unit variance this family agrees with Mathlib's Hermite polynomials. -/
@[simp]
theorem hermiteHeat_time_one (n : ℕ) :
    hermiteHeat n (1 : R) = (Polynomial.hermite n).map (Int.castRingHom R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermiteHeat_succ, ih, Polynomial.hermite_succ]
    simp [Polynomial.derivative_map]

/-- The parameterized Hermite differential equation. -/
theorem hermiteHeat_ode (n : ℕ) (t : R) :
    C t * derivative (derivative (hermiteHeat n t)) - X * derivative (hermiteHeat n t) +
      C (n : R) * hermiteHeat n t = 0 := by
  have h := derivative_hermiteHeat_succ n t
  rw [hermiteHeat_succ, derivative_sub, derivative_mul, derivative_mul] at h
  simp only [derivative_X, derivative_C, zero_mul, zero_add, one_mul, map_add, map_one] at h
  linear_combination -h

/-- Spatial second derivatives lower the index by two. -/
theorem derivative_derivative_hermiteHeat_add_two (n : ℕ) (t : R) :
    derivative (derivative (hermiteHeat (n + 2) t)) =
      C ((n + 2 : R) * (n + 1)) * hermiteHeat n t := by
  rw [derivative_hermiteHeat_succ (n + 1), derivative_mul, derivative_C,
    zero_mul, zero_add, derivative_hermiteHeat_succ, map_mul]
  simp only [Nat.cast_add, Nat.cast_one, map_add, map_one, C_ofNat]
  ring

/-- Scaling the variance and spot recovers the native probabilists' Hermite polynomial.
The formula requires no invertibility of the scale factor. -/
theorem eval_hermiteHeat_sq_mul (n : ℕ) (a x : R) :
    (hermiteHeat n (a ^ 2)).eval (a * x) =
      a ^ n * Polynomial.aeval x (Polynomial.hermite n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih' =>
    rw [hermiteHeat_add_two, eval_sub, eval_mul, eval_X, eval_mul, eval_C, ih, ih',
      Polynomial.hermite_add_two]
    simp only [map_sub, map_mul, aeval_X, nsmul_eq_mul, map_add, map_natCast, map_one,
      Nat.cast_add, Nat.cast_one, pow_add, pow_one]
    ring

end TauCeti
