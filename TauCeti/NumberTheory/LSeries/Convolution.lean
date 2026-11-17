/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Dirichlet series of convolution powers

Mathlib's `ArithmeticFunction.LSeriesHasSum_mul` multiplies the sums of two convergent Dirichlet
series. This file iterates it: if the Dirichlet series of `f` has sum `a` at `s`, then that of the
Dirichlet-convolution power `f ^ k` has sum `a ^ k`. The base case is the unit `δ`, whose series
has the single nonzero term `1` and therefore converges at every `s`.

## Main results

* `LSeriesHasSum_delta`: the Dirichlet series of `δ` has sum `1` at every `s`.
* `ArithmeticFunction.natCoe_pow`: the cast `ArithmeticFunction ℕ → ArithmeticFunction R`
  commutes with convolution powers.
* `ArithmeticFunction.LSeriesHasSum_pow`: if the Dirichlet series of `f` has sum `a` at `s`,
  then the Dirichlet series of `f ^ k` has sum `a ^ k`.
-/

public section

open scoped LSeries.notation

/-- The Dirichlet series of the unit `δ` has the single nonzero term `1`, so it converges at every
`s` with sum `1`. -/
theorem LSeriesHasSum_delta (s : ℂ) : LSeriesHasSum δ s 1 := by
  rw [LSeriesHasSum, funext (LSeries.term_delta s)]
  exact hasSum_ite_eq 1 1

namespace ArithmeticFunction

/-- The cast of an `ℕ`-valued arithmetic function commutes with Dirichlet-convolution powers. -/
@[simp, norm_cast]
theorem natCoe_pow {R : Type*} [Semiring R] (f : ArithmeticFunction ℕ) (k : ℕ) :
    (↑(f ^ k) : ArithmeticFunction R) = (f : ArithmeticFunction R) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, natCoe_one]
  | succ k ih => rw [pow_succ, pow_succ, natCoe_mul, ih]

/-- If the Dirichlet series of `f` has sum `a` at `s`, then the Dirichlet series of the
convolution power `f ^ k` has sum `a ^ k` at `s`. -/
theorem LSeriesHasSum_pow {f : ArithmeticFunction ℂ} {s a : ℂ} (hf : LSeriesHasSum ↗f s a)
    (k : ℕ) : LSeriesHasSum ↗(f ^ k) s (a ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, one_eq_delta]
    exact LSeriesHasSum_delta s
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact LSeriesHasSum_mul ih hf

end ArithmeticFunction
