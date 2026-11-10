/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrals of real polynomials

The integral of a real polynomial `p` over an interval `[a, b]` is computed termwise from its
coefficients: `∫ x in a..b, p.eval x = ∑ᵢ pᵢ (b ^ (i + 1) - a ^ (i + 1)) / (i + 1)`.

## Main results

* `Polynomial.integral_eval_eq_sum`: the integral of `p.eval` in terms of the coefficients of `p`.
-/

public section

open Finset

namespace Polynomial

/-- The integral of a real polynomial over `[a, b]`, in terms of its coefficients. -/
theorem integral_eval_eq_sum (p : ℝ[X]) (a b : ℝ) :
    ∫ x in a..b, p.eval x =
      ∑ i ∈ range (p.natDegree + 1), p.coeff i * ((b ^ (i + 1) - a ^ (i + 1)) / (i + 1)) := by
  simp_rw [eval_eq_sum_range]
  rw [intervalIntegral.integral_finsetSum fun i _ ↦
    ((continuous_pow i).const_mul _).intervalIntegrable _ _]
  exact sum_congr rfl fun i _ ↦ by rw [intervalIntegral.integral_const_mul, integral_pow]

end Polynomial
