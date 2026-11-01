/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Evaluating a polynomial at an inverse

A polynomial without constant term, evaluated at `w⁻¹`, is the finite sum
`∑_{1 ≤ k ≤ deg} c_k / w ^ k` of its coefficients. This is the form in which finite Laurent tails
`∑ c_k (z - s)⁻ᵏ` are recorded as polynomials in `(z - s)⁻¹`.
-/

public section

namespace TauCeti

open Polynomial

/-- A polynomial without constant term, evaluated at `w⁻¹`, is the finite sum of its
coefficients divided by the corresponding powers of `w`. -/
theorem _root_.Polynomial.eval_inv_eq_sum_fin_div_pow {K : Type*} [DivisionRing K] {P : K[X]}
    (hP : P.coeff 0 = 0) (w : K) :
    P.eval w⁻¹ = ∑ k : Fin P.natDegree, P.coeff (k + 1) / w ^ (k.val + 1) := by
  rw [eval_eq_sum_range, Finset.sum_range_succ', hP, zero_mul, add_zero,
    ← Fin.sum_univ_eq_sum_range]
  simp [div_eq_mul_inv]

end TauCeti
