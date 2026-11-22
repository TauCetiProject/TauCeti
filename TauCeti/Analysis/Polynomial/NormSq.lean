/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.RCLike.Basic

/-!
# The squared modulus of a polynomial as a quadratic form in its coefficients

Over `ℝ` or `ℂ`, the squared modulus of the value of a polynomial `Q` of degree at most `n` is the
Hermitian form `‖Q z‖² = ∑_{i, j ≤ n} conj (Q_i) Q_j conj z ^ i z ^ j` in its coefficients
(`Polynomial.ofReal_norm_eval_sq_eq_sum`).
-/

public section

namespace Polynomial

open ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `‖Q.eval z‖² = ∑ conj (Q_i) Q_j conj z ^ i z ^ j` for a polynomial `Q` of degree at most
`n`. -/
theorem ofReal_norm_eval_sq_eq_sum {Q : 𝕜[X]} {n : ℕ} (hQ : Q.natDegree < n + 1) (z : 𝕜) :
    ((‖Q.eval z‖ ^ 2 : ℝ) : 𝕜) =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        conj (Q.coeff i) * Q.coeff j * (conj z ^ (i : ℕ) * z ^ (j : ℕ)) := by
  rw [RCLike.ofReal_pow, ← RCLike.conj_mul, eval_eq_sum_range' hQ, ← Fin.sum_univ_eq_sum_range,
    map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, map_pow]
  ring

end Polynomial
