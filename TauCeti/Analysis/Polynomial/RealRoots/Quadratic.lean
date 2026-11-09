/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

/-!
# The real quadratic with a given conjugate pair of complex roots

For a complex number `z`, the real quadratic `X² - 2 Re z · X + ‖z‖²` has exactly the complex
roots `conj z` and `z`.

## Main results

* `Polynomial.aroots_quadratic_eq_conj_pair`: the complex roots of this quadratic.
-/

public section

open ComplexConjugate

namespace Polynomial

/-- The real quadratic `X² - 2 Re z · X + ‖z‖²` has exactly the complex roots `conj z` and `z`. -/
lemma aroots_quadratic_eq_conj_pair (z : ℂ) :
    (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : ℝ[X]).aroots ℂ = {conj z, z} := by
  have hQ : (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : ℝ[X]) =
      C 1 * X ^ 2 + C (-(2 * z.re)) * X + C (‖z‖ ^ 2) := by
    simp [sub_eq_add_neg]
  rw [hQ, aroots_quadratic_eq_pair_iff_of_ne_zero (by simp)]
  refine ⟨?_, ?_⟩
  · simp only [Complex.coe_algebraMap, map_one, neg_mul, one_mul, Complex.ofReal_neg,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [add_comm (conj z), Complex.add_conj]
    push_cast
    ring
  · simp only [Complex.coe_algebraMap, map_one, one_mul, Complex.ofReal_pow]
    rw [mul_comm, ← Complex.mul_conj']

end Polynomial
