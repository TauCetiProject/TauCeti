/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Polynomials evaluated at `ε`

Since `ε² = 0`, evaluating a polynomial `p` at the dual-number unit `ε` keeps only its first two
coefficients: the classical part of `p(ε)` is the constant coefficient of `p` and its
infinitesimal part is the linear coefficient.
-/

public section

open Polynomial

namespace DualNumber

variable {R B : Type*} [CommSemiring R] [CommRing B] [Algebra R B]

/-- A polynomial evaluated at `ε` is its constant coefficient plus its linear coefficient
times `ε`. -/
theorem aeval_eps (p : R[X]) :
    aeval (eps : DualNumber B) p =
      TrivSqZeroExt.inl (algebraMap R B (p.coeff 0)) +
        TrivSqZeroExt.inr (algebraMap R B (p.coeff 1)) := by
  rw [← zero_add (eps : DualNumber B),
    aeval_add_of_sq_eq_zero _ _ _ (by rw [sq, eps_mul_eps]),
    ← coeff_zero_eq_aeval_zero', ← coeff_zero_eq_aeval_zero']
  ext <;> simp [coeff_derivative, Algebra.algebraMap_eq_smul_one]

/-- The classical part of a polynomial evaluated at `ε` is its constant coefficient. -/
@[simp]
theorem fst_aeval_eps (p : R[X]) :
    (aeval (eps : DualNumber B) p).fst = algebraMap R B (p.coeff 0) := by
  simp [aeval_eps]

/-- The infinitesimal part of a polynomial evaluated at `ε` is its linear coefficient. -/
@[simp]
theorem snd_aeval_eps (p : R[X]) :
    (aeval (eps : DualNumber B) p).snd = algebraMap R B (p.coeff 1) := by
  simp [aeval_eps, Algebra.algebraMap_eq_smul_one]

end DualNumber
