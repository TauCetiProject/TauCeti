/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Polynomial evaluation and degree bounds

Substituting `C q * X` for the variable of the monomial `a Xⁿ` multiplies its coefficient by `qⁿ`.
This is the monomial case of Mathlib's `Polynomial.comp_C_mul_X_coeff`, stated as an equality of
polynomials so that it can be used to rewrite monomials directly.

We also record that functions `R → R` agreeing with polynomials of degree `< d` are closed under
adding a constant-scaled term (`TauCeti.exists_degree_lt_and_add_mul_const_eq_eval`).
-/

public section

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- Rescaling the variable of a monomial: `(a Xⁿ)(qX) = a qⁿ Xⁿ`. -/
theorem monomial_comp_C_mul_X (q a : R) (n : ℕ) :
    (monomial n a).comp (C q * X) = monomial n (a * q ^ n) := by
  ext k
  simp only [comp_C_mul_X_coeff, coeff_monomial, Finsupp.single_apply]
  split_ifs with h
  · rw [h]
  · rw [zero_mul]

end Polynomial

namespace TauCeti

open Polynomial

/-- Adding a constant-scaled term preserves a strict polynomial degree bound `< d` for evaluated
functions `R → R`. -/
theorem exists_degree_lt_and_add_mul_const_eq_eval {R : Type*} [CommSemiring R]
    {f₀ g : R → R} {d : WithBot ℕ} (c : R)
    (hf₀ : ∃ Q : R[X], Q.degree < d ∧ ∀ w, f₀ w = Q.eval w)
    (hg : ∃ Q : R[X], Q.degree < d ∧ ∀ w, g w = Q.eval w) :
    ∃ Q : R[X], Q.degree < d ∧ ∀ w, f₀ w + g w * c = Q.eval w := by
  obtain ⟨Q₀, hQ₀, hf₀'⟩ := hf₀
  obtain ⟨Q₁, hQ₁, hg'⟩ := hg
  refine ⟨Q₀ + Q₁ * C c, ?_, fun w ↦ by simp [hf₀' w, hg' w]⟩
  refine (degree_add_le Q₀ (Q₁ * C c)).trans_lt (max_lt hQ₀ ((degree_mul_le Q₁ (C c)).trans_lt ?_))
  exact (add_le_of_nonpos_right degree_C_le).trans_lt hQ₁

end TauCeti
