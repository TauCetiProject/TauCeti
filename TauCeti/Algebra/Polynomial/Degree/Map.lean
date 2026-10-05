/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Degrees of a polynomial under two coefficient maps

If two ring homomorphisms `φ` and `ψ` send exactly the same coefficients of a polynomial `p` to
zero, then `p.map φ` vanishes exactly when `p.map ψ` does, and the two have the same degree. This
is how the zero pattern of finitely many coefficients fixes the degrees of specialized
polynomials, for instance at two points of a base set on which a projection set used in
cylindrical algebraic decomposition is sign-invariant.
-/

public section

namespace Polynomial

variable {R S T : Type*} [Semiring R] [Semiring S] [Semiring T] {φ : R →+* S} {ψ : R →+* T}
  {p : R[X]}

/-- If `φ` and `ψ` send the same coefficients of `p` to zero, then `p.map φ` vanishes exactly
when `p.map ψ` does. -/
theorem map_eq_zero_iff_of_map_coeff_eq_zero_iff
    (h : ∀ i, φ (p.coeff i) = 0 ↔ ψ (p.coeff i) = 0) : p.map φ = 0 ↔ p.map ψ = 0 := by
  simp only [Polynomial.ext_iff, coeff_map, coeff_zero, h]

/-- If `φ` and `ψ` send the same coefficients of `p` to zero, then `p.map φ` and `p.map ψ` have
the same degree. -/
theorem natDegree_map_eq_of_map_coeff_eq_zero_iff
    (h : ∀ i, φ (p.coeff i) = 0 ↔ ψ (p.coeff i) = 0) :
    (p.map φ).natDegree = (p.map ψ).natDegree := by
  have key (n : ℕ) : (p.map φ).natDegree ≤ n ↔ (p.map ψ).natDegree ≤ n := by
    simp only [natDegree_le_iff_coeff_eq_zero, coeff_map, h]
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

end Polynomial
