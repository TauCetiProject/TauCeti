/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Fin.VecNotation

/-!
# Polynomials in two variables

For `φ : MvPolynomial (Fin 2) R` the monomial with exponent `s : Fin 2 →₀ ℕ` is
`X₀ ^ s 0 * X₁ ^ s 1`, of degree `s 0 + s 1`.  This file records the evaluation of `φ` at a pair
`(a, b)` as a sum over these monomials, and the description of the total degree of `φ` as the
largest `s 0 + s 1` over its support.  These are the forms in which a plane curve equation
`φ(x, y) = 0` of degree `n` is manipulated term by term.

## Main results

* `MvPolynomial.aeval_fin_two_eq_sum`: `φ(a, b) = ∑ₛ cₛ a ^ s 0 b ^ s 1`.
* `MvPolynomial.add_le_totalDegree_of_mem_support`: every monomial of `φ` has degree at most the
  total degree of `φ`.
* `MvPolynomial.exists_mem_support_add_eq_totalDegree`: a nonzero `φ` has a monomial of degree
  exactly its total degree.
-/

public section

namespace MvPolynomial

variable {R : Type*} [CommSemiring R]

/-- A polynomial in two variables evaluated at `(a, b)` is the sum of its terms
`c_s a ^ s 0 b ^ s 1`. -/
theorem aeval_fin_two_eq_sum {A : Type*} [CommSemiring A] [Algebra R A]
    (φ : MvPolynomial (Fin 2) R) (a b : A) :
    aeval ![a, b] φ = ∑ s ∈ φ.support, algebraMap R A (φ.coeff s) * (a ^ s 0 * b ^ s 1) := by
  rw [aeval_def, eval₂_eq']
  simp [Fin.prod_univ_two]

/-- The degree `s 0 + s 1` of a monomial in two variables, as the sum of its exponents. -/
private theorem sum_fin_two (s : Fin 2 →₀ ℕ) : (s.sum fun _ e ↦ e) = s 0 + s 1 := by
  rw [Finsupp.sum_fintype _ _ (by intros; rfl), Fin.sum_univ_two]

/-- Every monomial of a polynomial in two variables has degree at most its total degree. -/
theorem add_le_totalDegree_of_mem_support {φ : MvPolynomial (Fin 2) R} {s : Fin 2 →₀ ℕ}
    (hs : s ∈ φ.support) : s 0 + s 1 ≤ φ.totalDegree :=
  sum_fin_two s ▸ le_totalDegree hs

/-- A nonzero polynomial in two variables has a monomial whose degree is its total degree. -/
theorem exists_mem_support_add_eq_totalDegree {φ : MvPolynomial (Fin 2) R} (hφ : φ ≠ 0) :
    ∃ s ∈ φ.support, s 0 + s 1 = φ.totalDegree := by
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup φ.support
    (Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hφ)) fun s ↦ s.sum fun _ e ↦ e
  exact ⟨s, hs, (sum_fin_two s ▸ hsup).symm⟩

end MvPolynomial
