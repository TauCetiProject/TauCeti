/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Polynomial.natDegree_sub_eq_left_of_natDegree_lt` is what reads the degree off the leading term.
public import Mathlib.Algebra.Polynomial.Degree.Operations
-- `Polynomial.Monic` occurs in the statement below, and `Polynomial.monic_X_pow_sub` proves it.
public import Mathlib.Algebra.Polynomial.Monic

/-!
# The degree of `X ^ n - X - a`

For `1 < n` the trinomial `X ^ n - X - a` is `X ^ n` minus a polynomial of degree one, so it is
monic of degree `n`. These are the shape facts about the polynomial whose roots are the
Artin–Schreier elements in characteristic `n = p`, where the trinomial is separable and its roots
differ by elements of the prime field.

## Main results

* `Polynomial.natDegree_X_pow_sub_X`, with the trinomial form
  `Polynomial.natDegree_X_pow_sub_X_sub_C`, and `Polynomial.monic_X_pow_sub_X_sub_C`: for `1 < n`
  the trinomial has degree `n` and is monic.
-/

public section

namespace Polynomial

variable {R : Type*} [Ring R] {n : ℕ}

/-- For `1 < n` the trinomial `X ^ n - X - a` is monic: it is `X ^ n` minus a polynomial of
degree one. -/
theorem monic_X_pow_sub_X_sub_C [Nontrivial R] (hn : 1 < n) (a : R) :
    (X ^ n - X - C a : R[X]).Monic := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hdeg : (X + C a : R[X]).degree < (m + 1 : ℕ) := by
    rw [degree_X_add_C]
    exact_mod_cast by omega
  rw [sub_sub]
  exact monic_X_pow_sub hdeg

/-- For `1 < n` the binomial `X ^ n - X` has degree `n`. -/
@[simp]
theorem natDegree_X_pow_sub_X [Nontrivial R] (hn : 1 < n) :
    (X ^ n - X : R[X]).natDegree = n := by
  rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
  rw [natDegree_X_pow, natDegree_X]
  exact hn

/-- For `1 < n` the trinomial `X ^ n - X - a` has degree `n`.  The constant does not matter, so
`Polynomial.natDegree_X_pow_sub_X` is the form simp normalizes to. -/
theorem natDegree_X_pow_sub_X_sub_C [Nontrivial R] (hn : 1 < n) (a : R) :
    (X ^ n - X - C a : R[X]).natDegree = n := by
  rw [natDegree_sub_C]
  exact natDegree_X_pow_sub_X hn

end Polynomial
