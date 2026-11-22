/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

import Mathlib.Algebra.MvPolynomial.Nilpotent
import TauCeti.Algebra.MvPolynomial.Variables

/-!
# Irreducibility and non-associatedness of variable differences

Over an integral domain `R`, each root-difference hyperplane `X i - X j` (`i ≠ j`) in
`MvPolynomial σ R` is irreducible (`MvPolynomial.irreducible_X_sub_X`), and when `σ` carries a
preorder the differences `X i - X j` with `i < j` are pairwise non-associated
(`MvPolynomial.eq_of_associated_X_sub_X`). Over a unique factorization domain `R`, these linear
factors therefore form pairwise coprime primes, giving the prime factorization of Vandermonde and
root-system hyperplane products `∏_{i < j} (X i - X j)`.

## Main results

* `MvPolynomial.irreducible_X_sub_X`: for `i ≠ j` over an integral domain, `X i - X j` is
  irreducible in `MvPolynomial σ R`.
* `MvPolynomial.eq_of_associated_X_sub_X`: for `i < j` and `i' < j'` in a preordered index type
  over an integral domain, `Associated (X i - X j) (X i' - X j')` implies `i = i'` and `j = j'`.
-/

public section

namespace MvPolynomial

/-- Over an integral domain `R`, the difference `X i - X j` of two distinct variables is
irreducible in `MvPolynomial σ R`. -/
theorem irreducible_X_sub_X {σ R : Type*} [CommRing R] [IsDomain R] {i j : σ} (hij : i ≠ j) :
    Irreducible (X i - X j : MvPolynomial σ R) := by
  classical
  have h : (X i - X j : MvPolynomial σ R) = 1 * X i + -X j := by ring
  rw [h]
  exact irreducible_mul_X_add 1 (-X j) i one_ne_zero (by simp) (by simp [hij]) isRelPrime_one_left

/-- Over an integral domain `R`, if `i < j` and `i' < j'` in a preorder `σ` and `X i - X j` is
associated to `X i' - X j'` in `MvPolynomial σ R`, then `i = i'` and `j = j'`. -/
theorem eq_of_associated_X_sub_X {σ R : Type*} [Preorder σ] [CommRing R] [IsDomain R]
    {i j i' j' : σ} (hij : i < j) (hij' : i' < j')
    (hass : Associated (X i - X j : MvPolynomial σ R) (X i' - X j')) :
    i = i' ∧ j = j' := by
  classical
  obtain ⟨u, hu⟩ := hass
  obtain ⟨r, hr, huC⟩ := isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  have hvars : ({i, j} : Finset σ) = {i', j'} := by
    have hv := congrArg MvPolynomial.vars hu
    rwa [huC, mul_comm, vars_C_mul r hr.ne_zero, vars_X_sub_X hij.ne, vars_X_sub_X hij'.ne] at hv
  have hi : i = i' ∨ i = j' := by simpa using (Finset.ext_iff.mp hvars i).mp (by simp)
  have hj : j = i' ∨ j = j' := by simpa using (Finset.ext_iff.mp hvars j).mp (by simp)
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact absurd rfl hij.ne
  · exact ⟨rfl, rfl⟩
  · exact absurd (hij.trans hij') (lt_irrefl _)
  · exact absurd rfl hij.ne

end MvPolynomial
