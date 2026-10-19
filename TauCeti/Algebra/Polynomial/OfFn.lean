/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.OfFn

-- Proof-only: supply `Polynomial.X_sub_C_pow_dvd_iff` and `Polynomial.X_pow_dvd_iff`.
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div

/-!
# Recovering a polynomial of bounded degree from its coefficient vector

`Polynomial.ofFn n` and `Polynomial.toFn n` pass between vectors of length `n` and polynomials.
Mathlib records that a polynomial of `natDegree` below `n` is recovered from its first `n`
coefficients; this file states the same recovery in terms of `degree`, so that it also applies
to the zero polynomial. This file also records evaluation of the coefficient vector and
reconstruction of a coordinate vector as a power of `X`, and characterizes divisibility of
`ofFn n f` by `(X - t) ^ r` through the Taylor coefficients of order `< r` at `t`.
-/

public section

namespace TauCeti

open Polynomial

variable {R : Type*} [Semiring R] [DecidableEq R]

omit [DecidableEq R] in
/-- Evaluating the coefficient vector reads the corresponding polynomial coefficient. -/
@[simp]
theorem _root_.Polynomial.toFn_apply (n : ℕ) (p : R[X]) (i : Fin n) :
    toFn n p i = p.coeff i := (rfl)

-- Mathlib's `ofFn` takes `[DecidableEq R]`, so this instance occurs in the statement.
/-- The coordinate vector with value one at `l` reconstructs the monomial `X ^ l.val`. -/
@[simp]
theorem _root_.Polynomial.ofFn_single {n : ℕ} (l : Fin n) :
    ofFn n (fun i => if i = l then (1 : R) else 0) = X ^ l.val := by
  simp [ofFn_eq_sum_monomial, apply_ite (monomial _), monomial_one_right_eq_X_pow]

/-- A polynomial of degree below `n` is recovered from its vector of first `n` coefficients.
This is the `degree` form of `Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt`, which also covers
the zero polynomial. -/
theorem _root_.Polynomial.ofFn_comp_toFn_eq_id_of_degree_lt {n : ℕ} {p : R[X]} (h : p.degree < n) :
    ofFn n (toFn n p) = p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · exact ofFn_comp_toFn_eq_id_of_natDegree_lt ((natDegree_lt_iff_degree_lt hp).mpr h)

/-- `(X - t) ^ r` divides the polynomial with coefficient vector `f` if and only if its Taylor
coefficients of order `< r` at `t` vanish. -/
theorem _root_.Polynomial.X_sub_C_pow_dvd_ofFn_iff {R : Type*} [CommRing R] [DecidableEq R]
    (t : R) (r : ℕ) {n : ℕ} (f : Fin n → R) :
    (X - C t) ^ r ∣ ofFn n f ↔
      ∀ k < r, ∑ i : Fin n, f i * (t ^ ((i : ℕ) - k) * ((i : ℕ).choose k : R)) = 0 := by
  rw [ofFn_eq_sum_monomial, X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  refine forall₂_congr fun k _ ↦ ?_
  simp [← C_mul_X_pow_eq_monomial, finsetSum_coeff, coeff_X_add_C_pow]

end TauCeti
