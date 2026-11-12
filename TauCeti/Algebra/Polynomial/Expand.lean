/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.HasseDeriv

import Mathlib.Data.ZMod.Basic

/-!
# Hasse derivatives of expanded polynomials in prime characteristic

In exponential characteristic `p`, the Hasse derivatives of `g(X^(p^e))` vanish
at every order not divisible by `p^e`. Consequently Hasse differentiation of order below
`p^e` commutes with
multiplication by an expanded polynomial. This is the linearity over polynomials in
`X^(p^e)` used when differentiating restrictions to Frobenius graphs.

The statements hold over commutative semirings, including rings with zero divisors, and
include `e = 0`, when the only permitted order in the multiplication identity is zero.
Unlike ordinary differentiation, these identities also control orders between `p` and `p^e`.

The binomial-coefficient argument is the one underlying Iwaniec–Kowalski,
*Analytic Number Theory*, §11.6, Lemma 11.17. We use Mathlib's `Polynomial.expand`
and `Polynomial.hasseDeriv` throughout.
-/

public section

namespace Polynomial

variable {R : Type*} [CommSemiring R] {p : ℕ} [ExpChar R p]

/-- A Hasse derivative of order not divisible by `p^e` annihilates every polynomial in
`X^(p^e)`, over any commutative semiring of exponential characteristic `p`. -/
theorem hasseDeriv_expand_eq_zero {e k : ℕ} (hk : ¬p ^ e ∣ k)
    (g : R[X]) : hasseDeriv k (expand R (p ^ e) g) = 0 := by
  have hq : 0 < p ^ e := expChar_pow_pos R p e
  induction g using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | monomial n r =>
    have hpoly : (X + 1 : R[X]) ^ (n * p ^ e) =
        expand R (p ^ e) ((X + 1) ^ n) := by
      rw [Nat.mul_comm n, pow_mul, add_pow_expChar_pow, one_pow]
      simp
    have hchoose : (Nat.choose (n * p ^ e) k : R) = 0 := by
      rw [← coeff_X_add_one_pow R, hpoly, coeff_expand hq, ite_eq_right hk]
    simp only [expand_monomial, hasseDeriv_monomial, hchoose, zero_mul,
      monomial_zero_right]

/-- Hasse differentiation of order below `p^e` is linear over polynomials in `X^(p^e)`:
an expanded factor can be pulled outside the derivative. No factorial is inverted. -/
theorem hasseDeriv_expand_mul {e k : ℕ} (hk : k < p ^ e) (g f : R[X]) :
    hasseDeriv k (expand R (p ^ e) g * f) =
      expand R (p ^ e) g * hasseDeriv k f := by
  classical
  rw [hasseDeriv_mul, Finset.sum_eq_single (0, k)]
  · simp
  · intro ij hij hne
    have hij' := Finset.mem_antidiagonal.mp hij
    have hi : 0 < ij.1 := by
      by_contra! h
      have : ij = (0, k) := by ext <;> omega
      exact hne this
    rw [hasseDeriv_expand_eq_zero (Nat.not_dvd_of_pos_of_lt hi (by omega)), zero_mul]
  · simp

/-- At exponent zero the multiplication identity is the identity for the zeroth derivative. -/
example (g f : R[X]) :
    hasseDeriv 0 (expand R (p ^ 0) g * f) = g * f := by
  simp

/-- The identity includes orders at least the characteristic: here `p = 2`, `p^e = 4`,
and the order is `2`. -/
example : hasseDeriv 2 (expand (ZMod 2) (2 ^ 2) X * X ^ 2) =
    (X ^ 4 : (ZMod 2)[X]) := by
  rw [hasseDeriv_expand_mul (p := 2) (e := 2) (by decide)]
  simp [← monomial_one_one_eq_X, monomial_pow]

/-- The strict order bound is necessary: at order `p^e` an expanded `X` has derivative `1`,
whereas differentiating its cofactor `1` gives zero. -/
example : hasseDeriv 2 (expand (ZMod 2) (2 ^ 1) X * 1) = 1 ∧
    expand (ZMod 2) (2 ^ 1) X * hasseDeriv 2 1 = 0 := by
  norm_num [← monomial_one_one_eq_X, monomial_pow, hasseDeriv_apply_one]

end Polynomial
