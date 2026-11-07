/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Homogenize

/-!
# Homogenization of expanded polynomials

Expanding a polynomial by `m` substitutes `X ^ m` for `X`. Homogenizing this expansion in
degree `n * m` amounts to substituting `X₀ ^ m` and `X₁ ^ m` into its degree-`n`
homogenization. The evaluation form works over any commutative semiring, including at
points with a zero coordinate, and allows a change of coefficient ring.

This identity transfers polynomial expansion formulas to binary forms, in particular the
expansion identities for homogeneous cyclotomic values.
-/

public section

namespace Polynomial

variable {R : Type*} [CommSemiring R]

/-- Homogenizing `p(X ^ m)` in degree `n * m` substitutes the `m`-th powers of both variables
into the degree-`n` homogenization of `p`. The degree bound also permits `m = 0`. -/
theorem homogenize_expand (p : R[X]) {n : ℕ} (hn : p.natDegree ≤ n) (m : ℕ) :
    (expand R m p).homogenize (n * m) =
      MvPolynomial.aeval (fun i ↦ MvPolynomial.X i ^ m) (p.homogenize n) := by
  apply induction_with_natDegree_le
    (fun p ↦ (expand R m p).homogenize (n * m) =
      MvPolynomial.aeval (fun i ↦ MvPolynomial.X i ^ m) (p.homogenize n)) n
  · simp
  · intro k c _ hk
    simp only [map_mul, expand_C, map_pow, expand_X, ← pow_mul]
    rw [Nat.mul_comm m k]
    simp only [homogenize_C_mul, homogenize_X_pow hk,
      homogenize_X_pow (Nat.mul_le_mul_right m hk), map_mul, map_pow,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    simp only [MvPolynomial.algebraMap_eq, ← pow_mul]
    rw [Nat.mul_sub_left_distrib]
    simp only [Nat.mul_comm]
  · intro f g _ _ hf hg
    simp [hf, hg]
  · exact hn

/-- After mapping the coefficients along `f`, the degree-`n * m` homogenization of an
expansion evaluates at `x` as the degree-`n` homogenization evaluates at `x ^ m`.
No coordinate of `x` is required to be a unit or nonzero. -/
theorem eval₂_homogenize_expand {S : Type*} [CommSemiring S] (f : R →+* S)
    (p : R[X]) {n : ℕ} (hn : p.natDegree ≤ n) (m : ℕ) (x : Fin 2 → S) :
    MvPolynomial.eval₂ f x ((expand R m p).homogenize (n * m)) =
      MvPolynomial.eval₂ f (fun i ↦ x i ^ m) (p.homogenize n) := by
  rw [homogenize_expand p hn m, MvPolynomial.aeval_def]
  simpa only [MvPolynomial.algebraMap_eq, Function.comp_def, MvPolynomial.eval₂_X_pow]
    using (MvPolynomial.eval₂_assoc f x (fun i ↦ MvPolynomial.X i ^ m)
      (p.homogenize n)).symm

end Polynomial
