/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Absolute values of values of integer polynomials

Let `P ∈ ℤ[X_i : i ∈ ι]` have partial degrees `degreeOf i P ≤ L i` and length
`ℓ(P) = ∑_s |c_s|`, the sum of the absolute values of its coefficients. For a point `x` of a
commutative ring `R` and an absolute value `v` on `R`, the value
`P(x) = ∑_s c_s ∏ i, x_i ^ s_i` satisfies:

* `v(P(x)) ≤ ℓ(P) ∏ i, max(v(x_i), 1) ^ L i`;
* if `v` is nonarchimedean, the integer coefficients have `v(c_s) ≤ 1` and the ultrametric
  inequality removes the factor `ℓ(P)`: `v(P(x)) ≤ ∏ i, max(v(x_i), 1) ^ L i`.

These are the local estimates behind height bounds for values of integer polynomials.

## Main results

* `MvPolynomial.one_le_sum_abs_coeff`: a nonzero integer polynomial has length `ℓ(P) ≥ 1`.
* `AbsoluteValue.apply_prod_pow_le`: `v(∏ i, x_i ^ s_i) ≤ ∏ i, max(v(x_i), 1) ^ L i` for `s ≤ L`.
* `AbsoluteValue.apply_coeff_mul_prod_pow_le`: the same bound `v(c_s) ∏ i, max(v(x_i), 1) ^ L i`
  for a single term `c_s ∏ i, x_i ^ s_i` of `P(x)`.
* `AbsoluteValue.apply_aeval_le`: `v(P(x)) ≤ ℓ(P) ∏ i, max(v(x_i), 1) ^ L i`.
* `IsNonarchimedean.apply_aeval_le`: `v(P(x)) ≤ ∏ i, max(v(x_i), 1) ^ L i` for nonarchimedean `v`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §1.6.
-/

public section

open Finset MvPolynomial

variable {ι : Type*}

namespace MvPolynomial

/-- A nonzero integer polynomial has length `ℓ(P) ≥ 1`: the sum of the absolute values of its
coefficients is at least `1`, since it has a nonzero integer coefficient. -/
theorem one_le_sum_abs_coeff {P : MvPolynomial ι ℤ} (hP : P ≠ 0) :
    1 ≤ ∑ s ∈ P.support, |(P.coeff s : ℝ)| := by
  obtain ⟨s, hs⟩ := support_nonempty.mpr hP
  refine le_trans ?_ (single_le_sum (fun s _ ↦ abs_nonneg _) hs)
  exact_mod_cast Int.one_le_abs (mem_support_iff.mp hs)

end MvPolynomial

variable [Fintype ι]

namespace AbsoluteValue

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- A monomial `∏ i, x_i ^ s_i` with exponents `s_i ≤ L i` has absolute value at most
`∏ i, max(v(x_i), 1) ^ L i`. -/
theorem apply_prod_pow_le (v : AbsoluteValue R ℝ) {s L : ι → ℕ} (hs : ∀ i, s i ≤ L i)
    (x : ι → R) : v (∏ i, x i ^ s i) ≤ ∏ i, max (v (x i)) 1 ^ L i := by
  rw [map_prod]
  refine prod_le_prod₀ (fun i _ ↦ by positivity) fun i _ ↦ ?_
  rw [v.map_pow]
  exact (pow_le_pow_left₀ (v.nonneg _) (le_max_left _ _) _).trans
    (pow_le_pow_right₀ (le_max_right _ _) (hs i))

/-- A term `c_s ∏ i, x_i ^ s_i` of the value at `x` of an integer polynomial `P` with partial
degrees `degreeOf i P ≤ L i` has absolute value at most `v(c_s) ∏ i, max(v(x_i), 1) ^ L i`. -/
theorem apply_coeff_mul_prod_pow_le (v : AbsoluteValue R ℝ) {P : MvPolynomial ι ℤ} {L : ι → ℕ}
    (hL : ∀ i, P.degreeOf i ≤ L i) (x : ι → R) {s : ι →₀ ℕ} (hs : s ∈ P.support) :
    v (algebraMap ℤ R (P.coeff s) * ∏ i, x i ^ s i) ≤
      v (P.coeff s : R) * ∏ i, max (v (x i)) 1 ^ L i := by
  rw [v.map_mul, algebraMap_int_eq, eq_intCast]
  exact mul_le_mul_of_nonneg_left
    (v.apply_prod_pow_le (fun i ↦ (monomial_le_degreeOf i hs).trans (hL i)) x) (v.nonneg _)

/-- The value of an integer polynomial `P` with partial degrees `degreeOf i P ≤ L i` at a point
`x` has absolute value at most `ℓ(P) ∏ i, max(v(x_i), 1) ^ L i`, where `ℓ(P)` is the sum of the
absolute values of the coefficients of `P`. -/
theorem apply_aeval_le (v : AbsoluteValue R ℝ) {P : MvPolynomial ι ℤ} {L : ι → ℕ}
    (hL : ∀ i, P.degreeOf i ≤ L i) (x : ι → R) :
    v (aeval x P) ≤ (∑ s ∈ P.support, |(P.coeff s : ℝ)|) * ∏ i, max (v (x i)) 1 ^ L i := by
  rw [aeval_def, eval₂_eq', sum_mul]
  refine (v.sum_le _ _).trans <| sum_le_sum fun s hs ↦ ?_
  have hc : v (P.coeff s : R) ≤ |(P.coeff s : ℝ)| := by
    rw [← v.apply_natAbs_eq]
    exact (v.apply_nat_le_self _).trans_eq (by rw [Nat.cast_natAbs, Int.cast_abs])
  exact (v.apply_coeff_mul_prod_pow_le hL x hs).trans
    (mul_le_mul_of_nonneg_right hc (by positivity))

end AbsoluteValue

namespace IsNonarchimedean

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- At a nonarchimedean absolute value the value of an integer polynomial `P` with partial
degrees `degreeOf i P ≤ L i` at a point `x` has absolute value at most
`∏ i, max(v(x_i), 1) ^ L i`: the integer coefficients have absolute value at most `1`. -/
theorem apply_aeval_le {v : AbsoluteValue R ℝ} (hv : IsNonarchimedean v)
    {P : MvPolynomial ι ℤ} {L : ι → ℕ} (hL : ∀ i, P.degreeOf i ≤ L i) (x : ι → R) :
    v (aeval x P) ≤ ∏ i, max (v (x i)) 1 ^ L i := by
  rcases P.support.eq_empty_or_nonempty with hP | hP
  · rw [support_eq_empty.mp hP, map_zero, v.map_zero]
    positivity
  rw [aeval_def, eval₂_eq']
  refine (hv.apply_sum_le_sup hP).trans <| sup'_le _ _ fun s hs ↦ ?_
  exact (v.apply_coeff_mul_prod_pow_le hL x hs).trans <| mul_le_of_le_one_left (by positivity)
    (hv.apply_intCast_le_one (by simp) v.map_one v.map_neg)

end IsNonarchimedean
