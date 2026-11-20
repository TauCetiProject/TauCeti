/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# Binary monomials

In two variables, with `x = X 0` and `y = X 1`, the monomials `x ^ (d - i) * y ^ i` for
`0 ≤ i ≤ d` form a basis of the forms of degree `d`; `TauCeti.polynomialMonomial R d i` denotes
them, extended by zero for `i > d`. A diagonal matrix `diag(t₀, t₁)` acting by the substitution of
standard vectors `TauCeti.polynomialAction` scales `x ^ (d - i) * y ^ i` by
`t₀ ^ (d - i) * t₁ ^ i`, so it has weight `(d - i, i)`.

## Main definitions

* `TauCeti.polynomialMonomial`: the binary monomial `x ^ (d - i) * y ^ i`, zero for `i > d`.

## Main results

* `TauCeti.coeff_polynomialMonomial`: the binary monomial has coefficient `1` at the exponent
  `(d - i, i)` when `i ≤ d`, and `0` elsewhere.
* `TauCeti.polynomialAction_diagonal_polynomialMonomial`: the binary monomial has weight
  `(d - i, i)`.

## References

* P. Etingof, *Lie Groups and Lie Algebras*, arXiv:2201.09397v5, §11.4, p. 63: the
  representations of `SL₂` on homogeneous polynomials in two variables.
-/

public section

open MvPolynomial Matrix

namespace TauCeti

section Monomial

variable (R : Type*) [CommSemiring R] (d i : ℕ)

/-- The binary monomial `e_i^d = x ^ (d - i) * y ^ i` of degree `d`, where `x = X 0` and
`y = X 1`, for `i ≤ d`; it is zero for `i > d`. -/
noncomputable def polynomialMonomial : MvPolynomial (Fin 2) R :=
  if i ≤ d then X 0 ^ (d - i) * X 1 ^ i else 0

theorem polynomialMonomial_def :
    polynomialMonomial R d i = if i ≤ d then X 0 ^ (d - i) * X 1 ^ i else 0 :=
  (rfl)

variable {R d i}

theorem polynomialMonomial_of_le (h : i ≤ d) :
    polynomialMonomial R d i = X 0 ^ (d - i) * X 1 ^ i := by
  simp [polynomialMonomial, h]

@[simp]
theorem polynomialMonomial_of_lt (h : d < i) : polynomialMonomial R d i = 0 := by
  simp [polynomialMonomial, h.not_ge]

/-- For `i ≤ d`, the binary monomial `e_i^d` is the monomial with exponent `(d - i, i)` and
coefficient `1`. -/
theorem polynomialMonomial_eq_monomial (h : i ≤ d) :
    polynomialMonomial R d i =
      monomial (Finsupp.single 0 (d - i) + Finsupp.single 1 i) 1 := by
  rw [polynomialMonomial_of_le h, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial,
    one_mul]

variable (R) in
@[simp]
theorem polynomialMonomial_zero_zero : polynomialMonomial R 0 0 = 1 := by
  simp [polynomialMonomial]

variable (R d) in
theorem polynomialMonomial_zero_right : polynomialMonomial R d 0 = X 0 ^ d := by
  simp [polynomialMonomial]

variable (R d) in
theorem polynomialMonomial_self : polynomialMonomial R d d = X 1 ^ d := by
  simp [polynomialMonomial]

variable (R d i) in
/-- The binary monomial `e_i^d` is homogeneous of degree `d`, also when it vanishes. -/
theorem isHomogeneous_polynomialMonomial : (polynomialMonomial R d i).IsHomogeneous d := by
  by_cases h : i ≤ d
  · rw [polynomialMonomial_of_le h]
    simpa only [Nat.sub_add_cancel h] using (isHomogeneous_X_pow 0 (d - i)).mul
      (isHomogeneous_X_pow 1 i)
  · rw [polynomialMonomial_of_lt (not_le.mp h)]
    exact isHomogeneous_zero _ _ _

variable (R d i) in
theorem polynomialMonomial_mem_homogeneousSubmodule :
    polynomialMonomial R d i ∈ homogeneousSubmodule (Fin 2) R d :=
  isHomogeneous_polynomialMonomial R d i

variable (R d i) in
/-- The coefficients of the binary monomial `e_i^d`: `1` at the exponent `(d - i, i)` when
`i ≤ d`, and `0` otherwise. -/
@[simp]
theorem coeff_polynomialMonomial (s : Fin 2 →₀ ℕ) :
    (polynomialMonomial R d i).coeff s =
      if i ≤ d ∧ Finsupp.single 0 (d - i) + Finsupp.single 1 i = s then 1 else 0 := by
  by_cases h : i ≤ d
  · simp [polynomialMonomial_eq_monomial h, coeff_monomial, h]
  · simp [polynomialMonomial_of_lt (not_le.mp h), h]

/-- For `i ≤ d`, the binary monomial `e_i^d` has coefficient `1` at the exponent `(d - i, i)`. -/
theorem coeff_polynomialMonomial_self (h : i ≤ d) :
    (polynomialMonomial R d i).coeff (Finsupp.single 0 (d - i) + Finsupp.single 1 i) = 1 := by
  simp [h]

/-- The binary monomial `e_i^d` has coefficient `0` away from the exponent `(d - i, i)`. -/
theorem coeff_polynomialMonomial_of_ne {s : Fin 2 →₀ ℕ}
    (hs : s ≠ Finsupp.single 0 (d - i) + Finsupp.single 1 i) :
    (polynomialMonomial R d i).coeff s = 0 := by
  rw [coeff_polynomialMonomial, ite_eq_right_iff]
  exact fun h ↦ (hs h.2.symm).elim

variable (R d i) in
/-- **The weight of `e_i^d` is `(d - i, i)`**: the diagonal matrix `diag(t₀, t₁)` scales the
binary monomial `e_i^d` by `t₀ ^ (d - i) * t₁ ^ i`. -/
@[simp]
theorem polynomialAction_diagonal_polynomialMonomial (t : Fin 2 → R) :
    polynomialAction (diagonal t) (polynomialMonomial R d i) =
      (t 0 ^ (d - i) * t 1 ^ i) • polynomialMonomial R d i := by
  by_cases h : i ≤ d
  · rw [polynomialMonomial_of_le h, polynomialAction_diagonal, map_mul, map_pow, map_pow,
      rescale_X, rescale_X, smul_eq_C_mul, mul_pow, mul_pow, map_mul, map_pow, map_pow]
    ring
  · rw [polynomialMonomial_of_lt (not_le.mp h), map_zero, smul_zero]

end Monomial

end TauCeti
