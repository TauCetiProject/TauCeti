/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Finsupp.Multiset

/-!
# Monomials in multivariate polynomial rings

Multiplying together a multiset of variables, one factor per element, gives the monomial whose
exponent vector is the multiplicity function of the multiset: `TauCeti.prod_map_X_eq_monomial`.
Mathlib's `MvPolynomial.prod_X_pow_eq_monomial` says the same thing for a product indexed by the
support of an exponent vector; this is the multiset-indexed form, which is how the monomials of
`MvPolynomial.hsymm` and `MvPolynomial.msymm` are written.

The file also computes Mathlib's embedding `Polynomial.toMvPolynomial i`, which places a
univariate polynomial in the variable `Xᵢ`, on monomials.

## Main results

* `TauCeti.prod_map_X_eq_monomial`: the product of a multiset of variables is the monomial with
  coefficient `1` at the multiplicity function of the multiset.
* `MvPolynomial.coeff_prod_univ_X_pow`: the coefficients of the monomial `∏ᵢ Xᵢ ^ Lᵢ` in finitely
  many variables.
* `MvPolynomial.coeff_prod_X_pow_mul_prod_X_pow`: the coefficients of a product `Xᵃ Yᵇ` of
  monomials in two disjoint groups of variables.
* `MvPolynomial.eval₂_monomial_sumElim_of_eq_one`: evaluating `c X^a Y^e` with every `X`
  variable set to `1` gives the value of `c Y^e`.
* `Polynomial.toMvPolynomial_monomial`: a univariate monomial placed in `Xᵢ` is the multivariate
  monomial with exponent `n eᵢ`.
-/

public section

namespace TauCeti

open MvPolynomial

/-- **A monomial is the product of the variables it uses, with multiplicity.**  This is the form
in which the monomials of `MvPolynomial.hsymm` and `MvPolynomial.msymm` are written. -/
theorem prod_map_X_eq_monomial {σ : Type*} [DecidableEq σ] {R : Type*} [CommSemiring R]
    (s : Multiset σ) :
    (s.map (X : σ → MvPolynomial σ R)).prod = monomial s.toFinsupp (1 : R) := by
  rw [Finset.prod_multiset_map_count, ← prod_X_pow_eq_monomial, Multiset.toFinsupp_support]
  exact Finset.prod_congr rfl fun a _ => by rw [Multiset.toFinsupp_apply]

end TauCeti

namespace MvPolynomial

variable {ι A : Type*} [CommSemiring A]

/-- The coefficient of `Xᴷ` in the monomial `∏ᵢ Xᵢ ^ Lᵢ` in finitely many variables is `1` when
the exponents agree and `0` otherwise. -/
theorem coeff_prod_univ_X_pow [Fintype ι] (L : ι → ℕ) (K : ι →₀ ℕ) :
    (∏ i, (X i : MvPolynomial ι A) ^ L i).coeff K = if ∀ i, L i = K i then 1 else 0 := by
  classical
  simp [coeff_prod_X_pow, Finsupp.ext_iff, eq_comm]

/-- The coefficient of `Xᵉ` in the product `Xᵃ Yᵇ` of monomials in two disjoint groups of
finitely many variables `Xᵢ = X (inl i)` and `Yⱼ = X (inr j)` is `1` when `a` and `b` are the
restrictions of `e` and `0` otherwise. -/
theorem coeff_prod_X_pow_mul_prod_X_pow {κ : Type*} [Fintype ι] [Fintype κ] (a : ι → ℕ)
    (b : κ → ℕ) (e : ι ⊕ κ →₀ ℕ) :
    ((∏ i, (X (Sum.inl i) : MvPolynomial (ι ⊕ κ) A) ^ a i) *
        ∏ j, (X (Sum.inr j) : MvPolynomial (ι ⊕ κ) A) ^ b j).coeff e =
      if (∀ i, a i = e (Sum.inl i)) ∧ ∀ j, b j = e (Sum.inr j) then 1 else 0 := by
  have h := Fintype.prod_sum_type (fun k ↦ (X k : MvPolynomial (ι ⊕ κ) A) ^ Sum.elim a b k)
  simp only [Sum.elim_inl, Sum.elim_inr] at h
  rw [← h, coeff_prod_univ_X_pow]
  simp [Sum.forall]

/-- Evaluating the monomial `c X^a Y^e` in the variables `τ ⊕ σ` at a point whose `.inl`
coordinates are all `1` gives the value of `c Y^e` at the `.inr` coordinates. -/
theorem eval₂_monomial_sumElim_of_eq_one {σ τ R T : Type*} [CommSemiring R] [CommSemiring T]
    (φ : R →+* T) (x : τ ⊕ σ → T) (hx : ∀ h, x (.inl h) = 1) (a : τ →₀ ℕ) (e : σ →₀ ℕ)
    (c : R) :
    eval₂ φ x (monomial (a.sumElim e) c) = eval₂ φ (x ∘ Sum.inr) (monomial e c) := by
  simp [eval₂_monomial, Finsupp.prod_sumElim, Function.comp_def, hx]

end MvPolynomial

namespace Polynomial

/-- A univariate monomial placed in the variable `Xᵢ` is the monomial with exponent `n eᵢ`. -/
@[simp]
theorem toMvPolynomial_monomial {R σ : Type*} [CommSemiring R] (i : σ) (n : ℕ) (a : R) :
    (monomial n a).toMvPolynomial i = MvPolynomial.monomial (Finsupp.single i n) a := by
  simp [toMvPolynomial, MvPolynomial.X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
    MvPolynomial.C_mul_monomial]

end Polynomial
