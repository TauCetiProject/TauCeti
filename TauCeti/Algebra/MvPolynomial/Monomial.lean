/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Finsupp.Multiset
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

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
* `TauCeti.prod_X_pow_eq_monomial_equivFunOnFinite_symm`: `(X₁ ⋯ Xₙ) ^ k` is the
  monomial with all exponents `k`.
* `MvPolynomial.coeff_prod_univ_X_pow`: the coefficients of the monomial `∏ᵢ Xᵢ ^ Lᵢ` in finitely
  many variables.
* `MvPolynomial.coeff_prod_X_pow_mul_prod_X_pow`: the coefficients of a product `Xᵃ Yᵇ` of
  monomials in two disjoint groups of variables.
* `MvPolynomial.coeff_prod_X_mul_X_pow_eq_zero`: the monomials `∏_{(i, j)} (XᵢYⱼ) ^ lᵢⱼ` with
  `∑ l = d` have no coefficient outside bidegree `(d, d)` in the two groups of variables.
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

/-- A power of the product of all variables is the monomial with all exponents equal to that
power. -/
theorem prod_X_pow_eq_monomial_equivFunOnFinite_symm {σ R : Type*} [CommSemiring R]
    [Fintype σ] (k : ℕ) :
    (∏ i, X i : MvPolynomial σ R) ^ k = monomial (Finsupp.equivFunOnFinite.symm fun _ ↦ k) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), ← Finset.prod_pow]
  simp

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

/-- The monomials `∏_{(i, j)} (XᵢYⱼ) ^ lᵢⱼ` with `∑ l = d` have weight `d` in each group of
variables, so they have no coefficient outside bidegree `(d, d)`. -/
theorem coeff_prod_X_mul_X_pow_eq_zero {d : ℕ} {κ : Type*} [Fintype ι] [Fintype κ]
    {l : ι × κ →₀ ℕ} (hl : ∑ p, l p = d) {e : ι ⊕ κ →₀ ℕ}
    (h : ¬((∑ i, e (Sum.inl i) = d) ∧ ∑ j, e (Sum.inr j) = d)) :
    (∏ p, (X (Sum.inl p.1) * X (Sum.inr p.2) : MvPolynomial (ι ⊕ κ) A) ^ l p).coeff e = 0 := by
  have hw (w : ι ⊕ κ → ℕ) : IsWeightedHomogeneous w
      (∏ p, (X (Sum.inl p.1) * X (Sum.inr p.2) : MvPolynomial (ι ⊕ κ) A) ^ l p)
      (∑ p, l p • (w (Sum.inl p.1) + w (Sum.inr p.2))) :=
    IsWeightedHomogeneous.prod _ _ _ fun p _ ↦
      ((isWeightedHomogeneous_X A w _).mul (isWeightedHomogeneous_X A w _)).pow (l p)
  have hweight (w : ι ⊕ κ → ℕ) : Finsupp.weight w e =
      ∑ i, e (Sum.inl i) * w (Sum.inl i) + ∑ j, e (Sum.inr j) * w (Sum.inr j) := by
    simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_sum_type]
  rcases not_and_or.mp h with h | h
  · exact (hw (Sum.elim 1 0)).coeff_eq_zero e (by simpa [hweight, hl] using h)
  · exact (hw (Sum.elim 0 1)).coeff_eq_zero e (by simpa [hweight, hl] using h)

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
