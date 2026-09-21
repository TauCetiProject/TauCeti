/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Vieta's formulas for a family of roots indexed by a finite type

Mathlib reads the coefficients of a product of linear factors off the elementary symmetric
functions of the multiset of its roots (`Multiset.prod_X_sub_C_coeff`). Here the roots are a
family `x : σ → S` indexed by a finite type and the elementary symmetric functions are the
values of `MvPolynomial.esymm`: the `k`-th elementary symmetric polynomial at `x` is `(-1) ^ k`
times the coefficient of `∏ i, (X - C (x i))` in degree `card σ - k`.

Over a domain a monic polynomial of degree `card σ` whose roots, listed with multiplicity, are
the values of `x` is exactly that product, so the same formula computes its coefficients.

## Main results

* `MvPolynomial.aeval_esymm_eq_coeff_prod_X_sub_C`: the elementary symmetric polynomials at `x`
  are the signed coefficients of `∏ i, (X - C (x i))`.
* `Polynomial.eq_prod_X_sub_C_of_monic_of_roots_eq`: a monic polynomial whose roots are listed by
  `x` is the product of the linear factors `X - C (x i)`.
-/

public section

namespace MvPolynomial

variable {σ R S : Type*} [Fintype σ] [CommSemiring R] [CommRing S] [Algebra R S]

/-- **Vieta's formulas for an indexed family of roots**: the `k`-th elementary symmetric
polynomial, evaluated at `x : σ → S`, is `(-1) ^ k` times the coefficient of the monic polynomial
`∏ i, (X - C (x i))` in degree `card σ - k`. -/
theorem aeval_esymm_eq_coeff_prod_X_sub_C (x : σ → S) {k : ℕ} (hk : k ≤ Fintype.card σ) :
    aeval x (esymm σ R k) =
      (-1) ^ k * (∏ i, (Polynomial.X - Polynomial.C (x i))).coeff (Fintype.card σ - k) := by
  have hcard : Multiset.card (Finset.univ.val.map x) = Fintype.card σ := by simp
  have hprod : (∏ i, (Polynomial.X - Polynomial.C (x i))) =
      ((Finset.univ.val.map x).map fun t => Polynomial.X - Polynomial.C t).prod := by
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  rw [aeval_esymm_eq_multiset_esymm, hprod,
    Multiset.prod_X_sub_C_coeff _ (by rw [hcard]; exact Nat.sub_le _ _), hcard,
    Nat.sub_sub_self hk, ← mul_assoc, ← pow_add, ← Nat.two_mul, pow_mul]
  norm_num

end MvPolynomial

namespace Polynomial

variable {σ R : Type*} [Fintype σ] [CommRing R] [IsDomain R]

/-- A monic polynomial of degree `card σ` whose roots, with multiplicity, are listed by
`x : σ → R` is the product of the linear factors `X - C (x i)`. -/
theorem eq_prod_X_sub_C_of_monic_of_roots_eq {f : R[X]} {x : σ → R} (hf : f.Monic)
    (hdeg : f.natDegree = Fintype.card σ) (hroots : f.roots = Finset.univ.val.map x) :
    f = ∏ i, (X - C (x i)) := by
  have hcard : Multiset.card f.roots = f.natDegree := by simp [hroots, hdeg]
  conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hf hcard]
  rw [hroots, Finset.prod_eq_multiset_prod, Multiset.map_map]
  rfl

end Polynomial
