/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Vieta
import TauCeti.Algebra.Ring.Parity

/-!
# Vieta's formulas for indexed families of roots

Mathlib reads the coefficients of a product of linear factors off the elementary symmetric
functions of the multiset of its roots (`Multiset.prod_X_sub_C_coeff`). Here the roots are a
family `x : σ → S` indexed by a finite type and the elementary symmetric functions are the
values of `MvPolynomial.esymm`: the `k`-th elementary symmetric polynomial at `x` is `(-1) ^ k`
times the coefficient of `∏ i, (X - C (x i))` in degree `card σ - k`.

Over a domain, a monic polynomial whose degree is the size of a finite set `s` and whose
roots, with multiplicity, are the values of `x` on `s` is the product
`∏ i ∈ s, (X - C (x i))`. When `s` is all of a finite type `σ` this is the product above, so the
same formula computes its coefficients.

## Main results

* `MvPolynomial.aeval_esymm_eq_coeff_prod_X_sub_C`: the elementary symmetric polynomials at `x`
  are the signed coefficients of `∏ i, (X - C (x i))`.
* `Polynomial.eq_prod_X_sub_C_of_monic_of_roots_eq`: a monic polynomial whose roots are listed by
  `x` on a finite set `s` is the product of the linear factors `X - C (x i)` over `s`.
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
  rw [aeval_esymm_eq_multiset_esymm, Finset.prod_eq_multiset_prod,
    ← Function.comp_def (fun t => Polynomial.X - Polynomial.C t) x, ← Multiset.map_map,
    Multiset.prod_X_sub_C_coeff _ (by simp)]
  simp [Nat.sub_sub_self hk]

end MvPolynomial

namespace Polynomial

variable {σ R : Type*} [CommRing R] [IsDomain R]

/-- A monic polynomial of degree `s.card` whose roots, with multiplicity, are listed by `x` on the
finite set `s` is the product of the linear factors `X - C (x i)` over `s`. -/
theorem eq_prod_X_sub_C_of_monic_of_roots_eq {f : R[X]} {s : Finset σ} {x : σ → R}
    (hf : f.Monic) (hdeg : f.natDegree = s.card) (hroots : f.roots = s.val.map x) :
    f = ∏ i ∈ s, (X - C (x i)) := by
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hf (by simp [hroots, hdeg]), hroots,
    Multiset.map_map, Function.comp_def, Finset.prod_map_val]

end Polynomial
