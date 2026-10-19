/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Coefficient bounds for products and determinants of polynomials

Let `v` be an absolute value on a commutative semiring `R`. If every coefficient of `p` and of `q`
is bounded by `r` and `s` under `v`, then each coefficient of `p * q` is a sum of at most
`#p.support` products of coefficients, so it is bounded by `#p.support * (r * s)`. If `v` is
nonarchimedean, the ultrametric inequality removes the count. Iterating gives bounds for
finite products, and through the Leibniz expansion for determinants of matrices of polynomials:
an `m × m` determinant has at most `m!` terms, each a product of `m` entries.

The product estimates allow semiring-valued absolute values. Finite products use a commutative
domain as the value semiring so that `v 1 = 1`; the nonarchimedean estimates use a linear order,
while the other product estimates need only a partial order.

A polynomial whose partial degrees are `d j` has at most `∏ j, (d j + 1) ≤ 2 ^ ∑ j, d j`
monomials, which turns the support counts into powers of two.

These are the local estimates behind height bounds for products of polynomials and for
determinants of matrices of polynomials, such as the generalized Wronskians in the proof of
Roth's lemma.

## Main results

* `MvPolynomial.card_support_le_two_pow`: `#p.support ≤ 2 ^ ∑ j, p.degreeOf j`.
* `MvPolynomial.abv_coeff_prod_le`, `MvPolynomial.abv_coeff_prod_le_of_isNonarchimedean`:
  coefficient bounds for finite products.
* `MvPolynomial.abv_coeff_prod_le_two_pow`: without zero divisors,
  `v ((∏ k ∈ s, f k).coeff t) ≤ 2 ^ (∑ j, (∏ k ∈ s, f k).degreeOf j) * ∏ k ∈ s, C k`.
* `Matrix.abv_coeff_det_le`, `Matrix.abv_coeff_det_le_of_isNonarchimedean`: coefficient bounds
  for determinants of matrices of polynomials.

## References

* L. Pottmeyer, *Diophantine Approximation* (2022), §3.2, p. 84, and §3.4.6.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), Lemma 1.6.11.
* The arrangement of the product and determinant estimates follows Ralf Stephan's
  `DiophantineApproximation/PolynomialDeterminantHeight.lean` in `rwst/Subspace-Theorems`,
  snapshot `c26d909dc48cf7fe` (Apache 2.0).
-/

public section

open Finset
open scoped Nat

namespace MvPolynomial

section Support

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

/-- A polynomial in finitely many variables has at most `∏ j, (p.degreeOf j + 1)` monomials. -/
theorem card_support_le_prod_degreeOf (p : MvPolynomial σ R) :
    #p.support ≤ ∏ j, (p.degreeOf j + 1) := by
  classical
  calc #p.support
      ≤ #(Fintype.piFinset fun j ↦ range (p.degreeOf j + 1)) :=
        card_le_card_of_injOn (fun m ↦ ⇑m)
          (fun m hm ↦ by
            simpa [Nat.lt_succ_iff] using fun j ↦ monomial_le_degreeOf j (mem_coe.mp hm))
          (fun _ _ _ _ h ↦ DFunLike.coe_injective h)
    _ = ∏ j, (p.degreeOf j + 1) := by simp

/-- A polynomial in finitely many variables has at most `2 ^ ∑ j, p.degreeOf j` monomials. -/
theorem card_support_le_two_pow (p : MvPolynomial σ R) :
    #p.support ≤ 2 ^ ∑ j, p.degreeOf j := by
  rw [← prod_pow_eq_pow_sum]
  exact (card_support_le_prod_degreeOf p).trans
    (prod_le_prod fun j _ ↦ Nat.lt_two_pow_self)

end Support

section AbsoluteValue

variable {σ R S : Type*} [CommSemiring R]

/-- If the coefficients of `p` and `q` are bounded by `r` and `s` under an absolute value `v`,
then each coefficient of `p * q` is bounded by `#p.support * (r * s)`. -/
theorem abv_coeff_mul_le [Semiring S] [PartialOrder S] [IsOrderedRing S] {v : AbsoluteValue R S}
    (p q : MvPolynomial σ R) {r s : S} (hp : ∀ a, v (p.coeff a) ≤ r)
    (hq : ∀ a, v (q.coeff a) ≤ s) (t : σ →₀ ℕ) :
    v ((p * q).coeff t) ≤ #p.support * (r * s) := by
  classical
  have hrs : 0 ≤ r * s := mul_nonneg ((v.nonneg _).trans (hp 0)) ((v.nonneg _).trans (hq 0))
  have hpq : p * q = ∑ a ∈ p.support, monomial a (p.coeff a) * q := by
    rw [← sum_mul, ← as_sum]
  calc v ((p * q).coeff t)
      ≤ ∑ a ∈ p.support, v ((monomial a (p.coeff a) * q).coeff t) := by
        rw [hpq, coeff_sum]
        exact v.sum_le _ _
    _ ≤ ∑ _a ∈ p.support, r * s := sum_le_sum fun a _ ↦ by
        rw [coeff_monomial_mul']
        split_ifs
        · rw [map_mul]
          exact mul_le_mul (hp a) (hq _) (v.nonneg _) ((v.nonneg _).trans (hp a))
        · simpa using hrs
    _ = #p.support * (r * s) := by rw [sum_const, nsmul_eq_mul]

/-- If `v` is nonarchimedean and the coefficients of `p` and `q` are bounded by `r` and `s`,
then the coefficients of `p * q` are bounded by `r * s`. -/
theorem abv_coeff_mul_le_of_isNonarchimedean [Semiring S] [LinearOrder S] [PosMulMono S]
    [MulPosMono S] {v : AbsoluteValue R S} (p q : MvPolynomial σ R) (hv : IsNonarchimedean v)
    {r s : S} (hp : ∀ a, v (p.coeff a) ≤ r) (hq : ∀ a, v (q.coeff a) ≤ s) (t : σ →₀ ℕ) :
    v ((p * q).coeff t) ≤ r * s := by
  classical
  have hne : (antidiagonal t).Nonempty := ⟨(0, t), by simp⟩
  rw [coeff_mul]
  refine (hv.apply_sum_le_sup hne).trans (sup'_le hne _ fun x _ ↦ ?_)
  rw [map_mul]
  exact mul_le_mul (hp _) (hq _) (v.nonneg _) ((v.nonneg _).trans (hp x.1))

variable [Nontrivial R]

/-- If the coefficients of each `f k` are bounded by `C k` under an absolute value `v`, then each
coefficient of `∏ k ∈ s, f k` is bounded by `∏ k ∈ s, #(f k).support * C k`. -/
theorem abv_coeff_prod_le [CommSemiring S] [PartialOrder S] [IsOrderedRing S] [IsDomain S]
    {v : AbsoluteValue R S} {ι : Type*} {s : Finset ι} (f : ι → MvPolynomial σ R) {C : ι → S}
    (hf : ∀ k ∈ s, ∀ a, v ((f k).coeff a) ≤ C k) (t : σ →₀ ℕ) :
    v ((∏ k ∈ s, f k).coeff t) ≤ ∏ k ∈ s, (#(f k).support * C k) := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty =>
    rw [prod_empty, prod_empty, coeff_one]
    split_ifs <;> simp [v.map_one]
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, mul_assoc]
    exact abv_coeff_mul_le _ _ (hf a (mem_insert_self a s))
      (ih fun k hk ↦ hf k (mem_insert_of_mem hk)) t

/-- If `v` is nonarchimedean and the coefficients of each `f k` are bounded by `C k`, then the
coefficients of `∏ k ∈ s, f k` are bounded by `∏ k ∈ s, C k`. -/
theorem abv_coeff_prod_le_of_isNonarchimedean [CommSemiring S] [LinearOrder S] [IsOrderedRing S]
    [IsDomain S] {v : AbsoluteValue R S} {ι : Type*} {s : Finset ι}
    (f : ι → MvPolynomial σ R) (hv : IsNonarchimedean v) {C : ι → S}
    (hf : ∀ k ∈ s, ∀ a, v ((f k).coeff a) ≤ C k) (t : σ →₀ ℕ) :
    v ((∏ k ∈ s, f k).coeff t) ≤ ∏ k ∈ s, C k := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty =>
    rw [prod_empty, prod_empty, coeff_one]
    split_ifs <;> simp [v.map_one]
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact abv_coeff_mul_le_of_isNonarchimedean _ _ hv (hf a (mem_insert_self a s))
      (ih fun k hk ↦ hf k (mem_insert_of_mem hk)) t

/-- If `R` has no zero divisors and the coefficients of each `f k` are bounded by `C k` under an
absolute value `v`, then each coefficient of `∏ k ∈ s, f k` is bounded by
`2 ^ (∑ j, (∏ k ∈ s, f k).degreeOf j) * ∏ k ∈ s, C k`. -/
theorem abv_coeff_prod_le_two_pow [CommSemiring S] [PartialOrder S] [IsOrderedRing S] [IsDomain S]
    {v : AbsoluteValue R S} [Fintype σ] [NoZeroDivisors R] {ι : Type*} {s : Finset ι}
    (f : ι → MvPolynomial σ R) {C : ι → S} (hf : ∀ k ∈ s, ∀ a, v ((f k).coeff a) ≤ C k)
    (t : σ →₀ ℕ) :
    v ((∏ k ∈ s, f k).coeff t) ≤ 2 ^ (∑ j, (∏ k ∈ s, f k).degreeOf j) * ∏ k ∈ s, C k := by
  classical
  have hC : ∀ k ∈ s, 0 ≤ C k := fun k hk ↦ (v.nonneg _).trans (hf k hk 0)
  by_cases h0 : ∃ k ∈ s, f k = 0
  · obtain ⟨k, hk, hk0⟩ := h0
    rw [prod_eq_zero hk hk0]
    simpa using prod_nonneg hC
  push Not at h0
  calc v ((∏ k ∈ s, f k).coeff t) ≤ ∏ k ∈ s, (#(f k).support * C k) := abv_coeff_prod_le f hf t
    _ ≤ ∏ k ∈ s, ((2 : S) ^ (∑ j, (f k).degreeOf j) * C k) := by
      refine prod_le_prod₀ (fun k hk ↦ mul_nonneg (Nat.cast_nonneg _) (hC k hk)) fun k hk ↦ ?_
      refine mul_le_mul_of_nonneg_right ?_ (hC k hk)
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        (Nat.mono_cast (card_support_le_two_pow (f k)) :
          (#(f k).support : S) ≤ (2 ^ ∑ j, (f k).degreeOf j : ℕ))
    _ = 2 ^ (∑ j, (∏ k ∈ s, f k).degreeOf j) * ∏ k ∈ s, C k := by
      rw [prod_mul_distrib, prod_pow_eq_pow_sum, sum_comm]
      simp only [degreeOf_prod_eq s f h0]

end AbsoluteValue

end MvPolynomial

namespace Matrix

open Equiv MvPolynomial

variable {σ R S : Type*} [CommRing R] [Nontrivial R]
  [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] {v : AbsoluteValue R S}
  {n : Type*} [Fintype n] [DecidableEq n]

/-- If the entries of an `n × n` matrix of polynomials have at most `B` monomials each and
coefficients bounded by `C` under an absolute value `v`, then each coefficient of its determinant
is bounded by `n! • (B * C) ^ n`. -/
theorem abv_coeff_det_le (A : Matrix n n (MvPolynomial σ R)) {B : ℕ} {C : S}
    (hB : ∀ i j, #(A i j).support ≤ B) (hA : ∀ i j a, v ((A i j).coeff a) ≤ C)
    (t : σ →₀ ℕ) :
    v (A.det.coeff t) ≤ (Fintype.card n)! • (B * C) ^ Fintype.card n := by
  calc v (A.det.coeff t)
      ≤ ∑ τ : Perm n, v ((∏ i, A (τ i) i).coeff t) := by
        rw [det_apply, coeff_sum]
        refine (v.sum_le _ _).trans_eq (sum_congr rfl fun τ _ ↦ ?_)
        rw [coeff_smul, v.map_units_int_smul]
    _ ≤ ∑ _τ : Perm n, (B * C) ^ Fintype.card n := sum_le_sum fun τ _ ↦ by
        refine (abv_coeff_prod_le _ (fun i _ ↦ hA (τ i) i) t).trans ?_
        rw [← card_univ, ← prod_const]
        exact prod_le_prod₀
          (fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) ((v.nonneg _).trans (hA (τ i) i 0)))
          fun i _ ↦ mul_le_mul_of_nonneg_right (by exact_mod_cast hB (τ i) i)
            ((v.nonneg _).trans (hA (τ i) i 0))
    _ = (Fintype.card n)! • (B * C) ^ Fintype.card n := by simp [Fintype.card_perm]

/-- If `v` is nonarchimedean and the entries of an `n × n` matrix of polynomials have
coefficients bounded by `C`, then the coefficients of its determinant are bounded by `C ^ n`. -/
theorem abv_coeff_det_le_of_isNonarchimedean (A : Matrix n n (MvPolynomial σ R))
    (hv : IsNonarchimedean v) {C : S} (hA : ∀ i j a, v ((A i j).coeff a) ≤ C)
    (t : σ →₀ ℕ) :
    v (A.det.coeff t) ≤ C ^ Fintype.card n := by
  have hne : (univ : Finset (Perm n)).Nonempty := univ_nonempty
  rw [det_apply, coeff_sum]
  refine (hv.apply_sum_le_sup hne).trans (sup'_le hne _ fun τ _ ↦ ?_)
  rw [coeff_smul, v.map_units_int_smul, ← card_univ, ← prod_const]
  exact abv_coeff_prod_le_of_isNonarchimedean _ hv (fun i _ ↦ hA (τ i) i) t

end Matrix
