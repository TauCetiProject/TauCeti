/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Order
import TauCeti.Algebra.MvPolynomial.Coeff
import TauCeti.Algebra.MvPolynomial.Support
import TauCeti.Data.Finsupp.Weight

/-!
# Coefficient bounds for products, substitutions, and determinants of polynomials

Let `v` be an absolute value on a commutative semiring `R`. If every coefficient of `p` and of `q`
is bounded by `r` and `s` under `v`, then each coefficient of `p * q` is a sum of at most
`#p.support` products of coefficients, so it is bounded by `#p.support * (r * s)`. If `v` is
nonarchimedean, the ultrametric inequality removes the count. Iterating gives bounds for
finite products, for arbitrary polynomial substitutions `aeval f` on monomials and homogeneous
polynomials, and through the Leibniz expansion for determinants of matrices of polynomials:
an `m × m` determinant has at most `m!` terms, each a product of `m` entries.

The product estimates allow semiring-valued absolute values. Finite products use a commutative
domain as the value semiring so that `v 1 = 1`; the nonarchimedean estimates use a linear order,
while the other product estimates need only a partial order.

A polynomial whose partial degrees are `d j` has at most `∏ j, (d j + 1) ≤ 2 ^ ∑ j, d j`
monomials, which turns the support counts into powers of two.

For a finite sum of monomials with distinct exponents (in particular, a finite linear combination
of distinct variables), each coefficient is either one of the summands or zero, so a uniform
nonnegative bound on the summands transfers directly to all coefficients.

These are the local estimates behind height bounds for products of polynomials and for
determinants of matrices of polynomials, such as the generalized Wronskians in the proof of
Roth's lemma.

## Main results

* `MvPolynomial.card_support_le_two_pow`: `#p.support ≤ 2 ^ ∑ j, p.degreeOf j`.
* `MvPolynomial.abv_coeff_le_iSup_support`: `v (p.coeff b) ≤ ⨆ c : p.support, v (p.coeff c)`.
* `MvPolynomial.abv_coeff_sum_monomial_le`, `MvPolynomial.abv_coeff_sum_C_mul_X_le`: coefficient
  bounds for finite sums of monomials with distinct exponents and for finite linear combinations of
  distinct variables.
* `MvPolynomial.abv_coeff_prod_le`, `MvPolynomial.abv_coeff_prod_le_of_isNonarchimedean`:
  coefficient bounds for finite products.
* `MvPolynomial.abv_coeff_prod_le_two_pow`: without zero divisors,
  `v ((∏ k ∈ s, f k).coeff t) ≤ 2 ^ (∑ j, (∏ k ∈ s, f k).degreeOf j) * ∏ k ∈ s, C k`.
* `MvPolynomial.abv_coeff_aeval_monomial_le`,
  `MvPolynomial.abv_coeff_aeval_monomial_le_of_isNonarchimedean`: coefficient bounds for `aeval` on
  a monomial.
* `MvPolynomial.abv_coeff_aeval_le_of_isHomogeneous`,
  `MvPolynomial.abv_coeff_aeval_le_of_isHomogeneous_of_isNonarchimedean`: coefficient bounds for
  `aeval` on a homogeneous polynomial.
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

/-- Every coefficient of `p` has absolute value at most the supremum over `p.support`. -/
theorem abv_coeff_le_iSup_support (v : AbsoluteValue R ℝ) (p : MvPolynomial σ R) (b : σ →₀ ℕ) :
    v (p.coeff b) ≤ ⨆ c : p.support, v (p.coeff c) := by
  by_cases hb : b ∈ p.support
  · exact Finite.le_ciSup_of_le ⟨b, hb⟩ le_rfl
  · rw [notMem_support_iff.mp hb, map_zero]
    exact Real.iSup_nonneg fun _ ↦ v.nonneg _

/-- If distinct indices in `s` map to distinct exponents under `a` and every coefficient satisfies
`v (w j) ≤ B` with `0 ≤ B`, then every coefficient of `∑ j ∈ s, monomial (a j) (w j)` has
absolute value at most `B`. -/
theorem abv_coeff_sum_monomial_le [Semiring S] [PartialOrder S] {v : AbsoluteValue R S}
    {ι : Type*} {s : Finset ι} {a : ι → σ →₀ ℕ} {w : ι → R} (ha : Set.InjOn a s)
    {B : S} (hB0 : 0 ≤ B) (hw : ∀ j ∈ s, v (w j) ≤ B) (m : σ →₀ ℕ) :
    v ((∑ j ∈ s, monomial (a j) (w j)).coeff m) ≤ B := by
  classical
  by_cases hm : m ∈ s.image a
  · obtain ⟨j₀, hj₀, rfl⟩ := mem_image.1 hm
    rw [coeff_sum_monomial_of_injOn ha hj₀]
    exact hw j₀ hj₀
  · rw [notMem_support_iff.1 fun h ↦ hm (support_sum_monomial_subset s a w h), map_zero]
    exact hB0

/-- If `g` is injective on `s` and every coefficient satisfies `v (w j) ≤ B` with `0 ≤ B`, then
every coefficient of the linear combination `∑ j ∈ s, C (w j) * X (g j)` has absolute value at
most `B`. -/
theorem abv_coeff_sum_C_mul_X_le [Semiring S] [PartialOrder S] {v : AbsoluteValue R S}
    {ι : Type*} {s : Finset ι} {w : ι → R} {g : ι → σ} (hg : Set.InjOn g s)
    {B : S} (hB0 : 0 ≤ B) (hw : ∀ j ∈ s, v (w j) ≤ B) (m : σ →₀ ℕ) :
    v ((∑ j ∈ s, C (w j) * X (g j) : MvPolynomial σ R).coeff m) ≤ B := by
  simp_rw [C_mul_X_eq_monomial]
  exact abv_coeff_sum_monomial_le
    (fun _ hi _ hj h ↦ hg hi hj (Finsupp.single_left_injective one_ne_zero h)) hB0 hw m

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

/-- Substituting polynomials `f i` with `#(f i).support ≤ k` and coefficients bounded by `B` under
`v` into `monomial s a` produces coefficients bounded by `(k * B) ^ s.degree * v a`. -/
theorem abv_coeff_aeval_monomial_le {τ : Type*} [CommSemiring S] [PartialOrder S] [IsOrderedRing S]
    [IsDomain S] {v : AbsoluteValue R S} {f : σ → MvPolynomial τ R} {k : ℕ} {B : S}
    {s : σ →₀ ℕ} (hk : ∀ i ∈ s.support, #(f i).support ≤ k)
    (hB : ∀ i ∈ s.support, ∀ m, v ((f i).coeff m) ≤ B) (a : R) (t : τ →₀ ℕ) :
    v ((aeval f (monomial s a)).coeff t) ≤ (k * B) ^ s.degree * v a := by
  classical
  rw [aeval_monomial, algebraMap_eq, coeff_C_mul, map_mul,
    mul_comm (v a), s.prod_pow_eq_prod_sigma f]
  refine mul_le_mul_of_nonneg_right ?_ (v.nonneg a)
  refine (abv_coeff_prod_le (s := s.support.sigma fun i ↦ range (s i)) (fun q ↦ f q.1)
    (C := fun _ ↦ B) (fun q hq ↦ hB q.1 (mem_sigma.1 hq).1) t).trans ?_
  rw [← s.card_sigma_range_eq_degree, ← prod_const]
  refine prod_le_prod₀ (fun q hq ↦ mul_nonneg (Nat.cast_nonneg _)
    ((v.nonneg _).trans (hB q.1 (mem_sigma.1 hq).1 0))) fun q hq ↦ ?_
  exact mul_le_mul_of_nonneg_right (Nat.mono_cast (hk q.1 (mem_sigma.1 hq).1))
    ((v.nonneg _).trans (hB q.1 (mem_sigma.1 hq).1 0))

/-- Nonarchimedean companion to `abv_coeff_aeval_monomial_le`, without the support-size factor. -/
theorem abv_coeff_aeval_monomial_le_of_isNonarchimedean {τ : Type*} [CommSemiring S] [LinearOrder S]
    [IsOrderedRing S] [IsDomain S] {v : AbsoluteValue R S} (hv : IsNonarchimedean v)
    {f : σ → MvPolynomial τ R} {B : S} {s : σ →₀ ℕ}
    (hB : ∀ i ∈ s.support, ∀ m, v ((f i).coeff m) ≤ B) (a : R) (t : τ →₀ ℕ) :
    v ((aeval f (monomial s a)).coeff t) ≤ B ^ s.degree * v a := by
  classical
  rw [aeval_monomial, algebraMap_eq, coeff_C_mul, map_mul,
    mul_comm (v a), s.prod_pow_eq_prod_sigma f, ← s.card_sigma_range_eq_degree, ← prod_const]
  exact mul_le_mul_of_nonneg_right
    (abv_coeff_prod_le_of_isNonarchimedean (fun q ↦ f q.1) hv
      (fun q hq ↦ hB q.1 (mem_sigma.1 hq).1) t) (v.nonneg a)

/-- For a homogeneous polynomial `p` of degree `n`, substituting polynomials `f i` with
`#(f i).support ≤ k` and coefficients bounded by `B` under `v` into `p`, whose coefficients are
bounded by `C`, produces coefficients bounded by `#p.support * ((k * B) ^ n * C)`. -/
theorem abv_coeff_aeval_le_of_isHomogeneous {τ : Type*} [CommSemiring S] [PartialOrder S]
    [IsOrderedRing S] [IsDomain S] {v : AbsoluteValue R S} {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) {f : σ → MvPolynomial τ R} {k : ℕ} {B C : S}
    (hk : ∀ i ∈ p.vars, #(f i).support ≤ k)
    (hB : ∀ i ∈ p.vars, ∀ m, v ((f i).coeff m) ≤ B)
    (hpC : ∀ a, v (p.coeff a) ≤ C) (t : τ →₀ ℕ) :
    v ((aeval f p).coeff t) ≤ #p.support * ((k * B) ^ n * C) := by
  classical
  have hsum : aeval f p = ∑ s ∈ p.support, aeval f (monomial s (p.coeff s)) := by
    conv_lhs => rw [p.as_sum]
    exact map_sum _ _ _
  calc v ((aeval f p).coeff t)
      ≤ ∑ s ∈ p.support, v ((aeval f (monomial s (p.coeff s))).coeff t) := by
        rw [hsum, coeff_sum]
        exact v.sum_le _ _
    _ ≤ ∑ _s ∈ p.support, (k * B) ^ n * C := sum_le_sum fun s hs ↦ by
        have hdeg : s.degree = n := by
          rw [Finsupp.degree_eq_weight_one (R := ℕ)]
          exact hp (mem_support_iff.1 hs)
        have hsub : s.support ⊆ p.vars := support_subset_vars_of_mem_support hs
        have hpow : 0 ≤ (k * B : S) ^ s.degree := by
          rcases eq_or_ne s 0 with rfl | hs0
          · simp
          · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 hs0
            exact pow_nonneg
              (mul_nonneg (Nat.cast_nonneg _) ((v.nonneg _).trans (hB i (hsub hi) 0))) _
        rw [← hdeg]
        exact (abv_coeff_aeval_monomial_le (fun i hi ↦ hk i (hsub hi))
          (fun i hi ↦ hB i (hsub hi)) (p.coeff s) t).trans
          (mul_le_mul_of_nonneg_left (hpC s) hpow)
    _ = #p.support * ((k * B) ^ n * C) := by rw [sum_const, nsmul_eq_mul]

/-- Nonarchimedean companion to `abv_coeff_aeval_le_of_isHomogeneous`, without the support-size
factors. -/
theorem abv_coeff_aeval_le_of_isHomogeneous_of_isNonarchimedean {τ : Type*} [CommSemiring S]
    [LinearOrder S] [IsOrderedRing S] [IsDomain S] {v : AbsoluteValue R S}
    (hv : IsNonarchimedean v) {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    {f : σ → MvPolynomial τ R} {B C : S} (hB0 : 0 ≤ B)
    (hB : ∀ i ∈ p.vars, ∀ m, v ((f i).coeff m) ≤ B)
    (hpC : ∀ a, v (p.coeff a) ≤ C) (t : τ →₀ ℕ) :
    v ((aeval f p).coeff t) ≤ B ^ n * C := by
  classical
  have hC0 : 0 ≤ C := (v.nonneg _).trans (hpC 0)
  rcases eq_or_ne p 0 with rfl | hp0
  · simpa using mul_nonneg (pow_nonneg hB0 n) hC0
  have hne : p.support.Nonempty := support_nonempty.2 hp0
  have hsum : aeval f p = ∑ s ∈ p.support, aeval f (monomial s (p.coeff s)) := by
    conv_lhs => rw [p.as_sum]
    exact map_sum _ _ _
  rw [hsum, coeff_sum]
  refine (hv.apply_sum_le_sup hne).trans (sup'_le hne _ fun s hs ↦ ?_)
  have hdeg : s.degree = n := by
    rw [Finsupp.degree_eq_weight_one (R := ℕ)]
    exact hp (mem_support_iff.1 hs)
  rw [← hdeg]
  exact (abv_coeff_aeval_monomial_le_of_isNonarchimedean hv
    (fun i hi ↦ hB i (support_subset_vars_of_mem_support hs hi)) (p.coeff s) t).trans
    (mul_le_mul_of_nonneg_left (hpC s) (pow_nonneg hB0 _))

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
        rw [AddMonoidAlgebra.coeff_smul_apply, v.map_units_int_smul]
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
  rw [AddMonoidAlgebra.coeff_smul_apply, v.map_units_int_smul, ← card_univ, ← prod_const]
  exact abv_coeff_prod_le_of_isNonarchimedean _ hv (fun i _ ↦ hA (τ i) i) t

end Matrix
