/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Products of powers of the polynomials `X ^ n - 1`

A product `∏_{n ∈ I} (X ^ n - 1) ^ e(n)` with `e(0) = 0` (the factor `X ^ 0 - 1` is `0`) is
monic of degree `∑ n e(n)`. In characteristic zero the polynomials `X ^ n - 1`, `n ≥ 1`, are
multiplicatively independent: such a product determines its exponents. In characteristic zero a
primitive `N`-th root of unity is a simple root of `X ^ n - 1` exactly when `N ∣ n`, so its
multiplicity in the product is `∑_{N ∣ n} e(n)`; comparing these multiplicities over `ℂ` for the
largest `N` at which two exponent functions differ separates them. In characteristic `p`
independence fails, since `X ^ p - 1 = (X - 1) ^ p`.

Products of this shape are the integral form of a rational function `∏_n (X ^ n - 1) ^ γ(n)`
with integer exponents, the form in which Beukers, Cohen and Mellit parametrize hypergeometric
data by their gamma vector. Every product of cyclotomic polynomials has this form in
`RatFunc R`, by Möbius inversion of `X ^ n - 1 = ∏_{d ∣ n} Φ_d`.

## Main results

* `Polynomial.monic_prod_X_pow_sub_one_pow`, `Polynomial.natDegree_prod_X_pow_sub_one_pow`: the
  product is monic of degree `∑ n e(n)`.
* `Polynomial.count_roots_prod_X_pow_sub_one_pow`: in characteristic zero, the multiplicity of a
  primitive `N`-th root of unity in the product is `∑_{N ∣ n} e(n)`.
* `Polynomial.eq_of_prod_X_pow_sub_one_pow_eq`: in characteristic zero, equal products have equal
  exponents.
* `Polynomial.algebraMap_prod_cyclotomic_eq_prod_zpow`: a product of cyclotomic polynomials is
  `∏_n (X ^ n - 1) ^ (∑_{a, n ∣ a} μ(a / n))` in `RatFunc R`.

## References

* F. Beukers, H. Cohen and A. Mellit, *Finite hypergeometric functions*, Pure Appl. Math. Q. 11
  (2015), §1.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] {I : Finset ℕ} {e e' : ℕ → ℕ}

/-- A product of powers of the polynomials `X ^ n - 1` is monic when the exponent of
`X ^ 0 - 1 = 0` vanishes. -/
theorem monic_prod_X_pow_sub_one_pow (he : e 0 = 0) :
    (∏ n ∈ I, (X ^ n - 1 : R[X]) ^ e n).Monic := by
  refine monic_prod_of_monic _ _ fun n _ ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · rw [he, pow_zero]
    exact monic_one
  · exact (monic_X_pow_sub_C 1 hn).pow _

/-- A product of powers of the polynomials `X ^ n - 1` has degree `∑ n e(n)` when the exponent
of `X ^ 0 - 1 = 0` vanishes. -/
theorem natDegree_prod_X_pow_sub_one_pow [Nontrivial R] (he : e 0 = 0) :
    (∏ n ∈ I, (X ^ n - 1 : R[X]) ^ e n).natDegree = ∑ n ∈ I, n * e n := by
  have hmonic (n : ℕ) : ((X ^ n - 1 : R[X]) ^ e n).Monic := by
    simpa using monic_prod_X_pow_sub_one_pow (I := {n}) (R := R) (e := e) he
  rw [natDegree_prod_of_monic _ _ fun n _ ↦ hmonic n]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · rw [he, pow_zero, natDegree_one, zero_mul]
  · rw [← C_1, (monic_X_pow_sub_C (1 : R) hn).natDegree_pow, natDegree_X_pow_sub_C, mul_comm]

/-- In characteristic zero, the multiplicity of a primitive `N`-th root of unity `ζ` as a root
of `∏_{n ∈ I} (X ^ n - 1) ^ e(n)` is the sum of the exponents `e(n)` over the multiples `n` of
`N`. -/
theorem count_roots_prod_X_pow_sub_one_pow {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (I : Finset ℕ) {e : ℕ → ℕ} (he : e 0 = 0) :
    (∏ n ∈ I, (X ^ n - 1 : K[X]) ^ e n).roots.count ζ = ∑ n ∈ I, if N ∣ n then e n else 0 := by
  rw [roots_prod _ _ (monic_prod_X_pow_sub_one_pow he).ne_zero, Multiset.count_bind,
    Finset.sum_eq_multiset_sum]
  refine congr_arg Multiset.sum (Multiset.map_congr rfl fun n _ ↦ ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [he]
  rw [roots_pow, Multiset.count_nsmul, ← C_1, ← nthRoots]
  have hnodup : (nthRoots n (1 : K)).Nodup :=
    nodup_roots (C_1 (R := K) ▸ X_pow_sub_one_separable_iff.2 (Nat.cast_ne_zero.2 hn))
  by_cases hNn : N ∣ n
  · rw [ite_eq_left hNn, Multiset.count_eq_one_of_mem hnodup
      ((mem_nthRoots (Nat.pos_of_ne_zero hn)).2 (hζ.pow_eq_one_iff_dvd n |>.2 hNn)), mul_one]
  · rw [ite_eq_right hNn, Multiset.count_eq_zero.2 fun h ↦ hNn <| hζ.pow_eq_one_iff_dvd n |>.1 <|
      (mem_nthRoots (Nat.pos_of_ne_zero hn)).1 h, mul_zero]

/-- Multiplicative independence over `ℂ`, the case of
`Polynomial.eq_of_prod_X_pow_sub_one_pow_eq` from which the general one is deduced. -/
private lemma eq_of_prod_X_pow_sub_one_pow_eq_complex (he : e 0 = 0) (he' : e' 0 = 0)
    (h : ∏ n ∈ I, (X ^ n - 1 : ℂ[X]) ^ e n = ∏ n ∈ I, (X ^ n - 1 : ℂ[X]) ^ e' n) :
    ∀ n ∈ I, e n = e' n := by
  classical
  by_contra! hex
  -- The largest `N ∈ I` with `e N ≠ e' N`; a primitive `N`-th root of unity is a root of
  -- `X ^ n - 1` for exactly the multiples `n` of `N`, and among those in `I` only `N` has
  -- `e n ≠ e' n`, so the two products have different multiplicities at it.
  have hT : (I.filter fun n ↦ e n ≠ e' n).Nonempty := by
    obtain ⟨n, hn, hen⟩ := hex
    exact ⟨n, Finset.mem_filter.2 ⟨hn, hen⟩⟩
  set N := (I.filter fun n ↦ e n ≠ e' n).max' hT
  obtain ⟨hNI, heN⟩ : N ∈ I ∧ e N ≠ e' N := Finset.mem_filter.1 (Finset.max'_mem _ _)
  have hN0 : N ≠ 0 := by
    intro hN
    rw [hN, he, he'] at heN
    exact heN rfl
  have hζ := Complex.isPrimitiveRoot_exp N hN0
  have hcount := congr_arg (fun p ↦ p.roots.count (Complex.exp (2 * Real.pi * Complex.I / N))) h
  rw [count_roots_prod_X_pow_sub_one_pow hζ I he, count_roots_prod_X_pow_sub_one_pow hζ I he']
    at hcount
  replace hcount := congr_arg (Nat.cast : ℕ → ℤ) hcount
  push_cast at hcount
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hcount
  simp_rw [ite_sub_ite, sub_self] at hcount
  rw [Finset.sum_eq_single N (fun n hn hnN ↦ ?_) (fun h ↦ (h hNI).elim), ite_eq_left dvd_rfl,
    sub_eq_zero, Nat.cast_inj] at hcount
  · exact heN hcount
  · refine ite_eq_right_iff.2 fun hNn ↦ ?_
    rw [sub_eq_zero, Nat.cast_inj]
    by_contra hen
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hen (he.trans he'.symm)
    exact hnN (le_antisymm ((I.filter fun n ↦ e n ≠ e' n).le_max' n
      (Finset.mem_filter.2 ⟨hn, hen⟩)) (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hNn))

/-- Products of powers of the polynomials `X ^ n - 1` commute with every change of
coefficients. -/
@[simp]
theorem map_prod_X_pow_sub_one_pow {S : Type*} [CommRing S] (f : R →+* S) (I : Finset ℕ)
    (e : ℕ → ℕ) :
    (∏ n ∈ I, (X ^ n - 1 : R[X]) ^ e n).map f = ∏ n ∈ I, (X ^ n - 1 : S[X]) ^ e n := by
  simp [Polynomial.map_prod]

/-- In characteristic zero the polynomials `X ^ n - 1`, `n ≥ 1`, are multiplicatively
independent: if `∏_{n ∈ I} (X ^ n - 1) ^ e(n) = ∏_{n ∈ I} (X ^ n - 1) ^ e'(n)` and the
exponents of `X ^ 0 - 1 = 0` vanish, then `e = e'` on `I`. -/
theorem eq_of_prod_X_pow_sub_one_pow_eq [CharZero R] (he : e 0 = 0) (he' : e' 0 = 0)
    (h : ∏ n ∈ I, (X ^ n - 1 : R[X]) ^ e n = ∏ n ∈ I, (X ^ n - 1 : R[X]) ^ e' n) :
    ∀ n ∈ I, e n = e' n := by
  refine eq_of_prod_X_pow_sub_one_pow_eq_complex he he' ?_
  rw [← map_prod_X_pow_sub_one_pow (R := ℤ) (Int.castRingHom ℂ),
    ← map_prod_X_pow_sub_one_pow (R := ℤ) (Int.castRingHom ℂ)]
  refine congr_arg _ (Polynomial.map_injective (Int.castRingHom R) Int.cast_injective ?_)
  rwa [map_prod_X_pow_sub_one_pow, map_prod_X_pow_sub_one_pow]

section RatFunc

open scoped ArithmeticFunction.Moebius

variable [IsDomain R]

/-- Möbius inversion for one cyclotomic polynomial in `RatFunc R`,
`Φ_a = ∏_{n ∣ a} (X ^ n - 1) ^ μ(a / n)`, with the product spread over a finite set `S` of indices
containing the divisors of `a`. -/
theorem algebraMap_cyclotomic_eq_prod_zpow {a : ℕ} {S : Finset ℕ} (hS : a.divisors ⊆ S) :
    algebraMap R[X] (RatFunc R) (cyclotomic a R) =
      ∏ n ∈ S, algebraMap R[X] (RatFunc R) (X ^ n - 1) ^ (if n ∣ a then μ (a / n) else 0) := by
  rw [cyclotomic_eq_prod_X_pow_sub_one_pow_moebius,
    Nat.prod_divisorsAntidiagonal' fun i j ↦ algebraMap R[X] (RatFunc R) (X ^ j - 1) ^ μ i,
    ← Finset.prod_subset hS fun n _ hn ↦ by
      rcases eq_or_ne a 0 with rfl | ha
      · simp
      rw [ite_eq_right fun h ↦ hn (Nat.mem_divisors.2 ⟨h, ha⟩), zpow_zero]]
  exact Finset.prod_congr rfl fun n hn ↦ by rw [ite_eq_left (Nat.dvd_of_mem_divisors hn)]

/-- Möbius inversion for a product of cyclotomic polynomials in `RatFunc R`:
`∏_{a ∈ A} Φ_a = ∏_{n ∈ S} (X ^ n - 1) ^ (∑_{a ∈ A, n ∣ a} μ(a / n))` for a finite set `S` of
indices containing the divisors of the elements of `A`. -/
theorem algebraMap_prod_cyclotomic_eq_prod_zpow (A : Multiset ℕ) {S : Finset ℕ}
    (hS : ∀ a ∈ A, a.divisors ⊆ S) :
    algebraMap R[X] (RatFunc R) (A.map fun a ↦ cyclotomic a R).prod =
      ∏ n ∈ S, algebraMap R[X] (RatFunc R) (X ^ n - 1) ^
        ((A.filter (n ∣ ·)).map fun a ↦ μ (a / n)).sum := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul,
      algebraMap_cyclotomic_eq_prod_zpow (hS a (Multiset.mem_cons_self a A)),
      ih fun b hb ↦ hS b (Multiset.mem_cons_of_mem hb), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun n _ ↦ ?_
    -- The exponents at `n = 0` are values `μ (a / 0) = μ 0 = 0`.
    rcases Nat.eq_zero_or_pos n with rfl | hn₀
    · simp
    rw [← zpow_add₀ (RatFunc.algebraMap_ne_zero (X_pow_sub_C_ne_zero hn₀ 1)),
      Multiset.filter_cons]
    split_ifs <;> simp

end RatFunc

end Polynomial
