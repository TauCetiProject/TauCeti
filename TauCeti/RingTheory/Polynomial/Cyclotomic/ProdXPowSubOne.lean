/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Products of powers of the polynomials `X ^ n - 1`

A product `∏_{n ∈ I} (X ^ n - 1) ^ e(n)` with `e(0) = 0` (the factor `X ^ 0 - 1` is `0`) is
monic of degree `∑ n e(n)`. In characteristic zero the polynomials `X ^ n - 1`, `n ≥ 1`, are
multiplicatively independent: such a product determines its exponents. Over `ℂ` a primitive
`N`-th root of unity is a simple root of `X ^ n - 1` exactly when `N ∣ n`, so its multiplicity
in the product is `∑_{N ∣ n} e(n)`; comparing these multiplicities for the largest `N` at which
two exponent functions differ separates them. In characteristic `p` independence fails, since
`X ^ p - 1 = (X - 1) ^ p`.

Products of this shape are the integral form of a rational function `∏_n (X ^ n - 1) ^ γ(n)`
with integer exponents, the form in which Beukers, Cohen and Mellit parametrize hypergeometric
data by their gamma vector.

## Main results

* `Polynomial.monic_prod_X_pow_sub_one_pow`, `Polynomial.natDegree_prod_X_pow_sub_one_pow`: the
  product is monic of degree `∑ n e(n)`.
* `Polynomial.eq_of_prod_X_pow_sub_one_pow_eq`: in characteristic zero, equal products have equal
  exponents.

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

/-- The multiplicity of a primitive `N`-th root of unity `ζ` as a root of
`∏_{n ∈ I} (X ^ n - 1) ^ e(n)` is the sum of the exponents `e(n)` over the multiples `n` of `N`. -/
private lemma count_roots_prod_X_pow_sub_one_pow {ζ : ℂ} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (I : Finset ℕ) {e : ℕ → ℕ} (he : e 0 = 0) :
    (∏ n ∈ I, (X ^ n - 1 : ℂ[X]) ^ e n).roots.count ζ = ∑ n ∈ I, if N ∣ n then e n else 0 := by
  classical
  rw [roots_prod _ _ (monic_prod_X_pow_sub_one_pow he).ne_zero, Multiset.count_bind,
    Finset.sum_eq_multiset_sum]
  refine congr_arg Multiset.sum (Multiset.map_congr rfl fun n _ ↦ ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [he]
  rw [roots_pow, Multiset.count_nsmul, ← C_1, ← nthRoots]
  have hnodup := (Complex.isPrimitiveRoot_exp n hn).nthRoots_one_nodup
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
private lemma map_prod_X_pow_sub_one_pow {S : Type*} [CommRing S] (f : R →+* S) (I : Finset ℕ)
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

end Polynomial
