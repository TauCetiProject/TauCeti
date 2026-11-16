/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# Finite q-calculus and Jackson derivatives

This file develops the algebraic finite `q`-calculus toolkit over arbitrary commutative
(semi)rings, without any division or invertibility assumptions:

* `TauCeti.qFactorial q n`: the `q`-factorial `[n]_q! = ∏_{i=1}^n [i]_q`, where the `q`-integer
  `[i]_q = ∑_{j < i} q ^ j` is Mathlib's finite geometric sum.
* `TauCeti.qPochhammer x q n`: the finite multiplicative `q`-Pochhammer symbol
  `(x; q)_n = ∏_{i < n} (1 - x q ^ i)`.
* `Polynomial.jacksonDeriv q` and `Polynomial.adaptedJacksonDeriv q`: the Jackson derivative
  `D_q (X ^ n) = [n]_q X ^ (n - 1)` and adapted Jackson derivative
  `D'_q = (1 - q) D_q` on `A[X]`.
* `PowerSeries.jacksonDeriv q` and `PowerSeries.adaptedJacksonDeriv q`: the same operators on
  `A⟦X⟧`, compatible with polynomial coercion.

All identities are proved directly at the coefficient level over arbitrary commutative rings
(or commutative semirings where subtraction is absent), so they hold in positive characteristic
and at roots of unity without requiring `1 - q` to be invertible.

## Main results

* `TauCeti.qFactorial_one_left`: `[n]_1! = n!`.
* `TauCeti.qPochhammer_add`, `TauCeti.qPochhammer_succ'`: concatenation and shift identities
  `(x; q)_{m + n} = (x; q)_m (x q ^ m; q)_n` and `(x; q)_{n + 1} = (1 - x) (x q; q)_n`.
* `TauCeti.one_sub_pow_mul_qFactorial`: `(1 - q) ^ n [n]_q! = (q; q)_n`.
* `TauCeti.qPochhammer_inv_self`: for a unit `u : Rˣ`,
  `(u⁻¹; u⁻¹)_n = (-1) ^ n (u⁻¹) ^ (n (n + 1) / 2) (u; u)_n`.
* `Polynomial.jacksonDeriv_mul`, `PowerSeries.jacksonDeriv_mul`: the twisted Leibniz rule
  `D_q (f g) = D_q f * g + f(q X) * D_q g`.
* `Polynomial.jacksonDeriv_one`, `PowerSeries.jacksonDeriv_one`: at `q = 1`, `D_1` is the
  ordinary derivative and `D'_1 = 0`.
* `Polynomial.X_mul_adaptedJacksonDeriv`, `PowerSeries.X_mul_adaptedJacksonDeriv`:
  `X * D'_q f = f - f(q X)`.

## References

* W. J. G. Ong, notes of P. Scholze's course *V5A2 – The Habiro Ring of a Number Field*
  (winter 2024/25), Definition 1.1, Table 1, and Propositions 2.1–2.2.
-/

public section

open Finset
open scoped Polynomial PowerSeries

namespace TauCeti

/-! ### `q`-factorials -/

section QFactorial

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The `q`-factorial `[n]_q! = ∏_{i = 1}^n [i]_q`, where `[i]_q = ∑_{j < i} q ^ j`. -/
def qFactorial (q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, ∑ j ∈ range (i + 1), q ^ j

/-- Unfolding definition of `TauCeti.qFactorial`. -/
theorem qFactorial_def (q : R) (n : ℕ) :
    qFactorial q n = ∏ i ∈ range n, ∑ j ∈ range (i + 1), q ^ j :=
  (rfl)

@[simp]
theorem qFactorial_zero (q : R) : qFactorial q 0 = 1 := by
  simp [qFactorial]

@[simp]
theorem qFactorial_one (q : R) : qFactorial q 1 = 1 := by
  simp [qFactorial]

/-- Recursion for the `q`-factorial: `[n + 1]_q! = [n]_q! * [n + 1]_q`. -/
theorem qFactorial_succ (q : R) (n : ℕ) :
    qFactorial q (n + 1) = qFactorial q n * ∑ j ∈ range (n + 1), q ^ j :=
  prod_range_succ _ n

/-- Specializing the `q`-factorial at `q = 1` recovers the ordinary factorial. -/
@[simp]
theorem qFactorial_one_left (n : ℕ) : qFactorial (1 : R) n = (n.factorial : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qFactorial_succ, ih, one_geom_sum, Nat.factorial_succ, Nat.cast_mul, mul_comm]

/-- Specializing the `q`-factorial at `q = 0` gives `1`. -/
@[simp]
theorem qFactorial_zero_left (n : ℕ) : qFactorial (0 : R) n = 1 := by
  simp [qFactorial, zero_geom_sum]

/-- `q`-factorials commute with ring homomorphisms. -/
theorem map_qFactorial (f : R →+* S) (q : R) (n : ℕ) :
    f (qFactorial q n) = qFactorial (f q) n := by
  simp [qFactorial, map_prod, map_sum]

/-- If `m ≤ n`, then `[m]_q!` divides `[n]_q!`. -/
theorem qFactorial_dvd_of_le (q : R) {m n : ℕ} (h : m ≤ n) :
    qFactorial q m ∣ qFactorial q n :=
  prod_dvd_prod_of_subset _ _ _ (range_mono h)

/-- `[n]_q!` is a unit if and only if `[k]_q` is a unit for all `1 ≤ k ≤ n`. -/
theorem isUnit_qFactorial_iff (q : R) (n : ℕ) :
    IsUnit (qFactorial q n) ↔ ∀ k < n, IsUnit (∑ j ∈ range (k + 1), q ^ j) := by
  simp [qFactorial, IsUnit.prod_iff]

end QFactorial

/-! ### Finite `q`-Pochhammer symbols -/

section QPochhammer

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The finite multiplicative `q`-Pochhammer symbol `(x; q)_n = ∏_{i < n} (1 - x q ^ i)`. -/
def qPochhammer (x q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, (1 - x * q ^ i)

/-- Unfolding definition of `TauCeti.qPochhammer`. -/
theorem qPochhammer_def (x q : R) (n : ℕ) :
    qPochhammer x q n = ∏ i ∈ range n, (1 - x * q ^ i) :=
  (rfl)

@[simp]
theorem qPochhammer_zero (x q : R) : qPochhammer x q 0 = 1 := by
  simp [qPochhammer]

@[simp]
theorem qPochhammer_one (x q : R) : qPochhammer x q 1 = 1 - x := by
  simp [qPochhammer]

/-- Splitting off the last factor: `(x; q)_{n + 1} = (x; q)_n (1 - x q ^ n)`. -/
theorem qPochhammer_succ (x q : R) (n : ℕ) :
    qPochhammer x q (n + 1) = qPochhammer x q n * (1 - x * q ^ n) :=
  prod_range_succ _ n

/-- Shift law splitting off the first factor: `(x; q)_{n + 1} = (1 - x) (x q; q)_n`. -/
theorem qPochhammer_succ' (x q : R) (n : ℕ) :
    qPochhammer x q (n + 1) = (1 - x) * qPochhammer (x * q) q n := by
  rw [qPochhammer, prod_range_succ', pow_zero, mul_one, mul_comm, qPochhammer]
  congr 1
  exact prod_congr rfl fun i _ ↦ by rw [pow_succ', mul_assoc]

/-- Concatenation law: `(x; q)_{m + n} = (x; q)_m (x q ^ m; q)_n`. -/
theorem qPochhammer_add (x q : R) (m n : ℕ) :
    qPochhammer x q (m + n) = qPochhammer x q m * qPochhammer (x * q ^ m) q n := by
  rw [qPochhammer, prod_range_add, qPochhammer, qPochhammer]
  congr 1
  exact prod_congr rfl fun i _ ↦ by rw [pow_add, mul_assoc]

@[simp]
theorem qPochhammer_zero_left (q : R) (n : ℕ) : qPochhammer (0 : R) q n = 1 := by
  simp [qPochhammer]

/-- For `n ≠ 0`, `(1; q)_n = 0`. -/
theorem qPochhammer_one_left (q : R) {n : ℕ} (hn : n ≠ 0) : qPochhammer (1 : R) q n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp [qPochhammer_succ']

/-- At `q = 1`, `(x; 1)_n = (1 - x) ^ n`. -/
@[simp]
theorem qPochhammer_one_right (x : R) (n : ℕ) : qPochhammer x (1 : R) n = (1 - x) ^ n := by
  simp [qPochhammer]

/-- At `q = 0` and `n ≠ 0`, `(x; 0)_n = 1 - x`. -/
theorem qPochhammer_zero_right (x : R) {n : ℕ} (hn : n ≠ 0) : qPochhammer x (0 : R) n = 1 - x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp [qPochhammer_succ']

/-- The self-shifted product `(q; q)_n = ∏_{i < n} (1 - q ^ (i + 1))`. -/
theorem qPochhammer_self_eq_prod (q : R) (n : ℕ) :
    qPochhammer q q n = ∏ i ∈ range n, (1 - q ^ (i + 1)) := by
  rw [qPochhammer]
  exact prod_congr rfl fun i _ ↦ by rw [pow_succ']

/-- Finite `q`-Pochhammer products commute with ring homomorphisms. -/
theorem map_qPochhammer (f : R →+* S) (x q : R) (n : ℕ) :
    f (qPochhammer x q n) = qPochhammer (f x) (f q) n := by
  simp [qPochhammer, map_prod]

/-- If `m ≤ n`, then `(x; q)_m` divides `(x; q)_n`. -/
theorem qPochhammer_dvd_of_le (x q : R) {m n : ℕ} (h : m ≤ n) :
    qPochhammer x q m ∣ qPochhammer x q n :=
  prod_dvd_prod_of_subset _ _ _ (range_mono h)

/-- `(x; q)_n` is a unit if and only if each factor `1 - x q ^ i` (`i < n`) is a unit. -/
theorem isUnit_qPochhammer_iff (x q : R) (n : ℕ) :
    IsUnit (qPochhammer x q n) ↔ ∀ i < n, IsUnit (1 - x * q ^ i) := by
  simp [qPochhammer, IsUnit.prod_iff]

/-- `(q; q)_n` is a unit if and only if each `1 - q ^ (i + 1)` (`i < n`) is a unit. -/
theorem isUnit_qPochhammer_self_iff (q : R) (n : ℕ) :
    IsUnit (qPochhammer q q n) ↔ ∀ i < n, IsUnit (1 - q ^ (i + 1)) := by
  simp [qPochhammer_self_eq_prod, IsUnit.prod_iff]

/-- Polynomial identity relating `q`-factorials and finite `q`-Pochhammer symbols:
`(1 - q) ^ n * [n]_q! = (q; q)_n`. -/
theorem one_sub_pow_mul_qFactorial (q : R) (n : ℕ) :
    (1 - q) ^ n * qFactorial q n = qPochhammer q q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, qFactorial_succ, qPochhammer_succ, ← ih, ← pow_succ']
    calc (1 - q) ^ n * (1 - q) * (qFactorial q n * ∑ j ∈ range (n + 1), q ^ j)
        = (1 - q) ^ n * qFactorial q n * ((1 - q) * ∑ j ∈ range (n + 1), q ^ j) := by ring
      _ = (1 - q) ^ n * qFactorial q n * (1 - q ^ (n + 1)) := by rw [mul_neg_geom_sum]

/-- Inverse-parameter formula for a unit `u : Rˣ`:
`(u⁻¹; u⁻¹)_n = (-1) ^ n * (u⁻¹) ^ (n (n + 1) / 2) * (u; u)_n`. -/
theorem qPochhammer_inv_self (u : Rˣ) (n : ℕ) :
    qPochhammer (↑u⁻¹ : R) (↑u⁻¹ : R) n =
      (-1) ^ n * (↑u⁻¹ : R) ^ (n * (n + 1) / 2) * qPochhammer (u : R) (u : R) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have htri : (n + 1) * (n + 1 + 1) / 2 = n * (n + 1) / 2 + (n + 1) := by
      have : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
      rw [this, Nat.add_mul_div_left _ _ two_pos]
    have hfac : (1 - (↑u⁻¹ : R) ^ (n + 1)) =
        (-1) * (↑u⁻¹ : R) ^ (n + 1) * (1 - (u : R) ^ (n + 1)) := by
      have hinv : (↑u⁻¹ : R) ^ (n + 1) * (u : R) ^ (n + 1) = 1 := by
        rw [← mul_pow, Units.inv_mul, one_pow]
      rw [neg_one_mul, neg_mul, mul_sub, mul_one, hinv, neg_sub]
    rw [qPochhammer_succ, qPochhammer_succ, ← pow_succ', ← pow_succ', ih, hfac, htri, pow_add,
      pow_succ]
    ring

end QPochhammer

end TauCeti

/-! ### Polynomial Jackson derivative -/

namespace Polynomial

section Semiring

variable {A B : Type*} [CommSemiring A] [CommSemiring B]

/-- The **Jackson `q`-derivative** on polynomials, sending `X ^ n` to `[n]_q X ^ (n - 1)` where
`[n]_q = ∑_{i < n} q ^ i`. -/
noncomputable def jacksonDeriv (q : A) : A[X] →ₗ[A] A[X] :=
  lsum fun i ↦ monomial (i - 1) ∘ₗ LinearMap.mulLeft A (∑ j ∈ range i, q ^ j)

/-- Coefficient formula for `Polynomial.jacksonDeriv`:
`(D_q p).coeff n = [n + 1]_q * p.coeff (n + 1)`. -/
@[simp]
theorem coeff_jacksonDeriv (q : A) (p : A[X]) (n : ℕ) :
    (jacksonDeriv q p).coeff n = (∑ i ∈ range (n + 1), q ^ i) * p.coeff (n + 1) := by
  rw [jacksonDeriv, lsum_apply, sum_def, finsetSum_coeff]
  rw [Finset.sum_eq_single (n + 1)]
  · simp
  · intro i _ hi
    rcases i with _ | i
    · simp
    · simp [coeff_monomial, Nat.succ_inj.ne.mp hi]
  · intro h
    simp [notMem_support_iff.mp h]

@[simp]
theorem jacksonDeriv_C (q a : A) : jacksonDeriv q (C a) = 0 := by
  ext n
  simp

@[simp]
theorem jacksonDeriv_X (q : A) : jacksonDeriv q (X : A[X]) = 1 := by
  ext (_ | n) <;> simp [coeff_X, coeff_one]

/-- `D_q (X ^ (n + 1)) = C ([n + 1]_q) * X ^ n`. -/
@[simp]
theorem jacksonDeriv_X_pow_succ (q : A) (n : ℕ) :
    jacksonDeriv q (X ^ (n + 1) : A[X]) = C (∑ i ∈ range (n + 1), q ^ i) * X ^ n := by
  ext k
  rw [coeff_jacksonDeriv, coeff_X_pow, coeff_C_mul_X_pow]
  by_cases h : k = n <;> simp [h]

/-- At `q = 1`, the Jackson derivative is the ordinary polynomial derivative. -/
@[simp]
theorem jacksonDeriv_one : jacksonDeriv (1 : A) = derivative := by
  ext p n
  simp [coeff_derivative, mul_comm]

/-- The Jackson derivative commutes with coefficient ring homomorphisms. -/
theorem map_jacksonDeriv (φ : A →+* B) (q : A) (p : A[X]) :
    (jacksonDeriv q p).map φ = jacksonDeriv (φ q) (p.map φ) := by
  ext n
  simp [coeff_map, map_sum]

end Semiring

section Ring

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The **adapted Jackson `q`-derivative** `D'_q = (1 - q) D_q` on polynomials, sending `X ^ n` to
`(1 - q ^ n) X ^ (n - 1)`. -/
noncomputable def adaptedJacksonDeriv (q : A) : A[X] →ₗ[A] A[X] :=
  (1 - q) • jacksonDeriv q

/-- Unfolding definition of `Polynomial.adaptedJacksonDeriv`. -/
theorem adaptedJacksonDeriv_apply (q : A) (p : A[X]) :
    adaptedJacksonDeriv q p = (1 - q) • jacksonDeriv q p :=
  (rfl)

/-- Coefficient formula for `Polynomial.adaptedJacksonDeriv`:
`(D'_q p).coeff n = (1 - q ^ (n + 1)) * p.coeff (n + 1)`. -/
@[simp]
theorem coeff_adaptedJacksonDeriv (q : A) (p : A[X]) (n : ℕ) :
    (adaptedJacksonDeriv q p).coeff n = (1 - q ^ (n + 1)) * p.coeff (n + 1) := by
  rw [adaptedJacksonDeriv_apply, Algebra.smul_def, algebraMap_eq, coeff_C_mul, coeff_jacksonDeriv,
    ← mul_assoc, mul_neg_geom_sum]

@[simp]
theorem adaptedJacksonDeriv_C (q a : A) : adaptedJacksonDeriv q (C a) = 0 := by
  simp [adaptedJacksonDeriv_apply]

@[simp]
theorem adaptedJacksonDeriv_X (q : A) : adaptedJacksonDeriv q (X : A[X]) = C (1 - q) := by
  simp [adaptedJacksonDeriv_apply, Algebra.smul_def]

/-- `D'_q (X ^ (n + 1)) = C (1 - q ^ (n + 1)) * X ^ n`. -/
@[simp]
theorem adaptedJacksonDeriv_X_pow_succ (q : A) (n : ℕ) :
    adaptedJacksonDeriv q (X ^ (n + 1) : A[X]) = C (1 - q ^ (n + 1)) * X ^ n := by
  ext k
  rw [coeff_adaptedJacksonDeriv, coeff_X_pow, coeff_C_mul_X_pow]
  by_cases h : k = n <;> simp [h]

/-- At `q = 1`, the adapted Jackson derivative vanishes identically. -/
@[simp]
theorem adaptedJacksonDeriv_one : adaptedJacksonDeriv (1 : A) = 0 := by
  ext p n
  simp

/-- The adapted Jackson derivative commutes with coefficient ring homomorphisms. -/
theorem map_adaptedJacksonDeriv (φ : A →+* B) (q : A) (p : A[X]) :
    (adaptedJacksonDeriv q p).map φ = adaptedJacksonDeriv (φ q) (p.map φ) := by
  ext n
  simp [coeff_map]

/-- Difference identity: `X * D'_q p = p - p(q X)`. -/
theorem X_mul_adaptedJacksonDeriv (q : A) (p : A[X]) :
    X * adaptedJacksonDeriv q p = p - p.comp (C q * X) := by
  ext (_ | n)
  · simp [comp_C_mul_X_coeff]
  · simp only [coeff_X_mul, coeff_adaptedJacksonDeriv, coeff_sub, comp_C_mul_X_coeff]
    ring

end Ring

end Polynomial

/-! ### Power-series Jackson derivative -/

namespace PowerSeries

section Semiring

variable {A B : Type*} [CommSemiring A] [CommSemiring B]

/-- The **Jackson `q`-derivative** on power series, sending `X ^ n` to `[n]_q X ^ (n - 1)` where
`[n]_q = ∑_{i < n} q ^ i`. -/
noncomputable def jacksonDeriv (q : A) : A⟦X⟧ →ₗ[A] A⟦X⟧ where
  toFun f := mk fun n ↦ (∑ i ∈ range (n + 1), q ^ i) * coeff (n + 1) f
  map_add' f g := by ext n; simp [mul_add]
  map_smul' r f := by ext n; simp [mul_left_comm]

/-- Coefficient formula for `PowerSeries.jacksonDeriv`:
`coeff n (D_q f) = [n + 1]_q * coeff (n + 1) f`. -/
@[simp]
theorem coeff_jacksonDeriv (q : A) (f : A⟦X⟧) (n : ℕ) :
    coeff n (jacksonDeriv q f) = (∑ i ∈ range (n + 1), q ^ i) * coeff (n + 1) f := by
  simp [jacksonDeriv]

@[simp]
theorem jacksonDeriv_C (q a : A) : jacksonDeriv q (C a) = 0 := by
  ext n
  simp

@[simp]
theorem jacksonDeriv_X (q : A) : jacksonDeriv q (X : A⟦X⟧) = 1 := by
  ext (_ | n) <;> simp [coeff_X, coeff_one]

/-- `D_q (X ^ (n + 1)) = C ([n + 1]_q) * X ^ n`. -/
@[simp]
theorem jacksonDeriv_X_pow_succ (q : A) (n : ℕ) :
    jacksonDeriv q (X ^ (n + 1) : A⟦X⟧) = C (∑ i ∈ range (n + 1), q ^ i) * X ^ n := by
  ext k
  rw [coeff_jacksonDeriv, coeff_X_pow, coeff_C_mul_X_pow]
  by_cases h : k = n <;> simp [h]

/-- `PowerSeries.jacksonDeriv` agrees with `Polynomial.jacksonDeriv` on polynomials. -/
@[simp]
theorem jacksonDeriv_coe (q : A) (p : A[X]) :
    jacksonDeriv q (p : A⟦X⟧) = (Polynomial.jacksonDeriv q p : A⟦X⟧) := by
  ext n
  simp

/-- At `q = 1`, the Jackson derivative is the ordinary power-series derivative. -/
@[simp]
theorem jacksonDeriv_one (f : A⟦X⟧) : jacksonDeriv (1 : A) f = d⁄dX f := by
  ext n
  simp [coeff_derivative, mul_comm]

/-- The Jackson derivative commutes with coefficient ring homomorphisms. -/
theorem map_jacksonDeriv (φ : A →+* B) (q : A) (f : A⟦X⟧) :
    map φ (jacksonDeriv q f) = jacksonDeriv (φ q) (map φ f) := by
  ext n
  simp [map_sum]

/-- **Twisted Leibniz rule** for the Jackson derivative:
`D_q (f * g) = D_q f * g + f(q X) * D_q g`. -/
theorem jacksonDeriv_mul (q : A) (f g : A⟦X⟧) :
    jacksonDeriv q (f * g) = jacksonDeriv q f * g + rescale q f * jacksonDeriv q g := by
  ext n
  rw [coeff_jacksonDeriv, map_add, coeff_mul, coeff_mul, coeff_mul]
  -- Reindex the two convolution sums over `antidiagonal (n + 1)`.
  have h1 : ∑ x ∈ antidiagonal n, coeff x.1 (jacksonDeriv q f) * coeff x.2 g =
      ∑ x ∈ antidiagonal (n + 1), (∑ i ∈ range x.1, q ^ i) * (coeff x.1 f * coeff x.2 g) := by
    symm
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b ↦
      (∑ i ∈ range a, q ^ i) * (coeff a f * coeff b g)), Finset.sum_range_succ',
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b ↦
        coeff a (jacksonDeriv q f) * coeff b g)]
    simp [mul_assoc]
  have h2 : ∑ x ∈ antidiagonal n, coeff x.1 (rescale q f) * coeff x.2 (jacksonDeriv q g) =
      ∑ x ∈ antidiagonal (n + 1), q ^ x.1 * (∑ i ∈ range x.2, q ^ i) *
        (coeff x.1 f * coeff x.2 g) := by
    symm
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b ↦
      q ^ a * (∑ i ∈ range b, q ^ i) * (coeff a f * coeff b g)), Finset.sum_range_succ,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b ↦
        coeff a (rescale q f) * coeff b (jacksonDeriv q g))]
    simp only [Nat.sub_self, range_zero, sum_empty, mul_zero, zero_mul, add_zero, coeff_rescale,
      coeff_jacksonDeriv]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkn : n + 1 - k = n - k + 1 := by
      have := mem_range.mp hk
      omega
    rw [hkn]
    ring
  rw [h1, h2, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [← add_mul]
  congr 1
  rw [← (mem_antidiagonal.mp hx), Finset.sum_range_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ pow_add q x.1 i

end Semiring

section Ring

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The **adapted Jackson `q`-derivative** `D'_q = (1 - q) D_q` on power series, sending `X ^ n` to
`(1 - q ^ n) X ^ (n - 1)`. -/
noncomputable def adaptedJacksonDeriv (q : A) : A⟦X⟧ →ₗ[A] A⟦X⟧ :=
  (1 - q) • jacksonDeriv q

/-- Unfolding definition of `PowerSeries.adaptedJacksonDeriv`. -/
theorem adaptedJacksonDeriv_apply (q : A) (f : A⟦X⟧) :
    adaptedJacksonDeriv q f = (1 - q) • jacksonDeriv q f :=
  (rfl)

/-- Coefficient formula for `PowerSeries.adaptedJacksonDeriv`:
`coeff n (D'_q f) = (1 - q ^ (n + 1)) * coeff (n + 1) f`. -/
@[simp]
theorem coeff_adaptedJacksonDeriv (q : A) (f : A⟦X⟧) (n : ℕ) :
    coeff n (adaptedJacksonDeriv q f) = (1 - q ^ (n + 1)) * coeff (n + 1) f := by
  rw [adaptedJacksonDeriv_apply, coeff_smul, smul_eq_mul, coeff_jacksonDeriv, ← mul_assoc,
    mul_neg_geom_sum]

@[simp]
theorem adaptedJacksonDeriv_C (q a : A) : adaptedJacksonDeriv q (C a) = 0 := by
  simp [adaptedJacksonDeriv_apply]

@[simp]
theorem adaptedJacksonDeriv_X (q : A) : adaptedJacksonDeriv q (X : A⟦X⟧) = C (1 - q) := by
  simp [adaptedJacksonDeriv_apply, Algebra.smul_def]

/-- `D'_q (X ^ (n + 1)) = C (1 - q ^ (n + 1)) * X ^ n`. -/
@[simp]
theorem adaptedJacksonDeriv_X_pow_succ (q : A) (n : ℕ) :
    adaptedJacksonDeriv q (X ^ (n + 1) : A⟦X⟧) = C (1 - q ^ (n + 1)) * X ^ n := by
  ext k
  rw [coeff_adaptedJacksonDeriv, coeff_X_pow, coeff_C_mul_X_pow]
  by_cases h : k = n <;> simp [h]

/-- `PowerSeries.adaptedJacksonDeriv` agrees with `Polynomial.adaptedJacksonDeriv` on
polynomials. -/
@[simp]
theorem adaptedJacksonDeriv_coe (q : A) (p : A[X]) :
    adaptedJacksonDeriv q (p : A⟦X⟧) = (Polynomial.adaptedJacksonDeriv q p : A⟦X⟧) := by
  ext n
  simp

/-- At `q = 1`, the adapted Jackson derivative vanishes identically. -/
@[simp]
theorem adaptedJacksonDeriv_one : adaptedJacksonDeriv (1 : A) = 0 := by
  ext f n
  simp

/-- The adapted Jackson derivative commutes with coefficient ring homomorphisms. -/
theorem map_adaptedJacksonDeriv (φ : A →+* B) (q : A) (f : A⟦X⟧) :
    map φ (adaptedJacksonDeriv q f) = adaptedJacksonDeriv (φ q) (map φ f) := by
  ext n
  simp

/-- **Twisted Leibniz rule** for the adapted Jackson derivative:
`D'_q (f * g) = D'_q f * g + f(q X) * D'_q g`. -/
theorem adaptedJacksonDeriv_mul (q : A) (f g : A⟦X⟧) :
    adaptedJacksonDeriv q (f * g) =
      adaptedJacksonDeriv q f * g + rescale q f * adaptedJacksonDeriv q g := by
  simp only [adaptedJacksonDeriv_apply, jacksonDeriv_mul, smul_add, smul_mul_assoc,
    mul_smul_comm]

/-- Difference identity: `X * D'_q f = f - f(q X)`. -/
theorem X_mul_adaptedJacksonDeriv (q : A) (f : A⟦X⟧) :
    X * adaptedJacksonDeriv q f = f - rescale q f := by
  ext (_ | n)
  · rw [coeff_zero_X_mul, map_sub, coeff_rescale, pow_zero, one_mul, sub_self]
  · simp [coeff_succ_X_mul, coeff_rescale, sub_mul]

end Ring

end PowerSeries

/-! ### Polynomial twisted Leibniz rules via power-series embedding -/

namespace Polynomial

/-- **Twisted Leibniz rule** for the polynomial Jackson derivative:
`D_q (p * r) = D_q p * r + p(q X) * D_q r`. -/
theorem jacksonDeriv_mul {A : Type*} [CommSemiring A] (q : A) (p r : A[X]) :
    jacksonDeriv q (p * r) = jacksonDeriv q p * r + p.comp (C q * X) * jacksonDeriv q r := by
  apply coe_injective
  have hcomp : ((p.comp (C q * X) : A[X]) : A⟦X⟧) = PowerSeries.rescale q (p : A⟦X⟧) := by
    ext n
    simp only [coeff_coe, comp_C_mul_X_coeff, PowerSeries.coeff_rescale]
    exact mul_comm _ _
  rw [← PowerSeries.jacksonDeriv_coe, coe_mul, PowerSeries.jacksonDeriv_mul,
    PowerSeries.jacksonDeriv_coe, PowerSeries.jacksonDeriv_coe, ← hcomp, coe_add, coe_mul,
    coe_mul]

/-- **Twisted Leibniz rule** for the polynomial adapted Jackson derivative:
`D'_q (p * r) = D'_q p * r + p(q X) * D'_q r`. -/
theorem adaptedJacksonDeriv_mul {A : Type*} [CommRing A] (q : A) (p r : A[X]) :
    adaptedJacksonDeriv q (p * r) =
      adaptedJacksonDeriv q p * r + p.comp (C q * X) * adaptedJacksonDeriv q r := by
  simp only [adaptedJacksonDeriv_apply, jacksonDeriv_mul, smul_add, smul_mul_assoc,
    mul_smul_comm]

end Polynomial
