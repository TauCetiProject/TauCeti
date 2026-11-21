/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.Derivative
public import TauCeti.Algebra.Ring.QPochhammer
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# Finite q-calculus and Jackson derivatives

This file develops the algebraic finite `q`-calculus toolkit over arbitrary commutative
(semi)rings, without any division or invertibility assumptions, building on `TauCeti.qFactorial`
and `TauCeti.qPochhammer` from `TauCeti.Algebra.Ring.QPochhammer`:

* Supplementary unit/divisibility/zero-base lemmas for `TauCeti.qFactorial` and
  `TauCeti.qPochhammer`.
* `Polynomial.jacksonDeriv q` and `Polynomial.adaptedJacksonDeriv q`:
  `D_q (X ^ n) = [n]_q X ^ (n - 1)` and `D'_q = (1 - q) D_q` on `A[X]`.
* `PowerSeries.jacksonDeriv q` / `PowerSeries.adaptedJacksonDeriv q`: the same operators on `A⟦X⟧`,
  compatible with polynomial coercion.

All identities are proved directly at the coefficient level over arbitrary commutative (semi)rings,
holding in positive characteristic and at roots of unity without inverting `1 - q`.

## References

* W. J. G. Ong, notes of P. Scholze's course *V5A2 – The Habiro Ring of a Number Field*
  (winter 2024/25), Definition 1.1, Table 1, and Propositions 2.1–2.2.
-/

public section

open Finset
open scoped Polynomial PowerSeries

namespace TauCeti

/-! ### Supplementary `q`-factorial lemmas -/

section QFactorial

variable {R : Type*} [CommSemiring R]

/-- Specializing the `q`-factorial at `q = 0` gives `1`. -/
@[simp] theorem qFactorial_zero_left (n : ℕ) : qFactorial (0 : R) n = 1 := by
  simp [qFactorial_def, zero_geom_sum]

/-- If `m ≤ n`, then `[m]_q!` divides `[n]_q!`. -/
theorem qFactorial_dvd_of_le (q : R) {m n : ℕ} (h : m ≤ n) :
    qFactorial q m ∣ qFactorial q n := by
  rw [qFactorial_def, qFactorial_def]
  exact prod_dvd_prod_of_subset _ _ _ (range_mono h)

/-- `[n]_q!` is a unit if and only if `[k]_q` is a unit for all `1 ≤ k ≤ n`. -/
theorem isUnit_qFactorial_iff (q : R) (n : ℕ) :
    IsUnit (qFactorial q n) ↔ ∀ k < n, IsUnit (∑ j ∈ range (k + 1), q ^ j) := by
  simp [qFactorial_def, IsUnit.prod_iff]

end QFactorial

/-! ### Supplementary finite `q`-Pochhammer lemmas -/

section QPochhammer

variable {R : Type*} [CommRing R]

/-- At `q = 0` and `n ≠ 0`, `(x; 0)_n = 1 - x`. -/
theorem qPochhammer_zero_right (x : R) {n : ℕ} (hn : n ≠ 0) : qPochhammer x (0 : R) n = 1 - x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp [qPochhammer_succ']

/-- If `m ≤ n`, then `(x; q)_m` divides `(x; q)_n`. -/
theorem qPochhammer_dvd_of_le (x q : R) {m n : ℕ} (h : m ≤ n) :
    qPochhammer x q m ∣ qPochhammer x q n := by
  rw [qPochhammer_def, qPochhammer_def]
  exact prod_dvd_prod_of_subset _ _ _ (range_mono h)

/-- `(x; q)_n` is a unit if and only if each factor `1 - x q ^ i` (`i < n`) is a unit. -/
theorem isUnit_qPochhammer_iff (x q : R) (n : ℕ) :
    IsUnit (qPochhammer x q n) ↔ ∀ i < n, IsUnit (1 - x * q ^ i) := by
  simp [qPochhammer_def, IsUnit.prod_iff]

/-- `(q; q)_n` is a unit if and only if each `1 - q ^ (i + 1)` (`i < n`) is a unit. -/
theorem isUnit_qPochhammer_self_iff (q : R) (n : ℕ) :
    IsUnit (qPochhammer q q n) ↔ ∀ i < n, IsUnit (1 - q ^ (i + 1)) := by
  simp [qPochhammer_self, IsUnit.prod_iff]

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
@[simp] theorem coeff_jacksonDeriv (q : A) (p : A[X]) (n : ℕ) :
    (jacksonDeriv q p).coeff n = (∑ i ∈ range (n + 1), q ^ i) * p.coeff (n + 1) := by
  rw [jacksonDeriv, lsum_apply, sum_def, finsetSum_coeff, Finset.sum_eq_single (n + 1)]
  · simp
  · rintro (_ | i) _ hi
    · simp
    · simp [coeff_monomial, Nat.succ_inj.ne.mp hi]
  · intro h; simp [notMem_support_iff.mp h]

@[simp] theorem jacksonDeriv_C (q a : A) : jacksonDeriv q (C a) = 0 := by ext n; simp

@[simp] theorem jacksonDeriv_X (q : A) : jacksonDeriv q (X : A[X]) = 1 := by
  ext (_ | n) <;> simp [coeff_X, coeff_one]

/-- `D_q (X ^ (n + 1)) = C ([n + 1]_q) * X ^ n`. -/
@[simp] theorem jacksonDeriv_X_pow_succ (q : A) (n : ℕ) :
    jacksonDeriv q (X ^ (n + 1) : A[X]) = C (∑ i ∈ range (n + 1), q ^ i) * X ^ n := by
  ext k; rw [coeff_jacksonDeriv, coeff_X_pow, coeff_C_mul_X_pow]; by_cases h : k = n <;> simp [h]

/-- At `q = 1`, the Jackson derivative is the ordinary polynomial derivative. -/
@[simp] theorem jacksonDeriv_one : jacksonDeriv (1 : A) = derivative := by
  ext p n; simp [coeff_derivative, mul_comm]

/-- The Jackson derivative commutes with coefficient ring homomorphisms. -/
theorem map_jacksonDeriv (φ : A →+* B) (q : A) (p : A[X]) :
    (jacksonDeriv q p).map φ = jacksonDeriv (φ q) (p.map φ) := by
  ext n; simp [coeff_map, map_sum]

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
@[simp] theorem coeff_adaptedJacksonDeriv (q : A) (p : A[X]) (n : ℕ) :
    (adaptedJacksonDeriv q p).coeff n = (1 - q ^ (n + 1)) * p.coeff (n + 1) := by
  rw [adaptedJacksonDeriv_apply, Algebra.smul_def, algebraMap_eq, coeff_C_mul, coeff_jacksonDeriv,
    ← mul_assoc, mul_neg_geom_sum]

@[simp] theorem adaptedJacksonDeriv_C (q a : A) : adaptedJacksonDeriv q (C a) = 0 := by
  simp [adaptedJacksonDeriv_apply]

@[simp] theorem adaptedJacksonDeriv_X (q : A) : adaptedJacksonDeriv q (X : A[X]) = C (1 - q) := by
  simp [adaptedJacksonDeriv_apply, Algebra.smul_def]

/-- `D'_q (X ^ (n + 1)) = C (1 - q ^ (n + 1)) * X ^ n`. -/
@[simp] theorem adaptedJacksonDeriv_X_pow_succ (q : A) (n : ℕ) :
    adaptedJacksonDeriv q (X ^ (n + 1) : A[X]) = C (1 - q ^ (n + 1)) * X ^ n := by
  ext k
  rw [coeff_adaptedJacksonDeriv, coeff_X_pow, coeff_C_mul_X_pow]
  by_cases h : k = n <;> simp [h]

/-- At `q = 1`, the adapted Jackson derivative vanishes identically. -/
@[simp] theorem adaptedJacksonDeriv_one : adaptedJacksonDeriv (1 : A) = 0 := by ext p n; simp

/-- The adapted Jackson derivative commutes with coefficient ring homomorphisms. -/
theorem map_adaptedJacksonDeriv (φ : A →+* B) (q : A) (p : A[X]) :
    (adaptedJacksonDeriv q p).map φ = adaptedJacksonDeriv (φ q) (p.map φ) := by
  ext n; simp [coeff_map]

/-- Difference identity: `X * D'_q p = p - p(q X)`. -/
theorem X_mul_adaptedJacksonDeriv (q : A) (p : A[X]) :
    X * adaptedJacksonDeriv q p = p - p.comp (C q * X) := by
  ext (_ | n)
  · simp [comp_C_mul_X_coeff]
  · simp only [coeff_X_mul, coeff_adaptedJacksonDeriv, coeff_sub, comp_C_mul_X_coeff]; ring

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
@[simp] theorem coeff_jacksonDeriv (q : A) (f : A⟦X⟧) (n : ℕ) :
    coeff n (jacksonDeriv q f) = (∑ i ∈ range (n + 1), q ^ i) * coeff (n + 1) f := by
  simp [jacksonDeriv]

@[simp] theorem jacksonDeriv_C (q a : A) : jacksonDeriv q (C a) = 0 := by ext n; simp

@[simp] theorem jacksonDeriv_X (q : A) : jacksonDeriv q (X : A⟦X⟧) = 1 := by
  ext (_ | n) <;> simp [coeff_X, coeff_one]

/-- `D_q (X ^ (n + 1)) = C ([n + 1]_q) * X ^ n`. -/
@[simp] theorem jacksonDeriv_X_pow_succ (q : A) (n : ℕ) :
    jacksonDeriv q (X ^ (n + 1) : A⟦X⟧) = C (∑ i ∈ range (n + 1), q ^ i) * X ^ n := by
  ext k; rw [coeff_jacksonDeriv, coeff_X_pow, coeff_C_mul_X_pow]; by_cases h : k = n <;> simp [h]

/-- `PowerSeries.jacksonDeriv` agrees with `Polynomial.jacksonDeriv` on polynomials. -/
@[simp] theorem jacksonDeriv_coe (q : A) (p : A[X]) :
    jacksonDeriv q (p : A⟦X⟧) = (Polynomial.jacksonDeriv q p : A⟦X⟧) := by ext n; simp

/-- At `q = 1`, the Jackson derivative is the ordinary power-series derivative. -/
@[simp] theorem jacksonDeriv_one (f : A⟦X⟧) : jacksonDeriv (1 : A) f = d⁄dX f := by
  ext n; simp [coeff_derivative, mul_comm]

/-- The Jackson derivative commutes with coefficient ring homomorphisms. -/
theorem map_jacksonDeriv (φ : A →+* B) (q : A) (f : A⟦X⟧) :
    map φ (jacksonDeriv q f) = jacksonDeriv (φ q) (map φ f) := by ext n; simp [map_sum]

/-- **Twisted Leibniz rule** for the Jackson derivative:
`D_q (f * g) = D_q f * g + f(q X) * D_q g`. -/
theorem jacksonDeriv_mul (q : A) (f g : A⟦X⟧) :
    jacksonDeriv q (f * g) = jacksonDeriv q f * g + rescale q f * jacksonDeriv q g := by
  ext n
  rw [coeff_jacksonDeriv, map_add, coeff_mul, coeff_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b ↦ coeff a f * coeff b g),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b ↦ coeff a (jacksonDeriv q f) * coeff b g),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b ↦ coeff a (rescale q f) * coeff b (jacksonDeriv q g))]
  have h1 : ∑ k ∈ range (n + 1), coeff k (jacksonDeriv q f) * coeff (n - k) g =
      ∑ k ∈ range (n + 2), (∑ i ∈ range k, q ^ i) * (coeff k f * coeff (n + 1 - k) g) := by
    symm; rw [Finset.sum_range_succ']; simp [mul_assoc]
  have h2 : ∑ k ∈ range (n + 1), coeff k (rescale q f) * coeff (n - k) (jacksonDeriv q g) =
      ∑ k ∈ range (n + 2),
        q ^ k * (∑ i ∈ range (n + 1 - k), q ^ i) * (coeff k f * coeff (n + 1 - k) g) := by
    symm; rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, range_zero, sum_empty, mul_zero, zero_mul, add_zero, coeff_rescale,
      coeff_jacksonDeriv]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkn : n + 1 - k = n - k + 1 := by have := mem_range.mp hk; omega
    rw [hkn]; ring
  rw [h1, h2, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [← add_mul]
  congr 1
  have hle : k ≤ n + 1 := Nat.lt_succ_iff.mp (mem_range.mp hk)
  conv_lhs => rw [← Nat.add_sub_of_le hle]
  rw [Finset.sum_range_add, Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ pow_add q k i)

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
@[simp] theorem coeff_adaptedJacksonDeriv (q : A) (f : A⟦X⟧) (n : ℕ) :
    coeff n (adaptedJacksonDeriv q f) = (1 - q ^ (n + 1)) * coeff (n + 1) f := by
  rw [adaptedJacksonDeriv_apply, coeff_smul, smul_eq_mul, coeff_jacksonDeriv, ← mul_assoc,
    mul_neg_geom_sum]

@[simp] theorem adaptedJacksonDeriv_C (q a : A) : adaptedJacksonDeriv q (C a) = 0 := by
  simp [adaptedJacksonDeriv_apply]

@[simp] theorem adaptedJacksonDeriv_X (q : A) : adaptedJacksonDeriv q (X : A⟦X⟧) = C (1 - q) := by
  simp [adaptedJacksonDeriv_apply, Algebra.smul_def]

/-- `D'_q (X ^ (n + 1)) = C (1 - q ^ (n + 1)) * X ^ n`. -/
@[simp] theorem adaptedJacksonDeriv_X_pow_succ (q : A) (n : ℕ) :
    adaptedJacksonDeriv q (X ^ (n + 1) : A⟦X⟧) = C (1 - q ^ (n + 1)) * X ^ n := by
  ext k
  rw [coeff_adaptedJacksonDeriv, coeff_X_pow, coeff_C_mul_X_pow]
  by_cases h : k = n <;> simp [h]

/-- `PowerSeries.adaptedJacksonDeriv` agrees with `Polynomial.adaptedJacksonDeriv` on
polynomials. -/
@[simp] theorem adaptedJacksonDeriv_coe (q : A) (p : A[X]) :
    adaptedJacksonDeriv q (p : A⟦X⟧) = (Polynomial.adaptedJacksonDeriv q p : A⟦X⟧) := by
  ext n; simp

/-- At `q = 1`, the adapted Jackson derivative vanishes identically. -/
@[simp] theorem adaptedJacksonDeriv_one : adaptedJacksonDeriv (1 : A) = 0 := by ext f n; simp

/-- The adapted Jackson derivative commutes with coefficient ring homomorphisms. -/
theorem map_adaptedJacksonDeriv (φ : A →+* B) (q : A) (f : A⟦X⟧) :
    map φ (adaptedJacksonDeriv q f) = adaptedJacksonDeriv (φ q) (map φ f) := by ext n; simp

/-- **Twisted Leibniz rule** for the adapted Jackson derivative:
`D'_q (f * g) = D'_q f * g + f(q X) * D'_q g`. -/
theorem adaptedJacksonDeriv_mul (q : A) (f g : A⟦X⟧) :
    adaptedJacksonDeriv q (f * g) =
      adaptedJacksonDeriv q f * g + rescale q f * adaptedJacksonDeriv q g := by
  simp only [adaptedJacksonDeriv_apply, jacksonDeriv_mul, smul_add, smul_mul_assoc, mul_smul_comm]

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
    ext n; simp only [coeff_coe, comp_C_mul_X_coeff, PowerSeries.coeff_rescale]; exact mul_comm _ _
  rw [← PowerSeries.jacksonDeriv_coe, coe_mul, PowerSeries.jacksonDeriv_mul,
    PowerSeries.jacksonDeriv_coe, PowerSeries.jacksonDeriv_coe, ← hcomp, coe_add, coe_mul,
    coe_mul]

/-- **Twisted Leibniz rule** for the polynomial adapted Jackson derivative:
`D'_q (p * r) = D'_q p * r + p(q X) * D'_q r`. -/
theorem adaptedJacksonDeriv_mul {A : Type*} [CommRing A] (q : A) (p r : A[X]) :
    adaptedJacksonDeriv q (p * r) =
      adaptedJacksonDeriv q p * r + p.comp (C q * X) * adaptedJacksonDeriv q r := by
  simp only [adaptedJacksonDeriv_apply, jacksonDeriv_mul, smul_add, smul_mul_assoc, mul_smul_comm]

end Polynomial
