/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import TauCeti.Algebra.Polynomial.QDerivative
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# Power-series Jackson derivatives

This file develops the Jackson `q`-derivative and adapted Jackson `q`-derivative on formal power
series over arbitrary commutative (semi)rings, without any division or invertibility assumptions:

* `PowerSeries.jacksonDeriv q`: `D_q (X ^ n) = [n]_q X ^ (n - 1)` on `A⟦X⟧`, agreeing with
  `Polynomial.qDerivative q` on polynomials and specializing at `q = 1` to `d⁄dX`.
* `PowerSeries.adaptedJacksonDeriv q`: `D'_q = (1 - q) D_q` on `A⟦X⟧`, agreeing with
  `Polynomial.adaptedJacksonDeriv q` on polynomials.

Both operators hold over arbitrary commutative (semi)rings, including positive characteristic and
roots of unity without inverting `1 - q`. Mathematically, the Jackson derivative characterizes the
normalized `q`-exponential `jacksonExp` via `D_q f = f`, while the adapted derivative satisfies
`X * D'_q f = f - f(q X)` and thereby yields the shift equation `(1 - t) U_q(t) = U_q(q t)` for
the reciprocal `q`-Pochhammer series (`D'_q f = f`).

## References

* W. J. G. Ong, notes of P. Scholze's course *V5A2 – The Habiro Ring of a Number Field*, Bonn,
  winter 2024/25 (6 March 2025 version,
  https://wgabrielong.github.io/academic-writing/notes/bonn-winter-24-25/V5A2-Habiro-Rings/Habiro_Rings_Notes.pdf),
  Definition 1.1, Table 1, and Propositions 2.1–2.2.
-/

public section

open Finset
open scoped Polynomial PowerSeries

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

/-- `PowerSeries.jacksonDeriv` agrees with `Polynomial.qDerivative` on polynomials. -/
@[simp] theorem jacksonDeriv_coe (q : A) (p : A[X]) :
    jacksonDeriv q (p : A⟦X⟧) = (Polynomial.qDerivative q p : A⟦X⟧) := by
  ext n; simp [Polynomial.coeff_qDerivative, mul_comm]

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
