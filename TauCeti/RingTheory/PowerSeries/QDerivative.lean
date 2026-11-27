/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import TauCeti.Algebra.Polynomial.QDerivative
import Mathlib.Algebra.Ring.GeomSum
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Power-series Jackson derivatives

This file develops the Jackson `q`-derivative and adapted Jackson `q`-derivative on formal power
series, without any division or invertibility assumptions:

* `PowerSeries.qDerivative q`: `D_q (X ^ n) = [n]_q X ^ (n - 1)` on `A⟦X⟧` over any commutative
  semiring `A`, agreeing with `Polynomial.qDerivative q` on polynomials and specializing at `q = 1`
  to `d⁄dX`.
* `PowerSeries.adaptedQDerivative q`: `D'_q = (1 - q) D_q` on `A⟦X⟧` over any commutative ring
  `A`, agreeing with `Polynomial.adaptedQDerivative q` on polynomials.

The ordinary Jackson derivative works over arbitrary commutative semirings and the adapted
derivative over arbitrary commutative rings, including in positive characteristic and at roots of
unity; neither requires division or inverting `1 - q`. Mathematically, downstream in
`TauCeti.RingTheory.QCalculus.Series`:

* assuming every positive `q`-integer `[n + 1]_q` is a unit, `D_q f = f` together with
  `constantCoeff f = 1` characterizes the normalized `q`-exponential `TauCeti.jacksonExp`;
* assuming every `1 - q ^ n` for positive `n` is a unit, `D'_q f = f` together with
  `constantCoeff f = 1` characterizes the reciprocal `q`-Pochhammer series
  `TauCeti.qPochhammerInvSeries`, and `X * D'_q f = f - f(q X)` yields its shift equation
  `(1 - t) U_q(t) = U_q(q t)`.

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
noncomputable def qDerivative (q : A) : A⟦X⟧ →ₗ[A] A⟦X⟧ where
  toFun f := mk fun n ↦ (∑ i ∈ range (n + 1), q ^ i) * coeff (n + 1) f
  map_add' f g := by ext n; simp [mul_add]
  map_smul' r f := by ext n; simp [mul_left_comm]

/-- Coefficient formula for `PowerSeries.qDerivative`:
`coeff n (D_q f) = [n + 1]_q * coeff (n + 1) f`. -/
@[simp] theorem coeff_qDerivative (q : A) (f : A⟦X⟧) (n : ℕ) :
    coeff n (qDerivative q f) = (∑ i ∈ range (n + 1), q ^ i) * coeff (n + 1) f := by
  simp [qDerivative]

/-- The `q`-derivative of a constant power series is `0`. -/
@[simp] theorem qDerivative_C (q a : A) : qDerivative q (C a) = 0 := by ext n; simp

/-- The `q`-derivative of `1` is `0`. -/
@[simp] theorem qDerivative_one (q : A) : qDerivative q (1 : A⟦X⟧) = 0 := by ext n; simp

/-- The `q`-derivative of `X` is `1`. -/
@[simp] theorem qDerivative_X (q : A) : qDerivative q (X : A⟦X⟧) = 1 := by
  ext (_ | n) <;> simp [coeff_X, coeff_one]

/-- `D_q (X ^ n) = C ([n]_q) * X ^ (n - 1)`. -/
theorem qDerivative_X_pow (q : A) (n : ℕ) :
    qDerivative q (X ^ n : A⟦X⟧) = C (∑ i ∈ range n, q ^ i) * X ^ (n - 1) := by
  rcases n with _ | n
  · simp
  · ext k; rw [coeff_qDerivative, coeff_X_pow, coeff_C_mul_X_pow]; by_cases h : k = n <;> simp [h]

/-- `D_q (X ^ (n + 1)) = C ([n + 1]_q) * X ^ n`. -/
@[simp] theorem qDerivative_X_pow_succ (q : A) (n : ℕ) :
    qDerivative q (X ^ (n + 1) : A⟦X⟧) = C (∑ i ∈ range (n + 1), q ^ i) * X ^ n := by
  simpa using qDerivative_X_pow q (n + 1)

/-- `PowerSeries.qDerivative` agrees with `Polynomial.qDerivative` on polynomials. -/
@[simp] theorem qDerivative_coe (q : A) (p : A[X]) :
    qDerivative q (p : A⟦X⟧) = (Polynomial.qDerivative q p : A⟦X⟧) := by
  ext n; simp [Polynomial.coeff_qDerivative, mul_comm]

/-- At `q = 1`, `PowerSeries.qDerivative` is the ordinary derivative's underlying linear map. -/
@[simp] theorem qDerivative_one_eq_derivative :
    qDerivative (1 : A) = (d⁄dX : Derivation A A⟦X⟧ A⟦X⟧).toLinearMap := by
  ext f n; simp [coeff_derivative, mul_comm]

/-- At `q = 1`, `PowerSeries.qDerivative` agrees pointwise with `d⁄dX`. -/
theorem qDerivative_one_apply (f : A⟦X⟧) : qDerivative (1 : A) f = d⁄dX f :=
  congrArg (· f) qDerivative_one_eq_derivative

/-- The `q`-derivative commutes with coefficient ring homomorphisms. -/
theorem map_qDerivative (φ : A →+* B) (q : A) (f : A⟦X⟧) :
    map φ (qDerivative q f) = qDerivative (φ q) (map φ f) := by ext n; simp [map_sum]

/-- **Twisted Leibniz rule** for the `q`-derivative:
`D_q (f * g) = D_q f * g + f(q X) * D_q g`. -/
theorem qDerivative_mul (q : A) (f g : A⟦X⟧) :
    qDerivative q (f * g) = qDerivative q f * g + rescale q f * qDerivative q g := by
  ext n
  let pf : A[X] := trunc (n + 2) f
  let pg : A[X] := trunc (n + 2) g
  have hqd (h₁ h₂ : A⟦X⟧) (hh : trunc (n + 2) h₁ = trunc (n + 2) h₂) :
      trunc (n + 1) (qDerivative q h₁) = trunc (n + 1) (qDerivative q h₂) :=
    trunc_eq_trunc_iff.mpr fun k hk ↦ by
      simp only [coeff_qDerivative]
      rw [coeff_eq_of_trunc_eq hh (by omega)]
  have hres : trunc (n + 1) (rescale q (pf : A⟦X⟧)) = trunc (n + 1) (rescale q f) :=
    trunc_eq_trunc_iff.mpr fun k hk ↦ by
      simp only [coeff_rescale]
      rw [coeff_eq_of_trunc_eq (trunc_trunc f) (by omega)]
  have hlhs : coeff n (qDerivative q (f * g)) =
      coeff n ((Polynomial.qDerivative q (pf * pg) : A[X]) : A⟦X⟧) := by
    rw [← qDerivative_coe, Polynomial.coe_mul, coeff_qDerivative, coeff_qDerivative,
      coeff_mul_eq_coeff_trunc_mul_trunc f g (Nat.lt_succ_self (n + 1))]
  have hcomp :
      ((pf.comp (Polynomial.C q * Polynomial.X) : A[X]) : A⟦X⟧) = rescale q (pf : A⟦X⟧) := by
    ext k
    rw [Polynomial.coeff_coe, Polynomial.comp_C_mul_X_coeff, coeff_rescale, Polynomial.coeff_coe,
      mul_comm]
  have hrhs1 : coeff n (qDerivative q f * g) =
      coeff n ((Polynomial.qDerivative q pf * pg : A[X]) : A⟦X⟧) := by
    rw [Polynomial.coe_mul, ← qDerivative_coe]
    exact coeff_eq_of_trunc_eq (trunc_mul_eq_of_trunc_eq (hqd f _ (trunc_trunc f).symm)
      (trunc_eq_of_trunc_eq_of_le (trunc_trunc g).symm (by omega))) (Nat.lt_succ_self n)
  have hrhs2 : coeff n (rescale q f * qDerivative q g) =
      coeff n ((pf.comp (Polynomial.C q * Polynomial.X) * Polynomial.qDerivative q pg : A[X]) :
        A⟦X⟧) := by
    rw [Polynomial.coe_mul, hcomp, ← qDerivative_coe]
    exact coeff_eq_of_trunc_eq (trunc_mul_eq_of_trunc_eq hres.symm (hqd g _ (trunc_trunc g).symm))
      (Nat.lt_succ_self n)
  rw [hlhs, Polynomial.qDerivative_mul, Polynomial.coe_add, map_add, map_add, hrhs1, hrhs2]

end Semiring

section Ring

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The **adapted Jackson `q`-derivative** `D'_q = (1 - q) D_q` on power series, sending `X ^ n` to
`(1 - q ^ n) X ^ (n - 1)`. -/
noncomputable def adaptedQDerivative (q : A) : A⟦X⟧ →ₗ[A] A⟦X⟧ :=
  (1 - q) • qDerivative q

/-- Unfolding definition of `PowerSeries.adaptedQDerivative`. -/
theorem adaptedQDerivative_apply (q : A) (f : A⟦X⟧) :
    adaptedQDerivative q f = (1 - q) • qDerivative q f :=
  (rfl)

/-- Coefficient formula for `PowerSeries.adaptedQDerivative`:
`coeff n (D'_q f) = (1 - q ^ (n + 1)) * coeff (n + 1) f`. -/
@[simp] theorem coeff_adaptedQDerivative (q : A) (f : A⟦X⟧) (n : ℕ) :
    coeff n (adaptedQDerivative q f) = (1 - q ^ (n + 1)) * coeff (n + 1) f := by
  rw [adaptedQDerivative_apply, coeff_smul, smul_eq_mul, coeff_qDerivative, ← mul_assoc,
    mul_neg_geom_sum]

/-- The adapted Jackson derivative of a constant power series is `0`. -/
@[simp] theorem adaptedQDerivative_C (q a : A) : adaptedQDerivative q (C a) = 0 := by
  simp [adaptedQDerivative_apply]

/-- The adapted Jackson derivative of `1` is `0`. -/
@[simp] theorem adaptedQDerivative_one (q : A) : adaptedQDerivative q (1 : A⟦X⟧) = 0 := by
  ext n; simp

/-- The adapted Jackson derivative of `X` is `C (1 - q)`. -/
@[simp] theorem adaptedQDerivative_X (q : A) : adaptedQDerivative q (X : A⟦X⟧) = C (1 - q) := by
  simp [adaptedQDerivative_apply, Algebra.smul_def]

/-- `D'_q (X ^ n) = C (1 - q ^ n) * X ^ (n - 1)`. -/
theorem adaptedQDerivative_X_pow (q : A) (n : ℕ) :
    adaptedQDerivative q (X ^ n : A⟦X⟧) = C (1 - q ^ n) * X ^ (n - 1) := by
  rw [adaptedQDerivative_apply, Algebra.smul_def, algebraMap_eq, qDerivative_X_pow,
    ← mul_assoc, ← map_mul, mul_neg_geom_sum]

/-- `D'_q (X ^ (n + 1)) = C (1 - q ^ (n + 1)) * X ^ n`. -/
@[simp] theorem adaptedQDerivative_X_pow_succ (q : A) (n : ℕ) :
    adaptedQDerivative q (X ^ (n + 1) : A⟦X⟧) = C (1 - q ^ (n + 1)) * X ^ n := by
  simpa using adaptedQDerivative_X_pow q (n + 1)

/-- `PowerSeries.adaptedQDerivative` agrees with `Polynomial.adaptedQDerivative` on
polynomials. -/
@[simp] theorem adaptedQDerivative_coe (q : A) (p : A[X]) :
    adaptedQDerivative q (p : A⟦X⟧) = (Polynomial.adaptedQDerivative q p : A⟦X⟧) := by
  ext n; simp

/-- At `q = 1`, the adapted Jackson derivative vanishes identically. -/
@[simp] theorem adaptedQDerivative_base_one : adaptedQDerivative (1 : A) = 0 := by ext f n; simp

/-- The adapted Jackson derivative commutes with coefficient ring homomorphisms. -/
theorem map_adaptedQDerivative (φ : A →+* B) (q : A) (f : A⟦X⟧) :
    map φ (adaptedQDerivative q f) = adaptedQDerivative (φ q) (map φ f) := by ext n; simp

/-- **Twisted Leibniz rule** for the adapted Jackson derivative:
`D'_q (f * g) = D'_q f * g + f(q X) * D'_q g`. -/
theorem adaptedQDerivative_mul (q : A) (f g : A⟦X⟧) :
    adaptedQDerivative q (f * g) =
      adaptedQDerivative q f * g + rescale q f * adaptedQDerivative q g := by
  simp only [adaptedQDerivative_apply, qDerivative_mul, smul_add, smul_mul_assoc, mul_smul_comm]

/-- Difference identity: `X * D'_q f = f - f(q X)`. -/
theorem X_mul_adaptedQDerivative (q : A) (f : A⟦X⟧) :
    X * adaptedQDerivative q f = f - rescale q f := by
  ext (_ | n)
  · rw [coeff_zero_X_mul, map_sub, coeff_rescale, pow_zero, one_mul, sub_self]
  · simp [coeff_succ_X_mul, coeff_rescale, sub_mul]

end Ring

end PowerSeries
