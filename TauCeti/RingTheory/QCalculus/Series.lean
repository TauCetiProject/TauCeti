/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.PowerSeries
public import Mathlib.RingTheory.PowerSeries.Log
public import TauCeti.Algebra.Ring.QPochhammer.Basic
public import TauCeti.RingTheory.PowerSeries.Basic
public import TauCeti.RingTheory.PowerSeries.QDerivative
import Mathlib.Tactic.Ring
import TauCeti.RingTheory.PowerSeries.Log
import TauCeti.RingTheory.PowerSeries.Rescale

/-!
# Formal q-exponential and infinite q-Pochhammer series

This file constructs the formal power series of elementary `q`-calculus and establishes their
functional equations, formal logarithms, and integral `q`-adic realization:

* `TauCeti.jacksonExp q`: normalized Jackson `q`-exponential `∑_{n ≥ 0} t ^ n / [n]_q!`.
* `TauCeti.qPochhammerSeries q`: `E_q(t) = ∑_{n ≥ 0} (-1) ^ n q ^ (n (n - 1) / 2) t ^ n / (q; q)_n`.
* `TauCeti.qPochhammerInvSeries q`: `U_q(t) = ∑_{n ≥ 0} t ^ n / (q; q)_n`.
* `TauCeti.qBinomialSeries a q`: `∑_{n ≥ 0} (a; q)_n t ^ n / (q; q)_n`.
* `TauCeti.integralQPochhammer R`: integral infinite product `∏_{i ≥ 0} (1 - q ^ i t)` in
  `(R⟦X⟧)⟦X⟧`, defined by `q`-adic coefficient stabilization of `qPochhammer X (C X) N`.

The `q`-exponential and `q`-Pochhammer series are defined over any commutative semiring or ring
using `Ring.inverse` on the denominators (`qFactorial` and `qPochhammer`), with no unit hypotheses
on the definitions themselves. Theorems characterizing their differential and shift equations,
uniqueness, coefficient-map compatibility (`map_*`), reciprocal and `q`-binomial identities, and
formal logarithms carry explicit unit hypotheses (`∀ n, IsUnit (∑ i ∈ range (n + 1), q ^ i)` for
`jacksonExp` over any `CommSemiring`, and `∀ n, IsUnit (1 - q ^ (n + 1))` for `qPochhammerSeries`,
`qPochhammerInvSeries`, and `qBinomialSeries` over any `CommRing`), so every coefficient
denominator is a unit and `Ring.inverse` gives the exact multiplicative inverse. In
`jacksonExp_one`, the `[Algebra ℚ R]` structure supplies the units `[n + 1]_1 = n + 1`
automatically; by contrast, the formal logarithm identities `logOf_qPochhammerSeries` and
`logOf_qPochhammerInvSeries` require `[Algebra ℚ A]` together with the explicit unit hypothesis
`∀ n, IsUnit (1 - q ^ (n + 1))`. Meanwhile, `integralQPochhammer` requires no unit hypotheses.

## References

* W. J. G. Ong, notes of P. Scholze's course *V5A2 – The Habiro Ring of a Number Field*, Bonn,
  winter 2024/25 (6 March 2025 version,
  https://wgabrielong.github.io/academic-writing/notes/bonn-winter-24-25/V5A2-Habiro-Rings/Habiro_Rings_Notes.pdf),
  Propositions 1.5, 2.1, 2.2, 2.5, and Corollary 2.6.
-/

public section

open Finset PowerSeries
open scoped Polynomial PowerSeries

namespace TauCeti

/-! ### Normalized Jackson `q`-exponential -/

section JacksonExp

variable {A B : Type*} [CommSemiring A] [CommSemiring B]

/-- The **normalized Jackson `q`-exponential** `∑_{n ≥ 0} t ^ n / [n]_q!`, defined over any
commutative semiring via `Ring.inverse (qFactorial q n)`. Whenever every positive `[n]_q` is a
unit, every `[n]_q!` is a unit, `Ring.inverse` is its exact multiplicative inverse, and
`jacksonExp q` is the unique solution to `D_q f = f`, `constantCoeff f = 1`
(`TauCeti.eq_jacksonExp_iff`). -/
noncomputable def jacksonExp (q : A) : A⟦X⟧ :=
  PowerSeries.mk fun n ↦ Ring.inverse (qFactorial q n)

/-- Coefficient formula for `TauCeti.jacksonExp`: `coeff n (jacksonExp q) = ([n]_q!)⁻¹ʳ`. -/
@[simp] theorem coeff_jacksonExp (q : A) (n : ℕ) :
    coeff n (jacksonExp q) = Ring.inverse (qFactorial q n) :=
  coeff_mk n _

/-- The constant coefficient of `TauCeti.jacksonExp` is `1`. -/
@[simp] theorem constantCoeff_jacksonExp (q : A) :
    constantCoeff (jacksonExp q) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_jacksonExp, qFactorial_zero, Ring.inverse_one]

/-- The degree-`1` coefficient of the Jackson `q`-exponential is `1`. -/
theorem coeff_one_jacksonExp (q : A) : coeff 1 (jacksonExp q) = 1 := by
  rw [coeff_jacksonExp, qFactorial_one, Ring.inverse_one]

/-- The degree-`2` coefficient of the Jackson `q`-exponential is `(1 + q)⁻¹ʳ`. -/
theorem coeff_two_jacksonExp (q : A) : coeff 2 (jacksonExp q) = Ring.inverse (1 + q) := by
  rw [coeff_jacksonExp, qFactorial_succ, qFactorial_one, one_mul]; simp [sum_range_succ]

/-- Under unit hypotheses on all positive `[n]_q`, the Jackson exponential satisfies `D_q f = f`. -/
theorem qDerivative_jacksonExp {q : A} (hq : ∀ n, IsUnit (∑ i ∈ range (n + 1), q ^ i)) :
    qDerivative q (jacksonExp q) = jacksonExp q := by
  ext n
  rw [coeff_qDerivative, coeff_jacksonExp, coeff_jacksonExp, qFactorial_succ,
    Ring.inverse_mul (Or.inr (hq n)), ← mul_assoc, Ring.mul_inverse_cancel _ (hq n), one_mul]

/-- **Uniqueness of the Jackson initial-value problem**: when every positive `[n]_q` is a unit,
`jacksonExp q` is the unique power series satisfying `D_q f = f` and `constantCoeff f = 1`. -/
theorem eq_jacksonExp_iff {q : A} (hq : ∀ n, IsUnit (∑ i ∈ range (n + 1), q ^ i)) {f : A⟦X⟧} :
    f = jacksonExp q ↔ qDerivative q f = f ∧ constantCoeff f = 1 := by
  refine ⟨fun h ↦ h ▸ ⟨qDerivative_jacksonExp hq, constantCoeff_jacksonExp q⟩, ?_⟩
  rintro ⟨hderiv, hzero⟩
  ext n
  induction n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff_apply, hzero, coeff_jacksonExp, qFactorial_zero,
      Ring.inverse_one]
  | succ n ih =>
    have hstep := congrArg (coeff n) hderiv
    rw [coeff_qDerivative, ih, coeff_jacksonExp] at hstep
    rw [coeff_jacksonExp, qFactorial_succ, Ring.inverse_mul (Or.inr (hq n))]
    exact (Ring.inverse_mul_eq_iff_eq_mul _ _ _ (hq n)).mpr hstep.symm |>.symm

/-- The Jackson `q`-exponential commutes with coefficient ring homomorphisms whenever every
positive `[n]_q` is a unit. -/
theorem map_jacksonExp (φ : A →+* B) {q : A} (hq : ∀ n, IsUnit (∑ i ∈ range (n + 1), q ^ i)) :
    map φ (jacksonExp q) = jacksonExp (φ q) := by
  ext n
  rw [coeff_map, coeff_jacksonExp, coeff_jacksonExp, ← map_qFactorial]
  exact ((isUnit_qFactorial_iff q n).mpr fun k _ ↦ hq k).map_ringInverse φ

/-- At `q = 1` over a `ℚ`-algebra, where `[n + 1]_1 = n + 1` is automatically a unit, the
Jackson exponential is the ordinary exponential series. -/
@[simp] theorem jacksonExp_one {R : Type*} [CommRing R] [Algebra ℚ R] :
    jacksonExp (1 : R) = PowerSeries.exp R := by
  ext n
  rw [coeff_jacksonExp, coeff_exp, qFactorial_base_one]
  have hne : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hu : IsUnit (n.factorial : R) := by
    rw [← map_natCast (algebraMap ℚ R)]; exact (Ne.isUnit hne).map _
  apply hu.mul_left_cancel
  rw [Ring.mul_inverse_cancel _ hu, ← map_natCast (algebraMap ℚ R), ← map_mul,
    mul_one_div_cancel hne, map_one]

end JacksonExp

/-! ### Formal infinite `q`-Pochhammer, reciprocal, and `q`-binomial series -/

section FormalPochhammer

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The **formal infinite `q`-Pochhammer series**
`E_q(t) = ∑_{n ≥ 0} (-1) ^ n q ^ (n (n - 1) / 2) t ^ n / (q; q)_n`, defined over any commutative
ring via `Ring.inverse (qPochhammer q q n)`. Whenever every `1 - q ^ (n + 1)` is a unit, every
`(q; q)_n` is a unit and `Ring.inverse` is its exact multiplicative inverse. -/
noncomputable def qPochhammerSeries (q : A) : A⟦X⟧ :=
  PowerSeries.mk fun n ↦ (-1) ^ n * q ^ (n * (n - 1) / 2) * Ring.inverse (qPochhammer q q n)

/-- The **formal reciprocal `q`-Pochhammer series** `U_q(t) = ∑_{n ≥ 0} t ^ n / (q; q)_n`, defined
over any commutative ring via `Ring.inverse (qPochhammer q q n)`. Whenever every `1 - q ^ (n + 1)`
is a unit, every `(q; q)_n` is a unit, `Ring.inverse` is its exact multiplicative inverse, and
`U_q` is the multiplicative inverse of `qPochhammerSeries q`
(`TauCeti.qPochhammerSeries_mul_qPochhammerInvSeries`). -/
noncomputable def qPochhammerInvSeries (q : A) : A⟦X⟧ :=
  PowerSeries.mk fun n ↦ Ring.inverse (qPochhammer q q n)

/-- The **formal `q`-binomial series** `∑_{n ≥ 0} (a; q)_n t ^ n / (q; q)_n`, defined over any
commutative ring via `Ring.inverse (qPochhammer q q n)`. Whenever every `1 - q ^ (n + 1)` is a
unit, every `(q; q)_n` is a unit and `Ring.inverse` is its exact multiplicative inverse. -/
noncomputable def qBinomialSeries (a q : A) : A⟦X⟧ :=
  PowerSeries.mk fun n ↦ qPochhammer a q n * Ring.inverse (qPochhammer q q n)

/-- Coefficient formula for `TauCeti.qPochhammerSeries`:
`coeff n (E_q(t)) = (-1) ^ n * q ^ (n (n - 1) / 2) * ((q; q)_n)⁻¹ʳ`. -/
@[simp] theorem coeff_qPochhammerSeries (q : A) (n : ℕ) :
    coeff n (qPochhammerSeries q) =
      (-1) ^ n * q ^ (n * (n - 1) / 2) * Ring.inverse (qPochhammer q q n) :=
  coeff_mk n _

/-- Coefficient formula for `TauCeti.qPochhammerInvSeries`:
`coeff n (U_q(t)) = ((q; q)_n)⁻¹ʳ`. -/
@[simp] theorem coeff_qPochhammerInvSeries (q : A) (n : ℕ) :
    coeff n (qPochhammerInvSeries q) = Ring.inverse (qPochhammer q q n) :=
  coeff_mk n _

/-- Coefficient formula for `TauCeti.qBinomialSeries`:
`coeff n (qBinomialSeries a q) = (a; q)_n * ((q; q)_n)⁻¹ʳ`. -/
@[simp] theorem coeff_qBinomialSeries (a q : A) (n : ℕ) :
    coeff n (qBinomialSeries a q) = qPochhammer a q n * Ring.inverse (qPochhammer q q n) :=
  coeff_mk n _

/-- The constant coefficient of `TauCeti.qPochhammerSeries` is `1`. -/
@[simp] theorem constantCoeff_qPochhammerSeries (q : A) :
    constantCoeff (qPochhammerSeries q) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_qPochhammerSeries]; simp

/-- The constant coefficient of `TauCeti.qPochhammerInvSeries` is `1`. -/
@[simp] theorem constantCoeff_qPochhammerInvSeries (q : A) :
    constantCoeff (qPochhammerInvSeries q) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_qPochhammerInvSeries]; simp

/-- The constant coefficient of `TauCeti.qBinomialSeries` is `1`. -/
@[simp] theorem constantCoeff_qBinomialSeries (a q : A) :
    constantCoeff (qBinomialSeries a q) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_qBinomialSeries]; simp

/-- At `q = 0`, `E_0(t) = 1 - t`. -/
@[simp] theorem qPochhammerSeries_zero :
    qPochhammerSeries (0 : A) = 1 - X := by
  ext (_ | _ | n)
  · simp
  · simp
  · have hpos : 0 < (n + 2) * (n + 1) / 2 := Nat.div_pos (by nlinarith) two_pos
    simp [coeff_X, zero_pow (Nat.ne_of_gt hpos)]

/-- At `q = 0`, every coefficient of `U_0(t)` is `1`. -/
theorem coeff_qPochhammerInvSeries_zero (n : ℕ) :
    coeff n (qPochhammerInvSeries (0 : A)) = 1 := by simp

/-- The degree-`1` coefficient of `U_q(t)` is `(1 - q)⁻¹ʳ`. -/
theorem coeff_one_qPochhammerInvSeries (q : A) :
    coeff 1 (qPochhammerInvSeries q) = Ring.inverse (1 - q) := by simp

/-- The degree-`2` coefficient of `E_q(t)` is `q * ((1 - q) * (1 - q ^ 2))⁻¹ʳ`. -/
theorem coeff_two_qPochhammerSeries (q : A) :
    coeff 2 (qPochhammerSeries q) = q * Ring.inverse ((1 - q) * (1 - q ^ 2)) := by
  rw [coeff_qPochhammerSeries, qPochhammer_succ, qPochhammer_one]; norm_num [pow_two]

/-- At `a = 1`, the `q`-binomial series is `1`. -/
@[simp] theorem qBinomialSeries_one_left (q : A) :
    qBinomialSeries (1 : A) q = 1 := by
  ext (_ | n)
  · simp
  · simp [qPochhammer_eq_zero_of_mul_pow_eq_one (x := (1 : A)) (q := q) (i := 0)
      (Nat.succ_pos n) (by simp)]

/-- At `a = 0`, the `q`-binomial series is `U_q(t)`. -/
@[simp] theorem qBinomialSeries_zero_left (q : A) :
    qBinomialSeries (0 : A) q = qPochhammerInvSeries q := by ext n; simp

/-- The degree-`1` coefficient of `qBinomialSeries a q` is `(1 - a) * (1 - q)⁻¹ʳ`. -/
theorem coeff_one_qBinomialSeries (a q : A) :
    coeff 1 (qBinomialSeries a q) = (1 - a) * Ring.inverse (1 - q) := by simp

/-- `E_q` commutes with coefficient ring homomorphisms when all `1 - q ^ (n + 1)` are units. -/
theorem map_qPochhammerSeries (φ : A →+* B) {q : A} (hq : ∀ n, IsUnit (1 - q ^ (n + 1))) :
    map φ (qPochhammerSeries q) = qPochhammerSeries (φ q) := by
  ext n
  rw [coeff_map, coeff_qPochhammerSeries, coeff_qPochhammerSeries, map_mul, map_mul, map_pow,
    map_neg, map_one, map_pow, ← map_qPochhammer]
  exact congrArg _ (((isUnit_qPochhammer_self_iff q n).mpr fun k _ ↦ hq k).map_ringInverse φ)

/-- `U_q` commutes with coefficient ring homomorphisms when all `1 - q ^ (n + 1)` are units. -/
theorem map_qPochhammerInvSeries (φ : A →+* B) {q : A} (hq : ∀ n, IsUnit (1 - q ^ (n + 1))) :
    map φ (qPochhammerInvSeries q) = qPochhammerInvSeries (φ q) := by
  ext n
  rw [coeff_map, coeff_qPochhammerInvSeries, coeff_qPochhammerInvSeries, ← map_qPochhammer]
  exact ((isUnit_qPochhammer_self_iff q n).mpr fun k _ ↦ hq k).map_ringInverse φ

/-- `qBinomialSeries` commutes with coefficient ring homomorphisms when all `1 - q ^ (n + 1)` are
units. -/
theorem map_qBinomialSeries (φ : A →+* B) {a q : A} (hq : ∀ n, IsUnit (1 - q ^ (n + 1))) :
    map φ (qBinomialSeries a q) = qBinomialSeries (φ a) (φ q) := by
  ext n
  rw [coeff_map, coeff_qBinomialSeries, coeff_qBinomialSeries, map_mul, map_qPochhammer,
    ← map_qPochhammer φ q q n]
  exact congrArg _ (((isUnit_qPochhammer_self_iff q n).mpr fun k _ ↦ hq k).map_ringInverse φ)

/-- Under unit hypotheses on `1 - q ^ (n + 1)`, `U_q` satisfies the adapted Jackson differential
equation `D'_q U_q = U_q`. -/
theorem adaptedQDerivative_qPochhammerInvSeries {q : A} (hq : ∀ n, IsUnit (1 - q ^ (n + 1))) :
    adaptedQDerivative q (qPochhammerInvSeries q) = qPochhammerInvSeries q := by
  ext n
  rw [coeff_adaptedQDerivative, coeff_qPochhammerInvSeries, coeff_qPochhammerInvSeries,
    qPochhammer_succ, ← pow_succ', Ring.inverse_mul (Or.inr (hq n)), ← mul_assoc,
    Ring.mul_inverse_cancel _ (hq n), one_mul]

/-- **Uniqueness of the adapted Jackson initial-value problem**: when every `1 - q ^ (n + 1)` is a
unit, `U_q` is the unique power series satisfying `D'_q f = f` and `constantCoeff f = 1`. -/
theorem eq_qPochhammerInvSeries_iff {q : A} (hq : ∀ n, IsUnit (1 - q ^ (n + 1))) {f : A⟦X⟧} :
    f = qPochhammerInvSeries q ↔ adaptedQDerivative q f = f ∧ constantCoeff f = 1 := by
  refine ⟨fun h ↦ h ▸ ⟨adaptedQDerivative_qPochhammerInvSeries hq,
    constantCoeff_qPochhammerInvSeries q⟩, ?_⟩
  rintro ⟨hderiv, hzero⟩
  ext n
  induction n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff_apply, hzero, coeff_qPochhammerInvSeries, qPochhammer_zero,
      Ring.inverse_one]
  | succ n ih =>
    have hstep := congrArg (coeff n) hderiv
    rw [coeff_adaptedQDerivative, ih, coeff_qPochhammerInvSeries] at hstep
    rw [coeff_qPochhammerInvSeries, qPochhammer_succ, ← pow_succ',
      Ring.inverse_mul (Or.inr (hq n))]
    exact (Ring.inverse_mul_eq_iff_eq_mul _ _ _ (hq n)).mpr hstep.symm |>.symm

/-- **Shift identity for `U_q`**: when every `1 - q ^ n` (`n > 0`) is a unit,
`(1 - t) U_q(t) = U_q(q t)`. -/
theorem one_sub_X_mul_qPochhammerInvSeries {q : A} (hq : ∀ n, IsUnit (1 - q ^ (n + 1))) :
    (1 - X) * qPochhammerInvSeries q = rescale q (qPochhammerInvSeries q) := by
  have h := X_mul_adaptedQDerivative q (qPochhammerInvSeries q)
  rw [adaptedQDerivative_qPochhammerInvSeries hq] at h
  linear_combination -h

/-- **Shift identity for `E_q`**: when every `1 - q ^ n` (`n > 0`) is a unit,
`E_q(t) = (1 - t) E_q(q t)`. -/
theorem qPochhammerSeries_eq_one_sub_X_mul_rescale {q : A} (hq : ∀ n, IsUnit (1 - q ^ (n + 1))) :
    qPochhammerSeries q = (1 - X) * rescale q (qPochhammerSeries q) := by
  ext (_ | n)
  · simp
  · rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul, coeff_rescale, coeff_rescale]
    have htri : (n + 1) * n / 2 = n * (n - 1) / 2 + n := by
      simpa only [Nat.add_sub_cancel] using Nat.triangle_succ n
    have hstep : (1 - q ^ (n + 1)) * coeff (n + 1) (qPochhammerSeries q) =
        -q ^ n * coeff n (qPochhammerSeries q) := by
      rw [coeff_qPochhammerSeries, coeff_qPochhammerSeries, qPochhammer_succ, ← pow_succ',
        Ring.inverse_mul (Or.inr (hq n)), Nat.add_sub_cancel, htri, pow_add q (n * (n - 1) / 2) n,
        pow_succ (-1 : A) n]
      linear_combination
        (-q ^ n * ((-1) ^ n * q ^ (n * (n - 1) / 2) * Ring.inverse (qPochhammer q q n))) *
          Ring.mul_inverse_cancel _ (hq n)
    linear_combination hstep

/-- **Uniqueness for the shift equation of `E_q`**: when every `1 - q ^ (n + 1)` is a unit,
`E_q` is the unique power series with constant coefficient `1` satisfying `f = (1 - t) f(q t)`. -/
theorem eq_qPochhammerSeries_iff {q : A} (hq : ∀ n, IsUnit (1 - q ^ (n + 1))) {f : A⟦X⟧} :
    f = qPochhammerSeries q ↔ f = (1 - X) * rescale q f ∧ constantCoeff f = 1 := by
  refine ⟨fun h ↦ h ▸ ⟨qPochhammerSeries_eq_one_sub_X_mul_rescale hq,
    constantCoeff_qPochhammerSeries q⟩, ?_⟩
  rintro ⟨hshift, hzero⟩
  ext n
  induction n with
  | zero => rw [coeff_zero_eq_constantCoeff_apply, hzero, coeff_qPochhammerSeries]; simp
  | succ n ih =>
    have hf := congrArg (coeff (n + 1)) hshift
    have hE := congrArg (coeff (n + 1)) (qPochhammerSeries_eq_one_sub_X_mul_rescale hq)
    simp only [sub_mul, one_mul, map_sub, coeff_succ_X_mul, coeff_rescale] at hf hE
    rw [ih] at hf
    exact (hq n).mul_left_cancel (by linear_combination hf - hE)

/-- **Shift identity for `qBinomialSeries`**: when every `1 - q ^ n` (`n > 0`) is a unit,
`(1 - t) f(t) = (1 - a t) f(q t)`. -/
theorem one_sub_X_mul_qBinomialSeries (a : A) {q : A} (hq : ∀ n, IsUnit (1 - q ^ (n + 1))) :
    (1 - X) * qBinomialSeries a q = (1 - C a * X) * rescale q (qBinomialSeries a q) := by
  ext (_ | n)
  · simp
  · simp only [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_succ_X_mul, coeff_rescale]
    have hstep : (1 - q ^ (n + 1)) * coeff (n + 1) (qBinomialSeries a q) =
        (1 - a * q ^ n) * coeff n (qBinomialSeries a q) := by
      rw [coeff_qBinomialSeries, coeff_qBinomialSeries, qPochhammer_succ a q n,
        qPochhammer_succ q q n, ← pow_succ', Ring.inverse_mul (Or.inr (hq n))]
      linear_combination
        ((1 - a * q ^ n) * (qPochhammer a q n * Ring.inverse (qPochhammer q q n))) *
          Ring.mul_inverse_cancel _ (hq n)
    linear_combination hstep

/-- **Uniqueness for the `q`-binomial functional equation**: when every `1 - q ^ (n + 1)` is a
unit, `qBinomialSeries a q` is the unique power series with constant coefficient `1` satisfying
`(1 - t) f(t) = (1 - a t) f(q t)`. -/
theorem eq_qBinomialSeries_iff {a q : A} (hq : ∀ n, IsUnit (1 - q ^ (n + 1))) {f : A⟦X⟧} :
    f = qBinomialSeries a q ↔
      (1 - X) * f = (1 - C a * X) * rescale q f ∧ constantCoeff f = 1 := by
  have hB := one_sub_X_mul_qBinomialSeries a hq
  refine ⟨fun h ↦ h ▸ ⟨hB, constantCoeff_qBinomialSeries a q⟩, ?_⟩
  rintro ⟨heq, hzero⟩
  ext n
  induction n with
  | zero => rw [coeff_zero_eq_constantCoeff_apply, hzero, coeff_qBinomialSeries]; simp
  | succ n ih =>
    have hf := congrArg (coeff (n + 1)) heq
    have hB' := congrArg (coeff (n + 1)) hB
    simp only [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_succ_X_mul,
      coeff_rescale] at hf hB'
    rw [ih] at hf
    exact (hq n).mul_left_cancel (by linear_combination hf - hB')

/-- **General `q`-binomial identity**: when every `1 - q ^ n` (`n > 0`) is a unit,
`E_q(a t) U_q(t) = ∑_{n ≥ 0} (a; q)_n t ^ n / (q; q)_n`. -/
theorem rescale_qPochhammerSeries_mul_qPochhammerInvSeries (a : A) {q : A}
    (hq : ∀ n, IsUnit (1 - q ^ (n + 1))) :
    rescale a (qPochhammerSeries q) * qPochhammerInvSeries q = qBinomialSeries a q := by
  refine (eq_qBinomialSeries_iff hq).mpr ⟨?_, by simp⟩
  have hEa : rescale a (qPochhammerSeries q) =
      (1 - C a * X) * rescale q (rescale a (qPochhammerSeries q)) := by
    simpa [map_mul, map_sub, rescale_X, rescale_rescale, mul_comm a q] using
      congrArg (rescale a) (qPochhammerSeries_eq_one_sub_X_mul_rescale hq)
  rw [mul_left_comm, one_sub_X_mul_qPochhammerInvSeries hq, map_mul, ← mul_assoc, ← hEa]

/-- **Euler's reciprocal identity**: when every `1 - q ^ n` (`n > 0`) is a unit,
`E_q(t) U_q(t) = 1`. -/
theorem qPochhammerSeries_mul_qPochhammerInvSeries {q : A} (hq : ∀ n, IsUnit (1 - q ^ (n + 1))) :
    qPochhammerSeries q * qPochhammerInvSeries q = 1 := by
  simpa using rescale_qPochhammerSeries_mul_qPochhammerInvSeries (1 : A) hq

end FormalPochhammer

/-! ### Formal logarithms of `E_q` and `U_q` -/

section FormalLog

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- **Formal logarithm of `E_q`**: when every `1 - q ^ n` (`n > 0`) is a unit over a `ℚ`-algebra,
`log E_q(t) = -∑_{n ≥ 1} t ^ n / (n (1 - q ^ n))`. -/
theorem logOf_qPochhammerSeries {q : A} (hq : ∀ n, IsUnit (1 - q ^ (n + 1))) :
    logOf (qPochhammerSeries q) =
      PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ • -Ring.inverse (1 - q ^ n) := by
  have hlog : logOf (qPochhammerSeries q) =
      logOf (1 - X : A⟦X⟧) + rescale q (logOf (qPochhammerSeries q)) := by
    conv_lhs => rw [qPochhammerSeries_eq_one_sub_X_mul_rescale hq]
    rw [logOf_mul (by simp) (by simp), logOf_rescale q (constantCoeff_qPochhammerSeries q)]
  have h1X : logOf (1 - X : A⟦X⟧) = PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ • (-1 : A) := by
    simpa using logOf_one_sub_C_mul_X (1 : A)
  ext (_ | n)
  · simp [constantCoeff_logOf (constantCoeff_qPochhammerSeries q)]
  · have hstep := congrArg (coeff (n + 1)) hlog
    rw [map_add, coeff_rescale, h1X, coeff_mk] at hstep
    have hmul : (1 - q ^ (n + 1)) * coeff (n + 1) (logOf (qPochhammerSeries q)) =
        ((n + 1 : ℕ) : ℚ)⁻¹ • (-1 : A) := by linear_combination hstep
    rw [coeff_mk]
    apply (hq n).mul_left_cancel
    rw [hmul, smul_neg, smul_neg, mul_neg, mul_smul_comm, Ring.mul_inverse_cancel _ (hq n)]

/-- **Formal logarithm of `U_q`**: when every `1 - q ^ n` (`n > 0`) is a unit over a `ℚ`-algebra,
`log U_q(t) = ∑_{n ≥ 1} t ^ n / (n (1 - q ^ n))`. -/
theorem logOf_qPochhammerInvSeries {q : A} (hq : ∀ n, IsUnit (1 - q ^ (n + 1))) :
    logOf (qPochhammerInvSeries q) =
      PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ • Ring.inverse (1 - q ^ n) := by
  have h := congrArg logOf (qPochhammerSeries_mul_qPochhammerInvSeries hq)
  rw [logOf_mul (constantCoeff_qPochhammerSeries q) (constantCoeff_qPochhammerInvSeries q),
    logOf_one, logOf_qPochhammerSeries hq] at h
  ext n
  have hn := congrArg (coeff n) h
  simp only [map_add, coeff_mk, map_zero, smul_neg] at hn
  rw [coeff_mk]
  linear_combination hn

end FormalLog

/-! ### Integral infinite `q`-Pochhammer product in `(R⟦X⟧)⟦X⟧` -/

section IntegralPochhammer

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **Coefficientwise `q`-adic stabilization** of the finite `q`-Pochhammer product
`∏_{i < N} (1 - q ^ i t)` in `(R⟦X⟧)⟦X⟧`: the `[q ^ m t ^ k]` coefficient stabilizes for all
`N > m`. -/
theorem coeff_coeff_qPochhammer_eq_of_lt (m k : ℕ) {N : ℕ} (hN : m < N) :
    coeff m (coeff k (qPochhammer (X : (R⟦X⟧)⟦X⟧) (C (X : R⟦X⟧)) N)) =
      coeff m (coeff k (qPochhammer (X : (R⟦X⟧)⟦X⟧) (C (X : R⟦X⟧)) (m + 1))) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc, qPochhammer_succ]
    have hmul (f : (R⟦X⟧)⟦X⟧) :
        coeff m (coeff k (f * (1 - X * C (X : R⟦X⟧) ^ (m.succ + d)))) = coeff m (coeff k f) := by
      rw [mul_sub, mul_one, map_sub, map_sub, sub_eq_self]
      rcases k with _ | k
      · rw [← mul_assoc, mul_comm f X, mul_assoc, coeff_zero_X_mul, map_zero]
      · rw [← mul_assoc, mul_comm f X, mul_assoc, coeff_succ_X_mul, ← map_pow, coeff_mul_C,
          mul_comm, coeff_X_pow_mul']
        simp [Nat.not_le.mpr (by omega : m < m.succ + d)]
    rw [hmul, ih (by omega)]

variable (R) in
/-- The **integral infinite `q`-Pochhammer product** `∏_{i ≥ 0} (1 - q ^ i t)` in `(R⟦X⟧)⟦X⟧`,
constructed from the `q`-adically stabilized coefficients of the finite products
`qPochhammer X (C X) N`. -/
noncomputable def integralQPochhammer : (R⟦X⟧)⟦X⟧ :=
  PowerSeries.mk fun k ↦ PowerSeries.mk fun m ↦
    coeff m (coeff k (qPochhammer (X : (R⟦X⟧)⟦X⟧) (C (X : R⟦X⟧)) (m + 1)))

/-- **Polynomial-product projection equation**: for every `N > m`, the `[q ^ m t ^ k]` coefficient
of `integralQPochhammer R` equals the `q ^ m` coefficient of the `k`-th polynomial coefficient of
`qPochhammer Polynomial.X (Polynomial.C X) N`. -/
theorem coeff_coeff_integralQPochhammer_eq_of_lt (m k : ℕ) {N : ℕ} (hN : m < N) :
    coeff m (coeff k (integralQPochhammer R)) =
      coeff m ((qPochhammer (Polynomial.X : (R⟦X⟧)[X]) (Polynomial.C (X : R⟦X⟧)) N).coeff k) := by
  have hcoe :
      ((qPochhammer (Polynomial.X : (R⟦X⟧)[X]) (Polynomial.C (X : R⟦X⟧)) N : (R⟦X⟧)[X]) :
          (R⟦X⟧)⟦X⟧) =
        qPochhammer (X : (R⟦X⟧)⟦X⟧) (C (X : R⟦X⟧)) N := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_qPochhammer]
    simp
  rw [← Polynomial.coeff_coe, hcoe, integralQPochhammer, coeff_mk, coeff_mk,
    coeff_coeff_qPochhammer_eq_of_lt m k hN]

/-- The constant coefficient of `TauCeti.integralQPochhammer R` is `1`. -/
@[simp] theorem constantCoeff_integralQPochhammer : constantCoeff (integralQPochhammer R) = 1 := by
  ext m
  rw [← coeff_zero_eq_constantCoeff_apply,
    coeff_coeff_integralQPochhammer_eq_of_lt m 0 (Nat.lt_succ_self m),
    Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_qPochhammer, Polynomial.eval_X,
    Polynomial.eval_C, qPochhammer_zero_left]

/-- **Shift identity** for the integral infinite `q`-Pochhammer product:
`(t; q)_∞ = (1 - t) (q t; q)_∞` in `(R⟦X⟧)⟦X⟧`. -/
theorem integralQPochhammer_eq_one_sub_X_mul_rescale :
    integralQPochhammer R = (1 - X) * rescale (X : R⟦X⟧) (integralQPochhammer R) := by
  have hqPoch (m k N : ℕ) (hN : m < N) :
      coeff m (coeff k (integralQPochhammer R)) =
        coeff m (coeff k (qPochhammer (X : (R⟦X⟧)⟦X⟧) (C (X : R⟦X⟧)) N)) := by
    rw [integralQPochhammer, coeff_mk, coeff_mk, coeff_coeff_qPochhammer_eq_of_lt m k hN]
  ext k m
  rw [hqPoch m k (m + 2) (by omega),
    qPochhammer_succ' (X : (R⟦X⟧)⟦X⟧) (C (X : R⟦X⟧)) (m + 1)]
  have hres : qPochhammer ((X : (R⟦X⟧)⟦X⟧) * C (X : R⟦X⟧)) (C (X : R⟦X⟧)) (m + 1) =
      rescale (X : R⟦X⟧) (qPochhammer (X : (R⟦X⟧)⟦X⟧) (C (X : R⟦X⟧)) (m + 1)) := by
    rw [map_qPochhammer, rescale_X, rescale_C, mul_comm]
  rw [hres]
  rcases k with _ | k
  · simp [coeff_zero_eq_constantCoeff_apply, map_qPochhammer]
  · simp only [sub_mul, one_mul, map_sub, coeff_succ_X_mul, coeff_rescale, coeff_X_pow_mul']
    congr 1 <;> split_ifs with h
    · exact (hqPoch (m - (k + 1)) (k + 1) (m + 1) (by omega)).symm
    · rfl
    · exact (hqPoch (m - k) k (m + 1) (by omega)).symm
    · rfl

/-- The `q`-adically stabilized integral product `integralQPochhammer R` equals the formal series
`qPochhammerSeries X` in `(R⟦X⟧)⟦X⟧`. -/
theorem integralQPochhammer_eq_qPochhammerSeries :
    integralQPochhammer R = qPochhammerSeries (X : R⟦X⟧) :=
  (eq_qPochhammerSeries_iff (isUnit_one_sub_X_pow_succ (R := R))).mpr
    ⟨integralQPochhammer_eq_one_sub_X_mul_rescale, constantCoeff_integralQPochhammer⟩

/-- **Euler's reciprocal identity** for the integral infinite `q`-Pochhammer product in
`(R⟦X⟧)⟦X⟧`. -/
theorem integralQPochhammer_mul_qPochhammerInvSeries :
    integralQPochhammer R * qPochhammerInvSeries (X : R⟦X⟧) = 1 := by
  rw [integralQPochhammer_eq_qPochhammerSeries]
  exact qPochhammerSeries_mul_qPochhammerInvSeries (isUnit_one_sub_X_pow_succ (R := R))

/-- Base change of coefficients for `integralQPochhammer`. -/
theorem map_integralQPochhammer (φ : R →+* S) :
    map (map φ) (integralQPochhammer R) = integralQPochhammer S := by
  rw [integralQPochhammer_eq_qPochhammerSeries, integralQPochhammer_eq_qPochhammerSeries,
    map_qPochhammerSeries _ (isUnit_one_sub_X_pow_succ (R := R))]
  ext n
  simp

/-- Mapping `integralQPochhammer R` into Laurent-series coefficients `(R⸨X⸩)⟦X⟧` identifies it with
`qPochhammerSeries (single 1 1)`. -/
theorem map_ofPowerSeries_integralQPochhammer :
    map (HahnSeries.ofPowerSeries ℤ R) (integralQPochhammer R) =
      qPochhammerSeries (HahnSeries.single (1 : ℤ) (1 : R)) := by
  rw [integralQPochhammer_eq_qPochhammerSeries,
    map_qPochhammerSeries _ (isUnit_one_sub_X_pow_succ (R := R)), HahnSeries.ofPowerSeries_X]

/-- For every `m`, the `[q ^ m t]` coefficient of `integralQPochhammer R` is `-1`. -/
theorem coeff_coeff_one_integralQPochhammer (m : ℕ) :
    coeff m (coeff 1 (integralQPochhammer R)) = -1 := by
  have h (k : ℕ) := congrArg (fun f ↦ coeff k (coeff 1 f))
    (integralQPochhammer_eq_one_sub_X_mul_rescale (R := R))
  simp only [sub_mul, one_mul, map_sub, coeff_succ_X_mul, coeff_rescale, pow_one,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_integralQPochhammer, pow_zero, one_mul] at h
  induction m with
  | zero => simpa [coeff_zero_X_mul] using h 0
  | succ m ih => rw [← ih]; simpa [coeff_succ_X_mul] using h (m + 1)

/-- The `[q ^ 0 t ^ 2]` coefficient of `integralQPochhammer R` is `0`. -/
theorem coeff_zero_coeff_two_integralQPochhammer :
    coeff 0 (coeff 2 (integralQPochhammer R)) = 0 := by
  rw [coeff_coeff_integralQPochhammer_eq_of_lt 0 2 zero_lt_one, qPochhammer_one]
  simp [Polynomial.coeff_X, Polynomial.coeff_one]

/-- The `[q ^ 1 t ^ 2]` coefficient of `integralQPochhammer R` is `1`. -/
theorem coeff_one_coeff_two_integralQPochhammer :
    coeff 1 (coeff 2 (integralQPochhammer R)) = 1 := by
  have h2 : qPochhammer (Polynomial.X : (R⟦X⟧)[X]) (Polynomial.C (X : R⟦X⟧)) 2 =
      1 - Polynomial.X - Polynomial.X * Polynomial.C (X : R⟦X⟧) +
        Polynomial.X * (Polynomial.X * Polynomial.C (X : R⟦X⟧)) := by
    rw [qPochhammer_succ, qPochhammer_one]; ring
  rw [coeff_coeff_integralQPochhammer_eq_of_lt 1 2 (N := 2) (by omega), h2]
  simp [Polynomial.coeff_X, Polynomial.coeff_one, coeff_X]

end IntegralPochhammer

end TauCeti
