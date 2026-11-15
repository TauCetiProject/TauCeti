/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

import TauCeti.RingTheory.Polynomial.Hermite.Derivative

/-!
# Rotational addition theorem for probabilists' Hermite polynomials

This file proves Runge's rotational addition identity for Mathlib's probabilists' Hermite
polynomials `Polynomial.hermite : ℕ → ℤ[X]` over arbitrary commutative rings, without any
characteristic-zero or invertibility assumptions.

## Main results

* `TauCeti.hermite_aeval_mul_add_mul_of_sq_add_sq_eq_one` and
  `TauCeti.hermite_aeval_mul_sub_mul_of_sq_add_sq_eq_one`: Runge's rotational addition theorem
  (DLMF 18.18.12), `Heₙ(a x + b y) = ∑_{m=0}^n C(n, m) a^{n-m} b^m He_{n-m}(x) He_m(y)` (and its
  subtraction form) whenever `a ^ 2 + b ^ 2 = 1`.

## Proof outline

Using `Polynomial.mul_hermite_aeval`, we show that the bivariate binomial Hermite sum satisfies the
three-term recurrence `(a x + b y) Q_n = Q_{n+1} + n (a^2 + b^2) Q_{n-1}`. When `a ^ 2 + b ^ 2 = 1`,
this matches the recurrence for `Heₙ(a x + b y)`, and two-step induction on `n` gives equality over
every commutative ring.

## References

* C. Runge, *Über eine besondere Art von Integralgleichungen*, Math. Ann. **75** (1914), 130–132.
* A. Erdélyi et al., *Higher Transcendental Functions*, Vol. II, §10.13.
* NIST Digital Library of Mathematical Functions, [18.18.12](https://dlmf.nist.gov/18.18#E12),
  after rescaling from the physicists' `Hₙ` to the probabilists' `Heₙ`.
-/

public section

namespace TauCeti

open Polynomial

/-- The bivariate binomial sum `∑_{m=0}^n C(n, m) a^{n-m} b^m He_{n-m}(x) He_m(y)`. -/
private noncomputable def binomHermiteSum {R : Type*} [CommRing R] (a b x y : R) (n : ℕ) : R :=
  ∑ m ∈ Finset.range (n + 1),
    n.choose m • (a ^ (n - m) * b ^ m * aeval x (hermite (n - m)) * aeval y (hermite m))

private lemma binomHermiteSum_zero {R : Type*} [CommRing R] (a b x y : R) :
    binomHermiteSum a b x y 0 = 1 := by
  simp [binomHermiteSum]

/-- Pascal combination of the raising terms in `(a x + b y) * binomHermiteSum a b x y n`. -/
private lemma binomHermiteSum_raise {R : Type*} [CommRing R] (a b x y : R) (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1),
        (n.choose m : R) * (a ^ (n + 1 - m) * b ^ m *
          aeval x (hermite (n + 1 - m)) * aeval y (hermite m))) +
      (∑ m ∈ Finset.range (n + 1),
        (n.choose m : R) * (a ^ (n - m) * b ^ (m + 1) *
          aeval x (hermite (n - m)) * aeval y (hermite (m + 1)))) =
      binomHermiteSum a b x y (n + 1) := by
  unfold binomHermiteSum
  simp_rw [nsmul_eq_mul]
  rw [Finset.sum_range_succ' _ n, Finset.sum_range_succ _ n, Finset.sum_range_succ' _ (n + 1),
    Finset.sum_range_succ _ n]
  have hmid :
      (∑ k ∈ Finset.range n,
          (n.choose (k + 1) : R) * (a ^ (n + 1 - (k + 1)) * b ^ (k + 1) *
            aeval x (hermite (n + 1 - (k + 1))) * aeval y (hermite (k + 1)))) +
        (∑ k ∈ Finset.range n,
          (n.choose k : R) * (a ^ (n - k) * b ^ (k + 1) *
            aeval x (hermite (n - k)) * aeval y (hermite (k + 1)))) =
      ∑ k ∈ Finset.range n,
        ((n + 1).choose (k + 1) : R) * (a ^ (n + 1 - (k + 1)) * b ^ (k + 1) *
          aeval x (hermite (n + 1 - (k + 1))) * aeval y (hermite (k + 1))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.succ_sub_succ_eq_sub, Nat.choose_succ_succ' n k, Nat.cast_add, add_mul]
    ring
  simp only [Nat.choose_zero_right, Nat.choose_self, Nat.sub_zero, Nat.sub_self, pow_zero,
    hermite_zero, map_one, Nat.cast_one, one_mul, mul_one]
  rw [add_right_comm _ (a ^ (n + 1) * aeval x (hermite (n + 1))), ← add_assoc, hmid]

/-- Lowering `x`-terms in `(a x) * binomHermiteSum a b x y n`. -/
private lemma binomHermiteSum_lower_left {R : Type*} [CommRing R] (a b x y : R) (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1),
        (n.choose m : R) * ((n - m : ℕ) * a ^ 2 *
          (a ^ (n - 1 - m) * b ^ m * aeval x (hermite (n - 1 - m)) * aeval y (hermite m)))) =
      (n : R) * a ^ 2 * binomHermiteSum a b x y (n - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    unfold binomHermiteSum
    simp_rw [nsmul_eq_mul]
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hbinom : (n + 1).choose m * (n + 1 - m) = n.choose m * (n + 1) :=
      (Nat.choose_mul_succ_eq n m).symm
    calc
      ((n + 1).choose m : R) * ((n + 1 - m : ℕ) * a ^ 2 *
          (a ^ (n - m) * b ^ m * aeval x (hermite (n - m)) * aeval y (hermite m))) =
          ((((n + 1).choose m * (n + 1 - m) : ℕ) : R)) * (a ^ 2 *
            (a ^ (n - m) * b ^ m * aeval x (hermite (n - m)) * aeval y (hermite m))) := by
        push_cast; ring
      _ = _ := by
        rw [hbinom]
        push_cast
        ring

/-- Lowering `y`-terms in `(b y) * binomHermiteSum a b x y n`. -/
private lemma binomHermiteSum_lower_right {R : Type*} [CommRing R] (a b x y : R) (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1),
        (n.choose m : R) * ((m : R) * b ^ 2 *
          (a ^ (n - m) * b ^ (m - 1) * aeval x (hermite (n - m)) * aeval y (hermite (m - 1))))) =
      (n : R) * b ^ 2 * binomHermiteSum a b x y (n - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    unfold binomHermiteSum
    simp_rw [nsmul_eq_mul]
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hbinom : (n + 1).choose (m + 1) * (m + 1) = (n + 1) * n.choose m :=
      (Nat.add_one_mul_choose_eq n m).symm
    simp only [Nat.succ_sub_succ_eq_sub]
    calc
      ((n + 1).choose (m + 1) : R) * (((m + 1 : ℕ) : R) * b ^ 2 *
          (a ^ (n - m) * b ^ m * aeval x (hermite (n - m)) * aeval y (hermite m))) =
          ((((n + 1).choose (m + 1) * (m + 1) : ℕ) : R)) * (b ^ 2 *
            (a ^ (n - m) * b ^ m * aeval x (hermite (n - m)) * aeval y (hermite m))) := by
        push_cast; ring
      _ = _ := by
        rw [hbinom]
        push_cast
        ring

/-- Four-way expansion of `(a x + b y) * binomHermiteSum a b x y n` via the raising and lowering
terms of `mul_hermite_aeval`. -/
private lemma binomHermiteSum_mul_expand {R : Type*} [CommRing R] (a b x y : R) (n : ℕ) :
    (a * x + b * y) * binomHermiteSum a b x y n =
      ((∑ m ∈ Finset.range (n + 1),
          (n.choose m : R) * (a ^ (n + 1 - m) * b ^ m *
            aeval x (hermite (n + 1 - m)) * aeval y (hermite m))) +
        (∑ m ∈ Finset.range (n + 1),
          (n.choose m : R) * (a ^ (n - m) * b ^ (m + 1) *
            aeval x (hermite (n - m)) * aeval y (hermite (m + 1))))) +
      (∑ m ∈ Finset.range (n + 1),
          (n.choose m : R) * ((n - m : ℕ) * a ^ 2 *
            (a ^ (n - 1 - m) * b ^ m * aeval x (hermite (n - 1 - m)) *
              aeval y (hermite m)))) +
      (∑ m ∈ Finset.range (n + 1),
          (n.choose m : R) * ((m : R) * b ^ 2 *
            (a ^ (n - m) * b ^ (m - 1) * aeval x (hermite (n - m)) *
              aeval y (hermite (m - 1))))) := by
  unfold binomHermiteSum
  simp_rw [nsmul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm_le : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hx := mul_hermite_aeval (n - m) x
  have hy := mul_hermite_aeval m y
  have hsub_x : n - m + 1 = n + 1 - m := by lia
  have hpow_a : a * a ^ (n - m) = a ^ (n + 1 - m) := by rw [← pow_succ', hsub_x]
  have hpow_a2 :
      ((n - m : ℕ) : R) * (a * a ^ (n - m)) =
        ((n - m : ℕ) : R) * (a ^ 2 * a ^ (n - 1 - m)) := by
    rcases eq_or_lt_of_le hm_le with rfl | hlt
    · simp
    · have hidx : n - m + 1 = 2 + (n - 1 - m) := by lia
      congr 1
      rw [← pow_succ', ← pow_add, hidx]
  have hpow_b2 : (m : R) * (b * b ^ m) = (m : R) * (b ^ 2 * b ^ (m - 1)) := by
    rcases m with _ | m
    · simp
    · congr 1
      rw [← pow_succ', ← pow_add, Nat.add_sub_cancel]
      ring
  calc
    (a * x + b * y) * ((n.choose m : R) * (a ^ (n - m) * b ^ m *
        aeval x (hermite (n - m)) * aeval y (hermite m))) =
        (n.choose m : R) * ((a * a ^ (n - m)) * b ^ m *
          (x * aeval x (hermite (n - m))) * aeval y (hermite m)) +
        (n.choose m : R) * (a ^ (n - m) * (b * b ^ m) *
          aeval x (hermite (n - m)) * (y * aeval y (hermite m))) := by ring
    _ = (n.choose m : R) * ((a * a ^ (n - m)) * b ^ m *
          aeval x (hermite (n + 1 - m)) * aeval y (hermite m)) +
        (n.choose m : R) * (a ^ (n - m) * (b * b ^ m) *
          aeval x (hermite (n - m)) * aeval y (hermite (m + 1))) +
        (n.choose m : R) * ((((n - m : ℕ) : R) * (a * a ^ (n - m))) *
          (b ^ m * aeval x (hermite (n - 1 - m)) * aeval y (hermite m))) +
        (n.choose m : R) * (((m : R) * (b * b ^ m)) *
          (a ^ (n - m) * aeval x (hermite (n - m)) * aeval y (hermite (m - 1)))) := by
      rw [hx, hy, hsub_x, Nat.sub_right_comm n m 1]
      ring
    _ = _ := by
      rw [hpow_a2, hpow_b2, hpow_a, pow_succ' b]
      ring

/-- Three-term recurrence for `binomHermiteSum` at variance `a^2 + b^2`: for all `a, b, x, y` in
any commutative ring,
`(a x + b y) Q_n = Q_{n+1} + n (a^2 + b^2) Q_{n-1}`. -/
private lemma mul_binomHermiteSum {R : Type*} [CommRing R] (a b x y : R) (n : ℕ) :
    (a * x + b * y) * binomHermiteSum a b x y n =
      binomHermiteSum a b x y (n + 1) +
        (n : R) * (a ^ 2 + b ^ 2) * binomHermiteSum a b x y (n - 1) := by
  rw [binomHermiteSum_mul_expand, binomHermiteSum_raise, binomHermiteSum_lower_left,
    binomHermiteSum_lower_right]
  ring

/-- **Runge's rotational addition theorem** (Runge 1914; DLMF 18.18.12) for the probabilists'
Hermite polynomials: in any commutative ring `R`, whenever `a^2 + b^2 = 1`,
`Heₙ(a x + b y) = ∑_{m=0}^n C(n, m) a^{n-m} b^m He_{n-m}(x) He_m(y)`. -/
theorem hermite_aeval_mul_add_mul_of_sq_add_sq_eq_one {R : Type*} [CommRing R] (n : ℕ)
    {a b : R} (hab : a ^ 2 + b ^ 2 = 1) (x y : R) :
    aeval (a * x + b * y) (hermite n) =
      ∑ m ∈ Finset.range (n + 1),
        n.choose m • (a ^ (n - m) * b ^ m * aeval x (hermite (n - m)) * aeval y (hermite m)) := by
  change aeval (a * x + b * y) (hermite n) = binomHermiteSum a b x y n
  induction n using Nat.twoStepInduction with
  | zero => simp [binomHermiteSum_zero]
  | one =>
    have h1 := mul_binomHermiteSum a b x y 0
    simp only [binomHermiteSum_zero, mul_one, Nat.cast_zero, zero_mul, add_zero] at h1
    rw [hermite_one, aeval_X, ← h1]
  | more n ih0 ih1 =>
    have hP := mul_hermite_aeval (n + 1) (a * x + b * y)
    have hQ := mul_binomHermiteSum a b x y (n + 1)
    rw [hab, mul_one, Nat.add_sub_cancel] at hQ
    rw [Nat.add_sub_cancel, ih0, ih1] at hP
    exact add_right_cancel (hP.symm.trans hQ)

/-- Subtraction form of **Runge's rotational addition theorem**: in any commutative ring `R`,
whenever `a^2 + b^2 = 1`,
`Heₙ(a x - b y) = ∑_{m=0}^n (-1)^m C(n, m) a^{n-m} b^m He_{n-m}(x) He_m(y)`. -/
theorem hermite_aeval_mul_sub_mul_of_sq_add_sq_eq_one {R : Type*} [CommRing R] (n : ℕ)
    {a b : R} (hab : a ^ 2 + b ^ 2 = 1) (x y : R) :
    aeval (a * x - b * y) (hermite n) =
      ∑ m ∈ Finset.range (n + 1),
        (-1) ^ m *
          (n.choose m •
            (a ^ (n - m) * b ^ m * aeval x (hermite (n - m)) * aeval y (hermite m))) := by
  have hab' : a ^ 2 + (-b) ^ 2 = 1 := by simpa [neg_sq] using hab
  have hsub : a * x - b * y = a * x + (-b) * y := by ring
  rw [hsub, hermite_aeval_mul_add_mul_of_sq_add_sq_eq_one n hab' x y]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [neg_pow, nsmul_eq_mul, nsmul_eq_mul]
  ring

end TauCeti
