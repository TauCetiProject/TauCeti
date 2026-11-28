/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Exponential power series of divided powers

This file records basic properties of Mathlib's divided power exponential series
`DividedPowers.exp hI x = ∑ n, hI.dpow n x * X ^ n`, including its coefficients, constant
coefficient, behavior at `0` and finite sums, and interaction with `PowerSeries.rescale` and
`PowerSeries.map`.

## Main results

* `DividedPowers.coeff_exp`: the `n`-th coefficient of `hI.exp x` is `hI.dpow n x`.
* `DividedPowers.constantCoeff_exp`: `hI.exp x` has constant coefficient `1` for `x ∈ I`.
* `DividedPowers.exp_zero`: `hI.exp 0 = 1`.
* `DividedPowers.exp_sum`: `hI.exp (∑ i ∈ s, x i) = ∏ i ∈ s, hI.exp (x i)` for `x i ∈ I`.
* `DividedPowers.rescale_exp`: `PowerSeries.rescale a (hI.exp x) = hI.exp (a * x)` for `x ∈ I`.
* `DividedPowers.map_mul_dpow`: mapped divided-power multiplication identity.
* `DividedPowers.coeff_rescale_map_exp` and `DividedPowers.constantCoeff_rescale_map_exp`: the
  `n`-th coefficient and constant coefficient of
  `PowerSeries.rescale b (PowerSeries.map f (hI.exp x))`.
* `DividedPowers.rescale_map_exp_add` and `DividedPowers.rescale_map_exp_sum`: multiplicativity of
  `b ↦ PowerSeries.rescale b (PowerSeries.map f (hI.exp x))` under addition and finite sums.
-/

public section

open Finset

namespace DividedPowers

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A}

/-- The `n`-th coefficient of `hI.exp x` is `hI.dpow n x`. -/
@[simp]
theorem coeff_exp (hI : DividedPowers I) (n : ℕ) (x : A) :
    PowerSeries.coeff n (hI.exp x) = hI.dpow n x := by
  rw [DividedPowers.exp, PowerSeries.coeff_mk]

/-- For `x ∈ I`, the exponential series `hI.exp x` has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_exp (hI : DividedPowers I) {x : A} (hx : x ∈ I) :
    PowerSeries.constantCoeff (hI.exp x) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_exp, hI.dpow_zero hx]

/-- The divided power exponential series of `0` is `1`. -/
@[simp]
theorem exp_zero (hI : DividedPowers I) : hI.exp 0 = 1 := by
  ext n
  cases n with
  | zero => simp [hI.dpow_zero I.zero_mem]
  | succ n => simp [hI.dpow_eval_zero (Nat.succ_ne_zero n)]

/-- On elements of `I`, `DividedPowers.exp` turns finite sums into finite products. -/
theorem exp_sum {ι : Type*} (hI : DividedPowers I) (s : Finset ι) {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) :
    hI.exp (∑ i ∈ s, x i) = ∏ i ∈ s, hI.exp (x i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi,
      hI.exp_add (hx i (mem_insert_self i s))
        (Submodule.sum_mem _ fun k hk ↦ hx k (mem_insert_of_mem hk)),
      ih fun k hk ↦ hx k (mem_insert_of_mem hk)]

/-- Rescaling the variable in `hI.exp x` by `a` corresponds to multiplying `x` by `a`. -/
theorem rescale_exp (hI : DividedPowers I) (a : A) {x : A} (hx : x ∈ I) :
    PowerSeries.rescale a (hI.exp x) = hI.exp (a * x) := by
  ext n
  simp [PowerSeries.coeff_rescale, hI.dpow_mul hx]

/-- A ring homomorphism carries the divided-power multiplication identity
`f (hI.dpow m x) * f (hI.dpow n x) = ((m + n).choose m : B) * f (hI.dpow (m + n) x)`. -/
theorem map_mul_dpow {F : Type*} [FunLike F A B] [RingHomClass F A B]
    (hI : DividedPowers I) (f : F) {x : A} (hx : x ∈ I) (m n : ℕ) :
    f (hI.dpow m x) * f (hI.dpow n x) = ((m + n).choose m : B) * f (hI.dpow (m + n) x) := by
  rw [← map_mul, hI.mul_dpow hx, map_mul, map_natCast]

/-- Coefficient formula for a rescaled mapped divided-power exponential series. -/
theorem coeff_rescale_map_exp (hI : DividedPowers I) (f : A →+* B)
    (b : B) (n : ℕ) (x : A) :
    PowerSeries.coeff n (PowerSeries.rescale b (PowerSeries.map f (hI.exp x))) =
      b ^ n * f (hI.dpow n x) := by
  simp [PowerSeries.coeff_rescale, PowerSeries.coeff_map]

/-- For `x ∈ I`, the rescaled mapped exponential series has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_rescale_map_exp (hI : DividedPowers I) (f : A →+* B)
    (b : B) {x : A} (hx : x ∈ I) :
    PowerSeries.constantCoeff (PowerSeries.rescale b (PowerSeries.map f (hI.exp x))) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_rescale_map_exp, pow_zero, one_mul,
    hI.dpow_zero hx, map_one]

/-- Rescaling a mapped divided-power exponential series turns addition in the scaling parameter into
multiplication of power series. -/
theorem rescale_map_exp_add (hI : DividedPowers I) (f : A →+* B)
    (b₁ b₂ : B) {x : A} (hx : x ∈ I) :
    PowerSeries.rescale (b₁ + b₂) (PowerSeries.map f (hI.exp x)) =
      PowerSeries.rescale b₁ (PowerSeries.map f (hI.exp x)) *
        PowerSeries.rescale b₂ (PowerSeries.map f (hI.exp x)) := by
  ext n
  rw [coeff_rescale_map_exp, PowerSeries.coeff_mul, (Commute.all b₁ b₂).add_pow', sum_mul]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [← mem_antidiagonal.mp hk, nsmul_eq_mul, coeff_rescale_map_exp, coeff_rescale_map_exp]
  have hmul := map_mul_dpow hI f hx k.1 k.2
  calc ((k.1 + k.2).choose k.1 : B) * (b₁ ^ k.1 * b₂ ^ k.2) * f (hI.dpow (k.1 + k.2) x)
      = b₁ ^ k.1 * b₂ ^ k.2 * (((k.1 + k.2).choose k.1 : B) * f (hI.dpow (k.1 + k.2) x)) := by
        ring
    _ = b₁ ^ k.1 * b₂ ^ k.2 * (f (hI.dpow k.1 x) * f (hI.dpow k.2 x)) := by
        rw [← hmul]
    _ = b₁ ^ k.1 * f (hI.dpow k.1 x) * (b₂ ^ k.2 * f (hI.dpow k.2 x)) := by ring

/-- Rescaling a mapped divided-power exponential series turns finite sums in the scaling parameter
into finite products of power series. -/
theorem rescale_map_exp_sum {κ : Type*} (hI : DividedPowers I) (f : A →+* B)
    (t : Finset κ) (c : κ → B) {x : A} (hx : x ∈ I) :
    PowerSeries.rescale (∑ j ∈ t, c j) (PowerSeries.map f (hI.exp x)) =
      ∏ j ∈ t, PowerSeries.rescale (c j) (PowerSeries.map f (hI.exp x)) := by
  classical
  induction t using Finset.induction with
  | empty =>
    rw [sum_empty, prod_empty, PowerSeries.rescale_zero_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_exp hI hx, map_one, map_one]
  | insert j t hj ih =>
    rw [sum_insert hj, prod_insert hj, rescale_map_exp_add hI f _ _ hx, ih]

end DividedPowers
