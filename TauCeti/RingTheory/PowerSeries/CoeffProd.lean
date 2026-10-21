/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Coefficients of finite products of power series

A power series with vanishing constant coefficient is a multiple of `X`, so a product of `n` such
series is a multiple of `X ^ n`, and its coefficient in degree `n` is the product of the linear
coefficients of the factors. This file records that computation, with an extra factor `g` in
front whose constant coefficient comes along:

`coeff |s| (g * ∏_{i ∈ s} f i) = g(0) * ∏_{i ∈ s} f i'(0)`

whenever every `f i` has zero constant coefficient. It is the "leading term" extraction behind
limit arguments such as the Weyl dimension formula, where a product of `|Φ⁺|` factors each of
order one is divided by another such product.

Factors congruent to `1` modulo `X ^ (n + 1)` do not change the coefficient of degree `n`.
This also gives a finite-cutoff formula for products with many such factors.

## Main results

* `PowerSeries.coeff_card_mul_prod_of_constantCoeff_eq_zero`: the coefficient of
  `g * ∏_{i ∈ s} f i` in degree `|s|` is `constantCoeff g * ∏_{i ∈ s} coeff 1 (f i)` when each
  `f i` has zero constant coefficient.
* `PowerSeries.coeff_prod_eq_coeff_prod_of_X_pow_dvd_sub_one`: factors congruent to `1` modulo
  `X ^ (n + 1)` do not affect the `n`-th coefficient of a finite product.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommSemiring R] {ι : Type*}

/-- **The lowest coefficient of a product of power series without constant term.** If each
`f i`, `i ∈ s`, has zero constant coefficient, then `g * ∏_{i ∈ s} f i` has order at least `|s|`,
and its coefficient in degree `|s|` is the constant coefficient of `g` times the product of the
linear coefficients of the `f i`. -/
theorem coeff_card_mul_prod_of_constantCoeff_eq_zero (s : Finset ι) {f : ι → R⟦X⟧}
    (hf : ∀ i ∈ s, constantCoeff (f i) = 0) (g : R⟦X⟧) :
    coeff s.card (g * ∏ i ∈ s, f i) = constantCoeff g * ∏ i ∈ s, coeff 1 (f i) := by
  classical
  induction s using Finset.induction_on generalizing g with
  | empty => simp
  | insert a s ha ih =>
    -- The new factor is `f a = X * q`, so its linear coefficient is the constant coefficient of
    -- `q`, and the whole product has one factor of `X` in front, which lowers the degree by one.
    obtain ⟨q, hq⟩ := X_dvd_iff.mpr (hf a (Finset.mem_insert_self a s))
    have h1 : coeff 1 (f a) = constantCoeff q := by
      rw [hq, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
    have hX : g * ∏ i ∈ insert a s, f i = X * (g * q * ∏ i ∈ s, f i) := by
      rw [Finset.prod_insert ha, hq]; ring
    rw [hX, Finset.card_insert_of_notMem ha, coeff_succ_X_mul,
      ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)) (g * q), Finset.prod_insert ha, h1,
      map_mul]
    ring

section CommRing

variable {R : Type*} [CommRing R] {ι : Type*}

open Finset

/-- **Finite cutoff.** Factors congruent to `1` modulo `X ^ (n + 1)` do not change the `n`-th
coefficient of a finite product. -/
theorem coeff_prod_eq_coeff_prod_of_X_pow_dvd_sub_one [DecidableEq ι] {s t : Finset ι}
    (hts : t ⊆ s) {g : ι → R⟦X⟧} {n : ℕ} (h : ∀ i ∈ s \ t, X ^ (n + 1) ∣ g i - 1) :
    coeff n (∏ i ∈ s, g i) = coeff n (∏ i ∈ t, g i) := by
  have hdvd : X ^ (n + 1) ∣ ∏ i ∈ s \ t, g i - 1 := by
    refine prod_induction g (fun a ↦ X ^ (n + 1) ∣ a - 1) (fun a b ha hb ↦ ?_) (by simp) h
    have := dvd_add (dvd_mul_of_dvd_right hb a) ha
    rwa [mul_sub_one, sub_add_sub_cancel] at this
  obtain ⟨q, hq⟩ := hdvd
  rw [← prod_sdiff hts, sub_eq_iff_eq_add.1 hq, add_mul, one_mul, map_add, mul_assoc,
    coeff_X_pow_mul']
  simp

end CommRing

end PowerSeries
