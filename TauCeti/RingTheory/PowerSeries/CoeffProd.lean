/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.LinearCombination

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

The coefficient of degree one of any finite product is the sum, over the factors, of the linear
coefficient of that factor times the constant coefficients of the others.

Factors congruent to `1` modulo `X ^ (n + 1)` do not change the coefficient of degree `n`.
This also gives a finite-cutoff formula for products with many such factors.

Substituting `t = 1 - X` into `(1 - t ^ d) / (1 - t) = ∑_{j < d} t ^ j` gives a series with constant
coefficient `d` and linear coefficient `-d (d - 1) / 2`, which computes the linear coefficient of a
product of such factors.

## Main results

* `PowerSeries.coeff_card_mul_prod_of_constantCoeff_eq_zero`: the coefficient of
  `g * ∏_{i ∈ s} f i` in degree `|s|` is `constantCoeff g * ∏_{i ∈ s} coeff 1 (f i)` when each
  `f i` has zero constant coefficient.
* `PowerSeries.coeff_one_prod`: the linear coefficient of a finite product, a sum over the factors
  of the linear coefficient of one factor times the constant coefficients of the others.
* `PowerSeries.coeff_prod_eq_coeff_prod_of_X_pow_dvd_sub_one`: factors congruent to `1` modulo
  `X ^ (n + 1)` do not affect the `n`-th coefficient of a finite product.
* `PowerSeries.coeff_one_prod_sum_one_sub_X_pow_mul_two`: twice the linear coefficient of
  `∏_{i ∈ s} ∑_{j < dᵢ} (1 - X) ^ j` is `-(∏ dᵢ) ∑ (dᵢ - 1)`.
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

/-- **The linear coefficient of a finite product.** The coefficient of `X` in `∏_{i ∈ s} f i` is
the sum over `i ∈ s` of the linear coefficient of `f i` times the constant coefficients of the
other factors. -/
theorem coeff_one_prod [DecidableEq ι] (s : Finset ι) (f : ι → R⟦X⟧) :
    coeff 1 (∏ i ∈ s, f i) = ∑ i ∈ s, coeff 1 (f i) * ∏ j ∈ s.erase i, constantCoeff (f j) := by
  induction s using Finset.induction_on with
  | empty => simp [coeff_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, coeff_one_mul, ih, Finset.sum_insert ha, Finset.erase_insert ha,
      map_prod, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hi ha).symm,
      Finset.prod_insert fun h ↦ ha (Finset.mem_of_mem_erase h)]
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

/-- After the substitution `t = 1 - X`, the factor `(1 - t ^ d) / (1 - t) = ∑_{j < d} t ^ j` has
linear coefficient `-d (d - 1) / 2`, so the product of these factors has linear coefficient
`-(∏ dᵢ) ∑ (dᵢ - 1) / 2`. -/
theorem coeff_one_prod_sum_one_sub_X_pow_mul_two (s : Finset ι) (d : ι → ℕ) :
    coeff 1 (∏ i ∈ s, ∑ j ∈ range (d i), (1 - X : R⟦X⟧) ^ j) * 2 =
      -((∏ i ∈ s, (d i : R)) * ∑ i ∈ s, ((d i : R) - 1)) := by
  classical
  have hc (k : ℕ) : constantCoeff (∑ j ∈ range k, (1 - X : R⟦X⟧) ^ j) = k := by
    simp
  have hgauss (k : ℕ) : (∑ j ∈ range k, (j : R)) * 2 = k * (k - 1) := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, add_mul, ih]; push_cast; ring
  rw [coeff_one_prod, sum_mul, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun i hi ↦ ?_
  simp only [hc, map_sum, coeff_one_pow, map_sub, coeff_one, coeff_one_X, map_one,
    constantCoeff_X, sub_zero, one_pow, one_ne_zero, ite_false, zero_sub, mul_neg, mul_one,
    sum_neg_distrib]
  rw [← mul_prod_erase s (fun j ↦ (d j : R)) hi]
  linear_combination (-(∏ j ∈ s.erase i, (d j : R))) * hgauss (d i)

end CommRing

end PowerSeries
