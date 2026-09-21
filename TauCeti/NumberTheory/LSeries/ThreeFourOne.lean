/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.NonnegCombination

/-!
# The 3-4-1 positivity combination

This file packages the elementary positivity input in the classical `3-4-1` argument for
nonvanishing of Dirichlet series. For a phase `z` on the complex unit circle,

```text
3 + 4 Re(z) + Re(z²) = 2 (1 + Re(z))² ≥ 0.
```

The weights `3`, `4`, and `1` are nonnegative. We record their expression as a finite nonnegative
trigonometric combination and prove the corresponding inequality for logarithms of Euler factors.
These results contain no continuation, nonvanishing, or character-specific hypotheses; downstream
applications provide those analytic inputs separately.

## Main declarations

* `TauCeti.LSeries.isNonnegativeTrigonometricCombination_threeFourOne` packages the frequencies
  `0`, `1`, and `2` with weights `3`, `4`, and `1`.
* `TauCeti.LSeries.threeFourOne_re_neg_log_one_sub_nonneg` is the corresponding inequality for
  logarithms of Euler factors in the open unit disk.
* `TauCeti.LSeries.threeFourOne_re_neg_log_one_sub_div_cpow_nonneg` reads that inequality on the
  local factors of a Dirichlet series at a real base `x > 1`.

## Provenance

The `3-4-1` argument is classical; see Davenport, *Multiplicative Number Theory*, Chapter 4.
The logarithmic form specializes the private lemma `DirichletCharacter.re_log_comb_nonneg'` in
Mathlib's `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, by Michael Stoll and David Loeffler,
through `TauCeti.sum_re_neg_log_one_sub_nonneg`. The local-factor form below generalizes the
private lemma `DirichletCharacter.re_log_comb_nonneg` of the same file, which fixes the base to a
rational prime and the coefficient to a Dirichlet character value.
This is Layer 8.2 of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.
-/

public section

namespace TauCeti.LSeries

open Complex

noncomputable section

/-! ### The concrete 3-4-1 combination -/

/-- The three nonnegative weights `3`, `4`, and `1` in the `3-4-1` combination. -/
def threeFourOneWeight : Fin 3 → ℝ := ![3, 4, 1]

/-- The frequencies `0`, `1`, and `2` in the `3-4-1` combination. -/
def threeFourOneFrequency : Fin 3 → ℕ := ![0, 1, 2]

/-- The `3-4-1` trigonometric expression evaluated at a complex phase. -/
def threeFourOneCombination (z : ℂ) : ℝ := 3 + 4 * z.re + (z ^ 2).re

/-- The first `3-4-1` weight is `3`. -/
@[simp] theorem threeFourOneWeight_zero : threeFourOneWeight 0 = 3 := (rfl)

/-- The second `3-4-1` weight is `4`. -/
@[simp] theorem threeFourOneWeight_one : threeFourOneWeight 1 = 4 := (rfl)

/-- The third `3-4-1` weight is `1`. -/
@[simp] theorem threeFourOneWeight_two : threeFourOneWeight 2 = 1 := (rfl)

/-- The first `3-4-1` frequency is `0`. -/
@[simp] theorem threeFourOneFrequency_zero : threeFourOneFrequency 0 = 0 := (rfl)

/-- The second `3-4-1` frequency is `1`. -/
@[simp] theorem threeFourOneFrequency_one : threeFourOneFrequency 1 = 1 := (rfl)

/-- The third `3-4-1` frequency is `2`. -/
@[simp] theorem threeFourOneFrequency_two : threeFourOneFrequency 2 = 2 := (rfl)

/-- The defining formula for `threeFourOneCombination`. -/
theorem threeFourOneCombination_def (z : ℂ) :
    threeFourOneCombination z = 3 + 4 * z.re + (z ^ 2).re := (rfl)

/-- The abstract finite combination with `3-4-1` weights is the usual concrete expression. -/
@[simp]
theorem trigonometricCombination_threeFourOne (z : ℂ) :
    trigonometricCombination Finset.univ threeFourOneWeight threeFourOneFrequency z =
      threeFourOneCombination z := by
  rw [trigonometricCombination_def, threeFourOneCombination_def, Fin.sum_univ_three]
  simp only [threeFourOneWeight_zero, threeFourOneWeight_one, threeFourOneWeight_two,
    threeFourOneFrequency_zero, threeFourOneFrequency_one, threeFourOneFrequency_two,
    pow_zero, pow_one, one_re, mul_one, one_mul]

/-- On the unit circle the `3-4-1` expression is twice a square. -/
theorem threeFourOneCombination_eq_two_mul_sq {z : ℂ} (hz : ‖z‖ = 1) :
    threeFourOneCombination z = 2 * (z.re + 1) ^ 2 := by
  rw [threeFourOneCombination_def, pow_two, mul_re, ← sq, ← sq,
    ← Complex.sq_norm_sub_sq_re, hz]
  ring

/-- The weights and frequencies of the `3-4-1` expression form a finite nonnegative
trigonometric combination. -/
theorem isNonnegativeTrigonometricCombination_threeFourOne :
    IsNonnegativeTrigonometricCombination Finset.univ threeFourOneWeight
      threeFourOneFrequency := by
  intro z hz
  rw [trigonometricCombination_threeFourOne, threeFourOneCombination_eq_two_mul_sq hz]
  positivity

/-- The `3-4-1` expression is nonnegative on the closed complex unit disk. -/
theorem threeFourOneCombination_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ threeFourOneCombination z := by
  rw [← trigonometricCombination_threeFourOne]
  exact trigonometricCombination_nonneg_of_boundary
    isNonnegativeTrigonometricCombination_threeFourOne hz

/-! ### Euler-factor form -/

/-- The `3-4-1` inequality for logarithms of three Euler factors in the open unit disk. -/
theorem threeFourOne_re_neg_log_one_sub_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have h := sum_re_neg_log_one_sub_nonneg
    isNonnegativeTrigonometricCombination_threeFourOne ha₀ ha₁ hz
  simpa only [trigonometricCombination_def, Fin.sum_univ_three, threeFourOneWeight_zero,
    threeFourOneWeight_one, threeFourOneWeight_two, threeFourOneFrequency_zero,
    threeFourOneFrequency_one, threeFourOneFrequency_two, pow_zero, pow_one, mul_one,
    one_mul] using h

/-! ### Dirichlet local-factor form -/

/-- **The `3-4-1` inequality for the local factors of a Dirichlet series.** At a real base
`x > 1`, the three local ratios of the family `1, c, c ^ 2` read at the points `σ`, `σ + it` and
`σ + 2it` are `x ^ (-σ)` times the phases `1`, `z` and `z ^ 2`, where `z = c * x ^ (-it)` has
modulus at most one; so the `3-4-1` combination of their logarithms is nonnegative.

This is the shape in which an Euler product over the primes of a number field, or over the
rational primes, meets the inequality: `x` is the absolute norm of a prime and `c` is the value
there of a weight of modulus at most one. -/
theorem threeFourOne_re_neg_log_one_sub_div_cpow_nonneg {x : ℝ} (hx : 1 < x) {σ : ℝ}
    (hσ : 0 < σ) (t : ℝ) {c : ℂ} (hc : ‖c‖ ≤ 1) :
    0 ≤ 3 * (-log (1 - 1 / (x : ℂ) ^ (σ : ℂ))).re +
        4 * (-log (1 - c / (x : ℂ) ^ ((σ : ℂ) + I * t))).re +
        (-log (1 - c ^ 2 / (x : ℂ) ^ ((σ : ℂ) + 2 * I * t))).re := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hdiv (d w : ℂ) : d / (x : ℂ) ^ w = d * (x : ℂ) ^ (-w) := by
    rw [cpow_neg, div_eq_mul_inv]
  have hphase : ‖c * (x : ℂ) ^ (-(I * t))‖ ≤ 1 := by
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0]
    simpa using hc
  have hA : ((x ^ (-σ) : ℝ) : ℂ) = (x : ℂ) ^ (-(σ : ℂ)) := by
    rw [ofReal_cpow hx0.le, ofReal_neg]
  have hsq : ((x : ℂ) ^ (-(I * (t : ℂ)))) ^ 2 = (x : ℂ) ^ (-(2 * I * (t : ℂ))) := by
    rw [sq, ← cpow_add _ _ hxC]
    congr 1
    ring
  have h0 : 1 / (x : ℂ) ^ (σ : ℂ) = ((x ^ (-σ) : ℝ) : ℂ) := by
    rw [hA, hdiv, one_mul]
  have h1 : c / (x : ℂ) ^ ((σ : ℂ) + I * t) =
      ((x ^ (-σ) : ℝ) : ℂ) * (c * (x : ℂ) ^ (-(I * t))) := by
    rw [hA, hdiv, neg_add, cpow_add _ _ hxC]
    ring
  have h2 : c ^ 2 / (x : ℂ) ^ ((σ : ℂ) + 2 * I * t) =
      ((x ^ (-σ) : ℝ) : ℂ) * (c * (x : ℂ) ^ (-(I * t))) ^ 2 := by
    rw [hA, hdiv, neg_add, cpow_add _ _ hxC, mul_pow, hsq]
    ring
  rw [h0, h1, h2]
  exact threeFourOne_re_neg_log_one_sub_nonneg (Real.rpow_nonneg hx0.le _)
    (Real.rpow_lt_one_of_one_lt_of_neg hx (neg_neg_iff_pos.mpr hσ)) hphase

end

end TauCeti.LSeries
