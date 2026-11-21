/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.NonnegCombination
import Mathlib.Data.List.GetD

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

* `TauCeti.LSeries.threeFourOneCoeff` is the coefficient sequence `3, 4, 1, 0, 0, …`.
* `TauCeti.LSeries.isNonnegativeTrigonometricCombination_threeFourOne` packages these coefficients
  at the frequencies `k ∈ Finset.range 3`.
* `TauCeti.LSeries.threeFourOne_re_neg_log_one_sub_nonneg` is the corresponding inequality for
  logarithms of Euler factors in the open unit disk.

## Provenance

The `3-4-1` argument is classical; see Davenport, *Multiplicative Number Theory*, Chapter 4.
The logarithmic form specializes the private lemma `DirichletCharacter.re_log_comb_nonneg'` in
Mathlib's `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, by Michael Stoll and David Loeffler,
through `TauCeti.sum_re_neg_log_one_sub_nonneg`.
-/

public section

namespace TauCeti.LSeries

open Complex

noncomputable section

/-! ### The concrete 3-4-1 combination -/

/-- The `3-4-1` coefficients indexed by frequency: `3`, `4`, and `1` at `0`, `1`, and `2`, and
`0` at every larger frequency. -/
def threeFourOneCoeff (k : ℕ) : ℝ := ([3, 4, 1] : List ℝ).getD k 0

/-- The `3-4-1` trigonometric expression evaluated at a complex phase. -/
def threeFourOneCombination (z : ℂ) : ℝ := 3 + 4 * z.re + (z ^ 2).re

/-- The `3-4-1` coefficient at frequency `0` is `3`. -/
@[simp] theorem threeFourOneCoeff_zero : threeFourOneCoeff 0 = 3 := (rfl)

/-- The `3-4-1` coefficient at frequency `1` is `4`. -/
@[simp] theorem threeFourOneCoeff_one : threeFourOneCoeff 1 = 4 := (rfl)

/-- The `3-4-1` coefficient at frequency `2` is `1`. -/
@[simp] theorem threeFourOneCoeff_two : threeFourOneCoeff 2 = 1 := (rfl)

/-- The `3-4-1` coefficients vanish above frequency `2`. -/
@[simp] theorem threeFourOneCoeff_eq_zero {k : ℕ} (hk : 2 < k) : threeFourOneCoeff k = 0 := by
  unfold threeFourOneCoeff
  exact List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega)

/-- The defining formula for `threeFourOneCombination`. -/
theorem threeFourOneCombination_def (z : ℂ) :
    threeFourOneCombination z = 3 + 4 * z.re + (z ^ 2).re := (rfl)

/-- The abstract finite combination with the `3-4-1` coefficients is the usual concrete
expression. -/
@[simp]
theorem trigonometricCombination_threeFourOne (z : ℂ) :
    trigonometricCombination (Finset.range 3) (fun k ↦ (threeFourOneCoeff k : ℂ)) id z =
      threeFourOneCombination z := by
  simp [trigonometricCombination_def, threeFourOneCombination_def, Finset.sum_range_succ]

/-- On the unit circle the `3-4-1` expression is twice a square. -/
theorem threeFourOneCombination_eq_two_mul_sq {z : ℂ} (hz : ‖z‖ = 1) :
    threeFourOneCombination z = 2 * (z.re + 1) ^ 2 := by
  rw [threeFourOneCombination_def, pow_two, mul_re, ← sq, ← sq,
    ← Complex.sq_norm_sub_sq_re, hz]
  ring

/-- The `3-4-1` coefficients at the frequencies `0`, `1`, and `2` form a finite nonnegative
trigonometric combination. -/
theorem isNonnegativeTrigonometricCombination_threeFourOne :
    IsNonnegativeTrigonometricCombination (Finset.range 3) (fun k ↦ (threeFourOneCoeff k : ℂ))
      id := by
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
  simp [Finset.sum_range_succ] at h ⊢
  linarith

end

end TauCeti.LSeries
