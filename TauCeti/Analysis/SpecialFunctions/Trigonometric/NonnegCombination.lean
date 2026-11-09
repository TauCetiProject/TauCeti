/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.AbsMax

/-!
# Nonnegative trigonometric combinations

This file packages finite trigonometric combinations that are nonnegative on the complex unit
circle. It also transfers their pointwise nonnegativity to the closed unit disk and the Taylor
series of `-log (1 - z)`, giving a reusable logarithmic inequality.

## Main declarations

* `TauCeti.trigonometricCombination` is the real part of a finite weighted sum of powers.
* `TauCeti.IsNonnegativeTrigonometricCombination` asserts nonnegativity on the unit circle.
* `TauCeti.trigonometricCombination_nonneg_of_boundary` extends this nonnegativity to the closed
  unit disk.
* `TauCeti.sum_re_neg_log_one_sub_nonneg` transfers boundary nonnegativity to logarithms in the
  open unit disk.

## Provenance

The logarithmic transfer generalizes the private lemma `re_log_comb_nonneg'` in the
`DirichletCharacter` namespace of Mathlib's
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, due to Michael Stoll and David Loeffler, from
the fixed `3-4-1` weights to an arbitrary finite nonnegative combination.
-/

public section

namespace TauCeti

open Complex

noncomputable section

variable {ι : Type*}

/-- The real trigonometric combination with complex weights `c` and frequencies `m`, evaluated at
a complex phase `z`. On the unit circle `z = exp (θ * I)`, each term `(c i * z ^ m i).re` is a
linear combination of `cos (m i * θ)` and `sin (m i * θ)`. -/
def trigonometricCombination
    (s : Finset ι) (c : ι → ℂ) (m : ι → ℕ) (z : ℂ) : ℝ :=
  ∑ i ∈ s, (c i * z ^ m i).re

/-- The defining finite-sum formula for `trigonometricCombination`. -/
theorem trigonometricCombination_def (s : Finset ι) (c : ι → ℂ) (m : ι → ℕ) (z : ℂ) :
    trigonometricCombination s c m z = ∑ i ∈ s, (c i * z ^ m i).re := (rfl)

/-- The assertion that a finite trigonometric combination is nonnegative at every complex phase
on the unit circle. -/
abbrev IsNonnegativeTrigonometricCombination
    (s : Finset ι) (c : ι → ℂ) (m : ι → ℕ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ trigonometricCombination s c m z

variable {s : Finset ι} {c : ι → ℂ} {m : ι → ℕ}

/-- Nonnegativity of a trigonometric combination on the unit circle extends to the closed unit
disk. -/
theorem trigonometricCombination_nonneg_of_boundary
    (h : IsNonnegativeTrigonometricCombination s c m) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ trigonometricCombination s c m z := by
  -- Apply the maximum modulus principle on the unit disk to `exp (-∑ i ∈ s, c i * w ^ m i)`,
  -- whose norm is `Real.exp (-trigonometricCombination s c m w)`.
  let f : ℂ → ℂ := fun w ↦ exp (-∑ i ∈ s, c i * w ^ m i)
  have hf (w : ℂ) : ‖f w‖ ≤ 1 ↔ 0 ≤ trigonometricCombination s c m w := by
    simp [f, Complex.norm_exp, re_sum, trigonometricCombination_def]
  refine (hf z).1 <| Complex.norm_le_of_forall_mem_frontier_norm_le
    (Metric.isBounded_ball (x := 0) (r := 1))
    (by fun_prop : Differentiable ℂ f).diffContOnCl (fun w hw ↦ (hf w).2 (h w ?_)) ?_
  · rwa [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere_zero_iff_norm] at hw
  · rwa [closure_ball (0 : ℂ) one_ne_zero, mem_closedBall_zero_iff]

/-- Unit-circle nonnegativity of a trigonometric combination transfers to the Taylor series of
`-log (1 - w)` at the points `w = a * z ^ m i`, for `0 ≤ a < 1` and `z` in the closed unit
disk. -/
theorem sum_re_neg_log_one_sub_nonneg
    (h : IsNonnegativeTrigonometricCombination s c m)
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ ∑ i ∈ s, (c i * -log (1 - a * z ^ m i)).re := by
  have haz (i : ι) : ‖(a : ℂ) * z ^ m i‖ < 1 := by
    rw [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg ha₀]
    exact (mul_le_of_le_one_right ha₀ (pow_le_one₀ (norm_nonneg z) hz)).trans_lt ha₁
  have hsum : HasSum
      (fun n : ℕ ↦ ∑ i ∈ s, (c i * (((a : ℂ) * z ^ m i) ^ n / n)).re)
      (∑ i ∈ s, (c i * -log (1 - a * z ^ m i)).re) :=
    hasSum_sum fun i _ ↦ Complex.hasSum_re ((hasSum_taylorSeries_neg_log (haz i)).mul_left (c i))
  rw [← hsum.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  have hrewrite : ∑ i ∈ s, (c i * (((a : ℂ) * z ^ m i) ^ n / n)).re =
      (a ^ n / n) * trigonometricCombination s c m (z ^ n) := by
    simp only [trigonometricCombination_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← re_ofReal_mul]
    congr 1
    push_cast
    ring
  rw [hrewrite]
  exact mul_nonneg (by positivity) <| trigonometricCombination_nonneg_of_boundary h <| by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg z) hz

end

end TauCeti
