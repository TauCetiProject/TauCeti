/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.NumberTheory.ZetaValues
import TauCeti.Analysis.Calculus.Deriv.Fract

/-!
# Real and periodized Bernoulli functions

This file records elementary difference, evaluation, periodicity, continuity, and differentiability
properties of Mathlib's real-variable Bernoulli polynomial `bernoulliFun` and its `1`-periodic
extension `x ↦ bernoulliFun k (Int.fract x)`.

## Main results

* `TauCeti.bernoulliFun_eval_add_one`: the difference equation
  `B_k(x + 1) = B_k(x) + k x^(k-1)`.
* `TauCeti.bernoulliFun_three`, `TauCeti.bernoulliFun_four`: explicit formulas for `B₃` and `B₄`.
* `TauCeti.periodic_bernoulliFun_fract`: for every `k : ℕ`, `x ↦ B_k({x})` is `1`-periodic.
* `TauCeti.continuous_bernoulliFun_fract`: for `k ≠ 1`, the periodized Bernoulli function
  `x ↦ B_k({x})` is continuous on `ℝ`.
* `TauCeti.hasDerivAt_bernoulliFun_fract`: at every non-integer `t : ℝ`, `u ↦ B_k({u})` has
  derivative `k * B_{k - 1}({t})`.
-/

public section

namespace TauCeti

/-- The difference equation for Bernoulli polynomials: `B_k(x + 1) = B_k(x) + k * x ^ (k - 1)`. -/
theorem bernoulliFun_eval_add_one (k : ℕ) (x : ℝ) :
    bernoulliFun k (x + 1) = bernoulliFun k x + k * x ^ (k - 1) := by
  simpa [bernoulliFun, Polynomial.aeval_comp, add_comm]
    using congr($(Polynomial.bernoulli_comp_one_add_X k).aeval x)

/-- Explicit formula for `bernoulliFun 3`. -/
@[simp]
theorem bernoulliFun_three (x : ℝ) :
    bernoulliFun 3 x = x ^ 3 - 3 / 2 * x ^ 2 + 1 / 2 * x := by
  simp only [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add]
  norm_num [Nat.choose]
  ring

/-- Explicit formula for `bernoulliFun 4`. -/
@[simp]
theorem bernoulliFun_four (x : ℝ) :
    bernoulliFun 4 x = x ^ 4 - 2 * x ^ 3 + x ^ 2 - 30⁻¹ := by
  simp only [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add]
  norm_num [Nat.choose]
  ring

/-- For every `k : ℕ`, the periodized Bernoulli function `x ↦ B_k({x})` is `1`-periodic. -/
theorem periodic_bernoulliFun_fract (k : ℕ) :
    Function.Periodic (fun x : ℝ ↦ bernoulliFun k (Int.fract x)) 1 :=
  fun x ↦ by simp [Int.fract_add_one]

/-- For `k ≠ 1`, the periodized Bernoulli function `x ↦ B_k({x})` is continuous on `ℝ`. -/
theorem continuous_bernoulliFun_fract {k : ℕ} (hk : k ≠ 1) :
    Continuous fun x : ℝ ↦ bernoulliFun k (Int.fract x) :=
  ContinuousOn.comp_fract'' (continuous_bernoulliFun k).continuousOn
    (bernoulliFun_endpoints_eq_of_ne_one hk).symm

/-- At every non-integer `t : ℝ`, `u ↦ B_k({u})` has derivative `k * B_{k - 1}({t})`. -/
theorem hasDerivAt_bernoulliFun_fract (k : ℕ) {t : ℝ}
    (ht : t ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt (fun u : ℝ ↦ bernoulliFun k (Int.fract u))
      (k * bernoulliFun (k - 1) (Int.fract t)) t :=
  ((hasDerivAt_bernoulliFun k (Int.fract t)).comp t (Int.hasDerivAt_fract ht)).congr_deriv
    (mul_one _)

end TauCeti
