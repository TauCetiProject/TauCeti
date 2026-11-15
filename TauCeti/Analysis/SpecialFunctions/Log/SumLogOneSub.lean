/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Derivatives of a finite sum of logarithms `log (1 - 2 t aⱼ)`

For real weights `a : ι → ℝ` indexed by a finite set `s` and a real constant `c`, consider
`t ↦ -c / 2 * ∑ j ∈ s, log (1 - 2 * t * a j)`. When `c` is a positive natural number coerced to
`ℝ`, this is locally the cumulant-generating function of a weighted sum of independent chi-squared
variables, each with `c` degrees of freedom. For arbitrary real `c`, this file computes its first
two derivatives at every `t` with `1 - 2 * t * a j ≠ 0` for all `j ∈ s`:
`c * ∑ j ∈ s, a j / (1 - 2 * t * a j)` and `2 * c * ∑ j ∈ s, a j ^ 2 / (1 - 2 * t * a j) ^ 2`.
At `t = 0` these are `c * ∑ j ∈ s, a j` and `2 * c * ∑ j ∈ s, a j ^ 2`.

## Main results

* `TauCeti.hasDerivAt_neg_half_mul_sum_log` — the first derivative is
  `c * ∑ j ∈ s, a j / (1 - 2 * t * a j)`;
* `TauCeti.iteratedDeriv_two_neg_half_mul_sum_log` — the second derivative is
  `2 * c * ∑ j ∈ s, a j ^ 2 / (1 - 2 * t * a j) ^ 2`.
-/

public section

open Topology

namespace TauCeti

variable {ι : Type*}

/-- If `1 - 2 * t * a j ≠ 0` for all `j ∈ s`, then the function
`u ↦ -c / 2 * ∑ j ∈ s, log (1 - 2 * u * a j)` has derivative
`c * ∑ j ∈ s, a j / (1 - 2 * t * a j)` at `t`. -/
theorem hasDerivAt_neg_half_mul_sum_log (c : ℝ) (s : Finset ι) (a : ι → ℝ) {t : ℝ}
    (ht : ∀ j ∈ s, 1 - 2 * t * a j ≠ 0) :
    HasDerivAt (fun u => -c / 2 * ∑ j ∈ s, Real.log (1 - 2 * u * a j))
      (c * ∑ j ∈ s, a j / (1 - 2 * t * a j)) t := by
  have hj (j : ι) (hj : j ∈ s) :
      HasDerivAt (fun u : ℝ => Real.log (1 - 2 * u * a j))
        (-(2 * 1 * a j) / (1 - 2 * t * a j)) t :=
    ((((hasDerivAt_id' (x := t)).const_mul 2).mul_const (a j)).const_sub 1).log (ht j hj)
  refine ((HasDerivAt.fun_sum hj).const_mul (-c / 2)).congr_deriv ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- If `1 - 2 * t * a j ≠ 0` for all `j ∈ s`, then the function
`u ↦ -c / 2 * ∑ j ∈ s, log (1 - 2 * u * a j)` has second derivative
`2 * c * ∑ j ∈ s, a j ^ 2 / (1 - 2 * t * a j) ^ 2` at `t`. -/
theorem iteratedDeriv_two_neg_half_mul_sum_log (c : ℝ) (s : Finset ι) (a : ι → ℝ) {t : ℝ}
    (ht : ∀ j ∈ s, 1 - 2 * t * a j ≠ 0) :
    iteratedDeriv 2 (fun u => -c / 2 * ∑ j ∈ s, Real.log (1 - 2 * u * a j)) t =
      2 * c * ∑ j ∈ s, a j ^ 2 / (1 - 2 * t * a j) ^ 2 := by
  have hne : ∀ᶠ u in 𝓝 t, ∀ j ∈ s, 1 - 2 * u * a j ≠ 0 :=
    Filter.eventually_all_finset s |>.2 fun j hj =>
      (by fun_prop : Continuous fun u : ℝ => 1 - 2 * u * a j).continuousAt.eventually_ne (ht j hj)
  have hj (j : ι) (hj : j ∈ s) :
      HasDerivAt (fun u : ℝ => a j / (1 - 2 * u * a j))
        (2 * a j ^ 2 / (1 - 2 * t * a j) ^ 2) t := by
    convert (hasDerivAt_const t (a j)).fun_div
      ((((hasDerivAt_id' (x := t)).const_mul 2).mul_const (a j)).const_sub 1) (ht j hj) using 1
    ring
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  refine (((HasDerivAt.fun_sum hj).const_mul c).congr_of_eventuallyEq ?_).deriv.trans ?_
  · filter_upwards [hne] with u hu using (hasDerivAt_neg_half_mul_sum_log c s a hu).deriv
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

end TauCeti
