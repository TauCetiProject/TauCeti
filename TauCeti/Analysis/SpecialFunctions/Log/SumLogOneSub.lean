/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Derivatives at zero of a finite sum of logarithms `log (1 - 2 t aⱼ)`

For real weights `a : ι → ℝ` indexed by a finite type and a real constant `c`, consider
`t ↦ -c / 2 * ∑ j, log (1 - 2 * t * a j)`. When `c` is a positive natural number coerced to
`ℝ`, this is locally the cumulant-generating function of a weighted sum of independent chi-squared
variables, each with `c` degrees of freedom. For arbitrary real `c`, this file computes its first
two derivatives at `0`: `c * ∑ j, a j` and `2 * c * ∑ j, a j ^ 2`.

## Main results

* `TauCeti.hasDerivAt_neg_half_mul_sum_log` — the first derivative at `0` is `c * ∑ j, a j`;
* `TauCeti.iteratedDeriv_two_neg_half_mul_sum_log` — the second derivative at `0` is
  `2 * c * ∑ j, a j ^ 2`.
-/

public section

open Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The function `t ↦ -c / 2 * ∑ j, log (1 - 2 * t * a j)` has derivative `c * ∑ j, a j` at `0`. -/
theorem hasDerivAt_neg_half_mul_sum_log (c : ℝ) (a : ι → ℝ) :
    HasDerivAt (fun t => -c / 2 * ∑ j, Real.log (1 - 2 * t * a j))
      (c * ∑ j, a j) 0 := by
  have hj (j : ι) :
      HasDerivAt (fun t : ℝ => Real.log (1 - 2 * t * a j)) (-2 * a j) 0 := by
    simpa using ((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (a j)).const_sub 1).log
      (by norm_num)
  have hsum : HasDerivAt (fun t => ∑ j, Real.log (1 - 2 * t * a j))
      (∑ j, -2 * a j) 0 := HasDerivAt.fun_sum fun j _ => hj j
  refine (hsum.const_mul (-c / 2)).congr_deriv ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The function `t ↦ -c / 2 * ∑ j, log (1 - 2 * t * a j)` has second derivative
`2 * c * ∑ j, a j ^ 2` at `0`. -/
theorem iteratedDeriv_two_neg_half_mul_sum_log (c : ℝ) (a : ι → ℝ) :
    iteratedDeriv 2 (fun t => -c / 2 * ∑ j, Real.log (1 - 2 * t * a j)) 0 =
      2 * c * ∑ j, a j ^ 2 := by
  have haff (j : ι) (t : ℝ) :
      HasDerivAt (fun u : ℝ => 1 - 2 * u * a j) (-2 * a j) t := by
    simpa using (((hasDerivAt_id t).const_mul 2).mul_const (a j)).const_sub 1
  let f : ℝ → ℝ := fun t => -c / 2 * ∑ j, Real.log (1 - 2 * t * a j)
  let g : ℝ → ℝ := fun t => c * ∑ j, a j / (1 - 2 * t * a j)
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, 1 - 2 * t * a j ≠ 0 :=
    Filter.eventually_all.2 fun j =>
      (haff j 0).continuousAt.eventually_ne (by norm_num : (1 - 2 * 0 * a j : ℝ) ≠ 0)
  have hfg : deriv f =ᶠ[𝓝 (0 : ℝ)] g := by
    filter_upwards [hne] with t ht
    dsimp only [f, g]
    rw [(HasDerivAt.const_mul (-c / 2)
      (HasDerivAt.fun_sum fun j _ => (haff j t).log (ht j))).deriv, Finset.mul_sum,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by field_simp [ht j]
  have hg : HasDerivAt g (2 * c * ∑ j, a j ^ 2) 0 := by
    have hj (j : ι) :
        HasDerivAt (fun t : ℝ => a j / (1 - 2 * t * a j)) (2 * a j ^ 2) 0 := by
      refine ((hasDerivAt_const (0 : ℝ) (a j)).div (haff j 0) (by norm_num)).congr_deriv ?_
      norm_num
      ring
    refine ((HasDerivAt.fun_sum fun j _ => hj j).const_mul c).congr_deriv ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    ring_nf
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact (hg.congr_of_eventuallyEq hfg).deriv

end TauCeti
