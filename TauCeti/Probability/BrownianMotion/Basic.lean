/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Probability.BrownianMotion.Basic
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.HasLaw

/-!
# Basic properties of real Brownian motion

Basic unfiltered properties of a standard real pre-Brownian motion
(`ProbabilityTheory.IsPreBrownianReal`):

* any measure supporting a pre-Brownian motion assigns zero mass to every singleton
  (`MeasureTheory.NullSingletonClass`), since evaluation at time `1` has the nondegenerate
  Gaussian law `gaussianReal 0 1`;
* every even moment `(B s - B t) ^ (2 * m)` of a pre-Brownian increment equals
  `(2 * m - 1)‼ * dist s t ^ m`, regardless of the order of `s` and `t`.

## Main results

* `ProbabilityTheory.IsPreBrownianReal.nullSingletonClass`: any measure supporting a pre-Brownian
  motion assigns zero mass to singletons.
* `ProbabilityTheory.IsPreBrownianReal.integral_pow_two_mul_sub`: even moments of pre-Brownian
  increments in either time order.
-/

public section

open MeasureTheory
open scoped Nat NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Any measure supporting a pre-Brownian motion assigns zero mass to every single sample point. -/
theorem IsPreBrownianReal.nullSingletonClass (hB : IsPreBrownianReal B P) :
    NullSingletonClass P where
  measure_singleton ω := by
    have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
    exact (hB.hasLaw_eval 1).measure_singleton_eq_zero ω

/-- Every even moment `(B s - B t) ^ (2 m)` of a pre-Brownian increment equals
`(2 m - 1)‼ * dist s t ^ m`, regardless of the order of `s` and `t`. -/
theorem IsPreBrownianReal.integral_pow_two_mul_sub (hB : IsPreBrownianReal B P) (s t : ℝ≥0)
    (m : ℕ) :
    ∫ ω, (B s ω - B t ω) ^ (2 * m) ∂P = (2 * m - 1 : ℕ)‼ * dist s t ^ m := by
  have h := (hB.hasLaw_sub s t).integral_comp (f := fun x : ℝ ↦ x ^ (2 * m)) (by fun_prop)
  have hm := TauCeti.Probability.integral_sub_pow_two_mul_gaussianReal 0 (nndist s t) m
  simp only [sub_zero, coe_nndist] at hm
  simpa only [Function.comp_apply, Pi.sub_apply, mul_comm] using h.trans hm

end ProbabilityTheory
