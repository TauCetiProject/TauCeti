/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Unimodality of `x exp (1 - x)`

The function `x ↦ x exp (1 - x)` increases up to `1` and decreases thereafter. This controls
powers of the same function in the rescaled profile of Gamma kernels.
-/

public section

open Set

namespace Real

/-- The derivative of `x exp (1 - x)` is `(1 - x) exp (1 - x)`. -/
theorem hasDerivAt_mul_exp_one_sub (x : ℝ) :
    HasDerivAt (fun t ↦ t * exp (1 - t)) ((1 - x) * exp (1 - x)) x := by
  have h : HasDerivAt (fun t : ℝ ↦ t) 1 x := hasDerivAt_id x
  convert h.mul ((h.const_sub 1).exp) using 1
  ring

end Real

namespace TauCeti

open Real

/-- The function `x exp (1 - x)` is strictly increasing up to `1`. -/
theorem strictMonoOn_mul_exp_one_sub : StrictMonoOn (fun x : ℝ ↦ x * exp (1 - x)) (Iic 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Iic _) (by fun_prop) fun x hx ↦ ?_
  rw [interior_Iic, mem_Iio] at hx
  rw [(hasDerivAt_mul_exp_one_sub x).deriv]
  exact mul_pos (sub_pos.mpr hx) (exp_pos _)

/-- The function `x exp (1 - x)` is strictly decreasing from `1` onward. -/
theorem strictAntiOn_mul_exp_one_sub : StrictAntiOn (fun x : ℝ ↦ x * exp (1 - x)) (Ici 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici _) (by fun_prop) fun x hx ↦ ?_
  rw [interior_Ici, mem_Ioi] at hx
  rw [(hasDerivAt_mul_exp_one_sub x).deriv]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hx) (exp_pos _)

end TauCeti
