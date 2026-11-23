/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.HurwitzZeta.TaylorKernel
public import TauCeti.NumberTheory.LSeries.RiemannZeta.BernoulliKernel
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference

/-!
# Comparison between the Hurwitz and Bernoulli kernels

Specializes the complex Hurwitz generating kernel `TauCeti.hurwitzKernel` at `c = 1` and real
arguments `t : ℝ` to the real Bernoulli kernel `TauCeti.bernoulliKernel t`.

## Main results

* `TauCeti.hurwitzKernel_one_ofReal`:
  `hurwitzKernel 1 (t : ℂ) = (bernoulliKernel t : ℂ)` for every real `t`.
-/

public section

open Complex

namespace TauCeti

/-- At `c = 1` and real `t`, `hurwitzKernel 1 (t : ℂ)` coincides with the real Bernoulli kernel
`(bernoulliKernel t : ℂ)` (including at `t = 0`). -/
theorem hurwitzKernel_one_ofReal (t : ℝ) :
    hurwitzKernel 1 (t : ℂ) = (bernoulliKernel t : ℂ) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [hurwitzKernel_of_ne_zero 1 (ofReal_ne_zero.mpr ht), mul_div_assoc,
      Complex.exp_neg_mul_div_one_sub_exp_neg, bernoulliKernel_of_ne_zero ht]
    push_cast
    rw [sub_self, zero_mul, Complex.exp_zero, one_div, ← div_eq_mul_inv]

end TauCeti
