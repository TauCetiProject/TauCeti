/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.HurwitzZeta.TaylorKernel
public import TauCeti.NumberTheory.LSeries.RiemannZeta.BernoulliKernel

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
  · rw [hurwitzKernel_of_ne_zero 1 (ofReal_ne_zero.mpr ht), neg_one_mul,
      bernoulliKernel_of_ne_zero ht]
    push_cast
    have hexp : Complex.exp (-(t : ℂ)) * (Complex.exp (t : ℂ) - 1) =
        1 - Complex.exp (-(t : ℂ)) := by
      rw [mul_sub, mul_one, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    have hne1 : Complex.exp (t : ℂ) - 1 ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (by simpa using Real.exp_injective.ne ht)
    have hne2 : 1 - Complex.exp (-(t : ℂ)) ≠ 0 := by
      rw [← hexp]
      exact mul_ne_zero (Complex.exp_ne_zero _) hne1
    rw [div_eq_div_iff hne2 hne1]
    linear_combination (t : ℂ) * hexp

end TauCeti
