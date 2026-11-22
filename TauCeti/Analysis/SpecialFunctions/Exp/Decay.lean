/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Two-sided complex exponential decay

For a complex rate `a` with positive real part, the function
`x ↦ exp (-(a * |x|))` is little-o of every real power of `|x|` outside compact
subsets of the real line. Its norm is the real exponential with rate `a.re`. On the closed
right half-plane `exp (-ζ)` has norm at most one, so `‖1 - exp (-ζ)‖ ≤ ‖ζ‖` there.

## Main results

* `Complex.norm_exp_neg_mul_ofReal`: `‖exp (-(a r))‖ = exp (-(a.re r))` for real `r`.
* `TauCeti.cexp_neg_mul_abs_isLittleO_abs_rpow_cocompact`: two-sided decay with a
  complex rate of positive real part.
* `Complex.norm_one_sub_exp_neg_le`: `‖1 - exp (-ζ)‖ ≤ ‖ζ‖` for `0 ≤ ζ.re`.
-/

public section

open Filter Asymptotics

/-- For real `r`, the norm of `exp (-(a r))` is the real exponential `exp (-(a.re r))`. -/
theorem Complex.norm_exp_neg_mul_ofReal (a : ℂ) (r : ℝ) :
    ‖Complex.exp (-(a * r))‖ = Real.exp (-(a.re * r)) := by
  simp only [Complex.norm_exp, Complex.neg_re, Complex.re_mul_ofReal]

/-- On the closed right half-plane, `‖1 - exp (-ζ)‖ ≤ ‖ζ‖`: the derivative `-exp (-w)` of
`exp (-w)` has norm `exp (-w.re) ≤ 1` on the segment from `0` to `ζ`. -/
theorem Complex.norm_one_sub_exp_neg_le {ζ : ℂ} (hζ : 0 ≤ ζ.re) :
    ‖1 - Complex.exp (-ζ)‖ ≤ ‖ζ‖ := by
  have hs : Convex ℝ {w : ℂ | 0 ≤ w.re} := convex_halfSpace_re_ge (r := 0)
  have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun w => Complex.exp (-w))
    (f' := fun w => -Complex.exp (-w)) (C := 1)
    (fun w _ => by simpa using ((hasDerivAt_neg w).cexp).hasDerivWithinAt)
    (fun w hw => by
      rw [norm_neg, Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff, neg_nonpos]
      exact hw)
    (x := 0) (y := ζ) (by simp) hζ
  simpa [norm_sub_rev] using h

namespace TauCeti

/-- **Two-sided complex exponential decay beats every real power.** If a complex rate
has positive real part, then `exp (-(a * |x|))` is little-o of `|x| ^ s` as
`|x|` tends to infinity, for every real `s`.

The real-valued estimate is `exp_neg_mul_abs_isLittleO_abs_rpow_cocompact`.

Adapted from `ForTauCeti/Analysis/Fourier/ExponentialAbs.lean` in
[AIQ-Kitware/aiq-dkps-formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Apache-2.0; copyright 2026 Kitware, Inc.; authors Jon Crall and GPT 5.6 High). -/
theorem cexp_neg_mul_abs_isLittleO_abs_rpow_cocompact
    {a : ℂ} (ha : 0 < a.re) (s : ℝ) :
    (fun x : ℝ => Complex.exp (-(a * |x|)))
      =o[cocompact ℝ] (fun x : ℝ => |x| ^ s) := by
  apply IsLittleO.of_norm_left
  simpa only [Complex.norm_exp_neg_mul_ofReal] using
    (exp_neg_mul_abs_isLittleO_abs_rpow_cocompact ha s)

end TauCeti
