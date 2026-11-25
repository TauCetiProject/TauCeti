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
left half-plane `Re z ≤ 0` the exponential is `1`-Lipschitz, so `‖1 - exp (-ζ)‖ ≤ ‖ζ‖` for
`0 ≤ ζ.re`.

## Main results

* `Complex.norm_exp_neg_mul_ofReal`: `‖exp (-(a r))‖ = exp (-(a.re r))` for real `r`.
* `TauCeti.norm_cexp_neg_mul_lt_one`: `‖exp (-(h : ℂ) * z)‖ < 1` for `h > 0` and `0 < z.re`.
* `TauCeti.cexp_neg_mul_abs_isLittleO_abs_rpow_cocompact`: two-sided decay with a
  complex rate of positive real part.
* `Complex.lipschitzOnWith_exp_setOf_re_nonpos`: `exp` is `1`-Lipschitz on `Re z ≤ 0`.
* `Complex.norm_one_sub_exp_neg_le`: `‖1 - exp (-ζ)‖ ≤ ‖ζ‖` for `0 ≤ ζ.re`.
-/

public section

open Filter Asymptotics

/-- For real `r`, the norm of `exp (-(a r))` is the real exponential `exp (-(a.re r))`. -/
theorem Complex.norm_exp_neg_mul_ofReal (a : ℂ) (r : ℝ) :
    ‖Complex.exp (-(a * r))‖ = Real.exp (-(a.re * r)) := by
  simp only [Complex.norm_exp, Complex.neg_re, Complex.re_mul_ofReal]

/-- On the closed left half-plane `Re z ≤ 0` the exponential is `1`-Lipschitz: its derivative
`exp z` has norm `exp (Re z) ≤ 1` there. -/
theorem Complex.lipschitzOnWith_exp_setOf_re_nonpos :
    LipschitzOnWith 1 Complex.exp {z : ℂ | z.re ≤ 0} :=
  (convex_halfSpace_re_le 0).lipschitzOnWith_of_nnNorm_hasDerivWithin_le
    (fun z _ => (Complex.hasDerivAt_exp z).hasDerivWithinAt) fun z hz => by
      simpa only [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one, Complex.norm_exp,
        Real.exp_le_one_iff, Set.mem_ofPred_eq] using hz

/-- On the closed right half-plane, `‖1 - exp (-ζ)‖ ≤ ‖ζ‖`: the case `0`, `-ζ` of
`Complex.lipschitzOnWith_exp_setOf_re_nonpos`. -/
theorem Complex.norm_one_sub_exp_neg_le {ζ : ℂ} (hζ : 0 ≤ ζ.re) :
    ‖1 - Complex.exp (-ζ)‖ ≤ ‖ζ‖ := by
  have h := Complex.lipschitzOnWith_exp_setOf_re_nonpos.norm_sub_le
    (x := 0) (y := -ζ) (by simp) (by simpa using hζ)
  simpa using h

namespace TauCeti

/-- For `h > 0` and `0 < z.re`, the complex exponential `exp (-(h : ℂ) * z)` has norm strictly less
than `1`. -/
theorem norm_cexp_neg_mul_lt_one {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.exp (-(h : ℂ) * z)‖ < 1 := by
  rw [neg_mul, mul_comm (h : ℂ) z, Complex.norm_exp_neg_mul_ofReal]
  exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hz hh))

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
