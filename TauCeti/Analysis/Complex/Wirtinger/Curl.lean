/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Green.Basic

/-!
# Planar curls of the Wirtinger coordinate pairs

For a real-differentiable scalar map `F = u + i v : ℂ → ℂ`, the planar curls of the real
coordinate pairs `(u, -v)` and `(v, u)` entering Green's theorem for `F dz` are `-2 Im (\bar∂ F)`
and `2 Re (\bar∂ F)`.

## Main results

* `TauCeti.curl_re_neg_im_eq_neg_two_mul_im_conjWirtingerDeriv`
* `TauCeti.curl_im_re_eq_two_mul_re_conjWirtingerDeriv`
-/

public section

noncomputable section

open Complex

namespace TauCeti

/-- For real-differentiable `F = u + i v`, the curl of `(u, -v)` is `-2 Im (\bar∂ F)`. -/
theorem curl_re_neg_im_eq_neg_two_mul_im_conjWirtingerDeriv {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) :
    Green.curl (fun w ↦ (F w).re) (fun w ↦ -(F w).im) z =
      -2 * (conjWirtingerDeriv F z 1).im := by
  rw [Green.curl, fderiv_fun_neg]
  simp_rw [← Complex.reCLM_apply, ← Complex.imCLM_apply]
  rw [fderiv_fun_comp z Complex.imCLM.differentiableAt hF,
    fderiv_fun_comp z Complex.reCLM.differentiableAt hF,
    Complex.imCLM.fderiv, Complex.reCLM.fderiv, conjWirtingerDeriv_apply]
  simp only [neg_apply, ContinuousLinearMap.comp_apply, Complex.imCLM_apply,
    Complex.reCLM_apply, smul_eq_mul, add_im, mul_im, inv_im, re_ofNat, im_ofNat, neg_zero,
    zero_div, zero_mul, inv_re, normSq_ofNat, div_self_mul_self', add_zero, I_re, I_im, one_mul,
    mul_one]
  ring

/-- For real-differentiable `F = u + i v`, the curl of `(v, u)` is `2 Re (\bar∂ F)`. -/
theorem curl_im_re_eq_two_mul_re_conjWirtingerDeriv {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) :
    Green.curl (fun w ↦ (F w).im) (fun w ↦ (F w).re) z =
      2 * (conjWirtingerDeriv F z 1).re := by
  rw [Green.curl]
  simp_rw [← Complex.reCLM_apply, ← Complex.imCLM_apply]
  rw [fderiv_fun_comp z Complex.reCLM.differentiableAt hF,
    fderiv_fun_comp z Complex.imCLM.differentiableAt hF,
    Complex.reCLM.fderiv, Complex.imCLM.fderiv, conjWirtingerDeriv_apply]
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    smul_eq_mul, add_re, mul_re, inv_re, re_ofNat, normSq_ofNat, inv_im, im_ofNat, neg_zero,
    zero_div, zero_mul, sub_zero, I_re, I_im, one_mul, mul_one]
  ring

end TauCeti

end
