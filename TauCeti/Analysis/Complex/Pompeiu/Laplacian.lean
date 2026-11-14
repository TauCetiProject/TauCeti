/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Complex.Pompeiu.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.FDeriv.OfReal
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The Laplacian of the Cauchy transform

The Laplacian on `ℂ` factors as `Δ = 4 ∂ \bar∂`, and the normalized Cauchy transform `T` inverts
`\bar∂` on compactly supported `C¹` data. Since `T` also commutes with real directional
derivatives on such data, applying `\bar∂` to each first derivative of `T h` gives
`Δ (T h) = 4 ∂h = 2 (∂ₛh - i ∂ₜh)` for compactly supported `C²` data `h`.

For real data `f, g` and `h = f + i g`, taking real parts gives `Δ (Re T h) = 2 (∂ₛf + ∂ₜg)`, so
`ξ₀ = ½ Re (T h)` solves the divergence-form equation `Δξ = ∂ₛf + ∂ₜg`.

## Main results

* `HasCompactSupport.laplacian_cauchyTransform`: `Δ (T h) = 4 ∂h` for compactly supported `C²`
  data.
* `ContDiff.laplacian_re_cauchyTransform`: `Δ (Re T h) = 2 (∂ₛf + ∂ₜg)` for real compactly
  supported `C²` data `f, g`.
* `ContDiff.laplacian_half_re_cauchyTransform`, `ContDiff.contDiff_half_re_cauchyTransform`: the
  divergence-form solution formula `Δ (½ Re T h) = ∂ₛf + ∂ₜg`, and the smoothness of `½ Re T h`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4.
-/

public noncomputable section

open Complex InnerProductSpace Laplacian

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **`Δ = 4 ∂ \bar∂` on the Cauchy transform.** For compactly supported `C²` data `h`, the
Laplacian of `T h` is `4 ∂h = 2 (∂ₛh - i ∂ₜh)`. -/
theorem _root_.HasCompactSupport.laplacian_cauchyTransform {h : ℂ → F}
    (hc : HasCompactSupport h) (hh : ContDiff ℝ 2 h) (w : ℂ) :
    Δ (cauchyTransform h) w = (2 : ℂ) • (fderiv ℝ h w 1 - I • fderiv ℝ h w I) := by
  set u := cauchyTransform h
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hu : ContDiff ℝ 2 u := hc.contDiff_cauchyTransform hh
  have hu1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hdu (v : ℂ) : (fun y ↦ fderiv ℝ u y v) = cauchyTransform fun z ↦ fderiv ℝ h z v :=
    funext fun y ↦ hc.fderiv_cauchyTransform_apply hh1 y v
  -- Each directional derivative of `u` is a Cauchy transform, so `\bar∂` inverts it.
  have hdbar (v : ℂ) :
      fderiv ℝ (fun y ↦ fderiv ℝ u y v) w 1 + I • fderiv ℝ (fun y ↦ fderiv ℝ u y v) w I =
        (2 : ℂ) • fderiv ℝ h w v := by
    have hcv : HasCompactSupport fun z ↦ fderiv ℝ h z v :=
      (hc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] F ↦ L v) rfl
    have hv : ContDiff ℝ 1 fun z ↦ fderiv ℝ h z v :=
      (hh.fderiv_right (by norm_num)).clm_apply contDiff_const
    have e := hcv.conjWirtingerDeriv_cauchyTransform hv w
    rw [conjWirtingerDeriv_apply, ← hdu, smul_eq_mul, mul_one] at e
    rw [← e, smul_smul]
    norm_num
  have hsymm := (hu.contDiffAt (x := w)).isSymmSndFDerivAt (by simp) I 1
  have hd2 (a b : ℂ) : fderiv ℝ (fun y ↦ fderiv ℝ u y b) w a = fderiv ℝ (fderiv ℝ u) w a b := by
    rw [fderiv_clm_apply ((hu1.differentiable one_ne_zero) w) (differentiableAt_const _)]
    simp
  have hΔ := laplacian_eq_fderiv_fderiv_apply_one_add_fderiv_fderiv_apply_I
    ((hu1.differentiable one_ne_zero) w)
  have h1 := hdbar 1
  have hI := hdbar I
  rw [hd2, hd2] at h1 hI
  rw [hd2, hd2] at hΔ
  rw [hΔ]
  linear_combination (norm := match_scalars <;> first | ring1 | linear_combination I_sq)
    h1 - I • hI - I • hsymm

section RealData

variable {f g : ℂ → ℝ}

/-- The real part of the Cauchy transform of `f + i g` has Laplacian `2 (∂ₛf + ∂ₜg)`, twice the
divergence-form right-hand side. -/
theorem _root_.ContDiff.laplacian_re_cauchyTransform (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (w : ℂ) :
    Δ (fun w ↦ (cauchyTransform (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w).re) w =
      2 * (fderiv ℝ f w 1 + fderiv ℝ g w I) := by
  set h : ℂ → ℂ := fun z ↦ (f z : ℂ) + (g z : ℂ) * I
  have hh : ContDiff ℝ 2 h := hf.ofReal_add_ofReal_mul_I hg
  have hhc : HasCompactSupport h := hfc.ofReal_add_ofReal_mul_I hgc
  have hu : ContDiff ℝ 2 (cauchyTransform h) := hhc.contDiff_cauchyTransform hh
  have hre : (fun w ↦ (cauchyTransform h w).re) = reCLM ∘ cauchyTransform h := rfl
  rw [hre, hu.contDiffAt.laplacian_CLM_comp_left, Function.comp_apply,
    hhc.laplacian_cauchyTransform hh w,
    ((hf.differentiable two_ne_zero) w).fderiv_ofReal_add_ofReal_mul_I_apply
      ((hg.differentiable two_ne_zero) w),
    ((hf.differentiable two_ne_zero) w).fderiv_ofReal_add_ofReal_mul_I_apply
      ((hg.differentiable two_ne_zero) w)]
  simp only [reCLM_apply, smul_eq_mul, mul_re, sub_re, add_re, ofReal_re, ofReal_im, I_re, I_im,
    mul_im, add_im, sub_im, re_ofNat, im_ofNat]
  ring

/-- The smoothness half of the solution formula: for compactly supported real `Cⁿ` data `f, g`
and `h = f + i g`, the function `½ Re (T h)` is `Cⁿ`. -/
theorem _root_.ContDiff.contDiff_half_re_cauchyTransform {n : ℕ∞} (hf : ContDiff ℝ n f)
    (hg : ContDiff ℝ n g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ContDiff ℝ n fun w ↦ (cauchyTransform (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w).re / 2 :=
  (reCLM.contDiff.comp <| (hfc.ofReal_add_ofReal_mul_I hgc).contDiff_cauchyTransform
    (hf.ofReal_add_ofReal_mul_I hg)).div_const 2

/-- **The divergence-form solution formula.** For real compactly supported `C²` data `f, g` and
`h = f + i g`, the function `ξ₀ = ½ Re (T h)` solves `Δξ₀ = ∂ₛf + ∂ₜg` at every point. -/
theorem _root_.ContDiff.laplacian_half_re_cauchyTransform (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (w : ℂ) :
    Δ (fun w ↦ (cauchyTransform (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w).re / 2) w =
      fderiv ℝ f w 1 + fderiv ℝ g w I := by
  set u := fun w ↦ (cauchyTransform (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w).re
  have hu : ContDiff ℝ 2 u := reCLM.contDiff.comp <|
    (hfc.ofReal_add_ofReal_mul_I hgc).contDiff_cauchyTransform (hf.ofReal_add_ofReal_mul_I hg)
  -- `laplacian_smul` is stated for a scalar multiple `c • u`, so write `u / 2` as `2⁻¹ • u`.
  have hhalf : (fun w ↦ u w / 2) = (2⁻¹ : ℝ) • u :=
    funext fun w ↦ by rw [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  rw [hhalf, laplacian_smul _ hu.contDiffAt, hf.laplacian_re_cauchyTransform hg hfc hgc w,
    smul_eq_mul]
  ring

end RealData

end TauCeti
