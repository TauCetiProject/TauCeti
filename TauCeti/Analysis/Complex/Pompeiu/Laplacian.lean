/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Complex.Pompeiu.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The Laplacian of the Cauchy transform

The Laplacian on `ℂ` factors as `Δ = 4 ∂ \bar∂`, and the normalized Cauchy transform `T` inverts
`\bar∂` on compactly supported `C¹` data. Since `T` also commutes with real directional
derivatives on such data, applying `\bar∂` to each first derivative of `T h` gives
`Δ (T h) = 4 ∂h = 2 (∂ₛh - i ∂ₜh)` for compactly supported `C²` data `h`.

## Main results

* `HasCompactSupport.laplacian_cauchyTransform`: `Δ (T h) = 4 ∂h` for compactly supported `C²`
  data.

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
  have hΔ : Δ u w = fderiv ℝ (fun y ↦ fderiv ℝ u y 1) w 1 +
      fderiv ℝ (fun y ↦ fderiv ℝ u y I) w I := by
    rw [laplacian_eq_sum_fderiv_fderiv_apply Complex.orthonormalBasisOneI
      ((hu1.differentiable one_ne_zero) w), Fin.sum_univ_two]
    simp
  have h1 := hdbar 1
  have hI := hdbar I
  rw [hd2, hd2] at h1 hI
  rw [hd2, hd2] at hΔ
  rw [hΔ]
  linear_combination (norm := match_scalars <;> first | ring1 | linear_combination I_sq)
    h1 - I • hI - I • hsymm

end TauCeti
