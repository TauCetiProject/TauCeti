/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Potential
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Smooth local solutions of the inhomogeneous Cauchy–Riemann equation

The identity `bar∂ ∂ u = Δu / 4` converts the planar Newtonian potential into a right
inverse for `bar∂` on smooth compactly supported functions. Cutting off the source gives
a smooth solution near any specified point. This supplies integrating factors for scalar
Cauchy–Riemann equations with a smooth zeroth-order coefficient.

The construction uses `TauCeti.laplacian_planarNewtonianKernel_convolution`, whose kernel
is normalized by `-ΔG = δ`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Chapter I.
-/

public noncomputable section

open Complex Filter InnerProductSpace Laplacian Topology
open scoped Convolution ContDiff

namespace TauCeti

/-- The mixed Wirtinger derivative of a complex-valued function on the plane is one quarter
of its real Laplacian. -/
theorem conjWirtingerDeriv_wirtingerDeriv_apply_one {u : ℂ → ℂ} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) :
    conjWirtingerDeriv (fun w ↦ wirtingerDeriv u w 1) z 1 = (4 : ℂ)⁻¹ * Δ u z := by
  have hd := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hp (v : ℂ) : DifferentiableAt ℝ (fun w ↦ fderiv ℝ u w v) z :=
    hd.clm_apply (differentiableAt_const _)
  have hc := (hu.isSymmSndFDerivAt (by norm_num)).eq (1 : ℂ) I
  rw [laplacian_eq_sum_fderiv_fderiv_apply Complex.orthonormalBasisOneI hd,
    Fin.sum_univ_two]
  simp only [Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [conjWirtingerDeriv_apply, wirtingerDeriv_apply, smul_eq_mul, mul_one]
  have hW := (((hp 1).hasFDerivAt.fun_sub
    ((hp I).hasFDerivAt.const_mul I)).const_mul (2 : ℂ)⁻¹)
  rw [hW.fderiv]
  simp only [sub_apply, smul_apply, smul_eq_mul,
    fderiv_clm_apply hd (differentiableAt_const _), fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  rw [hc]
  ring_nf
  simp
  ring

/-- A smooth compactly supported source has a global smooth `bar∂` primitive. -/
theorem exists_contDiff_conjWirtingerDeriv_eq_of_hasCompactSupport {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ g : ℂ → ℂ, ContDiff ℝ ∞ g ∧ ∀ z, conjWirtingerDeriv g z 1 = f z := by
  let u := planarNewtonianKernel ⋆ f
  have hu : ContDiff ℝ ∞ u := contDiff_planarNewtonianKernel_convolution hf hfc
  have hdu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hp (v : ℂ) : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ u z v) :=
    hdu.clm_apply contDiff_const
  have hW : ContDiff ℝ ∞ (fun z ↦ wirtingerDeriv u z 1) := by
    simp only [wirtingerDeriv_apply, smul_eq_mul, mul_one]
    exact contDiff_const.mul ((hp 1).sub (contDiff_const.mul (hp I)))
  refine ⟨fun z ↦ (-4 : ℂ) * wirtingerDeriv u z 1, contDiff_const.mul hW, fun z ↦ ?_⟩
  have hΔ := congrFun (laplacian_planarNewtonianKernel_convolution (hf.of_le (by simp)) hfc) z
  have hm := conjWirtingerDeriv_wirtingerDeriv_apply_one
    (z := z) (hu.of_le (by simp)).contDiffAt
  rw [hΔ] at hm
  simp only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one, Pi.neg_apply] at hm ⊢
  rw [fderiv_const_mul (hW.differentiable (by simp) z) (-4 : ℂ)]
  simp only [smul_apply, smul_eq_mul]
  linear_combination -4 * hm

/-- Every smooth source admits a smooth `bar∂` primitive near any specified point. -/
theorem exists_contDiff_conjWirtingerDeriv_eventuallyEq {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    ∃ g : ℂ → ℂ, ContDiff ℝ ∞ g ∧ ∀ᶠ w in 𝓝 z, conjWirtingerDeriv g w 1 = f w := by
  let χ : ContDiffBump z := ⟨1, 2, by norm_num, by norm_num⟩
  have hχ : ContDiff ℝ ∞ (fun w ↦ (χ w : ℂ)) := Complex.ofRealCLM.contDiff.comp χ.contDiff
  obtain ⟨g, hg, heq⟩ := exists_contDiff_conjWirtingerDeriv_eq_of_hasCompactSupport
    (hχ.mul hf) ((χ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right)
  refine ⟨g, hg, ?_⟩
  filter_upwards [χ.eventuallyEq_one] with w hw
  simpa [hw] using heq w

end TauCeti
