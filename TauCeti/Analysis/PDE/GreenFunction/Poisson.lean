/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.GreenFunction.Disk
public import Mathlib.Analysis.Complex.Poisson
import TauCeti.Analysis.PDE.FundamentalSolution.Gradient

/-!
# The Poisson kernel as a boundary derivative of the planar Green kernel

The outward radial derivative of the Dirichlet Green kernel on a planar disk is the negative
of Mathlib's Poisson kernel, divided by `2π`, when the radius is parametrized from zero to one.
This identifies the boundary term in Green's representation formula with the existing Poisson
kernel, both on the unit disk and after translation and dilation.

The normalization follows Evans, *Partial Differential Equations*, Chapter 2, §2.2.
-/

public section

noncomputable section

namespace TauCeti

open Complex InnerProductSpace

/-- On the boundary of the unit disk, the outward radial derivative of the Green kernel
with pole `a` is the negative of the Poisson kernel divided by `2π`. -/
theorem hasDerivAt_planarGreenKernel_radial {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    HasDerivAt (fun t : ℝ => planarGreenKernel a (t • z))
      (-(poissonKernel 0 a z) / (2 * Real.pi)) 1 := by
  obtain ⟨hza, hca⟩ := planarGreenKernel_boundary_ne ha hz
  have hf₁ := hasFDerivAt_planarNewtonianKernel_sub (sub_ne_zero.mp hza)
  have h₁ : HasDerivAt (fun t : ℝ => planarNewtonianKernel (t • z - a))
      ((-(2 * Real.pi)⁻¹ * (‖z - a‖ ^ 2)⁻¹) * ⟪z - a, z⟫_ℝ) 1 := by
    have hf : HasFDerivAt (fun w : ℂ => planarNewtonianKernel (w - a))
        ((-(2 * Real.pi)⁻¹ * (‖z - a‖ ^ 2)⁻¹) • innerSL ℝ (z - a))
        ((fun t : ℝ => t • z) 1) := by simpa only [one_smul] using hf₁
    simpa only [Function.comp_def, id_eq, one_smul, smul_apply, smul_eq_mul,
      innerSL_apply_apply] using
      hf.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).smul_const z)
  have hf₂ := hasFDerivAt_planarNewtonianKernel hca
  have h₂ : HasDerivAt
      (fun t : ℝ => planarNewtonianKernel (1 + t • (-(starRingEnd ℂ a * z))))
      ((-(2 * Real.pi)⁻¹ * (‖1 - starRingEnd ℂ a * z‖ ^ 2)⁻¹) *
        ⟪1 - starRingEnd ℂ a * z, -(starRingEnd ℂ a * z)⟫_ℝ) 1 := by
    have hf : HasFDerivAt planarNewtonianKernel
        ((-(2 * Real.pi)⁻¹ * (‖1 - starRingEnd ℂ a * z‖ ^ 2)⁻¹) •
          innerSL ℝ (1 - starRingEnd ℂ a * z))
        ((fun t : ℝ => 1 + t • (-(starRingEnd ℂ a * z))) 1) := by
      simpa only [one_smul, ← sub_eq_add_neg] using hf₂
    simpa only [Function.comp_def, id_eq, one_smul, smul_apply, smul_eq_mul,
      innerSL_apply_apply] using
      hf.comp_hasDerivAt 1
        (((hasDerivAt_id (1 : ℝ)).smul_const (-(starRingEnd ℂ a * z))).const_add 1)
  have harg (t : ℝ) : 1 - starRingEnd ℂ a * (t • z) =
      1 + t • (-(starRingEnd ℂ a * z)) := by
    rw [mul_smul_comm, smul_neg]
    abel
  have heq : (fun t : ℝ => planarGreenKernel a (t • z)) =
      fun t : ℝ => planarNewtonianKernel (t • z - a) -
        planarNewtonianKernel (1 + t • (-(starRingEnd ℂ a * z))) := by
    funext t
    rw [planarGreenKernel_def]
    rw [harg]
  rw [heq]
  have hnorm : ‖1 - starRingEnd ℂ a * z‖ = ‖z - a‖ := by
    have hsq := norm_sq_one_sub_conj_mul_sub_norm_sq_sub z a
    rw [hz] at hsq
    norm_num at hsq
    nlinarith [norm_nonneg (1 - starRingEnd ℂ a * z), norm_nonneg (z - a)]
  have hzsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h : ‖z‖ ^ 2 = 1 := by rw [hz]; norm_num
    rw [Complex.sq_norm, normSq_apply] at h
    nlinarith
  have hcore :
      (z.re * (z.re + (-a).re) + z.im * (z.im + (-a).im)) -
        ((-(starRingEnd ℂ a * z)).re *
          ((-(starRingEnd ℂ a * z)).re + (1 : ℂ).re) +
          (-(starRingEnd ℂ a * z)).im *
            ((-(starRingEnd ℂ a * z)).im + (1 : ℂ).im)) =
        1 - ‖a‖ ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]
    simp only [neg_re, neg_im, conj_re, conj_im, mul_re, mul_im, one_re, one_im,
      add_zero]
    nlinarith [hzsq]
  have hinnercore :
      ⟪z - a, z⟫_ℝ -
        ⟪1 - starRingEnd ℂ a * z, -(starRingEnd ℂ a * z)⟫_ℝ =
        1 - ‖a‖ ^ 2 := by
    simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      sub_re, sub_im, neg_re, neg_im, one_re, one_im] at hcore ⊢
    nlinarith [hcore]
  convert h₁.sub h₂ using 1
  · simp only [poissonKernel_def, sub_zero, hz, one_pow]
    rw [hnorm, ← hinnercore]
    ring

/-- The outward radial derivative of the unit-disk Green kernel, as an ordinary real
derivative. -/
@[simp] theorem deriv_planarGreenKernel_radial {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    deriv (fun t : ℝ => planarGreenKernel a ((t : ℂ) * z)) 1 =
      -(poissonKernel 0 a z) / (2 * Real.pi) := by
  simpa only [Complex.real_smul] using
    (hasDerivAt_planarGreenKernel_radial ha hz).deriv

/-- The spatial derivative of the unit-disk Green kernel on the outward unit normal equals
the negative Poisson kernel divided by `2π`. -/
@[simp] theorem fderiv_planarGreenKernel_normal {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    (fderiv ℝ (planarGreenKernel a) z) z =
      -(poissonKernel 0 a z) / (2 * Real.pi) := by
  have hdiff := differentiableAt_planarGreenKernel_boundary ha hz
  have hcurve := ((hasDerivAt_id (1 : ℝ)).smul_const z).differentiableAt
  have hd := fderiv_comp_deriv (f := fun t : ℝ => t • z)
    (l := planarGreenKernel a) 1 (by simpa only [one_smul] using hdiff) hcurve
  have hcurve_deriv : deriv (fun t : ℝ => t • z) 1 = z := by
    simpa using ((hasDerivAt_id (1 : ℝ)).smul_const z).deriv
  have hradial : deriv (fun t : ℝ => planarGreenKernel a (t • z)) 1 =
      -(poissonKernel 0 a z) / (2 * Real.pi) := by
    simpa only [Complex.real_smul] using deriv_planarGreenKernel_radial ha hz
  simpa only [Function.comp_def, one_smul, hcurve_deriv, hradial] using hd.symm

/-- On the boundary of any positive-radius disk, the derivative of the Green kernel along
the radius from the center to the boundary point is the negative of Mathlib's Poisson kernel
divided by `2π`. The derivative uses the dimensionless radial parameter `t`; the unit outward normal
derivative is obtained by dividing by the disk radius. -/
theorem hasDerivAt_planarGreenKernelDisk_radial {c a z : ℂ} {R : ℝ}
    (hR : 0 < R) (ha : ‖a - c‖ < R) (hz : ‖z - c‖ = R) :
    HasDerivAt (fun t : ℝ => planarGreenKernelDisk c R a (c + t • (z - c)))
      (-(poissonKernel c a z) / (2 * Real.pi)) 1 := by
  have hz' : ‖R⁻¹ • (z - c)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, hz]
    exact inv_mul_cancel₀ hR.ne'
  have hP : poissonKernel 0 (R⁻¹ • (a - c)) (R⁻¹ • (z - c)) =
      poissonKernel c a z := by
    have hRne : R ≠ 0 := hR.ne'
    simp only [poissonKernel_def, sub_zero, sub_sub_sub_cancel_right, ← smul_sub,
      norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    field_simp
  have hfun : (fun t : ℝ => planarGreenKernelDisk c R a (c + t • (z - c))) =
      fun t : ℝ => planarGreenKernel (R⁻¹ • (a - c)) (t • (R⁻¹ • (z - c))) := by
    funext t
    rw [planarGreenKernelDisk_def]
    congr 1
    simp only [add_sub_cancel_left, smul_smul]
    rw [mul_comm R⁻¹ t]
  rw [hfun, ← hP]
  exact hasDerivAt_planarGreenKernel_radial (norm_inv_smul_sub_lt_one hR ha) hz'

/-- The radial derivative of the disk Green kernel in terms of the Poisson kernel. -/
@[simp] theorem deriv_planarGreenKernelDisk_radial {c a z : ℂ} {R : ℝ}
    (hR : 0 < R) (ha : ‖a - c‖ < R) (hz : ‖z - c‖ = R) :
    deriv (fun t : ℝ => planarGreenKernelDisk c R a (c + (t : ℂ) * (z - c))) 1 =
      -(poissonKernel c a z) / (2 * Real.pi) := by
  simpa only [Complex.real_smul] using
    (hasDerivAt_planarGreenKernelDisk_radial hR ha hz).deriv

/-- The spatial derivative of the disk Green kernel on the outward unit normal is the
negative Poisson kernel divided by `2πR`. -/
@[simp] theorem fderiv_planarGreenKernelDisk_normal {c a z : ℂ} {R : ℝ}
    (hR : 0 < R) (ha : ‖a - c‖ < R) (hz : ‖z - c‖ = R) :
    (fderiv ℝ (planarGreenKernelDisk c R a) z) (R⁻¹ • (z - c)) =
      -(poissonKernel c a z) / (2 * Real.pi * R) := by
  have hdiff := differentiableAt_planarGreenKernelDisk_boundary hR ha hz
  have hcz : c + (1 : ℝ) • (z - c) = z := by
    simp only [one_smul]
    abel
  have hcurve := (((hasDerivAt_id (1 : ℝ)).smul_const (z - c)).const_add c).differentiableAt
  have hd := fderiv_comp_deriv (f := fun t : ℝ => c + t • (z - c))
    (l := planarGreenKernelDisk c R a) 1
    (by simpa only [hcz] using hdiff) hcurve
  have hcurve_deriv : deriv (fun t : ℝ => c + t • (z - c)) 1 = z - c := by
    simpa using (((hasDerivAt_id (1 : ℝ)).smul_const (z - c)).const_add c).deriv
  have hradial_deriv :
      deriv (fun t : ℝ => planarGreenKernelDisk c R a (c + t • (z - c))) 1 =
        -(poissonKernel c a z) / (2 * Real.pi) := by
    simpa only [Complex.real_smul] using deriv_planarGreenKernelDisk_radial hR ha hz
  have hradial : (fderiv ℝ (planarGreenKernelDisk c R a) z) (z - c) =
      -(poissonKernel c a z) / (2 * Real.pi) := by
    simpa only [Function.comp_def, hcz, hcurve_deriv, hradial_deriv] using hd.symm
  rw [map_smul, smul_eq_mul, hradial]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end TauCeti

end
