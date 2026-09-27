/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.GreenFunction.Disk
public import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

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

open Complex

/-- The logarithmic norm of a real affine line in `ℂ` has the expected derivative away from
the zero of the line. -/
private theorem hasDerivAt_log_norm_real_smul_add (z w : ℂ) (h : z + w ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖t • z + w‖)
      ((z.re * (z.re + w.re) + z.im * (z.im + w.im)) / ‖z + w‖ ^ 2) 1 := by
  have hsq : HasDerivAt (fun t : ℝ => ‖t • z + w‖ ^ 2)
      (2 * (z.re * (z.re + w.re) + z.im * (z.im + w.im))) 1 := by
    convert (((hasDerivAt_id (1 : ℝ)).smul_const z).const_add w).norm_sq using 1
    · ext t
      simp only [id_eq, add_comm]
    · simp only [id_eq, one_smul, Complex.inner, Complex.mul_re, Complex.conj_re,
        Complex.conj_im, add_re, add_im]
      ring
  have hlog := (Real.hasDerivAt_log (by simpa using h)).comp 1 hsq
  have hfun : (fun t : ℝ => Real.log ‖t • z + w‖) =
      fun t : ℝ => (Real.log (‖t • z + w‖ ^ 2)) / 2 := by
    funext t
    rw [Real.log_pow]
    ring
  rw [hfun]
  convert hlog.div_const 2 using 1 <;> simp [Complex.sq_norm]; ring

private theorem differentiableAt_planarGreenKernel {a z : ℂ}
    (hza : z - a ≠ 0) (hca : 1 - starRingEnd ℂ a * z ≠ 0) :
    DifferentiableAt ℝ (planarGreenKernel a) z := by
  have hinner1 : DifferentiableAt ℝ (fun w : ℂ => w - a) z := by
    fun_prop
  have h₁ : DifferentiableAt ℝ (fun w : ℂ => Real.log ‖w - a‖) z :=
    by simpa only [Function.comp_def, id_eq] using
      (((differentiableAt_id : DifferentiableAt ℝ (id : ℂ → ℂ) (z - a)).norm ℂ hza).log
        (norm_ne_zero_iff.mpr hza)).comp z hinner1
  have hinner : DifferentiableAt ℝ (fun w : ℂ => 1 - starRingEnd ℂ a * w) z := by
    fun_prop
  have h₂ : DifferentiableAt ℝ
      (fun w : ℂ => Real.log ‖1 - starRingEnd ℂ a * w‖) z :=
    by simpa only [Function.comp_def, id_eq] using
      (((differentiableAt_id : DifferentiableAt ℝ (id : ℂ → ℂ)
        (1 - starRingEnd ℂ a * z)).norm ℂ hca).log
        (norm_ne_zero_iff.mpr hca)).comp z hinner
  convert (h₁.const_mul (-(2 * Real.pi)⁻¹)).sub
    (h₂.const_mul (-(2 * Real.pi)⁻¹)) using 1
  ext w
  simp only [planarGreenKernel_def, planarNewtonianKernel_def, Pi.sub_apply]

/-- At a boundary point of the unit disk, neither logarithmic argument in the planar Green
kernel vanishes when the pole lies inside the disk. -/
private theorem planarGreenKernel_boundary_ne {a z : ℂ}
    (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    z - a ≠ 0 ∧ 1 - starRingEnd ℂ a * z ≠ 0 := by
  have hza : z - a ≠ 0 := by
    intro h
    have : z = a := sub_eq_zero.mp h
    rw [this] at hz
    linarith
  have hca : 1 - starRingEnd ℂ a * z ≠ 0 := by
    intro h
    have heq : starRingEnd ℂ a * z = 1 := (sub_eq_zero.mp h).symm
    have hnorm : ‖starRingEnd ℂ a * z‖ = 1 := by rw [heq]; simp
    rw [norm_mul, Complex.norm_conj, hz, mul_one] at hnorm
    linarith
  exact ⟨hza, hca⟩

/-- The planar Green kernel is differentiable at a boundary point of the unit disk when its
pole lies inside the disk. -/
theorem differentiableAt_planarGreenKernel_boundary {a z : ℂ}
    (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    DifferentiableAt ℝ (planarGreenKernel a) z := by
  obtain ⟨hza, hca⟩ := planarGreenKernel_boundary_ne ha hz
  exact differentiableAt_planarGreenKernel hza hca

/-- On the boundary of the unit disk, the outward radial derivative of the Green kernel
with pole `a` is the negative of the Poisson kernel divided by `2π`. -/
theorem hasDerivAt_planarGreenKernel_radial {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    HasDerivAt (fun t : ℝ => planarGreenKernel a (t • z))
      (-(poissonKernel 0 a z) / (2 * Real.pi)) 1 := by
  obtain ⟨hza, hca⟩ := planarGreenKernel_boundary_ne ha hz
  have h₁ := hasDerivAt_log_norm_real_smul_add z (-a)
    (by simpa only [sub_eq_add_neg] using hza)
  have h₂ := hasDerivAt_log_norm_real_smul_add
    (-(starRingEnd ℂ a * z)) 1 (by simpa only [neg_add_eq_sub] using hca)
  have harg (t : ℝ) : 1 - starRingEnd ℂ a * (t • z) =
      t • (-(starRingEnd ℂ a * z)) + 1 := by
    rw [mul_smul_comm, smul_neg]
    abel
  have heq : (fun t : ℝ => planarGreenKernel a (t • z)) =
      fun t : ℝ => -(2 * Real.pi)⁻¹ * Real.log ‖t • z + -a‖ -
        (-(2 * Real.pi)⁻¹ * Real.log ‖t • (-(starRingEnd ℂ a * z)) + 1‖) := by
    funext t
    rw [planarGreenKernel_def, planarNewtonianKernel_def, planarNewtonianKernel_def]
    rw [harg]
    simp only [sub_eq_add_neg]
  rw [heq]
  have hmul : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hfactor : z * (1 - starRingEnd ℂ z * a) = z - a := by
    calc
      z * (1 - starRingEnd ℂ z * a) = z - (z * starRingEnd ℂ z) * a := by ring
      _ = z - a := by rw [hmul, one_mul]
  have hnorm : ‖1 - starRingEnd ℂ a * z‖ = ‖z - a‖ := by
    calc
      ‖1 - starRingEnd ℂ a * z‖ = ‖starRingEnd ℂ (1 - starRingEnd ℂ z * a)‖ := by
        simp [mul_comm]
      _ = ‖1 - starRingEnd ℂ z * a‖ := Complex.norm_conj _
      _ = ‖z * (1 - starRingEnd ℂ z * a)‖ := by rw [norm_mul, hz, one_mul]
      _ = ‖z - a‖ := by rw [hfactor]
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
  convert ((h₁.const_mul (-(2 * Real.pi)⁻¹)).sub
    (h₂.const_mul (-(2 * Real.pi)⁻¹))) using 1
  · simp only [poissonKernel_def, sub_zero, hz, one_pow]
    rw [← sub_eq_add_neg z a, neg_add_eq_sub, hnorm, ← hcore]
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
theorem fderiv_planarGreenKernel_normal {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
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

/-- The Green kernel of a positive-radius disk is differentiable at a boundary point when
its pole lies inside the disk. -/
theorem differentiableAt_planarGreenKernelDisk_boundary {c a z : ℂ} {R : ℝ}
    (hR : 0 < R) (ha : ‖a - c‖ < R) (hz : ‖z - c‖ = R) :
    DifferentiableAt ℝ (planarGreenKernelDisk c R a) z := by
  have hz' : ‖R⁻¹ • (z - c)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, hz]
    exact inv_mul_cancel₀ hR.ne'
  have hcoord : DifferentiableAt ℝ (fun w : ℂ => R⁻¹ • (w - c)) z := by
    fun_prop
  -- The disk kernel is opaque here, so use its public equation to rewrite the whole function.
  have hfun : planarGreenKernelDisk c R a =
      fun w : ℂ => planarGreenKernel (R⁻¹ • (a - c)) (R⁻¹ • (w - c)) :=
    funext (planarGreenKernelDisk_def c R a)
  rw [hfun]
  simpa only [Function.comp_def] using
    (differentiableAt_planarGreenKernel_boundary
      (norm_inv_smul_sub_lt_one hR ha) hz').comp z hcoord

/-- The spatial derivative of the disk Green kernel on the outward unit normal is the
negative Poisson kernel divided by `2πR`. -/
theorem fderiv_planarGreenKernelDisk_normal {c a z : ℂ} {R : ℝ}
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
