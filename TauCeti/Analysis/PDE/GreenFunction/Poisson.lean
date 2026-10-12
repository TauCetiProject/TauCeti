/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.GreenFunction.Disk
public import TauCeti.Analysis.PDE.GreenFunction.Ball
public import TauCeti.Analysis.Complex.Poisson.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Gradient
import Mathlib.Analysis.Complex.Harmonic.Poisson

/-!
# Planar Poisson kernels and the Euclidean ball kernel

The outward radial derivative of the Dirichlet Green kernel on a planar disk is the negative
of Mathlib's Poisson kernel, divided by `2π`, when the radius is parametrized from zero to one.
This identifies the boundary term in Green's representation formula with the existing Poisson
kernel, both on the unit disk and after translation and dilation.

The file also reconciles the two-dimensional specialization of the Euclidean-ball Poisson
kernel with Mathlib's complex kernel.  Consequently its circle average is normalized at every
pole in the disk, and it gives the Poisson representation of harmonic functions with respect to
arc length on the unit circle.

The normalization follows Evans, *Partial Differential Equations*, Chapter 2, §2.2.
-/

public section

noncomputable section

namespace TauCeti

open Complex InnerProductSpace

/-- The boundary inner-product identity used in the radial derivative of the planar Green
kernel. -/
private theorem planarGreenKernel_boundary_inner_sub {a z : ℂ} (hz : ‖z‖ = 1) :
    ⟪z - a, z⟫_ℝ -
      ⟪1 - starRingEnd ℂ a * z, -(starRingEnd ℂ a * z)⟫_ℝ =
      1 - ‖a‖ ^ 2 := by
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
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    sub_re, sub_im, neg_re, neg_im, one_re, one_im] at hcore ⊢
  nlinarith [hcore]

/-- On the boundary of the unit disk, the outward radial derivative of the Green kernel
with pole `a` is the negative of the Poisson kernel divided by `2π`. -/
theorem hasDerivAt_planarGreenKernel_radial {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    HasDerivAt (fun t : ℝ => planarGreenKernel a (t • z))
      (-(poissonKernel 0 a z) / (2 * Real.pi)) 1 := by
  have hnorm : ‖1 - starRingEnd ℂ a * z‖ = ‖z - a‖ := by
    have hsq := norm_sq_one_sub_conj_mul_sub_norm_sq_sub z a
    rw [hz] at hsq
    norm_num at hsq
    nlinarith [norm_nonneg (1 - starRingEnd ℂ a * z), norm_nonneg (z - a)]
  obtain ⟨hza, hca⟩ :=
    sub_ne_zero_and_one_sub_conj_mul_ne_zero_of_norm_lt_one_of_norm_eq_one ha hz
  have h₁ : HasDerivAt (fun t : ℝ => planarNewtonianKernel (t • z - a))
      ((-(2 * Real.pi)⁻¹ * (‖z - a‖ ^ 2)⁻¹) * ⟪z - a, z⟫_ℝ) 1 := by
    simpa only [one_smul, sub_eq_add_neg, add_comm] using
      hasDerivAt_planarNewtonianKernel_affine (-a) z (t := 1)
        (by simpa only [one_smul, add_comm, ← sub_eq_add_neg] using hza)
  have h₂ : HasDerivAt
      (fun t : ℝ => planarNewtonianKernel (1 + t • (-(starRingEnd ℂ a * z))))
      ((-(2 * Real.pi)⁻¹ * (‖1 - starRingEnd ℂ a * z‖ ^ 2)⁻¹) *
        ⟪1 - starRingEnd ℂ a * z, -(starRingEnd ℂ a * z)⟫_ℝ) 1 := by
    simpa only [one_smul, sub_eq_add_neg] using
      hasDerivAt_planarNewtonianKernel_affine 1 (-(starRingEnd ℂ a * z)) (t := 1)
        (by simpa only [one_smul, ← sub_eq_add_neg] using hca)
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
  convert h₁.sub h₂ using 1
  · simp only [poissonKernel_def, sub_zero, hz, one_pow]
    rw [hnorm, ← planarGreenKernel_boundary_inner_sub hz]
    ring

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
    exact (hasDerivAt_planarGreenKernel_radial ha hz).deriv
  simpa only [Function.comp_def, one_smul, hcurve_deriv, hradial] using hd.symm

/-- On the boundary of any positive-radius disk, the derivative of the Green kernel along
the radius from the center to the boundary point is the negative of Mathlib's Poisson kernel
divided by `2π`. The derivative uses the dimensionless radial parameter `t`; the unit outward normal
derivative is obtained by dividing by the disk radius. -/
theorem hasDerivAt_planarGreenKernelDisk_radial {c a z : ℂ} {R : ℝ}
    (hR : 0 < R) (ha : ‖a - c‖ < R) (hz : ‖z - c‖ = R) :
    HasDerivAt (fun t : ℝ => planarGreenKernelDisk c R a (c + t • (z - c)))
      (-(poissonKernel c a z) / (2 * Real.pi)) 1 := by
  have hz' := (norm_inv_smul_eq_one_iff hR).2 hz
  have hfun : (fun t : ℝ => planarGreenKernelDisk c R a (c + t • (z - c))) =
      fun t : ℝ => planarGreenKernel (R⁻¹ • (a - c)) (t • (R⁻¹ • (z - c))) := by
    funext t
    rw [planarGreenKernelDisk_def]
    congr 1
    simp only [add_sub_cancel_left, smul_smul]
    rw [mul_comm R⁻¹ t]
  rw [hfun, ← poissonKernel_inv_mul_sub (Complex.ofReal_ne_zero.mpr hR.ne')]
  simp only [← Complex.ofReal_inv, Complex.real_smul]
  exact hasDerivAt_planarGreenKernel_radial ((norm_inv_smul_lt_one_iff hR).2 ha) hz'

/-- The spatial derivative of the disk Green kernel on the outward unit normal is the
negative Poisson kernel divided by `2πR`. -/
@[simp] theorem fderiv_planarGreenKernelDisk_normal {c a z : ℂ} {R : ℝ}
    (hR : 0 < R) (ha : ‖a - c‖ < R) (hz : ‖z - c‖ = R) :
    (fderiv ℝ (planarGreenKernelDisk c R a) z) ((R : ℂ)⁻¹ * (z - c)) =
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
    exact (hasDerivAt_planarGreenKernelDisk_radial hR ha hz).deriv
  have hradial : (fderiv ℝ (planarGreenKernelDisk c R a) z) (z - c) =
      -(poissonKernel c a z) / (2 * Real.pi) := by
    simpa only [Function.comp_def, hcz, hcurve_deriv, hradial_deriv] using hd.symm
  rw [← Complex.ofReal_inv, ← Complex.real_smul, map_smul, smul_eq_mul, hradial]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-! ### Compatibility with the Euclidean-ball Poisson kernel -/

/-- In two dimensions, the Euclidean-ball Poisson kernel, transported along the standard
orthonormal coordinates of `ℂ`, is Mathlib's Poisson kernel divided by the circumference
`2π` of the unit circle. -/
theorem ballPoissonKernel_two_repr {a z : ℂ} (hz : ‖z‖ = 1) :
    2 * Real.pi * ballPoissonKernel 2
        (Complex.orthonormalBasisOneI.repr a) (Complex.orthonormalBasisOneI.repr z) =
      poissonKernel 0 a z := by
  rw [ballPoissonKernel_def, poissonKernel_def]
  simp only [sub_zero, LinearIsometryEquiv.norm_map, hz, one_pow]
  rw [MeasureTheory.measureReal_def, EuclideanSpace.volume_ball_fin_two]
  rw [ENNReal.toReal_mul]
  norm_num [ENNReal.toReal_ofReal Real.pi_nonneg]
  rw [← map_sub, LinearIsometryEquiv.norm_map, norm_sub_rev]
  field_simp [Real.pi_ne_zero]

/-- Scaling by the two-dimensional ball Poisson kernel under `circleAverage` is `(2π)⁻¹` times
scaling by Mathlib's Poisson kernel. This form applies to arbitrary vector-valued boundary data;
no harmonicity or integrability hypothesis is needed for the identity. -/
theorem circleAverage_ballPoissonKernel_two_fun_smul_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) {a : ℂ} :
    Real.circleAverage (fun z =>
      ballPoissonKernel 2 (Complex.orthonormalBasisOneI.repr a)
        (Complex.orthonormalBasisOneI.repr z) • f z) 0 1 =
      (2 * Real.pi)⁻¹ •
        Real.circleAverage (fun z => poissonKernel 0 a z • f z) 0 1 := by
  calc
    Real.circleAverage (fun z =>
        ballPoissonKernel 2 (Complex.orthonormalBasisOneI.repr a)
          (Complex.orthonormalBasisOneI.repr z) • f z) 0 1 =
        Real.circleAverage (fun z => (2 * Real.pi)⁻¹ • (poissonKernel 0 a z • f z)) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
      simp only
      rw [smul_smul, ← ballPoissonKernel_two_repr hznorm]
      field_simp [Real.pi_ne_zero]
    _ = (2 * Real.pi)⁻¹ •
        Real.circleAverage (fun z => poissonKernel 0 a z • f z) 0 1 :=
      Real.circleAverage_fun_smul

/-- The two-dimensional ball Poisson kernel represents a function harmonic on the open unit disk
and continuous on its closure by integration against arc length on the unit circle. Since
`circleAverage` is normalized by `2π`, the right side carries the reciprocal factor. -/
theorem circleAverage_ballPoissonKernel_two_fun_mul {f : ℂ → ℝ} {a : ℂ}
    (hf : HarmonicContOnCl f (Metric.ball 0 1)) (ha : ‖a‖ < 1) :
    Real.circleAverage (fun z =>
      ballPoissonKernel 2 (Complex.orthonormalBasisOneI.repr a)
        (Complex.orthonormalBasisOneI.repr z) * f z) 0 1 =
      (2 * Real.pi)⁻¹ * f a := by
  have hw : a ∈ Metric.ball (0 : ℂ) 1 := by simpa [Metric.mem_ball] using ha
  have h := circleAverage_ballPoissonKernel_two_fun_smul_eq f (a := a)
  rw [← Pi.smul_def' (poissonKernel 0 a) f, hf.circleAverage_poissonKernel_smul hw] at h
  simpa only [smul_eq_mul] using h

/-- The circle average of the two-dimensional ball Poisson kernel is `(2π)⁻¹`; equivalently,
its integral against arc length on the unit circle is one. -/
theorem circleAverage_ballPoissonKernel_two {a : ℂ} (ha : ‖a‖ < 1) :
    Real.circleAverage (fun z => ballPoissonKernel 2
      (Complex.orthonormalBasisOneI.repr a) (Complex.orthonormalBasisOneI.repr z)) 0 1 =
      (2 * Real.pi)⁻¹ := by
  simpa using circleAverage_ballPoissonKernel_two_fun_mul
    (f := fun _ : ℂ => (1 : ℝ)) harmonicContOnCl_const ha

end TauCeti

end
