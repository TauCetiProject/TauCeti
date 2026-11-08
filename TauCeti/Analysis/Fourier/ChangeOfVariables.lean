/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import TauCeti.MeasureTheory.Function.Lp.Dilation

/-!
# Linear change of variables for the Fourier transform

Precomposing a function by a continuous real linear automorphism rescales its Fourier transform
by the inverse absolute determinant and precomposes it by the adjoint of the inverse. This is the
change of coordinates needed to transport Fourier identities from the standard integer lattice
to an arbitrary full lattice. For a dilation `x ↦ c • x` it reads
`𝓕 (f (c • ·)) y = |c ^ n|⁻¹ • 𝓕 f (c⁻¹ • y)` in dimension `n`, so that dilating a function does not
change the `L¹` norm of its Fourier transform, while replacing `g` by `g (R⁻¹ • ·)`, `R > 0`,
multiplies the `Lʳ` norm of its inverse Fourier transform by `R ^ (n - n / r)`.

The Jacobian factor comes from Mathlib's
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`. The formulas use the total Bochner
integral, so no integrability hypothesis is necessary. They apply to functions with values in any
complex normed space, including Schwartz functions by coercion.

## Main results

* `ContinuousLinearEquiv.fourier_comp`: change of variables for the Fourier transform.
* `ContinuousLinearEquiv.fourierInv_comp`: the corresponding inverse-transform formula.
* `TauCeti.fourier_comp_smul`, `TauCeti.fourierInv_comp_smul`: the dilation formulas.
* `TauCeti.integral_norm_fourierInv_comp_smul`: dilation preserves the `L¹` norm of the inverse
  Fourier transform.
* `TauCeti.eLpNorm_fourierInv_comp_inv_smul`: dilation rescales the `Lʳ` norm of the inverse
  Fourier transform.
-/

public section

open MeasureTheory Module
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Fourier change of variables under a real linear automorphism. The frequency transforms by
the adjoint of the inverse, and the scalar is the inverse absolute determinant. -/
theorem _root_.ContinuousLinearEquiv.fourier_comp (A : E ≃L[ℝ] E) (f : E → F) (y : E) :
    𝓕 (f ∘ A) y = |A.toLinearEquiv.toLinearMap.det|⁻¹ •
      𝓕 f (ContinuousLinearMap.adjoint (A.symm : E →L[ℝ] E) y) := by
  have hinner (x : E) :
      ⟪A x, ContinuousLinearMap.adjoint (A.symm : E →L[ℝ] E) y⟫ = ⟪x, y⟫ := by
    simp [ContinuousLinearMap.adjoint_inner_right]
  simp only [Real.fourier_eq, Function.comp_apply]
  simp_rw [← hinner]
  have hcov := integral_map_equiv (μ := volume) A.toHomeomorph.toMeasurableEquiv
    (fun x : E ↦ 𝐞 (-⟪x, ContinuousLinearMap.adjoint (A.symm : E →L[ℝ] E) y⟫) • f x)
  simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph] at hcov
  rw [← hcov]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    A.toLinearEquiv.isUnit_det'.ne_zero
  simp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] at hmap
  rw [hmap, integral_smul_measure]
  simp [abs_inv]

/-- The inverse Fourier transform has the same linear change-of-variables law. -/
theorem _root_.ContinuousLinearEquiv.fourierInv_comp (A : E ≃L[ℝ] E) (f : E → F) (y : E) :
    𝓕⁻ (f ∘ A) y = |A.toLinearEquiv.toLinearMap.det|⁻¹ •
      𝓕⁻ f (ContinuousLinearMap.adjoint (A.symm : E →L[ℝ] E) y) := by
  simp only [Real.fourierInv_eq_fourier_neg, A.fourier_comp, map_neg]

/-- **Fourier transform of a dilation**: `𝓕 (f (c • ·)) y = |c ^ n|⁻¹ • 𝓕 f (c⁻¹ • y)`, where
`n` is the dimension. -/
theorem fourier_comp_smul (f : E → F) {c : ℝ} (hc : c ≠ 0) (y : E) :
    𝓕 (fun x ↦ f (c • x)) y = |c ^ finrank ℝ E|⁻¹ • 𝓕 f (c⁻¹ • y) := by
  have hinner (x : E) : ⟪x, y⟫ = ⟪c • x, c⁻¹ • y⟫ := by
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  simp only [Real.fourier_eq]
  simp_rw [hinner]
  rw [Measure.integral_comp_smul volume (fun x ↦ 𝐞 (-⟪x, c⁻¹ • y⟫) • f x), abs_inv]

/-- **Inverse Fourier transform of a dilation**:
`𝓕⁻ (f (c • ·)) y = |c ^ n|⁻¹ • 𝓕⁻ f (c⁻¹ • y)`, where `n` is the dimension. -/
theorem fourierInv_comp_smul (f : E → F) {c : ℝ} (hc : c ≠ 0) (y : E) :
    𝓕⁻ (fun x ↦ f (c • x)) y = |c ^ finrank ℝ E|⁻¹ • 𝓕⁻ f (c⁻¹ • y) := by
  simp only [Real.fourierInv_eq_fourier_neg, fourier_comp_smul f hc, smul_neg]

/-- Dilating a function does not change the `L¹` norm of its inverse Fourier transform:
`∫ ‖𝓕⁻ (f (c • ·))‖ = ∫ ‖𝓕⁻ f‖`. -/
theorem integral_norm_fourierInv_comp_smul (f : E → F) {c : ℝ} (hc : c ≠ 0) :
    ∫ y, ‖𝓕⁻ (fun x ↦ f (c • x)) y‖ = ∫ y, ‖𝓕⁻ f y‖ := by
  simp_rw [fourierInv_comp_smul f hc, norm_smul, norm_inv, Real.norm_eq_abs, abs_abs]
  rw [integral_const_mul, Measure.integral_comp_inv_smul volume (fun y ↦ ‖𝓕⁻ f y‖), smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.2 (pow_ne_zero _ hc)), one_mul]

/-- **Dilating a function rescales the `Lʳ` norm of its inverse Fourier transform:** for `R > 0`,
the inverse Fourier transform of `ξ ↦ g (R⁻¹ • ξ)` has `Lʳ` norm `R ^ (n - n / r)` times that of
`𝓕⁻ g`, where `n` is the dimension. -/
theorem eLpNorm_fourierInv_comp_inv_smul (g : E → F) {R : ℝ} (hR : 0 < R) (r : ℝ≥0∞) :
    eLpNorm (𝓕⁻ fun ξ ↦ g (R⁻¹ • ξ)) r volume =
      ENNReal.ofReal (R ^ ((finrank ℝ E : ℝ) - finrank ℝ E / r.toReal)) *
        eLpNorm (𝓕⁻ g) r volume := by
  have h : (𝓕⁻ fun ξ ↦ g (R⁻¹ • ξ)) =
      (R ^ finrank ℝ E : ℝ) • fun x ↦ 𝓕⁻ g ((R⁻¹)⁻¹ • x) := by
    ext x
    simp [fourierInv_comp_smul g (inv_ne_zero hR.ne'), abs_of_pos hR]
  rw [h, eLpNorm_const_smul, Measure.eLpNorm_comp_inv_smul volume _ (inv_ne_zero hR.ne'),
    abs_of_pos (inv_pos.2 hR), ← mul_assoc,
    ← ofReal_norm, Real.norm_eq_abs, abs_of_pos (by positivity),
    ← ENNReal.ofReal_mul (by positivity), Real.inv_rpow hR.le, ← Real.rpow_natCast,
    ← Real.rpow_neg hR.le, ← Real.rpow_add hR, sub_eq_add_neg]

end TauCeti
