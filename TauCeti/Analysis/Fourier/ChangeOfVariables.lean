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
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.MeasureTheory.Function.Lp.Dilation

/-!
# Linear change of variables for the Fourier transform

Precomposing a function by a continuous real linear automorphism rescales its Fourier transform
by the inverse absolute determinant and precomposes it by the adjoint of the inverse. This is the
change of coordinates needed to transport Fourier identities from the standard integer lattice
to an arbitrary full lattice. For a dilation `x ↦ c • x` it reads
`𝓕 (f (c • ·)) y = |c ^ n|⁻¹ • 𝓕 f (c⁻¹ • y)` in dimension `n`, so that dilating a function does not
change the `L¹` norm of its Fourier transform and multiplies the `k`-th moment
`∫ ‖y‖ ^ k ‖𝓕⁻ f y‖` of its inverse Fourier transform by `|c| ^ k`, while replacing `g` by
`g (R⁻¹ • ·)`, `R > 0`, multiplies the `Lʳ` norm of its inverse Fourier transform by
`R ^ (n - n / r)`.

The Jacobian factor comes from Mathlib's
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`. The formulas use the total Bochner
integral, so no integrability hypothesis is necessary. They apply to functions with values in any
complex normed space, including Schwartz functions by coercion.

## Main results

* `ContinuousLinearEquiv.fourier_comp`: change of variables for the Fourier transform.
* `ContinuousLinearEquiv.fourierInv_comp`: the corresponding inverse-transform formula.
* `TauCeti.fourier_comp_smul`, `TauCeti.fourierInv_comp_smul`: the dilation formulas.
* `TauCeti.support_fourier_comp_smul`: dilating a function by `c` dilates the support of its
  Fourier transform by `c`.
* `TauCeti.integral_norm_pow_mul_norm_fourierInv_comp_smul`: dilation by `c` multiplies the
  `k`-th moment of the inverse Fourier transform by `|c| ^ k`.
* `TauCeti.integral_norm_fourierInv_comp_smul`: dilation preserves the `L¹` norm of the inverse
  Fourier transform.
* `TauCeti.eLpNorm_fourierInv_comp_inv_smul`: dilation rescales the `Lʳ` norm of the inverse
  Fourier transform.
* `TauCeti.fourier_comp_sub_const`, `TauCeti.support_fourier_comp_sub_const`: translating a
  function by `a` multiplies its Fourier transform by the character `𝐞 (-⟪a, ·⟫)`, so the support
  of the Fourier transform does not change.
* `TauCeti.fourier_fourierChar_smul`: modulation by the character `𝐞 ⟪·, c⟫` translates the
  Fourier transform by `c`.
* `TauCeti.fourier_smul_const`: the Fourier transform of `f · • v` is `𝓕 f · • v`.
* `TauCeti.exp_inner_mul_I_eq_fourierChar`: the exponential `exp(i ⟪y, ξ⟫)` is the Fourier
  character at the frequency `ξ / 2π`.
-/

public section

open MeasureTheory Module
open scoped ENNReal FourierTransform RealInnerProductSpace Real Pointwise

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
`n` is the dimension. For `c = 0` both sides vanish, or agree trivially in dimension zero. -/
theorem fourier_comp_smul (f : E → F) (c : ℝ) (y : E) :
    𝓕 (fun x ↦ f (c • x)) y = |c ^ finrank ℝ E|⁻¹ • 𝓕 f (c⁻¹ • y) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rcases subsingleton_or_nontrivial E with hE | hE
    · simp only [Real.fourier_eq, finrank_zero_of_subsingleton, pow_zero, abs_one, inv_one,
        one_smul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      simp [Subsingleton.elim x 0, Subsingleton.elim y 0]
    · have hn : finrank ℝ E ≠ 0 := (finrank_pos (R := ℝ) (M := E)).ne'
      simp only [Real.fourier_eq, zero_pow hn, abs_zero, inv_zero, zero_smul]
      by_cases hi : Integrable (fun x : E ↦ 𝐞 (-⟪x, y⟫) • f 0)
      · have h := hi.norm
        simp only [Circle.norm_smul] at h
        rw [integrable_const_iff] at h
        rcases h with h | h
        · simp [norm_eq_zero.1 h]
        · exact absurd (measure_univ_of_isAddLeftInvariant (volume : Measure E))
            (measure_lt_top (volume : Measure E) Set.univ).ne
      · exact integral_undef hi
  · have hinner (x : E) : ⟪x, y⟫ = ⟪c • x, c⁻¹ • y⟫ := by
      rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    simp only [Real.fourier_eq]
    simp_rw [hinner]
    rw [Measure.integral_comp_smul volume (fun x ↦ 𝐞 (-⟪x, c⁻¹ • y⟫) • f x), abs_inv]

/-- **Frequencies of a dilation**: the Fourier transform of `f (c • ·)` is supported on the dilate
`c • support (𝓕 f)` of the support of `𝓕 f`. -/
theorem support_fourier_comp_smul (f : E → F) {c : ℝ} (hc : c ≠ 0) :
    Function.support (𝓕 (fun x ↦ f (c • x))) = c • Function.support (𝓕 f) := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc, Function.mem_support, Function.mem_support,
    fourier_comp_smul f, smul_ne_zero_iff_right (by simp [hc])]

/-- **Inverse Fourier transform of a dilation**:
`𝓕⁻ (f (c • ·)) y = |c ^ n|⁻¹ • 𝓕⁻ f (c⁻¹ • y)`, where `n` is the dimension. -/
theorem fourierInv_comp_smul (f : E → F) (c : ℝ) (y : E) :
    𝓕⁻ (fun x ↦ f (c • x)) y = |c ^ finrank ℝ E|⁻¹ • 𝓕⁻ f (c⁻¹ • y) := by
  simp only [Real.fourierInv_eq_fourier_neg, fourier_comp_smul f, smul_neg]

/-- Dilating a function by `c` multiplies the `k`-th moment of its inverse Fourier transform by
`|c| ^ k`: `∫ ‖y‖ ^ k ‖𝓕⁻ (f (c • ·)) y‖ = |c| ^ k ∫ ‖y‖ ^ k ‖𝓕⁻ f y‖`. -/
theorem integral_norm_pow_mul_norm_fourierInv_comp_smul (f : E → F) (k : ℕ) {c : ℝ}
    (hc : c ≠ 0) :
    ∫ y, ‖y‖ ^ k * ‖𝓕⁻ (fun x ↦ f (c • x)) y‖ = |c| ^ k * ∫ y, ‖y‖ ^ k * ‖𝓕⁻ f y‖ := by
  have hc' : |c ^ finrank ℝ E| ≠ 0 := abs_ne_zero.2 (pow_ne_zero _ hc)
  have hck : |c| ^ k ≠ 0 := pow_ne_zero _ (abs_ne_zero.2 hc)
  have h (y : E) : ‖y‖ ^ k * ‖𝓕⁻ (fun x ↦ f (c • x)) y‖ =
      (|c ^ finrank ℝ E|⁻¹ * |c| ^ k) * (‖c⁻¹ • y‖ ^ k * ‖𝓕⁻ f (c⁻¹ • y)‖) := by
    simp only [fourierInv_comp_smul f, norm_smul, norm_inv, Real.norm_eq_abs, abs_abs, mul_pow,
      inv_pow]
    field_simp
  simp_rw [h]
  rw [integral_const_mul, Measure.integral_comp_inv_smul volume (fun y ↦ ‖y‖ ^ k * ‖𝓕⁻ f y‖),
    smul_eq_mul]
  field_simp

/-- Dilating a function does not change the `L¹` norm of its inverse Fourier transform:
`∫ ‖𝓕⁻ (f (c • ·))‖ = ∫ ‖𝓕⁻ f‖`. -/
theorem integral_norm_fourierInv_comp_smul (f : E → F) {c : ℝ} (hc : c ≠ 0) :
    ∫ y, ‖𝓕⁻ (fun x ↦ f (c • x)) y‖ = ∫ y, ‖𝓕⁻ f y‖ := by
  simpa using integral_norm_pow_mul_norm_fourierInv_comp_smul f 0 hc

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
    simp [fourierInv_comp_smul g, abs_of_pos hR]
  rw [h, eLpNorm_const_smul, Measure.eLpNorm_comp_inv_smul volume _ (inv_ne_zero hR.ne'),
    abs_of_pos (inv_pos.2 hR), ← mul_assoc,
    ← ofReal_norm, Real.norm_eq_abs, abs_of_pos (by positivity),
    ← ENNReal.ofReal_mul (by positivity), Real.inv_rpow hR.le, ← Real.rpow_natCast,
    ← Real.rpow_neg hR.le, ← Real.rpow_add hR, sub_eq_add_neg]

/-! ### Translation -/

/-- **Fourier transform of a translate**: translation becomes modulation,
`𝓕 (f (· - a)) ξ = 𝐞 (-⟪a, ξ⟫) • 𝓕 f ξ`. -/
theorem fourier_comp_sub_const (f : E → F) (a ξ : E) :
    𝓕 (fun x ↦ f (x - a)) ξ = 𝐞 (-⟪a, ξ⟫) • 𝓕 f ξ := by
  -- On functions, `𝓕` is the Fourier integral for the pairing `innerₗ E`.
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right 𝐞 volume (innerₗ E) f (-a)) ξ
  simp only [Function.comp_def, ← sub_eq_add_neg, map_neg, LinearMap.neg_apply,
    innerₗ_apply_apply] at h
  exact h

/-- **Frequencies of a translate**: translating a function does not change the support of its
Fourier transform. -/
theorem support_fourier_comp_sub_const (f : E → F) (a : E) :
    Function.support (𝓕 (fun x ↦ f (x - a))) = Function.support (𝓕 f) := by
  ext ξ
  rw [Function.mem_support, Function.mem_support, fourier_comp_sub_const,
    Circle.smul_def, smul_ne_zero_iff_right (Circle.coe_ne_zero _)]

/-! ### Translation in frequency -/

/-- **Modulation**: multiplying by the character `𝐞 ⟪·, c⟫` translates the Fourier transform,
`𝓕 (𝐞 ⟪·, c⟫ • f) ζ = 𝓕 f (ζ - c)`. -/
theorem fourier_fourierChar_smul (f : E → F) (c ζ : E) :
    𝓕 (fun y ↦ 𝐞 ⟪y, c⟫ • f y) ζ = 𝓕 f (ζ - c) := by
  simp only [Real.fourier_eq]
  congr 1 with y
  rw [smul_smul, ← AddChar.map_add_eq_mul, inner_sub_right, neg_sub, neg_add_eq_sub]

/-- The Fourier transform of a scalar function times a constant vector:
`𝓕 (f · • v) w = 𝓕 f w • v`. -/
theorem fourier_smul_const [CompleteSpace F] (f : E → ℂ) (v : F) (w : E) :
    𝓕 (fun z ↦ f z • v) w = 𝓕 f w • v := by
  simp only [Real.fourier_eq, ← smul_assoc]
  exact integral_smul_const _ v

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The exponential `exp(i ⟪y, ξ⟫)` is the Fourier character `𝐞 ⟪y, ξ / 2π⟫`. -/
theorem exp_inner_mul_I_eq_fourierChar (y ξ : E) :
    Complex.exp (⟪y, ξ⟫ * Complex.I) = 𝐞 ⟪y, (2 * π)⁻¹ • ξ⟫ := by
  rw [Real.fourierChar_apply, inner_smul_right]
  congr 2
  push_cast
  field_simp

end TauCeti
