/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.RingTheory.Complex

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The self-dual measures of the standard characters of `ℝ` and `ℂ`

The standard additive character of `ℝ` is `ψ_ℝ(x) = exp (2πi x)` (Mathlib's `Real.fourierChar`,
written `𝐞`), and that of `ℂ` is `ψ_ℂ = ψ_ℝ ∘ Tr_{ℂ/ℝ}`, `ψ_ℂ(z) = exp (2πi (z + conj z))`
(`TauCeti.complexTraceChar`). For an additive character `ψ` of a field `F` and a measure `μ` on
`F`, the Fourier transform of `f : F → E` for the pairing `(x, y) ↦ ψ (x y)` is Mathlib's

`Fourier.fourierIntegral ψ μ f (y) = ∫ ψ (-(x y)) • f x dμ(x)`,

the convention of `AddChar.selfDualMeasure` at the finite places. The transform with the opposite
sign is `y ↦ Fourier.fourierIntegral ψ μ f (-y)`, so both have the same self-dual measures.

This file proves that Lebesgue measure `dx` on `ℝ` and twice Lebesgue measure `2 dx dy` on `ℂ` are
self-dual: for an integrable `f` with integrable transform, the double transform at `x` is
`f (-x)` whenever `f` is continuous at `-x` (`Real.fourierIntegral_fourierIntegral_fourierChar`
and `TauCeti.fourierIntegral_fourierIntegral_complexTraceChar`). On `ℂ` the transform for `ψ_ℂ`
and `2 dx dy` is `w ↦ 2 𝓕 f (2 conj w)` in terms of the transform `𝓕` of `ℂ` as a real inner
product space (`TauCeti.fourierIntegral_complexTraceChar`); the substitution `w ↦ 2 conj w` has
Jacobian `4`, which the factor `2` of the measure, appearing once in each transform, cancels. As
checks,
`exp (-π x²)` and `exp (-2π |z|²)` are their own transforms
(`Real.fourierIntegral_fourierChar_gaussian`, `TauCeti.fourierIntegral_complexTraceChar_gaussian`).

## Main definitions

* `TauCeti.complexTraceChar`: the standard character `z ↦ exp (2πi Tr_{ℂ/ℝ} z)` of `ℂ`.

## Main results

* `Real.fourierIntegral_fourierIntegral_fourierChar`: `dx` is self-dual for `ψ_ℝ`.
* `TauCeti.fourierIntegral_complexTraceChar`: the transform for `ψ_ℂ` and `2 dx dy` in terms of
  Mathlib's `𝓕`.
* `TauCeti.fourierIntegral_fourierIntegral_complexTraceChar`: `2 dx dy` is self-dual for `ψ_ℂ`.

## References

The two self-duality statements are adapted from `realTamagawaMeasure_selfDual` and
`complexTamagawaMeasure_selfDual` in `RiemannMasullo/AppA_AlgebraicNT/Sec3.lean` of the
Riemann–Masullo formalization (https://github.com/mccorvie/riemann-masullo), which states them as
Plancherel identities for the Pontryagin dual.

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich, eds., *Algebraic Number Theory* (1967), §2.2.
-/

public section

noncomputable section

open MeasureTheory Complex FourierTransform Real
open scoped ENNReal ComplexConjugate RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### The real place -/

namespace Real

/-- For the character `𝐞` and Lebesgue measure, `Fourier.fourierIntegral` is Mathlib's `𝓕`. -/
theorem fourierIntegral_fourierChar_volume (f : ℝ → E) :
    Fourier.fourierIntegral 𝐞 volume f = 𝓕 f :=
  funext fun w ↦ (fourier_real_eq f w).symm

/-- **Lebesgue measure is self-dual for `ψ_ℝ(x) = exp (2πi x)`**: for an integrable `f` with
integrable transform, the double transform at `x` is `f (-x)` if `f` is continuous at `-x`. -/
theorem fourierIntegral_fourierIntegral_fourierChar [CompleteSpace E] {f : ℝ → E}
    (hf : Integrable f) (hf' : Integrable (Fourier.fourierIntegral 𝐞 volume f)) {x : ℝ}
    (hx : ContinuousAt f (-x)) :
    Fourier.fourierIntegral 𝐞 volume (Fourier.fourierIntegral 𝐞 volume f) x = f (-x) := by
  rw [fourierIntegral_fourierChar_volume] at hf' ⊢
  rw [fourierIntegral_fourierChar_volume, ← neg_neg x, ← fourierInv_eq_fourier_neg, neg_neg]
  exact hf.fourierInv_fourier_eq hf' hx

/-- The Gaussian `exp (-π x²)` is its own transform for `ψ_ℝ` and Lebesgue measure. -/
theorem fourierIntegral_fourierChar_gaussian (w : ℝ) :
    Fourier.fourierIntegral 𝐞 volume (fun x : ℝ ↦ cexp (-π * ‖x‖ ^ 2)) w = cexp (-π * ‖w‖ ^ 2) := by
  rw [fourierIntegral_fourierChar_volume,
    fourier_gaussian_innerProductSpace (by simp [Real.pi_pos])]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  simp only [div_self hπ, one_cpow, one_mul]
  congr 1
  field_simp

end Real

/-! ### The complex place -/

namespace TauCeti

/-- **The standard additive character of `ℂ`**: `ψ_ℂ(z) = exp (2πi Tr_{ℂ/ℝ} z)
= exp (2πi (z + conj z))`. Twice Lebesgue measure is self-dual for it
(`fourierIntegral_fourierIntegral_complexTraceChar`). -/
def complexTraceChar : AddChar ℂ Circle :=
  Real.fourierChar.compAddMonoidHom (Algebra.trace ℝ ℂ).toAddMonoidHom

/-- `ψ_ℂ(z) = exp (2πi · 2 Re z)`. -/
theorem complexTraceChar_apply (z : ℂ) : complexTraceChar z = 𝐞 (2 * z.re) := by
  rw [← Algebra.trace_complex_apply]
  rfl

/-- `2 Re (z w)` is the real inner product of `z` with `2 conj w`. -/
private theorem two_mul_re_mul (z w : ℂ) : 2 * (z * w).re = ⟪z, (2 : ℝ) • conj w⟫ := by
  rw [Complex.inner, Complex.real_smul]
  simp only [mul_re, conj_re, conj_im, ofReal_re, ofReal_im, mul_im]
  ring

/-- **The transform for `ψ_ℂ` and `2 dx dy` in terms of Mathlib's `𝓕`**: it is `2 𝓕 f (2 conj w)`,
where `𝓕` is the Fourier transform of `ℂ` as a real inner product space. -/
theorem fourierIntegral_complexTraceChar (f : ℂ → E) (w : ℂ) :
    Fourier.fourierIntegral complexTraceChar ((2 : ℝ≥0∞) • volume) f w =
      (2 : ℝ) • 𝓕 f ((2 : ℝ) • conj w) := by
  rw [Fourier.fourierIntegral_def, integral_smul_measure, fourier_eq, ENNReal.toReal_ofNat]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  simp only [complexTraceChar_apply, neg_re, mul_neg, two_mul_re_mul]

/-- The transform of `2 g (2 ·)` at `2 x` is `𝓕 g x`, by the substitution `u ↦ 2 u` of
Jacobian `4`. -/
private theorem fourier_two_smul_comp_two_smul (g : ℂ → E) (x : ℂ) :
    (2 : ℝ) • 𝓕 (fun u ↦ (2 : ℝ) • g ((2 : ℝ) • u)) ((2 : ℝ) • x) = 𝓕 g x := by
  simp only [fourier_eq, real_inner_smul_right, ← real_inner_smul_left, smul_comm _ (2 : ℝ)]
  rw [integral_smul, Measure.integral_comp_smul volume (fun t ↦ 𝐞 (-⟪t, x⟫) • g t) (2 : ℝ),
    finrank_real_complex, smul_smul, smul_smul]
  norm_num

/-- **Twice Lebesgue measure is self-dual for `ψ_ℂ(z) = exp (2πi (z + conj z))`**: for an integrable
`f` with integrable transform, the double transform at `x` is `f (-x)` if `f` is continuous at
`-x`. -/
theorem fourierIntegral_fourierIntegral_complexTraceChar [CompleteSpace E] {f : ℂ → E}
    (hf : Integrable f)
    (hf' : Integrable (Fourier.fourierIntegral complexTraceChar ((2 : ℝ≥0∞) • volume) f))
    {x : ℂ} (hx : ContinuousAt f (-x)) :
    Fourier.fourierIntegral complexTraceChar ((2 : ℝ≥0∞) • volume)
      (Fourier.fourierIntegral complexTraceChar ((2 : ℝ≥0∞) • volume) f) x = f (-x) := by
  set h : ℂ → E := fun u ↦ (2 : ℝ) • 𝓕 f ((2 : ℝ) • u)
  have hF : Fourier.fourierIntegral complexTraceChar ((2 : ℝ≥0∞) • volume) f = h ∘ conjLIE :=
    funext (fourierIntegral_complexTraceChar f)
  -- `𝓕 f` is integrable, since `h` is and `h` rescales `𝓕 f`
  have hh : Integrable h := by
    rw [hF] at hf'
    exact ((LinearIsometryEquiv.measurePreserving conjLIE).integrable_comp_emb
      conjLIE.toHomeomorph.measurableEmbedding).1 hf'
  have hg : Integrable (𝓕 f) := by
    have hfun : (fun u ↦ 𝓕 f ((2 : ℝ) • u)) = (2⁻¹ : ℝ) • h := by
      ext u
      simp only [h, Pi.smul_apply, smul_smul]
      norm_num
    exact (integrable_comp_smul_iff volume (𝓕 f) two_ne_zero).1 (hfun ▸ hh.smul _)
  rw [hF, fourierIntegral_complexTraceChar, fourier_comp_linearIsometry,
    show conjLIE ((2 : ℝ) • conj x) = (2 : ℝ) • x by
      apply Complex.ext <;> simp, fourier_two_smul_comp_two_smul,
    ← neg_neg x, ← fourierInv_eq_fourier_neg, neg_neg]
  exact hf.fourierInv_fourier_eq hg hx

/-- The Gaussian `exp (-2π |z|²)` is its own transform for `ψ_ℂ` and `2 dx dy`. -/
theorem fourierIntegral_complexTraceChar_gaussian (w : ℂ) :
    Fourier.fourierIntegral complexTraceChar ((2 : ℝ≥0∞) • volume)
      (fun z : ℂ ↦ cexp (-(2 * π) * ‖z‖ ^ 2)) w = cexp (-(2 * π) * ‖w‖ ^ 2) := by
  have hb : 0 < (((2 * π : ℝ) : ℂ)).re := by simp [Real.pi_pos]
  have h := fourier_gaussian_innerProductSpace hb ((2 : ℝ) • conj w)
  push_cast at h
  rw [fourierIntegral_complexTraceChar, h, finrank_real_complex]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [show (π : ℂ) / (2 * π) = 2⁻¹ by field_simp, norm_smul, norm_conj]
  rw [show ((2 : ℕ) : ℂ) / 2 = 1 by norm_num, cpow_one, Complex.real_smul, ← mul_assoc,
    show ((2 : ℝ) : ℂ) * 2⁻¹ = 1 by norm_num, one_mul, Real.norm_ofNat]
  congr 1
  field_simp
  push_cast
  ring

end TauCeti
