/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.Bochner.BochnerTheorem
import TauCeti.Analysis.Bochner.Fourier.Convention
import TauCeti.Analysis.Bochner.Fourier.Nonneg
import TauCeti.Analysis.Fourier.Continuous

/-!
# Fourier inversion for measures with integrable characteristic function

A finite Borel measure whose characteristic function `φ = charFun μ` is integrable is absolutely
continuous with respect to Lebesgue measure, with a bounded continuous density obtained by
Fourier inversion of `φ`. On the real line the density is

`f(x) = (2π)⁻¹ * Re ∫ t, exp (-i t x) * φ(t) dt`,

recorded here as `MeasureTheory.Measure.charFunDensity μ`. This is the classical inversion
theorem used to produce densities of laws that are specified through their characteristic
function, such as the stable laws.

On a finite-dimensional real inner-product space `V` the density is stated in Mathlib's
`2π` Fourier convention: it is the real part of the inverse Fourier transform of
`v ↦ φ((-2π) • v)`. The proof combines the `L¹` case of Bochner's theorem
(`TauCeti.integral_fourierAtom_withDensity_re_fourierInv`), applied to this positive-definite
integrable function, with uniqueness of measures with a given characteristic function.

On `ℝ` the density is nonnegative, continuous and bounded by `(2π)⁻¹ * ∫ ‖φ‖` for every finite
measure; without integrability of `φ` the defining integral diverges and the density is zero.

## Main declarations

* `MeasureTheory.Measure.eq_withDensity_re_fourierInv_charFun`: a finite measure with integrable
  characteristic function has density `(𝓕⁻ (φ ∘ ((-2π) • ·))).re`.
* `MeasureTheory.Measure.charFunDensity`: the inversion density of a measure on `ℝ`.
* `MeasureTheory.Measure.eq_withDensity_charFunDensity`: **the inversion theorem** on `ℝ`.
* `MeasureTheory.Measure.charFunDensity_nonneg`, `MeasureTheory.Measure.continuous_charFunDensity`
  and `MeasureTheory.Measure.charFunDensity_le`: nonnegativity, continuity and the uniform bound.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.,
  Wiley (1971), Section XV.3, Theorem 3.
-/

public section

noncomputable section

open Complex
open scoped ComplexOrder FourierTransform Real

namespace MeasureTheory.Measure

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] in
/-- The rescaled characteristic function `v ↦ φ((-2π) • v)` of a finite measure has a
positive-semidefinite subtraction kernel. -/
private theorem posSemidef_charFun_neg_two_pi_smul (μ : Measure V) [IsFiniteMeasure μ] :
    Matrix.PosSemidef fun a b : V ↦ charFun μ ((-2 * π) • (a - b)) := by
  simpa only [TauCeti.integral_fourierAtom_eq_charFun_neg_two_pi_smul] using
    TauCeti.posSemidef_fourierConventionCharFun_sub (ν := μ)

/-- **Fourier inversion for measures.** A finite measure on a finite-dimensional real
inner-product space whose characteristic function `φ` is integrable has density
`(𝓕⁻ (v ↦ φ((-2π) • v))).re` with respect to Lebesgue measure. -/
theorem eq_withDensity_re_fourierInv_charFun {μ : Measure V} [IsFiniteMeasure μ]
    (h : Integrable (charFun μ)) :
    μ = volume.withDensity fun x ↦
      ENNReal.ofReal (𝓕⁻ (fun v ↦ charFun μ ((-2 * π) • v)) x).re := by
  set F : V → ℂ := fun v ↦ charFun μ ((-2 * π) • v)
  have hF (v : V) : ∫ q, TauCeti.fourierAtom v q ∂μ = F v :=
    TauCeti.integral_fourierAtom_eq_charFun_neg_two_pi_smul v
  have hpd : Matrix.PosSemidef fun a b : V ↦ F (a - b) := posSemidef_charFun_neg_two_pi_smul μ
  have hint : Integrable F := h.comp_smul TauCeti.neg_two_pi_ne_zero
  have hcont : Continuous F := continuous_charFun.comp (continuous_const_smul _)
  have := isFiniteMeasure_withDensity_ofReal
    (TauCeti.integrable_fourierInv_of_posSemidef F hpd hint hcont).re.hasFiniteIntegral
  refine TauCeti.Measure.ext_of_forall_integral_fourierAtom_eq fun v ↦ ?_
  rw [TauCeti.integral_fourierAtom_withDensity_re_fourierInv F hpd hint hcont v, hF]

end InnerProductSpace

/-! ### The real line -/

/-- The **inversion density** of a measure `μ` on `ℝ` with characteristic function `φ`:
`x ↦ (2π)⁻¹ * Re ∫ t, exp (-i t x) * φ(t) dt`. When `φ` is integrable and `μ` is finite this is
a density of `μ` (`eq_withDensity_charFunDensity`); otherwise the integral diverges and the
function vanishes. -/
def charFunDensity (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (2 * π)⁻¹ * (∫ t : ℝ, cexp (-(t * x * I)) * charFun μ t).re

theorem charFunDensity_def (μ : Measure ℝ) (x : ℝ) :
    charFunDensity μ x = (2 * π)⁻¹ * (∫ t : ℝ, cexp (-(t * x * I)) * charFun μ t).re := by
  rw [charFunDensity]

variable {μ : Measure ℝ}

private theorem norm_cexp_mul_charFun (x t : ℝ) :
    ‖cexp (-(t * x * I)) * charFun μ t‖ = ‖charFun μ t‖ := by
  rw [norm_mul, Complex.norm_exp]
  simp

private theorem integrable_cexp_mul_charFun_iff [IsFiniteMeasure μ] (x : ℝ) :
    Integrable (fun t : ℝ ↦ cexp (-(t * x * I)) * charFun μ t) ↔ Integrable (charFun μ) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ cexp (-(t * x * I)) * charFun μ t) :=
    ((by fun_prop : Continuous fun t : ℝ ↦ cexp (-(t * x * I))).mul
      continuous_charFun).aestronglyMeasurable
  exact ⟨fun h ↦ h.mono continuous_charFun.aestronglyMeasurable
      (ae_of_all _ fun t ↦ (norm_cexp_mul_charFun x t).ge),
    fun h ↦ h.mono hmeas (ae_of_all _ fun t ↦ (norm_cexp_mul_charFun x t).le)⟩

/-- Without integrability of the characteristic function, the inversion density vanishes. -/
theorem charFunDensity_of_not_integrable [IsFiniteMeasure μ] (h : ¬ Integrable (charFun μ))
    (x : ℝ) : charFunDensity μ x = 0 := by
  rw [charFunDensity_def, integral_undef ((integrable_cexp_mul_charFun_iff x).not.mpr h)]
  simp

/-- The inversion density is the real part of the inverse Fourier transform, in Mathlib's `2π`
convention, of `v ↦ φ((-2π) • v)`: substitute `t = -2πv`. -/
private theorem charFunDensity_eq_re_fourierInv (μ : Measure ℝ) (x : ℝ) :
    charFunDensity μ x = (𝓕⁻ (fun v : ℝ ↦ charFun μ ((-2 * π) • v)) x).re := by
  have h := integral_comp_mul_left (fun t : ℝ ↦ cexp (-(t * x * I)) * charFun μ t) (-2 * π)
  rw [abs_inv, abs_mul, abs_neg, abs_two, abs_of_pos Real.pi_pos] at h
  rw [charFunDensity_def, Real.fourierInv_eq', ← smul_eq_mul, ← Complex.smul_re, ← h]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  push_cast
  ring_nf

/-- The inversion density of a finite measure is nonnegative everywhere. -/
theorem charFunDensity_nonneg [IsFiniteMeasure μ] (x : ℝ) : 0 ≤ charFunDensity μ x := by
  by_cases h : Integrable (charFun μ)
  · rw [charFunDensity_eq_re_fourierInv]
    exact TauCeti.fourierInv_re_nonneg_of_posSemidef _ (posSemidef_charFun_neg_two_pi_smul μ)
      (h.comp_smul TauCeti.neg_two_pi_ne_zero) (continuous_charFun.comp (continuous_const_smul _))
      x
  · rw [charFunDensity_of_not_integrable h]

/-- The inversion density of a finite measure is continuous. -/
theorem continuous_charFunDensity [IsFiniteMeasure μ] : Continuous (charFunDensity μ) := by
  by_cases h : Integrable (charFun μ)
  · rw [funext (charFunDensity_eq_re_fourierInv μ)]
    exact continuous_re.comp (h.comp_smul TauCeti.neg_two_pi_ne_zero).continuous_fourierInv
  · rw [funext (charFunDensity_of_not_integrable h)]
    exact continuous_const

/-- The inversion density is bounded by `(2π)⁻¹` times the `L¹` norm of the characteristic
function. -/
theorem charFunDensity_le (μ : Measure ℝ) (x : ℝ) :
    charFunDensity μ x ≤ (2 * π)⁻¹ * ∫ t, ‖charFun μ t‖ := by
  rw [charFunDensity_def]
  gcongr
  calc (∫ t : ℝ, cexp (-(t * x * I)) * charFun μ t).re
      ≤ ‖∫ t : ℝ, cexp (-(t * x * I)) * charFun μ t‖ := re_le_norm _
    _ ≤ ∫ t : ℝ, ‖cexp (-(t * x * I)) * charFun μ t‖ := norm_integral_le_integral_norm _
    _ = ∫ t, ‖charFun μ t‖ := by simp_rw [norm_cexp_mul_charFun]

/-- **The inversion theorem.** A finite measure on `ℝ` with integrable characteristic function
`φ` has the bounded continuous density `x ↦ (2π)⁻¹ * Re ∫ t, exp (-i t x) * φ(t) dt` with respect
to Lebesgue measure. -/
theorem eq_withDensity_charFunDensity [IsFiniteMeasure μ] (h : Integrable (charFun μ)) :
    μ = volume.withDensity fun x ↦ ENNReal.ofReal (charFunDensity μ x) := by
  simp_rw [charFunDensity_eq_re_fourierInv]
  exact eq_withDensity_re_fourierInv_charFun h

end MeasureTheory.Measure
