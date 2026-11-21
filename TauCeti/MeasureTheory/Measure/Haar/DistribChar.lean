/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Change of variables along the distributive Haar character

Let a group `G` act distributively and continuously on a locally compact additive group `A`.
Mathlib's distributive Haar character `MeasureTheory.distribHaarChar A g` is the factor by which
`g` scales additive Haar measure: `μ (g • s) = distribHaarChar A g * μ s`. This file states the
same fact for pushforwards and integrals,

`μ.map (g • ·) = (distribHaarChar A g)⁻¹ • μ`,

`∫ x, f (g • x) ∂μ = (distribHaarChar A g)⁻¹ • ∫ x, f x ∂μ`,

which is the form in which the character enters Fourier analysis: for a field `F` acting on
itself, `distribHaarChar F a` is the module `|a|_F` of `a ∈ Fˣ`, and the substitution `x ↦ a x`
in an integral over `F` produces the factor `|a|_F⁻¹`.

The module of the archimedean fields is computed here: a nonzero real scalar `a` scales Haar
measure on a finite-dimensional real space `E` by `|a| ^ dim_ℝ E`, and a nonzero complex scalar
scales Haar measure on a finite-dimensional complex space by `|a| ^ dim_ℝ E` as well. In
particular the module of `ℝ` is the usual absolute value and the module of `ℂ` is
`|a| ^ 2 = a * conj a`. The module of a nonarchimedean local field is
`MeasureTheory.distribHaarChar_eq_normalizedAbsoluteValue`.

## Main results

* `MeasureTheory.Measure.map_smul_eq_inv_distribHaarChar_smul`: pushing a Haar measure forward
  along `g • ·` divides it by `distribHaarChar A g`.
* `MeasureTheory.integral_comp_smul_eq_inv_distribHaarChar_smul`: the corresponding change of
  variables for Bochner integrals.
* `MeasureTheory.distribHaarChar_real_eq`, `MeasureTheory.distribHaarChar_complex_eq`: the
  module of a nonzero real, resp. complex, scalar acting on a finite-dimensional space `E` is
  `|a| ^ dim_ℝ E`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, §2.2.
* A. Weil, *Basic Number Theory*, Chapter I, §2.
-/

public section

open Module Set
open scoped NNReal ENNReal Pointwise

namespace MeasureTheory

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [LocallyCompactSpace A] [ContinuousConstSMul G A]
  [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular]

namespace Measure

/-- Pushing an additive Haar measure forward along `g • ·` divides it by the distributive Haar
character of `g`. -/
theorem map_smul_eq_inv_distribHaarChar_smul (g : G) :
    μ.map (g • ·) = (distribHaarChar A g)⁻¹ • μ := by
  ext s hs
  rw [map_apply (continuous_const_smul g).measurable hs, preimage_smul, smul_apply,
    ← distribHaarChar_mul, map_inv, nnreal_smul_coe_apply]

end Measure

/-- **Change of variables along the distributive Haar character**: for an additive Haar measure
`μ`, `∫ x, f (g • x) ∂μ = (distribHaarChar A g)⁻¹ • ∫ x, f x ∂μ`. No integrability hypothesis is
needed. -/
theorem integral_comp_smul_eq_inv_distribHaarChar_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : A → E) (g : G) :
    ∫ x, f (g • x) ∂μ = ((distribHaarChar A g : ℝ))⁻¹ • ∫ x, f x ∂μ := by
  have he : MeasurableEmbedding (g • · : A → A) := (Homeomorph.smul g).measurableEmbedding
  rw [← he.integral_map, Measure.map_smul_eq_inv_distribHaarChar_smul,
    integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_inv]

section Archimedean

variable (E : Type*) [NormedAddCommGroup E]

/-- A nonzero real scalar `a` scales additive Haar measure on a finite-dimensional real normed
space `E` by `|a| ^ dim_ℝ E`. For `E = ℝ` the module of `a` is its absolute value. -/
theorem distribHaarChar_real_eq [NormedSpace ℝ E] [FiniteDimensional ℝ E] (a : ℝˣ) :
    distribHaarChar E a = ‖(a : ℝ)‖₊ ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ)
    (Metric.measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne ?_
  rw [Units.smul_def, Measure.addHaar_smul, abs_pow, ← Real.norm_eq_abs, ← coe_nnNorm,
    ← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal]

/-- A nonzero complex scalar `a` scales additive Haar measure on a finite-dimensional complex
normed space `E` by `|a| ^ dim_ℝ E`. For `E = ℂ` the module of `a` is `|a| ^ 2 = a * conj a`. -/
theorem distribHaarChar_complex_eq [NormedSpace ℂ E] [FiniteDimensional ℂ E] (a : ℂˣ) :
    distribHaarChar E a = ‖(a : ℂ)‖₊ ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ)
    (Metric.measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne ?_
  have h := Measure.addHaar_image_linearMap μ
    (((a : ℂ) • LinearMap.id : E →ₗ[ℂ] E).restrictScalars ℝ) (Metric.ball 0 1)
  rw [LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, mul_one, map_pow,
    Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, ← pow_mul, abs_pow, abs_norm,
    ← finrank_real_of_complex, ← coe_nnNorm, ← NNReal.coe_pow,
    ENNReal.ofReal_coe_nnreal] at h
  rw [Units.smul_def, ← h, ← Set.image_smul]
  simp

end Archimedean

end MeasureTheory
