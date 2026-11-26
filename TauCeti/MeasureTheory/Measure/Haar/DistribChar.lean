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
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Change of variables and congruence for the distributive Haar character

Let a group `G` act distributively and continuously on a locally compact additive group `A`.
Mathlib's distributive Haar character `MeasureTheory.distribHaarChar A g` is the factor by which
`g` scales additive Haar measure: `μ (g • s) = distribHaarChar A g * μ s`. This file proves
congruence across group actions (`distribHaarChar_eq_of_smul_eq`), and states the scaling fact for
pushforwards and integrals,

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

* `MeasureTheory.distribHaarChar_eq_of_smul_eq`: if `∀ a : A, g • a = h • a`, then
  `distribHaarChar A g = distribHaarChar A h`.
* `MeasureTheory.Measure.map_smul_eq_inv_distribHaarChar_smul`: pushing a Haar measure forward
  along `g • ·` divides it by `distribHaarChar A g`.
* `MeasureTheory.Measure.map_smul_withDensity`: a measure with density `f` with respect to a Haar
  measure is invariant under `g • ·` when `distribHaarChar A g * f (g • x) = f x`.
* `MeasureTheory.integral_comp_smul_eq_inv_distribHaarChar_smul`: the corresponding change of
  variables for Bochner integrals.
* `MeasureTheory.distribHaarChar_eq_nnnorm_det`: a group acting `ℝ`-linearly on a
  finite-dimensional real space scales Haar measure by the absolute value of the determinant.
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

section Congruence

open MeasureTheory.Measure TopologicalSpace

/-- If two elements of possibly different groups act continuously and distributively on the same
locally compact topological additive group `A` by the same map, then they have the same
distributive Haar character. -/
theorem distribHaarChar_eq_of_smul_eq {G H A : Type*} [Group G] [Group H] [AddCommGroup A]
    [DistribMulAction G A] [DistribMulAction H A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [ContinuousConstSMul G A] [ContinuousConstSMul H A] {g : G} {h : H}
    (hgh : ∀ a : A, g • a = h • a) :
    distribHaarChar A g = distribHaarChar A h := by
  borelize A
  let K : PositiveCompacts A := Classical.arbitrary (PositiveCompacts A)
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := addHaarMeasure K) (s := (K : Set A))
    (by simp [addHaarMeasure_self]) (by simp [addHaarMeasure_self]) ?_
  have hsmul : g • (K : Set A) = h • (K : Set A) := by
    ext x
    simp [Set.mem_smul_set, hgh]
  rw [hsmul, ← distribHaarChar_mul (addHaarMeasure K) h (K : Set A)]

end Congruence

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

/-- A measure with density `f` with respect to an additive Haar measure `μ` is invariant under
`g • ·` when `f` scales by the inverse of the distributive Haar character of `g`:
`distribHaarChar A g * f (g • x) = f x`. -/
theorem map_smul_withDensity {f : A → ℝ≥0∞} (g : G)
    (hfg : ∀ x, (distribHaarChar A g : ℝ≥0∞) * f (g • x) = f x) :
    (μ.withDensity f).map (g • ·) = μ.withDensity f := by
  have he : MeasurableEmbedding (g • · : A → A) := (Homeomorph.smul g).measurableEmbedding
  -- Write `f` as the weight `distribHaarChar A g • f` pulled back along `g • ·`.
  have hf : f = ((distribHaarChar A g : ℝ≥0∞) • f) ∘ (g • ·) := funext fun x ↦ (hfg x).symm
  conv_lhs => rw [hf]
  rw [he.map_withDensity_comp, map_smul_eq_inv_distribHaarChar_smul, ENNReal.smul_def,
    withDensity_smul_measure, withDensity_smul' _ _ ENNReal.coe_ne_top, smul_smul]
  -- The two scalars `(distribHaarChar A g)⁻¹` and `distribHaarChar A g` cancel.
  simp [ENNReal.inv_mul_cancel, (distribHaarChar_pos (A := A)).ne']

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

/-- A group `G` acting `ℝ`-linearly on a finite-dimensional real normed space `E` scales additive
Haar measure by the absolute value of the determinant: `distribHaarChar E g = ‖det (g • ·)‖₊`. -/
theorem distribHaarChar_eq_nnnorm_det [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DistribMulAction G E] [SMulCommClass G ℝ E] [ContinuousConstSMul G E] (g : G) :
    distribHaarChar E g = ‖LinearMap.det (DistribSMul.toLinearMap ℝ E g)‖₊ := by
  borelize E
  let μ : Measure E := Measure.addHaar
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ)
    (Metric.measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne ?_
  rw [← Set.image_smul, ← ENNReal.ofReal_coe_nnreal, coe_nnNorm, Real.norm_eq_abs]
  exact Measure.addHaar_image_linearMap μ (DistribSMul.toLinearMap ℝ E g) _

/-- A nonzero real scalar `a` scales additive Haar measure on a finite-dimensional real normed
space `E` by `|a| ^ dim_ℝ E`. For `E = ℝ` the module of `a` is its absolute value. -/
theorem distribHaarChar_real_eq [NormedSpace ℝ E] [FiniteDimensional ℝ E] (a : ℝˣ) :
    distribHaarChar E a = ‖(a : ℝ)‖₊ ^ finrank ℝ E := by
  have h : DistribSMul.toLinearMap ℝ E a = (a : ℝ) • LinearMap.id := by ext; rfl
  simp [distribHaarChar_eq_nnnorm_det, h]

/-- A nonzero complex scalar `a` scales additive Haar measure on a finite-dimensional complex
normed space `E` by `|a| ^ dim_ℝ E`. For `E = ℂ` the module of `a` is `|a| ^ 2 = a * conj a`. -/
theorem distribHaarChar_complex_eq [NormedSpace ℂ E] [FiniteDimensional ℂ E] (a : ℂˣ) :
    distribHaarChar E a = ‖(a : ℂ)‖₊ ^ finrank ℝ E := by
  have h : DistribSMul.toLinearMap ℝ E a =
      ((a : ℂ) • (LinearMap.id : E →ₗ[ℂ] E)).restrictScalars ℝ := by
    ext; rfl
  rw [distribHaarChar_eq_nnnorm_det, h, LinearMap.det_restrictScalars]
  ext
  simp [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, finrank_real_of_complex, pow_mul,
    pow_right_comm]

end Archimedean

end MeasureTheory
