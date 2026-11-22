/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Basic characteristic-function identities

Complements Mathlib's `Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic` with scaling of
`MeasureTheory.charFun` by an `ℝ≥0∞` measure factor, pushforward integral evaluation for an
a.e.-measurable random variable, integrability of the characteristic integrand against any finite
measure, the real-line characteristic integrand identity `TauCeti.exp_inner_mul_I_real`, and the
finite-dimensional Euclidean `L²` characteristic integrand identity `TauCeti.exp_inner_toLp_mul_I`.
-/

public section

open Complex MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace MeasureTheory

/-- Scaling a measure by `c : ℝ≥0∞` multiplies its characteristic function by `c.toReal`. -/
@[simp]
theorem charFun_smul_measure {E : Type*} [Inner ℝ E] [MeasurableSpace E]
    {μ : Measure E} (c : ℝ≥0∞) (t : E) :
    charFun (c • μ) t = (c.toReal : ℂ) * charFun μ t := by
  simp [charFun_apply, integral_smul_measure, Complex.real_smul]

/-- The characteristic function of the pushforward measure `μ.map X` equals the integral of
`ω ↦ exp (⟪X ω, t⟫ * I)` with respect to `μ`. -/
theorem charFun_map_eq_integral {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {X : Ω → E} (hX : AEMeasurable X μ) (t : E) :
    charFun (μ.map X) t = ∫ ω, exp ((⟪X ω, t⟫ : ℂ) * I) ∂μ := by
  rw [charFun_apply, integral_map hX (by fun_prop)]

end MeasureTheory

/-- On `ℝ`, the characteristic integrand `exp (⟪x, t⟫ * I)` equals `exp (I * t * x)`. -/
theorem TauCeti.exp_inner_mul_I_real (x t : ℝ) :
    exp ((⟪x, t⟫ : ℂ) * I) = exp (I * (t : ℂ) * (x : ℂ)) := by
  simp only [RCLike.inner_apply, conj_trivial]; congr 1; push_cast; ring

/-- On `EuclideanSpace ℝ κ`, the characteristic integrand `exp (⟪toLp 2 x, v⟫ * I)` equals
`exp (I * ∑ i, v i * x i)`. -/
theorem TauCeti.exp_inner_toLp_mul_I {κ : Type*} [Fintype κ] (x : κ → ℝ)
    (v : EuclideanSpace ℝ κ) :
    exp ((⟪MeasurableEquiv.toLp 2 (κ → ℝ) x, v⟫ : ℂ) * I) = exp (I * ∑ i, v i * x i) := by
  simp only [MeasurableEquiv.toLp_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  congr 1; push_cast; ring

/-- The characteristic integrand `ω ↦ exp (⟪X ω, t⟫ * I)` of an a.e.-measurable random variable
is integrable with respect to any finite measure. -/
theorem AEMeasurable.integrable_exp_inner_mul_I {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {X : Ω → E} (hX : AEMeasurable X μ) (t : E) :
    Integrable (fun ω ↦ exp ((⟪X ω, t⟫ : ℂ) * I)) μ :=
  (integrable_const (1 : ℝ)).mono'
    ((by fun_prop : Continuous fun x : E ↦ exp ((⟪x, t⟫ : ℂ) * I)).measurable.comp_aemeasurable
      hX).aestronglyMeasurable
    (ae_of_all μ fun _ ↦ by rw [Complex.norm_exp_ofReal_mul_I])
