/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Convolution powers of measures

This file defines the additive convolution powers of a measure on a measurable additive monoid.
It records their algebraic, measure-theoretic, measurability, and integration properties.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [AddMonoid α]

/-- The `n`-fold additive convolution of a measure.  The zeroth power is the point mass at zero. -/
def convolutionPower (μ : Measure α) : ℕ → Measure α
  | 0 => Measure.dirac 0
  | n + 1 => convolutionPower μ n ∗ μ

/-- The zeroth convolution power is the point mass at zero. -/
@[simp]
theorem convolutionPower_zero (μ : Measure α) : μ.convolutionPower 0 = Measure.dirac 0 := (rfl)

/-- A successor convolution power appends one copy of the measure. -/
@[simp]
theorem convolutionPower_succ (μ : Measure α) (n : ℕ) :
    μ.convolutionPower (n + 1) = μ.convolutionPower n ∗ μ := (rfl)

/-- Convolution powers of an s-finite measure are s-finite. -/
instance sfinite_convolutionPower (μ : Measure α) [SFinite μ] (n : ℕ) :
    SFinite (μ.convolutionPower n) := by
  induction n with
  | zero => simp only [convolutionPower_zero]; infer_instance
  | succ n ih => simp only [convolutionPower_succ]; infer_instance

variable [MeasurableAdd₂ α]

/-- The first convolution power is the original measure. -/
theorem convolutionPower_one (μ : Measure α) [SFinite μ] : μ.convolutionPower 1 = μ := by
  rw [convolutionPower_succ, convolutionPower_zero, dirac_zero_conv]

/-- Convolution powers turn addition of exponents into convolution. -/
theorem convolutionPower_add (μ : Measure α) [SFinite μ] (m n : ℕ) :
    μ.convolutionPower (m + n) = μ.convolutionPower m ∗ μ.convolutionPower n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, convolutionPower_succ, convolutionPower_succ, ih, conv_assoc]

/-- Every convolution power of a probability measure is a probability measure. -/
instance isProbabilityMeasure_convolutionPower (μ : Measure α) [IsProbabilityMeasure μ]
    (n : ℕ) : IsProbabilityMeasure (μ.convolutionPower n) := by
  induction n with
  | zero => simp only [convolutionPower_zero]; infer_instance
  | succ n ih => simp only [convolutionPower_succ]; infer_instance

/-- On probability measures, each fixed convolution power depends measurably on the measure. -/
@[fun_prop]
theorem measurable_convolutionPower (n : ℕ) :
    Measurable fun μ : ProbabilityMeasure α => (μ : Measure α).convolutionPower n := by
  induction n with
  | zero => simpa only [convolutionPower_zero] using
      (measurable_const : Measurable fun _ : ProbabilityMeasure α => Measure.dirac (0 : α))
  | succ n ih =>
      have hpow : Measurable fun μ : ProbabilityMeasure α =>
          (⟨(μ : Measure α).convolutionPower n, inferInstance⟩ : ProbabilityMeasure α) :=
        ih.subtype_mk
      have hprod : Measurable fun μ : ProbabilityMeasure α =>
          ((μ : Measure α).convolutionPower n).prod (μ : Measure α) :=
        ProbabilityMeasure.measurable_fun_prod.comp (hpow.prodMk measurable_id)
      simp only [convolutionPower_succ, Measure.conv]
      convert (Measure.measurable_map _ measurable_add).comp hprod using 1
      rfl

/-- Convolution powers of a point mass add its atom repeatedly. -/
theorem convolutionPower_dirac (x : α) (n : ℕ) :
    (Measure.dirac x).convolutionPower n = Measure.dirac (n • x) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, succ_nsmul]

/-- Every convolution power of the point mass at zero is again concentrated at zero. -/
@[simp]
theorem convolutionPower_dirac_zero (n : ℕ) :
    (Measure.dirac (0 : α)).convolutionPower n = Measure.dirac 0 := by
  simpa using convolutionPower_dirac (α := α) 0 n

/-- A measurable additive homomorphism transports convolution powers to convolution powers of the
pushforward measure. -/
theorem map_convolutionPower {β : Type*} [MeasurableSpace β] [AddMonoid β]
    [MeasurableAdd₂ β] (μ : Measure α) [SFinite μ] (f : α →+ β) (hf : Measurable f)
    (n : ℕ) :
    (μ.convolutionPower n).map f = (μ.map f).convolutionPower n := by
  induction n with
  | zero => simp [Measure.map_dirac' hf]
  | succ n ih =>
      rw [convolutionPower_succ, convolutionPower_succ,
        map_conv_addMonoidHom f hf, ih]

/-- Integration against a successor convolution power is iterated integration against the
preceding power and one further copy of the measure. -/
theorem lintegral_convolutionPower_succ (μ : Measure α) [SFinite μ] (n : ℕ)
    (f : α → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂μ.convolutionPower (n + 1) =
      ∫⁻ x, ∫⁻ y, f (x + y) ∂μ ∂μ.convolutionPower n := by
  rw [convolutionPower_succ, lintegral_conv hf]

end MeasureTheory.Measure
