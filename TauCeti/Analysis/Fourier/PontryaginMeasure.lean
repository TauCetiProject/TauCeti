/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.PontryaginDualEval
public import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Fourier–Stieltjes transform of measures on a Pontryagin dual

Integrating character evaluations against a finite positive measure on the Pontryagin dual
defines a complex-valued function on the original additive group. The transform records the
measure's mass at the identity and respects addition, scaling, and point masses.
-/

public section

open MeasureTheory

namespace TauCeti

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
  [MeasurableSpace (PontryaginDual (Multiplicative G))]

/-- The Fourier–Stieltjes transform of a finite measure on the Pontryagin dual of an
additive group. -/
@[expose]
noncomputable def _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform
    [OpensMeasurableSpace (PontryaginDual (Multiplicative G))]
    (μ : FiniteMeasure (PontryaginDual (Multiplicative G))) (g : G) : ℂ :=
  ∫ χ, (χ (Multiplicative.ofAdd g) : ℂ) ∂μ.toMeasure

variable [OpensMeasurableSpace (PontryaginDual (Multiplicative G))]

/-- At the identity, the transform records the total mass of the measure. -/
@[simp]
theorem _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_zero
    (μ : FiniteMeasure (PontryaginDual (Multiplicative G))) :
    μ.pontryaginMeasureTransform 0 = (μ.toMeasure.real Set.univ : ℂ) := by
  simp [FiniteMeasure.pontryaginMeasureTransform]

/-- The transform of the zero measure vanishes. -/
@[simp]
theorem _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_zero_measure :
    (0 : FiniteMeasure (PontryaginDual (Multiplicative G))).pontryaginMeasureTransform = 0 := by
  funext g
  simp [FiniteMeasure.pontryaginMeasureTransform]

/-- The transform commutes with nonnegative scalar multiplication of finite measures. -/
@[simp]
theorem _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_smul
    (c : NNReal) (μ : FiniteMeasure (PontryaginDual (Multiplicative G))) :
    (c • μ).pontryaginMeasureTransform = c • μ.pontryaginMeasureTransform := by
  funext g
  simp [FiniteMeasure.pontryaginMeasureTransform]

/-- The transform commutes with addition of finite measures. -/
@[simp]
theorem _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_add
    (μ ν : FiniteMeasure (PontryaginDual (Multiplicative G))) :
    (μ + ν).pontryaginMeasureTransform =
      μ.pontryaginMeasureTransform + ν.pontryaginMeasureTransform := by
  funext g
  rw [show (μ + ν).pontryaginMeasureTransform g =
      ∫ χ, (χ (Multiplicative.ofAdd g) : ℂ) ∂(μ + ν).toMeasure from rfl,
    FiniteMeasure.toMeasure_add,
    integral_add_measure (PontryaginDual.integrable_eval_ofAdd (μ := μ.toMeasure) g)
      (PontryaginDual.integrable_eval_ofAdd (μ := ν.toMeasure) g)]
  rfl

/-- The transform of a point mass is its character. -/
@[simp]
theorem _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_dirac
    (χ : PontryaginDual (Multiplicative G)) (g : G) :
    FiniteMeasure.pontryaginMeasureTransform
      (⟨Measure.dirac χ, inferInstance⟩ : FiniteMeasure
        (PontryaginDual (Multiplicative G))) g =
      (χ (Multiplicative.ofAdd g) : ℂ) := by
  simp [FiniteMeasure.pontryaginMeasureTransform,
    integral_dirac' _ _ (PontryaginDual.continuous_eval_ofAdd g).stronglyMeasurable]

end TauCeti
