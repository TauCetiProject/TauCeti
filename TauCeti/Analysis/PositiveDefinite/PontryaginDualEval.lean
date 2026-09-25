/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.AdditiveCharacter
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Evaluation of Pontryagin characters

Evaluation at a fixed group element is continuous on the Pontryagin dual. Its complex-valued
form is integrable against every finite measure.
-/

public section

open MeasureTheory

namespace TauCeti.PontryaginDual

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]

/-- Evaluating a Pontryagin character at a fixed additive group element is continuous. -/
theorem continuous_eval_ofAdd (g : G) :
    Continuous (fun χ : _root_.PontryaginDual (Multiplicative G) =>
      (χ (Multiplicative.ofAdd g) : ℂ)) := by
  have h : Continuous (fun χ : (Multiplicative G →ₜ* Circle) =>
      (χ (Multiplicative.ofAdd g) : Circle)) :=
    continuous_eval_const (Multiplicative.ofAdd g)
  exact (LipschitzWith.subtype_val (Submonoid.unitSphere ℂ).carrier).continuous.comp h

variable [MeasurableSpace (_root_.PontryaginDual (Multiplicative G))]
  [OpensMeasurableSpace (_root_.PontryaginDual (Multiplicative G))]

/-- Evaluation of a Pontryagin character is integrable against a finite measure. -/
theorem integrable_eval_ofAdd
    {μ : Measure (_root_.PontryaginDual (Multiplicative G))} [IsFiniteMeasure μ] (g : G) :
    Integrable (fun χ : _root_.PontryaginDual (Multiplicative G) =>
      (χ (Multiplicative.ofAdd g) : ℂ)) μ :=
  (integrable_const (1 : ℝ)).mono'
    (continuous_eval_ofAdd g).aestronglyMeasurable
    (.of_forall fun χ => by simp)

end TauCeti.PontryaginDual
