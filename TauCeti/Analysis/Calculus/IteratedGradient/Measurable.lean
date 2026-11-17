/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import TauCeti.Analysis.Calculus.IteratedGradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.Calculus.Gradient

/-!
# Measurability of iterated gradients

On a finite-dimensional real inner product space with its Borel σ-algebra, every iterated-gradient
field `TauCeti.iteratedGradientChain f j` of an arbitrary scalar function `f` is strongly
measurable. No differentiability is needed: the gradient is Borel measurable
(`TauCeti.measurable_gradient`), and so is the Fréchet derivative of every function into a
complete space (`measurable_fderiv`), with the totalized value `0` where it does not exist.

## Main declarations

* `TauCeti.stronglyMeasurable_iteratedGradientChain`,
  `TauCeti.aestronglyMeasurable_iteratedGradientChain`: every iterated-gradient field is strongly
  measurable.
-/

public section

namespace TauCeti

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Every iterated-gradient field of an arbitrary scalar function is strongly measurable. -/
@[fun_prop]
theorem stronglyMeasurable_iteratedGradientChain (f : E → ℝ) (j : ℕ) :
    StronglyMeasurable (iteratedGradientChain f j) := by
  cases j with
  | zero =>
      rw [iteratedGradientChain_zero]
      exact (measurable_gradient f).stronglyMeasurable
  | succ j =>
      rw [iteratedGradientChain_succ]
      exact (measurable_fderiv ℝ (iteratedGradientChain f j)).stronglyMeasurable

/-- Every iterated-gradient field of an arbitrary scalar function is almost everywhere strongly
measurable. -/
@[fun_prop]
theorem aestronglyMeasurable_iteratedGradientChain (f : E → ℝ) (j : ℕ) {μ : Measure E} :
    AEStronglyMeasurable (iteratedGradientChain f j) μ :=
  (stronglyMeasurable_iteratedGradientChain f j).aestronglyMeasurable

end TauCeti
