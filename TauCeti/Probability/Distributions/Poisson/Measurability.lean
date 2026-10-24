/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic

import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.MeasureTheory.Measure.ProductKernel
/-!
# Parameter measurability for the Poisson distribution

Measurability in the rate lets measurable rate maps produce measurable measure-valued Poisson
families and permits packaging such families as kernels.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace TauCeti.Probability
/-- **The Poisson family is measurable in its rate.**

This permits composition with measurable rate maps and packages the resulting measure-valued
family as a kernel. -/
@[fun_prop] theorem measurable_poissonMeasure : Measurable fun r : ℝ≥0 => poissonMeasure r := by
  simp only [poissonMeasure]
  exact TauCeti.MeasureTheory.measurable_sum_smul_dirac fun n => by fun_prop

/-- A finite product of Poisson laws is measurable jointly in its rate vector. -/
@[fun_prop]
theorem measurable_pi_poissonMeasure {ι : Type*} [Fintype ι] :
    Measurable fun r : ι → ℝ≥0 => Measure.pi (fun i => poissonMeasure (r i)) := by
  let ν (i : ι) (r : ι → ℝ≥0) : ProbabilityMeasure ℕ :=
    ⟨poissonMeasure (r i), inferInstance⟩
  have hν (i : ι) : Measurable (ν i) :=
    (measurable_poissonMeasure.comp (measurable_pi_apply i)).subtype_mk
  exact TauCeti.MeasureTheory.measurable_probabilityMeasure_pi_toMeasure ν hν

/-- The finite product of Poisson laws with rates `p i * Real.toNNReal x` is a measurable
mixing kernel on the real line. -/
@[fun_prop]
theorem measurable_pi_poissonMeasure_mul_toNNReal {ι : Type*} [Fintype ι] (p : ι → ℝ≥0) :
    Measurable fun x : ℝ => Measure.pi (fun i => poissonMeasure (p i * Real.toNNReal x)) :=
  measurable_pi_poissonMeasure.comp (Measurable.of_eval fun _ => by fun_prop)
end TauCeti.Probability
