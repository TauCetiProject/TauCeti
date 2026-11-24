/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Stieltjes
public import TauCeti.Probability.Kernel.Finite
public import Mathlib.Probability.Process.Adapted

/-!
# Adapted random Stieltjes measures and integrals

An adapted increasing right-continuous real-valued process gives a random Stieltjes measure. Its
restriction to `(a,t]` is measurable for the original sigma algebra at time `t`. Integrating a
nonnegative progressive process against these measures preserves adaptation, without moment
bounds, completeness or right continuity of the filtration. Infinite integral values are
allowed. The open initial endpoint excludes any initial atom, while terminal jumps are retained.

The time order can be `ℝ` or `ℝ≥0`. The paths are supplied as native Stieltjes functions, so
monotonicity and right continuity hold everywhere; no unproved repair on a future-measurable
null event is used.
These positive random measures are the integrators for the increasing parts of finite-variation
processes.

## References

* P. Protter, *Stochastic Integration and Differential Equations*, second edition, Chapter I.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MeasureTheory

variable {Ω R : Type*} {mΩ : MeasurableSpace Ω}
  [LinearOrder R] [TopologicalSpace R] [OrderTopology R] [CompactIccSpace R]
  [MeasurableSpace R] [BorelSpace R] [SecondCountableTopology R] [DenselyOrdered R]
  {ℱ : Filtration R mΩ} {f : Ω → StieltjesFunction R}

/-- The past restriction of an adapted Stieltjes measure is measurable in the current sigma
algebra. The measure has mass `f ω t - f ω a` on `(a,t]` when `a ≤ t`. -/
theorem Adapted.measurable_restrict_measure_Ioc
    (hf : Adapted ℱ (fun t ω ↦ f ω t)) (a t : R) :
    Measurable[ℱ t] (fun ω ↦ (f ω).measure.restrict (Ioc a t)) :=
  StieltjesFunction.measurable_restrict_measure_Ioc fun _ hu ↦ hf.measurable_le hu.2

/-- The nonnegative Stieltjes integral of a progressive process against an adapted increasing
right-continuous process is adapted. Neither a uniform mass bound nor integrability is needed. -/
theorem IsProgressive.adapted_setLIntegral_measure_stieltjesFunction {H : R → Ω → ℝ≥0∞}
    (hH : IsProgressive ℱ H) (hf : Adapted ℱ (fun t ω ↦ f ω t)) (a : R) :
    Adapted ℱ (fun t ω ↦ ∫⁻ u in Ioc a t, H u ω ∂(f ω).measure) := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  let κ : Kernel Ω R := ⟨fun ω ↦ (f ω).measure.restrict (Ioc a t),
    hf.measurable_restrict_measure_Ioc a t⟩
  have : ∀ ω, IsFiniteMeasure (κ ω) := fun ω ↦ by
    constructor
    simp [κ, StieltjesFunction.measure_Ioc]
  have : IsSFiniteKernel κ := κ.isSFiniteKernel_of_isFiniteMeasure
  have hmeas : Measurable fun p : R × Ω ↦ H (min p.1 t) p.2 := by
    exact (hH t).comp
      (((measurable_fst.min measurable_const).subtype_mk
        (h := fun p ↦ min_le_right p.1 t)).prodMk measurable_snd)
  have h := hmeas.lintegral_kernel_prod_left' (κ := κ)
  convert h using 1
  ext ω
  simp only [κ, Kernel.coe_mk]
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro u hu
  simp only [min_eq_left hu.2]

end MeasureTheory
